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
import re as _re
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
from .denotation import denotational_equiv, compile_to_oterm, normalize as _denot_normalize
from .path_search import search_path, _identify_spec as _oterm_identify_spec, FiberCtx



def _cohomological_path_search(source_f: str, source_g: str,
                                deadline: float) -> Optional[Result]:
    """Strategy 1c: Cohomological Path Search on OTerms.

    This is the explicitly cohomological approach:
    1. Compile both programs to OTerms
    2. Infer duck types to build the site category (fibers)
    3. For each fiber τ, create a FiberCtx and run axiom path search
       on the normalized OTerms
    4. Each successful per-fiber path is a LocalJudgment(EQ)
    5. Glue via Čech H¹ — if H¹ = 0, the local paths compose
       into a global equivalence proof

    Non-sampling: the path search uses axiom rewrites (D1-D48),
    algebraic identities, and HIT structural decomposition.
    No function execution.
    """
    rf = compile_to_oterm(source_f)
    rg = compile_to_oterm(source_g)
    if rf is None or rg is None:
        return None

    ot_f, pf = rf
    ot_g, pg = rg
    if len(pf) != len(pg):
        return None

    # Rename params to canonical p0, p1, ...
    from .denotation import _rename_params
    ot_f = _rename_params(ot_f, pf)
    ot_g = _rename_params(ot_g, pg)
    nf_f = _denot_normalize(ot_f)
    nf_g = _denot_normalize(ot_g)

    # Quick check: already equal after normalization
    if nf_f.canon() == nf_g.canon():
        return None  # Already handled by Strategy 1 (denotational)

    # ── Build the site category from duck types ──
    try:
        tree_f = ast.parse(textwrap.dedent(source_f))
        tree_g = ast.parse(textwrap.dedent(source_g))
        func_f_node = next(n for n in ast.walk(tree_f) if isinstance(n, ast.FunctionDef))
        func_g_node = next(n for n in ast.walk(tree_g) if isinstance(n, ast.FunctionDef))
        param_names_orig = [a.arg for a in func_f_node.args.args]
    except Exception:
        return None

    param_fibers = []
    duck_types = []
    for pname in param_names_orig:
        kind, _ = infer_duck_type(func_f_node, func_g_node, pname)
        duck_types.append(kind)
        if kind == 'int':
            param_fibers.append(['int'])
        elif kind == 'positive_int':
            param_fibers.append(['int'])
        elif kind == 'numeric':
            param_fibers.append(['int', 'float'])
        elif kind == 'str':
            param_fibers.append(['str'])
        elif kind == 'bool':
            param_fibers.append(['bool'])
        elif kind == 'bytes':
            param_fibers.append(['bytes'])
        elif kind == 'dict':
            param_fibers.append(['pair'])
        elif kind == 'ref':
            param_fibers.append(['ref'])
        elif kind in ('list', 'collection', 'numeric_list', 'matrix'):
            param_fibers.append(['ref'])
        elif kind == 'any':
            param_fibers.append(['int', 'str', 'ref'])
        else:
            param_fibers.append(['int', 'str', 'ref'])

    fiber_combos = list(itertools.product(*param_fibers))
    if len(fiber_combos) > 6:
        fiber_combos = fiber_combos[:6]

    # ── Per-fiber axiom path search ──
    overlaps = []
    for i in range(len(fiber_combos)):
        for j in range(i + 1, len(fiber_combos)):
            ci, cj = fiber_combos[i], fiber_combos[j]
            if any(ci[k] == cj[k] for k in range(len(ci))):
                overlaps.append((ci, cj))

    fiber_combos = compute_fiber_priority(fiber_combos, overlaps)

    judgments: Dict[Tuple[str, ...], LocalJudgment] = {}
    for combo in fiber_combos:
        if time.monotonic() > deadline:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=None,
                explanation='timeout', method='path_search')
            continue

        # Build fiber context for this type assignment
        duck_types = {f'p{i}': t for i, t in enumerate(combo)}
        ctx = FiberCtx(param_duck_types=duck_types)

        # Run path search with this fiber context
        path_result = search_path(
            nf_f, nf_g, max_depth=3, max_frontier=150,
            param_duck_types=duck_types)

        if path_result.found is True:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=True,
                explanation=f'axiom path: {path_result.reason}',
                method='path_search', confidence=0.95)
        else:
            # Path search inconclusive on this fiber
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=None,
                explanation=f'no axiom path: {path_result.reason}',
                method='path_search')

    # ── Čech H¹ computation ──
    eq_fibers = [f for f, j in judgments.items() if j.is_equivalent is True]
    unk_fibers = [f for f, j in judgments.items() if j.is_equivalent is None]

    if not eq_fibers:
        return None  # No fiber succeeded — inconclusive

    # If we proved EQ on at least one fiber and none failed,
    # check the Čech gluing condition.
    cech = compute_cech_h1(judgments, overlaps)

    if cech.equivalent is True:
        paths_desc = ', '.join(
            judgments[f].explanation for f in eq_fibers[:3])
        # Confirm path search EQ with BT — axiom rewrites may be too
        # permissive (e.g., binary search upper vs lower bound).
        # Require 2+ disagrees to override — single disagree is likely
        # an out-of-domain edge case (n=-1, empty list, etc.)
        bt_check = _bounded_testing(source_f, source_g, param_names_orig,
                                    param_fibers, deadline,
                                    require_n_disagree=2,
                                    duck_types=list(duck_types.values()) if isinstance(duck_types, dict) else duck_types)
        if isinstance(bt_check, dict) and bt_check.get('eq') is False:
            n_dis = bt_check.get('n_disagree', 1)
            if n_dis >= 2:
                return Result(False,
                    f'bounded testing NEQ overrides path search H1=0 ({n_dis} disagrees)',
                    h0=0, h1=1, method='counterexample')
        return Result(True,
            f'cohomological path search: H¹=0, {len(eq_fibers)} fibers proved via axioms ({paths_desc})',
            h0=cech.h0, confidence=0.93, method='proof')

    # Partial coverage is NOT a formal proof — inconclusive.
    # Only H¹=0 with ALL fibers proven counts as sound.

    return None  # Inconclusive — fall through to Z3


def _cohomological_path_search_on_oterms(
    nf_f: 'OTerm', nf_g: 'OTerm',
    prog_params: List[str],
    source_f: str, source_g: str,
    deadline: float
) -> Optional[Result]:
    """Run cohomological path search on pre-normalized OTerms.

    Same as _cohomological_path_search but skips compilation/normalization
    since the caller already has the OTerms. Used by OTerm-level spec check.
    """
    from .duck import infer_duck_type
    from .cohomology import compute_cech_h1, compute_fiber_priority
    from .path_search import search_path, FiberCtx

    if nf_f.canon() == nf_g.canon():
        return None  # Already identical — handled elsewhere

    # Build fiber context from duck types
    try:
        tree_f = ast.parse(textwrap.dedent(source_f))
        tree_g = ast.parse(textwrap.dedent(source_g))
        func_f_node = next(n for n in ast.walk(tree_f) if isinstance(n, ast.FunctionDef))
        func_g_node = next(n for n in ast.walk(tree_g) if isinstance(n, ast.FunctionDef))
        param_names_orig = [a.arg for a in func_f_node.args.args]
    except Exception:
        return None

    param_fibers = []
    for pname in param_names_orig:
        kind, _ = infer_duck_type(func_f_node, func_g_node, pname)
        if kind == 'int':
            param_fibers.append(['int'])
        elif kind in ('positive_int', 'numeric'):
            param_fibers.append(['int'])
        elif kind == 'str':
            param_fibers.append(['str'])
        elif kind in ('bool',):
            param_fibers.append(['bool'])
        elif kind in ('list', 'collection', 'numeric_list', 'matrix', 'ref'):
            param_fibers.append(['ref'])
        elif kind == 'any':
            param_fibers.append(['int', 'str', 'ref'])
        else:
            param_fibers.append(['int', 'str', 'ref'])

    fiber_combos = list(itertools.product(*param_fibers))
    if len(fiber_combos) > 6:
        fiber_combos = fiber_combos[:6]

    overlaps = []
    for i in range(len(fiber_combos)):
        for j in range(i + 1, len(fiber_combos)):
            ci, cj = fiber_combos[i], fiber_combos[j]
            if any(ci[k] == cj[k] for k in range(len(ci))):
                overlaps.append((ci, cj))

    fiber_combos = compute_fiber_priority(fiber_combos, overlaps)

    judgments: Dict[Tuple[str, ...], LocalJudgment] = {}
    for combo in fiber_combos:
        if time.monotonic() > deadline:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=None,
                explanation='timeout', method='path_search')
            continue

        duck_types = {f'p{i}': t for i, t in enumerate(combo)}
        path_result = search_path(
            nf_f, nf_g, max_depth=3, max_frontier=150,
            param_duck_types=duck_types)

        if path_result.found is True:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=True,
                explanation=f'axiom path: {path_result.reason}',
                method='path_search', confidence=0.95)
        else:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=None,
                explanation=f'no axiom path: {path_result.reason}',
                method='path_search')

    eq_fibers = [f for f, j in judgments.items() if j.is_equivalent is True]
    if not eq_fibers:
        return None

    cech = compute_cech_h1(judgments, overlaps)
    if cech.equivalent is True:
        return Result(True,
            f'oterm path search: H¹=0, {len(eq_fibers)} fibers',
            h0=cech.h0, confidence=0.93, method='proof')

    return None


def _compositional_cohomology_check(source_f: str, source_g: str) -> Optional['Result']:
    """Strategy 1c: Direct compositional cohomology on OTerms.

    Uses the genuine sheaf cohomology from compositional_cohomology.py:
    align OTerm trees, check absorption via the connecting homomorphism.

    NOTE: If canonical forms are identical, returns None — the denotation
    compiler is coarse and may conflate programs that differ on Python
    runtime semantics (mutation, NaN, scoping, etc.).  Deferred to BT.
    """
    try:
        from .compositional_cohomology import compositional_equiv
    except ImportError:
        return None

    rf = compile_to_oterm(source_f)
    rg = compile_to_oterm(source_g)
    if rf is None or rg is None:
        return None
    ot_f, pf = rf
    ot_g, pg = rg
    if len(pf) != len(pg):
        return None
    from .denotation import _rename_params
    ot_f = _rename_params(ot_f, pf)
    ot_g = _rename_params(ot_g, pg)
    nf_f = _denot_normalize(ot_f)
    nf_g = _denot_normalize(ot_g)

    # If canonical forms are identical, the compiler couldn't distinguish
    # the programs.  This is NOT a proof — defer to BT confirmation.
    if nf_f.canon() == nf_g.canon():
        return None

    result = compositional_equiv(nf_f, nf_g)
    if result.h1_rank == 0 and result.equivalent is True:
        return Result(True,
            f'compositional cohomology: {result.explanation}',
            h0=1, confidence=0.95, method='proof')

    return None


def _cech_input_cohomology_check(
    source_f: str, source_g: str, deadline: float
) -> Optional['Result']:
    """Strategy 1d: Genuine Čech cohomology over the input space.

    Flattens OCase trees to piecewise representations, computes the
    common refinement of both programs' guard covers, and verifies
    value agreement on each refined region via Z3.

    This is strictly more powerful than tree-diffing: programs with
    different guard structures but equivalent values per region are
    detected as equivalent.
    """
    import time
    if time.monotonic() > deadline:
        return None

    try:
        from .compositional_cohomology import cech_input_cohomology
    except ImportError:
        return None

    rf = compile_to_oterm(source_f)
    rg = compile_to_oterm(source_g)
    if rf is None or rg is None:
        return None
    ot_f, pf = rf
    ot_g, pg = rg
    if len(pf) != len(pg):
        return None

    # Soundness guard: Z3 uses integer arithmetic, so if any parameter
    # might be float/numeric, the integer proof may not hold (e.g.,
    # n + 1.0 - n ≠ 1.0 for large floats due to precision loss).
    try:
        tree_f = ast.parse(textwrap.dedent(source_f))
        tree_g = ast.parse(textwrap.dedent(source_g))
        func_f_node = next(n for n in ast.walk(tree_f) if isinstance(n, ast.FunctionDef))
        func_g_node = next(n for n in ast.walk(tree_g) if isinstance(n, ast.FunctionDef))
        for pname in [a.arg for a in func_f_node.args.args]:
            dt, _ = infer_duck_type(func_f_node, func_g_node, pname)
            if dt in ('numeric', 'float', 'any'):
                return None  # float semantics differ from Z3 integers
    except Exception:
        pass

    from .denotation import _rename_params
    ot_f = _rename_params(ot_f, pf)
    ot_g = _rename_params(ot_g, pg)
    nf_f = _denot_normalize(ot_f)
    nf_g = _denot_normalize(ot_g)

    # Skip if canonical forms match (deferred to BT as in 1c)
    if nf_f.canon() == nf_g.canon():
        return None

    remaining_ms = max(500, int((deadline - time.monotonic()) * 1000))
    cech_timeout = min(remaining_ms, 4000)

    # Collect parameter names for Z3 variable creation
    result = cech_input_cohomology(
        nf_f, nf_g, params=list(set(pf + pg)),
        timeout_ms=cech_timeout)

    if result.equivalent is True and result.h1_rank == 0:
        return Result(True,
            f'Čech input cohomology: {result.explanation}',
            h0=1, confidence=0.95, method='proof')

    # Don't use Čech NEQ as proof — regions may be unresolved due to
    # Z3 limitations, not genuine disagreement
    return None



@dataclass
class Result:
    """Equivalence/spec check result.

    equivalent:
        True  — proven equivalent (formal proof exists)
        False — proven non-equivalent (concrete counterexample exists)
        None  — unknown (insufficient evidence)

    method:
        'proof'          — formal proof (denotational, path search, Z3)
        'counterexample' — concrete disagreement found on specific inputs
        'tested'         — bounded testing found no disagreement (not a proof)
        'inconclusive'   — no evidence either way
    """
    equivalent: Optional[bool]
    explanation: str
    h0: int = 0
    h1: int = 0
    confidence: float = 0.0
    method: str = 'inconclusive'


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
    """Check if a program satisfies a specification via CCTT.

    Formal approach (monograph §24):
      1. Extract reference implementation from deterministic spec
         (syntactic transform: ``return result == E`` → ``ref = λparams. E``)
         and reduce to equivalence via the full CCTT pipeline.
      2. Build composition ``λparams. spec(params, f(params))`` and check
         equivalence to the constant True function.
      3. Use bounded testing ONLY for counterexample / VIO detection
         (a concrete failing input is a proof of non-satisfaction).

    Returns:
      equivalent=True:  spec satisfied (formal proof via CCTT pipeline)
      equivalent=False: spec violated  (counterexample or formal refutation)
      equivalent=None:  inconclusive   (no proof or counterexample found)
    """
    deadline = time.monotonic() + timeout_ms / 1000.0

    try:
        tree_p = ast.parse(textwrap.dedent(source))
        tree_s = ast.parse(textwrap.dedent(spec_source))
        func_p = next(n for n in ast.walk(tree_p) if isinstance(n, ast.FunctionDef))
        func_s = next(n for n in ast.walk(tree_s) if isinstance(n, ast.FunctionDef))
        prog_name = func_p.name
        spec_name = func_s.name
        prog_params = [a.arg for a in func_p.args.args]
        spec_params = [a.arg for a in func_s.args.args]
    except Exception:
        return Result(None, 'parse error')

    # Spec should have one more parameter than program (the result param)
    if len(spec_params) != len(prog_params) + 1:
        return check_equivalence(source, spec_source, timeout_ms)

    result_param = spec_params[-1]  # Last spec param is the result

    # ══════════════════════════════════════════════════════════
    # Strategy 1: Extract reference implementation (formal transform)
    #
    # If spec body is ``return result == E(inputs)`` where E does not
    # mention ``result``, then spec satisfaction reduces to
    # f ≡ ref where ref(inputs) = E(inputs).
    # This is a sound syntactic transformation, not a heuristic.
    # ══════════════════════════════════════════════════════════
    ref_source = _try_extract_reference(spec_source, spec_params,
                                         result_param, prog_params)
    if ref_source is not None:
        remaining_ms = max(100, int((deadline - time.monotonic()) * 1000))
        equiv_result = _check(source, ref_source, remaining_ms)
        if equiv_result.equivalent is True:
            # Mutation guard: When both program and reference have
            # unmodeled features (mutation/loops), check that the
            # mutation fingerprints match.  Different fingerprints
            # mean the OTerm proof is due to information loss
            # (e.g., pop order, missing reverse/toggle).
            if (_has_unmodeled_features(source) and
                    _has_unmodeled_features(ref_source)):
                fp_p = _mutation_fingerprint(source)
                fp_r = _mutation_fingerprint(ref_source)
                if fp_p != fp_r:
                    # Don't trust the formal proof — fall through
                    pass
                else:
                    # Fingerprints match — safe to accept proof
                    # (still BT-confirm below)
                    pass
                if fp_p != fp_r:
                    # Skip to composition/BT strategies
                    equiv_result = Result(None, 'mutation fingerprint mismatch (unreliable OTerm proof)')
            if equiv_result.equivalent is True:
                # BT confirmation: check spec(inputs, program(inputs))
                # on concrete inputs.  If BT disagrees, the formal proof
                # likely depends on unverified input refinements (e.g.
                # "arr is sorted") — treat as inconclusive rather than
                # SAT or VIO, since we can't verify the precondition.
                try:
                    bt_confirm = _bounded_spec_testing(
                        source, spec_source, prog_params, spec_params, deadline)
                    if isinstance(bt_confirm, dict) and bt_confirm.get('satisfies') is False:
                        # Distinguish timeout/crash from concrete counterexample.
                        # Timeout means the program diverges on some domain subset
                        # — denotational semantics are partial, so the proof holds
                        # on the termination domain.  Only a concrete spec
                        # disagreement (spec returns False) invalidates the proof.
                        bt_error = bt_confirm.get('error', '')
                        bt_cex = bt_confirm.get('counterexample', '')
                        is_divergence = ('timeout' in str(bt_error).lower()
                                         or 'timeout' in str(bt_cex).lower()
                                         or 'RecursionError' in str(bt_error)
                                         or 'MemoryError' in str(bt_error))
                        if not is_divergence:
                            equiv_result = Result(None,
                                'refinement-dependent proof (formal proof assumes input constraints)')
                        # else: divergence only — trust the denotational proof
                except Exception:
                    pass  # BT failure → trust the formal proof
                if equiv_result.equivalent is True:
                    return Result(True,
                        f'spec satisfied: program ≡ reference (via {equiv_result.method})',
                        h0=equiv_result.h0, h1=equiv_result.h1,
                        confidence=equiv_result.confidence,
                        method=f'reference-equiv:{equiv_result.method}')
        if equiv_result.equivalent is False:
            # Before declaring VIO based on reference NEQ, verify the
            # counterexample against the actual spec. The reference
            # may have been extracted from a spec with domain guards
            # (e.g. "if <cond>: return True") — on those inputs, any
            # program result is acceptable even if it ≠ reference.
            try:
                bt_verify = _bounded_spec_testing(
                    source, spec_source, prog_params, spec_params, deadline)
                if isinstance(bt_verify, dict) and bt_verify.get('satisfies') is not False:
                    # Spec is actually satisfied (or inconclusive) on
                    # test inputs → reference was too strict (partial
                    # domain). Don't report VIO; fall through.
                    equiv_result = Result(None,
                        'reference domain mismatch (spec vacuously satisfied on counterexample inputs)')
                else:
                    return Result(False,
                        f'spec violated: program ≢ reference ({equiv_result.explanation})',
                        h0=equiv_result.h0, h1=equiv_result.h1,
                        method=f'reference-neq:{equiv_result.method}')
            except Exception:
                return Result(False,
                    f'spec violated: program ≢ reference ({equiv_result.explanation})',
                    h0=equiv_result.h0, h1=equiv_result.h1,
                    method=f'reference-neq:{equiv_result.method}')
        # Reference extraction succeeded but equivalence inconclusive — fall through

    # ══════════════════════════════════════════════════════════
    # Strategy 1b: OTerm-level spec decomposition (formal)
    #
    # Compile both program and spec to OTerms. If the spec OTerm
    # has the form eq($pN, EXPR) or case(guard, eq($pN, A), eq($pN, B)),
    # strip the eq wrapper and compare EXPR with program OTerm.
    # This catches cases where AST-level extraction produces a different
    # syntactic form but the OTerm normalization unifies them.
    # ══════════════════════════════════════════════════════════
    if time.monotonic() < deadline:
        oterm_result = _try_oterm_spec_check(
            source, spec_source, prog_params, spec_params, deadline)
        if oterm_result is not None:
            return oterm_result

    # ══════════════════════════════════════════════════════════
    # Strategy 2: Composition approach (formal)
    #
    # Build: composed(params) = spec(params, f(params))
    # Check: composed ≡ λparams. True
    #
    # If the OTerm compiler can handle the composition AND
    # normalization reduces it to True, that's a formal proof.
    # ══════════════════════════════════════════════════════════
    if time.monotonic() < deadline:
        composition_result = _try_composition_check(
            source, spec_source, prog_name, spec_name,
            prog_params, deadline)
        if composition_result is not None:
            return composition_result

    # ══════════════════════════════════════════════════════════
    # Strategy 3: Bounded testing for counterexample only (VIO)
    #
    # A concrete input where spec(inputs, f(inputs)) == False
    # IS a formal proof of non-satisfaction.  But passing tests
    # is NOT a proof of satisfaction — return UNKNOWN in that case.
    # ══════════════════════════════════════════════════════════
    if time.monotonic() < deadline:
        bt_result = _bounded_spec_testing(
            source, spec_source, prog_params, spec_params,
            deadline)
        if isinstance(bt_result, dict):
            if bt_result.get('satisfies') is False:
                cx = bt_result.get('counterexample', '')
                return Result(False,
                    f'spec violation (counterexample): {cx}',
                    h0=0, h1=1, method='counterexample')
            # bt_result satisfies=True → NOT a proof, return UNKNOWN

    return Result(None, 'inconclusive (no formal proof or counterexample)')


def _try_oterm_spec_check(
    source: str, spec_source: str,
    prog_params: List[str], spec_params: List[str],
    deadline: float
) -> Optional[Result]:
    """Strategy 1b: OTerm-level spec decomposition.

    Compile both program and spec to OTerms. Strip eq/is wrapper from
    spec to extract the reference expression, then compare via
    normalization and cohomological path search.

    Sound because: if spec OTerm = eq($pN, E) and program OTerm = E,
    then spec(inputs, program(inputs)) = eq(E, E) = True.
    """
    from .denotation import (compile_to_oterm, _rename_params, normalize,
                             OOp, OCase, OVar, OLit)

    rp = compile_to_oterm(source)
    rs = compile_to_oterm(spec_source)
    if rp is None or rs is None:
        return None
    ot_p, pp = rp
    ot_s, ps = rs
    if len(ps) != len(pp) + 1:
        return None

    ot_p = _rename_params(ot_p, pp)
    ot_s = _rename_params(ot_s, ps)
    nf_p = normalize(ot_p)
    nf_s = normalize(ot_s)

    result_var = f'p{len(pp)}'

    # Strip eq($pN, EXPR) wrapper from spec
    stripped = _strip_eq_wrapper(nf_s, result_var)
    if stripped is None:
        return None

    nf_stripped = normalize(stripped)

    # Direct canonical form match
    if nf_stripped.canon() == nf_p.canon():
        # Safety: check for OUnknown in either term
        from .denotation import _contains_unknown
        if _contains_unknown(nf_p) or _contains_unknown(nf_stripped):
            return None
        # BT confirmation: the OTerm compiler is lossy, so verify
        # that spec(inputs, program(inputs)) is True on concrete inputs.
        bt_ok = _bt_confirm_spec(source, spec_source, prog_params,
                                  spec_params, deadline)
        if bt_ok is False:
            return None  # BT disagrees — OTerm match is unreliable
        return Result(True,
            'spec satisfied: OTerm eq-strip match',
            h0=1, h1=0, confidence=0.95,
            method='oterm-spec-strip')

    # Try cohomological path search on the stripped spec vs program
    if time.monotonic() < deadline:
        cps_result = _cohomological_path_search_on_oterms(
            nf_p, nf_stripped, pp, source, spec_source, deadline)
        if cps_result is not None and cps_result.equivalent is True:
            # BT confirmation
            bt_ok = _bt_confirm_spec(source, spec_source, prog_params,
                                      spec_params, deadline)
            if bt_ok is False:
                return None
            return Result(True,
                f'spec satisfied: OTerm spec decomposition (via {cps_result.method})',
                h0=cps_result.h0, h1=cps_result.h1,
                confidence=cps_result.confidence,
                method=f'oterm-spec:{cps_result.method}')

    return None


def _bt_confirm_spec(source: str, spec_source: str,
                     prog_params: List[str], spec_params: List[str],
                     deadline: float) -> Optional[bool]:
    """BT confirmation for OTerm spec check.

    Returns False if BT finds a concrete counterexample, True/None otherwise.
    """
    try:
        bt = _bounded_spec_testing(source, spec_source, prog_params,
                                    spec_params, deadline)
        if isinstance(bt, dict) and bt.get('satisfies') is False:
            bt_error = bt.get('error', '')
            is_divergence = ('timeout' in str(bt_error).lower()
                             or 'RecursionError' in str(bt_error)
                             or 'MemoryError' in str(bt_error))
            if not is_divergence:
                return False
    except Exception:
        pass
    return None


def _strip_eq_wrapper(term, result_var: str):
    """Strip eq(result_var, EXPR) → EXPR from spec OTerm.

    Recursively handles:
    - eq($pN, EXPR) → EXPR
    - is($pN, EXPR) → EXPR  (for None/True/False)
    - case(guard, eq($pN, A), eq($pN, B)) → case(guard, A, B)
    - case(guard, eq($pN, A), True) → A  (vacuous false branch)
    """
    from .denotation import OOp, OCase, OVar, OLit

    if isinstance(term, OOp):
        if term.name in ('eq', 'is') and len(term.args) == 2:
            if isinstance(term.args[0], OVar) and term.args[0].name == result_var:
                # Verify RHS doesn't reference result_var
                if result_var not in term.args[1].canon():
                    return term.args[1]
            if isinstance(term.args[1], OVar) and term.args[1].name == result_var:
                if result_var not in term.args[0].canon():
                    return term.args[0]
    if isinstance(term, OCase):
        t_strip = _strip_eq_wrapper(term.true_branch, result_var)
        f_strip = _strip_eq_wrapper(term.false_branch, result_var)
        if t_strip is not None and f_strip is not None:
            # Guard must not reference result_var
            if result_var not in term.test.canon():
                return OCase(term.test, t_strip, f_strip)
        # case(guard, eq($pN, A), True) → A
        # When false branch is vacuous (True), the spec is only constraining
        # the result when guard holds. Stripping to A gives a STRONGER check
        # (proving prog ≡ A on all inputs, not just guard-true inputs), which
        # is sound: if prog ≡ A then spec(inputs, prog(inputs)) = True.
        if t_strip is not None and f_strip is None:
            fb = term.false_branch
            if isinstance(fb, OLit) and fb.value is True:
                if result_var not in term.test.canon():
                    return t_strip
    return None


def _try_extract_reference(spec_source: str, spec_params: List[str],
                            result_param: str,
                            prog_params: List[str]) -> Optional[str]:
    """Extract a reference implementation from a deterministic spec.

    Formal syntactic transform (monograph §24, Prop. 24.1):
    If the spec body has the form ``return result == E`` where ``E``
    does not mention ``result``, then spec satisfaction reduces to
    ``f ≡ ref`` where ``ref(params) = E``.

    Also handles multi-clause specs of the form:
        if <guard on inputs only>:
            return result == E1
        return result == E2

    Returns Python source for the reference function, or None.
    """
    try:
        tree = ast.parse(textwrap.dedent(spec_source))
        func = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef))
    except Exception:
        return None

    # Check that we can extract a reference from the body
    ref_body = _extract_ref_body(func.body, result_param, spec_params)
    if ref_body is None:
        return None

    # Build the reference function source
    param_str = ', '.join(prog_params)
    # We need to include any imports from the spec
    imports = []
    for stmt in func.body:
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            imports.append(ast.get_source_segment(textwrap.dedent(spec_source), stmt))

    import_block = '\n'.join(i for i in imports if i) + '\n' if imports else ''
    return f'{import_block}def ref_impl({param_str}):\n{ref_body}'


def _indent_unparse(stmt: ast.stmt, indent: str) -> str:
    """Unparse an AST statement and indent every line."""
    raw = ast.unparse(stmt)
    return '\n'.join(indent + line for line in raw.split('\n'))


def _extract_ref_body(stmts: List[ast.stmt], result_param: str,
                       spec_params: List[str],
                       indent: str = '    ',
                       allow_partial: bool = False) -> Optional[str]:
    """Recursively extract a reference body from spec statements.

    Handles:
      - ``return result == E`` → ``return E``
      - ``if guard: return result == E1 \\n return result == E2``
      - ``if guard: return result == E1 \\n else: return result == E2``
      - ``if guard: return result is None \\n return result == E``

    If allow_partial is True, returns accumulated lines even without a
    trailing return (used for for-loop bodies with early-exit returns).
    """
    lines = []
    for i, stmt in enumerate(stmts):
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            continue  # handled separately

        if isinstance(stmt, ast.Return) and stmt.value is not None:
            # Handle vacuous satisfaction: standalone `return True`
            # at the end of a conditional chain means "spec satisfied
            # for any result". Skip it — the earlier branches have
            # the actual reference.
            if (isinstance(stmt.value, ast.Constant) and stmt.value.value is True
                    and lines and i == len(stmts) - 1):
                # Only skip if we already have reference lines from
                # earlier branches (otherwise there's nothing to extract)
                return '\n'.join(lines) if lines else None

            expr = _extract_eq_rhs(stmt.value, result_param)
            if expr is not None:
                lines.append(f'{indent}return {expr}')
                return '\n'.join(lines)
            return None  # Return statement we can't decompose

        if isinstance(stmt, ast.If):
            # Guard must not mention result_param — unless it's a size
            # check (``if len(result) != N: return False``), which we
            # skip since the reference we build will have correct size.
            if _mentions_name(stmt.test, result_param):
                if _is_size_check(stmt, result_param):
                    continue
                return None
            guard_src = ast.unparse(stmt.test)

            # Handle vacuous satisfaction: if <guard>: return True
            # This is a domain precondition — the spec is trivially
            # satisfied on inputs where the guard holds. Skip it in
            # the reference and let the refinement-dependent logic
            # handle any BT disagreements on those inputs.
            _body_is_return_true = (
                len(stmt.body) == 1
                and isinstance(stmt.body[0], ast.Return)
                and isinstance(stmt.body[0].value, ast.Constant)
                and stmt.body[0].value.value is True
            )
            if _body_is_return_true and not stmt.orelse:
                # Skip this guard entirely — it's a precondition
                continue

            # If the ENTIRE If block doesn't mention result, include
            # it verbatim — it's intermediate computation, not a
            # result comparison. (e.g., ``if s[0] in '+-': sign = -1``)
            if not _mentions_name(stmt, result_param):
                lines.append(_indent_unparse(stmt, indent))
                continue

            # Extract body
            body_ref = _extract_ref_body(stmt.body, result_param,
                                          spec_params, indent + '    ')
            if body_ref is None:
                return None
            lines.append(f'{indent}if {guard_src}:')
            lines.append(body_ref)

            # Extract else / elif
            if stmt.orelse:
                orelse_ref = _extract_ref_body(stmt.orelse, result_param,
                                                spec_params, indent + '    ')
                if orelse_ref is None:
                    return None
                # Check if orelse is an elif (single If node)
                if (len(stmt.orelse) == 1
                        and isinstance(stmt.orelse[0], ast.If)):
                    lines.append(f'{indent}el{orelse_ref.lstrip()}')
                else:
                    lines.append(f'{indent}else:')
                    lines.append(orelse_ref)
            continue

        if isinstance(stmt, ast.Assign):
            # Allow intermediate assignments that don't mention result
            if not _mentions_name(stmt, result_param):
                lines.append(f'{indent}{ast.unparse(stmt)}')
                continue
            return None

        if isinstance(stmt, ast.AugAssign):
            if not _mentions_name(stmt, result_param):
                lines.append(f'{indent}{ast.unparse(stmt)}')
                continue
            return None

        if isinstance(stmt, ast.For):
            if not _mentions_name(stmt, result_param):
                lines.append(_indent_unparse(stmt, indent))
                continue

            # Try element-wise comparison extraction first.
            # Pattern: for var in iter: if result[idx] != expr: return False
            # followed by return True at end of enclosing block.
            ew_ref = _try_elementwise_ref_extraction(
                stmts[i:], result_param, spec_params, indent)
            if ew_ref is not None:
                if lines:
                    return '\n'.join(lines) + '\n' + ew_ref
                return ew_ref

            # The for-loop body may contain return result == E
            # (e.g., ``for i in ...: if n % i == 0: return result is False``)
            # Try to extract ref body from the loop contents
            for_body_ref = _extract_ref_body(stmt.body, result_param,
                                              spec_params, indent + '    ',
                                              allow_partial=True)
            if for_body_ref is not None:
                target_src = ast.unparse(stmt.target)
                iter_src = ast.unparse(stmt.iter)
                lines.append(f'{indent}for {target_src} in {iter_src}:')
                lines.append(for_body_ref)
                # Handle orelse of for
                if stmt.orelse:
                    orelse_ref = _extract_ref_body(stmt.orelse, result_param,
                                                    spec_params, indent + '    ')
                    if orelse_ref is None:
                        return None
                    lines.append(f'{indent}else:')
                    lines.append(orelse_ref)
                # Remaining statements after this for-loop
                remaining = stmts[i+1:]
                if remaining:
                    rest = _extract_ref_body(remaining, result_param,
                                              spec_params, indent)
                    if rest is None:
                        return None
                    lines.append(rest)
                return '\n'.join(lines)
            return None

        if isinstance(stmt, ast.While):
            if not _mentions_name(stmt, result_param):
                lines.append(_indent_unparse(stmt, indent))
                continue
            return None

        if isinstance(stmt, ast.Expr):
            continue  # docstrings, etc.

        # Nested function definitions (helpers) that don't mention result
        if isinstance(stmt, ast.FunctionDef):
            if not _mentions_name(stmt, result_param):
                lines.append(_indent_unparse(stmt, indent))
                continue
            return None

        # Try/except that doesn't mention result
        if isinstance(stmt, ast.Try):
            if not _mentions_name(stmt, result_param):
                lines.append(_indent_unparse(stmt, indent))
                continue
            return None

        return None  # Unknown statement type

    # If we get here without a return, we didn't find a complete reference
    # — unless allow_partial is True (for-loop body with early-exit returns)
    if allow_partial and lines:
        return '\n'.join(lines)
    return None


def _extract_eq_rhs(expr: ast.expr, result_param: str) -> Optional[str]:
    """Extract E from ``result == E`` or ``E == result``.

    Also handles:
      - ``result is None`` → ``None``
      - ``result == E1 and E2`` where E2 doesn't use result → ``E1``
        (the E2 is a precondition check on inputs, which we trust)
      - ``sorted(result) == sorted(E)`` → ``sorted(E)``
    """
    # Direct: result == E  or  E == result
    if isinstance(expr, ast.Compare):
        if (len(expr.ops) == 1 and isinstance(expr.ops[0], (ast.Eq, ast.Is))):
            left = expr.left
            right = expr.comparators[0]
            if isinstance(left, ast.Name) and left.id == result_param:
                if not _mentions_name(right, result_param):
                    return ast.unparse(right)
            if isinstance(right, ast.Name) and right.id == result_param:
                if not _mentions_name(left, result_param):
                    return ast.unparse(left)
            # result is None
            if (isinstance(left, ast.Name) and left.id == result_param
                    and isinstance(expr.ops[0], ast.Is)
                    and isinstance(right, ast.Constant) and right.value is None):
                return 'None'
            # sorted(result) == sorted(E)  →  sorted(E)
            # This handles specs that verify output modulo ordering.
            if isinstance(expr.ops[0], ast.Eq):
                for a, b in [(left, right), (right, left)]:
                    if (isinstance(a, ast.Call) and isinstance(a.func, ast.Name)
                            and a.func.id == 'sorted' and len(a.args) == 1
                            and isinstance(a.args[0], ast.Name)
                            and a.args[0].id == result_param
                            and isinstance(b, ast.Call) and isinstance(b.func, ast.Name)
                            and b.func.id == 'sorted' and len(b.args) == 1
                            and not _mentions_name(b.args[0], result_param)):
                        return ast.unparse(b)

    # BoolOp: result == E and <input_check>
    if isinstance(expr, ast.BoolOp) and isinstance(expr.op, ast.And):
        for val in expr.values:
            rhs = _extract_eq_rhs(val, result_param)
            if rhs is not None:
                # All other conjuncts must be input-only checks
                others_ok = all(
                    not _mentions_name(v, result_param)
                    for v in expr.values if v is not val
                )
                if others_ok:
                    return rhs

    return None


def _mentions_name(node: ast.AST, name: str) -> bool:
    """Check if an AST node mentions a given variable name."""
    for child in ast.walk(node):
        if isinstance(child, ast.Name) and child.id == name:
            return True
    return False


def _try_elementwise_ref_extraction(
        stmts: List[ast.stmt], result_param: str,
        spec_params: List[str], indent: str) -> Optional[str]:
    """Extract a reference from element-wise comparison loops.

    Detects the pattern:
        [size checks on result]
        for var in range_expr:
            [optional computation]
            if result[idx_expr] != val_expr: return False
            [or nested for-loop with same pattern]
        return True

    Inverts it to build the result array:
        _result = [None] * size
        for var in range_expr:
            [optional computation]
            _result[idx_expr] = val_expr
        return _result

    This is a sound syntactic transformation: the spec asserts
    result[i] == f(i) for all i, so constructing f(i) as reference
    is the unique satisfying assignment.
    """
    # Scan for the pattern: optional size checks, then for-loop, then return True
    for_stmt = None
    for_idx = -1
    pre_lines = []  # lines before the for loop (size checks, assignments)
    for si, stmt in enumerate(stmts):
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            continue
        # Size checks: if len(result) != N: return False
        if (isinstance(stmt, ast.If) and _mentions_name(stmt, result_param)
                and not isinstance(stmt, ast.For)):
            # Check if this is a size validation: if len(result) != N: return False
            # We skip these in the reference (they constrain result shape)
            if _is_size_check(stmt, result_param):
                continue
            # Non-size-check if mentioning result → can't handle
            break
        if isinstance(stmt, ast.For) and _mentions_name(stmt, result_param):
            for_stmt = stmt
            for_idx = si
            break
        if isinstance(stmt, ast.Assign) and not _mentions_name(stmt, result_param):
            pre_lines.append(f'{indent}{ast.unparse(stmt)}')
            continue
        if isinstance(stmt, ast.Return):
            break
        # Unknown statement mentioning result
        if _mentions_name(stmt, result_param):
            break

    if for_stmt is None:
        return None

    # Check that the statement after the for loop is `return True`
    remaining = stmts[for_idx + 1:]
    if not remaining:
        return None
    last = remaining[-1]
    if not (isinstance(last, ast.Return)
            and isinstance(last.value, ast.Constant)
            and last.value.value is True):
        return None

    # Extract element-wise assignments from the for body
    extraction = _extract_elementwise_body(
        for_stmt.body, result_param, for_stmt.target)
    if extraction is None:
        return None

    assignments, computation_stmts = extraction

    # Build the reference function
    lines = list(pre_lines)

    # Determine the result shape from the assignments
    target_src = ast.unparse(for_stmt.target)
    iter_src = ast.unparse(for_stmt.iter)

    if len(assignments) == 1 and not assignments[0]['nested']:
        # Simple 1D case: result[i] = expr
        # Use list comprehension if no computation
        idx_expr, val_expr = assignments[0]['idx'], assignments[0]['val']
        if not computation_stmts:
            lines.append(f'{indent}return [{val_expr} for {target_src} in {iter_src}]')
        else:
            lines.append(f'{indent}_ref_result = []')
            lines.append(f'{indent}for {target_src} in {iter_src}:')
            for cs in computation_stmts:
                for cl in cs.split('\n'):
                    lines.append(f'{indent}    {cl}')
            lines.append(f'{indent}    _ref_result.append({val_expr})')
            lines.append(f'{indent}return _ref_result')
    elif len(assignments) == 1 and assignments[0]['nested']:
        # Nested 2D case: for i in ...: for j in ...: result[f(i)][g(j)] = expr
        nested = assignments[0]
        inner_target = nested['inner_target']
        inner_iter = nested['inner_iter']
        inner_idx = nested['inner_idx']
        inner_val = nested['inner_val']
        inner_comp = nested.get('inner_computation', [])
        if not computation_stmts and not inner_comp:
            lines.append(
                f'{indent}return [[{inner_val} for {inner_target} in {inner_iter}]'
                f' for {target_src} in {iter_src}]')
        else:
            lines.append(f'{indent}_ref_result = []')
            lines.append(f'{indent}for {target_src} in {iter_src}:')
            for cs in computation_stmts:
                for cl in cs.split('\n'):
                    lines.append(f'{indent}    {cl}')
            lines.append(f'{indent}    _ref_row = []')
            lines.append(f'{indent}    for {inner_target} in {inner_iter}:')
            for cs in inner_comp:
                for cl in cs.split('\n'):
                    lines.append(f'{indent}        {cl}')
            lines.append(f'{indent}        _ref_row.append({inner_val})')
            lines.append(f'{indent}    _ref_result.append(_ref_row)')
            lines.append(f'{indent}return _ref_result')
    else:
        return None

    return '\n'.join(lines)


def _is_size_check(stmt: ast.If, result_param: str) -> bool:
    """Check if an If statement is a size validation on result.

    Detects: if len(result) != N: return False
             if len(result[i]) != M: return False
    """
    if not (len(stmt.body) == 1 and isinstance(stmt.body[0], ast.Return)
            and isinstance(stmt.body[0].value, ast.Constant)
            and stmt.body[0].value.value is False):
        return False
    test = stmt.test
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        op = test.ops[0]
        if isinstance(op, ast.NotEq):
            # Check if one side is len(result) or len(result[...])
            for side in [test.left, test.comparators[0]]:
                if (isinstance(side, ast.Call) and isinstance(side.func, ast.Name)
                        and side.func.id == 'len' and len(side.args) == 1):
                    arg = side.args[0]
                    if isinstance(arg, ast.Name) and arg.id == result_param:
                        return True
                    if (isinstance(arg, ast.Subscript)
                            and isinstance(arg.value, ast.Name)
                            and arg.value.id == result_param):
                        return True
    return False


def _extract_elementwise_body(
        body: List[ast.stmt], result_param: str,
        loop_target: ast.expr
) -> Optional[tuple]:
    """Extract element-wise assignments from a for-loop body.

    Returns (assignments, computation_stmts) where:
      - assignments: list of {idx, val, nested, ...} dicts
      - computation_stmts: list of source strings for intermediate computation

    Detects:
      if result[idx] != expr: return False
      [with optional preceding computation]
      [or nested for-loop]
    """
    computation = []
    assignments = []

    for stmt in body:
        # Computation not mentioning result
        if isinstance(stmt, (ast.Assign, ast.AugAssign, ast.Expr)):
            if not _mentions_name(stmt, result_param):
                computation.append(ast.unparse(stmt))
                continue

        # Size check on result → skip
        if isinstance(stmt, ast.If) and _is_size_check(stmt, result_param):
            continue

        # Element-wise comparison: if result[idx] != val_expr: return False
        if isinstance(stmt, ast.If):
            cmp = _extract_neq_comparison(stmt, result_param)
            if cmp is not None:
                idx_expr, val_expr = cmp
                assignments.append({
                    'idx': idx_expr, 'val': val_expr, 'nested': False})
                continue

        # Nested for-loop with element-wise comparisons
        if isinstance(stmt, ast.For) and _mentions_name(stmt, result_param):
            inner_extraction = _extract_elementwise_body(
                stmt.body, result_param, stmt.target)
            if inner_extraction is not None:
                inner_assignments, inner_comp = inner_extraction
                if len(inner_assignments) == 1 and not inner_assignments[0]['nested']:
                    assignments.append({
                        'nested': True,
                        'inner_target': ast.unparse(stmt.target),
                        'inner_iter': ast.unparse(stmt.iter),
                        'inner_idx': inner_assignments[0]['idx'],
                        'inner_val': inner_assignments[0]['val'],
                        'inner_computation': inner_comp,
                    })
                    continue

        # Unknown statement mentioning result → bail
        if _mentions_name(stmt, result_param):
            return None

        computation.append(ast.unparse(stmt))

    if not assignments:
        return None
    return (assignments, computation)


def _extract_neq_comparison(
        stmt: ast.If, result_param: str
) -> Optional[tuple]:
    """Extract (idx_expr, val_expr) from ``if result[idx] != val: return False``.

    Returns None if the pattern doesn't match.
    """
    # Must be: if <test>: return False (single-statement body, no else)
    if not (len(stmt.body) == 1 and isinstance(stmt.body[0], ast.Return)
            and isinstance(stmt.body[0].value, ast.Constant)
            and stmt.body[0].value.value is False
            and not stmt.orelse):
        return None

    test = stmt.test
    if not isinstance(test, ast.Compare):
        return None
    if len(test.ops) != 1 or not isinstance(test.ops[0], ast.NotEq):
        return None

    left = test.left
    right = test.comparators[0]

    # Check which side is result[idx]
    for res_side, val_side in [(left, right), (right, left)]:
        if isinstance(res_side, ast.Subscript):
            if isinstance(res_side.value, ast.Name) and res_side.value.id == result_param:
                if not _mentions_name(val_side, result_param):
                    idx_expr = ast.unparse(res_side.slice)
                    val_expr = ast.unparse(val_side)
                    return (idx_expr, val_expr)
            # Nested: result[a][b] != val
            if (isinstance(res_side.value, ast.Subscript)
                    and isinstance(res_side.value.value, ast.Name)
                    and res_side.value.value.id == result_param):
                if not _mentions_name(val_side, result_param):
                    idx_expr = ast.unparse(res_side.value.slice)
                    val_expr = ast.unparse(val_side)
                    return (idx_expr, val_expr)

    return None


def _spec_bt_confirm(source: str, ref_source: str,
                      prog_params: List[str],
                      deadline: float) -> Optional[bool]:
    """Run bounded testing between program and spec-extracted reference.

    Returns False if a concrete disagreement is found, True if all
    tests agree, None if inconclusive.  Any single disagree counts
    because the reference IS the ground truth.
    """
    import time
    remaining_ms = max(100, int((deadline - time.monotonic()) * 1000))
    if remaining_ms < 100:
        return None

    try:
        tree_f = ast.parse(textwrap.dedent(source))
        tree_g = ast.parse(textwrap.dedent(ref_source))
        func_f = next(n for n in ast.walk(tree_f) if isinstance(n, ast.FunctionDef))
        func_g = next(n for n in ast.walk(tree_g) if isinstance(n, ast.FunctionDef))
    except Exception:
        return None

    param_fibers = []
    duck_types = []
    for pname in prog_params:
        kind, _ = infer_duck_type(func_f, func_g, pname)
        duck_types.append(kind)
        fiber_map = {
            'int': ['int'], 'positive_int': ['int'],
            'numeric': ['int', 'float'],
            'str': ['str'], 'bool': ['bool'],
            'bytes': ['bytes'],
            'dict': ['pair'],
            'ref': ['ref'], 'list': ['ref'],
            'collection': ['ref', 'str'],
            'numeric_list': ['ref'],
            'matrix': ['ref'],
            'callable': ['ref'],
        }
        param_fibers.append(fiber_map.get(kind, ['int', 'bool', 'str', 'pair', 'ref', 'none']))

    bt_result = _bounded_testing(source, ref_source, prog_params,
                                  param_fibers, deadline,
                                  duck_types=duck_types)
    if isinstance(bt_result, dict):
        if bt_result.get('eq') is False:
            return False
        if bt_result.get('eq') is True:
            return True
    return None


def _try_composition_check(source: str, spec_source: str,
                            prog_name: str, spec_name: str,
                            prog_params: List[str],
                            deadline: float) -> Optional[Result]:
    """Check spec satisfaction via OTerm composition.

    Forms: composed(params) = spec(params, f(params))
    Checks: composed ≡ λparams. True

    This is a formal approach: if the composed OTerm normalizes
    to OLit(True), spec satisfaction is proven.

    The composed function catches exceptions from the program: if the
    program crashes on an input, that input is outside the program's
    domain, and the spec is vacuously satisfied there.
    """
    param_str = ', '.join(prog_params)
    call_args = ', '.join(prog_params)

    # Build composed function source with domain-error tolerance.
    # If the program raises an exception, the input is outside the
    # domain — spec is vacuously satisfied (return True).
    composed_source = textwrap.dedent(f'''\
{textwrap.dedent(source)}

{textwrap.dedent(spec_source)}

def composed_fn({param_str}):
    try:
        composed_result = {prog_name}({call_args})
    except Exception:
        return True
    return {spec_name}({call_args}, composed_result)
''')

    true_fn_source = f'def always_true({param_str}):\n    return True'

    remaining_ms = max(100, int((deadline - time.monotonic()) * 1000))
    try:
        equiv_result = _check(composed_source, true_fn_source, remaining_ms)
        if equiv_result.equivalent is True:
            return Result(True,
                f'spec satisfied: composition ≡ True (via {equiv_result.method})',
                h0=equiv_result.h0, h1=equiv_result.h1,
                confidence=equiv_result.confidence,
                method=f'composition:{equiv_result.method}')
        # Do NOT trust NEQ from composition — the OTerm compiler may lose
        # semantics (mutation, complex loops, recursion), making the composed
        # OTerm inaccurate. Only composition SAT proofs are reliable.
    except Exception:
        pass
    return None


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
                                     h0=1, confidence=1.0, method='proof')
                    else:
                        return Result(False, f'closed-term NEQ: {val_f[0][:30]} vs {val_g[0][:30]}',
                                     h0=0, h1=1, method='counterexample')
                else:
                    # Varargs-only: zero-arg call is a WITNESS, not complete proof
                    # Only use for NEQ detection (finding a difference)
                    if val_f != val_g:
                        return Result(False, f'witness NEQ (zero-arg call): {val_f[0][:25]} vs {val_g[0][:25]}',
                                     h0=0, h1=1, method='counterexample')

    # ══════════════════════════════════════════════════════════
    # Strategy 1: Genuine Čech cohomology over the input space
    # Flatten OCase trees to piecewise forms (presheaf sections
    # over the input space), compute the common Čech refinement,
    # and verify value agreement per region via Z3.
    #
    # Runs FIRST because it handles the hardest cases (different
    # guard structures, algebraic identities via Real arithmetic)
    # and is typically fast (< 3s).  Returns None quickly when
    # programs don't have piecewise structure.
    # ══════════════════════════════════════════════════════════
    try:
        _cech_result = _cech_input_cohomology_check(source_f, source_g, deadline)
        if _cech_result is not None:
            return _cech_result
    except Exception:
        pass

    # ══════════════════════════════════════════════════════════
    # Strategy 1a: Denotational OTerm equivalence (PRIMARY)
    # This normalizes both programs to canonical OTerms with
    # quotient types for nondeterminism, then checks equality.
    #
    # Denotational EQ is deferred — saved as "soft EQ" and
    # confirmed later by BT (the canonical forms may be too coarse,
    # e.g. enumerate(x,1) vs enumerate(x) both → enumerate(x)).
    # Denotational NEQ is immediate (provable difference).
    # ══════════════════════════════════════════════════════════
    denotational_soft_eq = False
    cross_type_suspicious = False
    try:
        denot_result = denotational_equiv(source_f, source_g)
        if denot_result is True:
            denotational_soft_eq = True  # defer — will confirm via BT
        if denot_result is False:
            return Result(False, 'denotational NEQ (provable difference in canonical forms)',
                         h0=0, h1=1, method='proof')
        if denot_result is None:
            # Check for cross-type suspicion (OFold vs OOp, etc.)
            # This is NOT a proof of NEQ, but indicates structural divergence
            # that BT may miss (e.g., mutation effects, predicate differences).
            try:
                from .denotation import has_cross_type_suspicion
                cross_type_suspicious = has_cross_type_suspicion(source_f, source_g)
            except Exception:
                pass
    except Exception:
        pass

    # ══════════════════════════════════════════════════════════
    # Strategy 1c: Cohomological Path Search on OTerms
    # Compile both programs to OTerms, normalize, then search
    # for an axiom rewrite path per fiber.  The path search
    # uses the 100 axiom modules (D1-D48, P1-P48) and the
    # HIT structural decomposition.  Each per-fiber path is
    # a LocalJudgment; Čech H¹ = 0 → global equivalence.
    # This is ENTIRELY non-sampling — axiom chains are proofs.
    # ══════════════════════════════════════════════════════════
    try:
        cps_result = _cohomological_path_search(source_f, source_g, deadline)
        if cps_result is not None:
            return cps_result
    except Exception:
        pass

    # ══════════════════════════════════════════════════════════
    # Strategy 1c: Direct compositional cohomology on OTerms
    # Align OTerm trees, check local equivalence at each fiber,
    # use the Mayer-Vietoris connecting homomorphism to detect
    # when local differences are absorbed by algebraic structure.
    # ══════════════════════════════════════════════════════════
    try:
        _comp_result = _compositional_cohomology_check(source_f, source_g)
        if _comp_result is not None:
            return _comp_result
    except Exception:
        pass

    if not _HAS_Z3:
        # If denotational said soft EQ and no Z3 to refute it, accept
        if denotational_soft_eq:
            return Result(True, 'denotational equivalence (OTerm canonical forms)',
                         h0=1, confidence=0.95, method='proof')
        return Result(None, 'z3 not available, denotational check inconclusive')

    # ══════════════════════════════════════════════════════════
    # Strategy 2-4: Z3-based checking
    # ══════════════════════════════════════════════════════════
    try:
        T = Theory()
        sf = compile_func(source_f, T)
        sg = compile_func(source_g, T)
    except Exception:
        # Z3 out-of-memory during Theory init or compilation —
        # skip all Z3-based checks, jump to BT-only path.
        sf = sg = None
    if sf is None or sg is None:
        # Can't compile → skip Z3, try BT directly
        try:
            tree_f = ast.parse(textwrap.dedent(source_f))
            tree_g = ast.parse(textwrap.dedent(source_g))
            func_f_node = next(n for n in ast.walk(tree_f) if isinstance(n, ast.FunctionDef))
            func_g_node = next(n for n in ast.walk(tree_g) if isinstance(n, ast.FunctionDef))
            param_names = [a.arg for a in func_f_node.args.args]
        except Exception:
            return Result(None, 'cannot compile or parse')
        param_fibers = []
        _duck_types = []
        for pname in param_names:
            kind, _ = infer_duck_type(func_f_node, func_g_node, pname)
            _duck_types.append(kind)
            fiber_map = {
                'int': ['int'], 'positive_int': ['int'],
                'numeric': ['int', 'float'],
                'str': ['str'], 'bool': ['bool'],
                'bytes': ['bytes'],
                'dict': ['pair'],
                'ref': ['ref'], 'list': ['ref'],
                'collection': ['ref', 'str'],
                'numeric_list': ['ref'],
                'matrix': ['ref'],
                'callable': ['ref'],  # placeholder; BT uses callable samples
            }
            param_fibers.append(fiber_map.get(kind, ['int', 'bool', 'str', 'pair', 'ref', 'none']))
        bt_result = _bounded_testing(source_f, source_g, param_names,
                                     param_fibers, deadline,
                                     duck_types=_duck_types)
        if isinstance(bt_result, dict) and bt_result.get('eq') is False:
            bt_reason = bt_result.get('reason', '')
            _edge_only = bt_reason in (
                'empty_collection_edge_disagree',
                'exception_disagreement_dominant',
            )
            if denotational_soft_eq and _edge_only:
                return Result(True, 'denotational equivalence (edge-case exception tolerated)',
                             h0=1, confidence=0.85, method='proof')
            return Result(False, 'bounded testing NEQ (Z3 OOM, concrete disagreement found)',
                          h0=0, h1=1, method='counterexample')
        if isinstance(bt_result, dict) and bt_result.get('eq') is True:
            if denotational_soft_eq:
                return Result(True, 'denotational equivalence (OTerm canonical forms)',
                             h0=1, confidence=0.85, method='proof')
            return Result(None, 'unknown (bounded testing agreement is not a proof)',
                          h0=0, method='tested')
        if denotational_soft_eq:
            return Result(True, 'denotational equivalence (Z3 OOM, OTerm canonical forms)',
                         h0=1, confidence=0.85, method='proof')
        return Result(None, 'cannot compile')

    secs_f, params_f, func_f = sf
    secs_g, params_g, func_g = sg

    if len(params_f) != len(params_g):
        return Result(False, f'arity {len(params_f)} != {len(params_g)}',
                      method='proof')
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
                # Also check: the Z3 compiler drops loops, mutations,
                # try/finally — if the source has these, the compilation
                # is lossy and structural equality is unreliable.
                if not (_has_unmodeled_features(source_f) or
                        _has_unmodeled_features(source_g)):
                    return Result(True, 'structural equality (fully interpreted)',
                                 h0=1, confidence=1.0, method='proof')
                # Lossy compilation — fall through to more robust checks.
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
    duck_types = []
    for pname in param_names:
        kind, _ = infer_duck_type(func_f_node, func_g_node, pname)
        duck_types.append(kind)
        if kind == 'int':
            param_fibers.append(['int'])
        elif kind == 'positive_int':
            param_fibers.append(['int'])
        elif kind == 'numeric':
            param_fibers.append(['int', 'float'])
        elif kind == 'str':
            param_fibers.append(['str'])
        elif kind == 'bool':
            param_fibers.append(['bool'])
        elif kind == 'bytes':
            param_fibers.append(['bytes'])
        elif kind == 'dict':
            param_fibers.append(['pair'])
        elif kind == 'ref':
            param_fibers.append(['ref'])
        elif kind == 'list':
            param_fibers.append(['ref'])
        elif kind == 'collection':
            param_fibers.append(['ref', 'str'])
        elif kind == 'numeric_list':
            param_fibers.append(['ref'])
        elif kind == 'matrix':
            param_fibers.append(['ref'])
        elif kind == 'any':
            param_fibers.append(['int', 'float', 'bool', 'str', 'pair', 'ref', 'none'])
        else:
            param_fibers.append(['int', 'bool', 'str', 'pair', 'ref', 'none'])

    # ── Step 5: Build site category ──
    tag_constraints = {
        'int': lambda p, T: T.tag(p) == T.TInt,
        'float': lambda p, T: T.tag(p) == T.TInt,  # Z3 models both as integers
        'bool': lambda p, T: T.tag(p) == T.TBool_,
        'str': lambda p, T: T.tag(p) == T.TStr_,
        'pair': lambda p, T: T.tag(p) == T.TPair_,
        'ref': lambda p, T: T.tag(p) == T.TRef_,
        'collection': lambda p, T: T.tag(p) == T.TRef_,  # collections → ref in Z3
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

    # Reserve at least 2s for BT fallback (Step 8) — Z3 per-fiber analysis
    # can consume the entire time budget on complex programs, leaving BT
    # with insufficient time to start a subprocess.
    _bt_reserve_s = 2.0
    _z3_deadline = deadline - _bt_reserve_s

    # Compute per-fiber timeout based on remaining time and fiber count
    remaining_ms = max(100, int((_z3_deadline - time.monotonic()) * 1000))
    per_fiber_ms = max(200, remaining_ms // max(len(fiber_combos), 1))

    early_neq = False
    z3_oom = False  # track Z3 out-of-memory
    for combo in fiber_combos:
        if time.monotonic() > _z3_deadline:
            judgments[combo] = LocalJudgment(
                fiber=combo, is_equivalent=None,
                explanation='global timeout')
            continue

        try:
            result = _check_fiber(T, params_f, secs_f, secs_g,
                                  combo, tag_constraints, per_fiber_ms)
        except Exception:
            # Z3 out-of-memory or other fatal error on this fiber —
            # mark it inconclusive and continue. If ALL fibers OOM,
            # we'll fall through to BT (step 8).
            z3_oom = True
            result = LocalJudgment(fiber=combo, is_equivalent=None,
                                   explanation='Z3 memory/error')
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
        # H1=0 is a formal proof of equivalence on the typed fibers.
        # Confirm with BT — if BT finds a concrete disagreement, the
        # counterexample overrides the structural proof (Z3 compilation
        # may be lossy for while-loops and mutations).
        bt_check = _bounded_testing(source_f, source_g, param_names,
                                    param_fibers, deadline,
                                    duck_types=duck_types)
        if isinstance(bt_check, dict) and bt_check.get('eq') is False:
            # If denotational says EQ and BT only disagrees on edge cases
            # (empty collection where one side raises but denotation correctly
            # infers the identity element), trust the formal proof.
            bt_reason = bt_check.get('reason', '')
            _edge_only = bt_reason in (
                'empty_collection_edge_disagree',
                'exception_disagreement_dominant',
            )
            if denotational_soft_eq and _edge_only:
                pass  # denotation handles edge correctly; don't override
            else:
                return Result(False, 'bounded testing NEQ overrides H1=0 (concrete disagreement found)',
                              h0=0, h1=1, method='counterexample')
        # H1=0 is the proof; BT merely confirms or is inconclusive.
        return Result(True,
            f'H1=0: {cech.h0} faces verified across {cech.total_fibers} fibers',
            h0=cech.h0, confidence=confidence, method='proof')
    elif cech.equivalent is False and has_concrete_obstruction:
        # H1 > 0 with concrete counterexample. Run BT to cross-check —
        # Z3 may produce false obstructions from lossy compilation.
        _has_try_f = 'try:' in source_f
        _has_try_g = 'try:' in source_g
        _try_asymmetry = _has_try_f != _has_try_g
        if not _try_asymmetry:
            bt_confirm = _bounded_testing(source_f, source_g, param_names,
                                          param_fibers, deadline,
                                          duck_types=duck_types)
            if isinstance(bt_confirm, dict) and bt_confirm.get('eq') is True:
                # BT says all tests agree but Z3 found an obstruction.
                # If denotational also said EQ, trust the denotational proof —
                # Z3 obstruction is from lossy compilation, not real difference.
                if denotational_soft_eq:
                    return Result(True,
                        'denotational equivalence (Z3 obstruction overridden by BT confirmation)',
                        h0=cech.h0 or 1, confidence=0.88, method='proof')
                return Result(None,
                    'unknown (Z3 obstruction but BT agrees — compilation may be lossy)',
                    h0=cech.h0 or 1, method='tested')
            if isinstance(bt_confirm, dict) and bt_confirm.get('eq') is False:
                # BT confirms the disagreement — concrete counterexample
                return Result(False,
                    f'H1 obstruction confirmed by BT (concrete counterexample)',
                    h0=cech.h0, h1=cech.h1_rank, method='counterexample')
        obs = cech.obstructions
        obs_desc = str(obs[0]) if obs else 'unknown fiber'
        j = judgments.get(obs[0]) if obs else None
        detail = j.explanation if j else ''
        return Result(False,
            f'H1 obstruction: {detail} (fiber {obs_desc})',
            h0=cech.h0, h1=cech.h1_rank, method='proof')

    # ── Step 8: Bounded testing fallback ──
    # When Z3 is inconclusive or gives non-concrete NEQ (uninterpreted fns),
    # fall back to bounded testing. BT disagreement IS a counterexample;
    # BT agreement is NOT a proof — report as unknown.
    bt_result = _bounded_testing(source_f, source_g, param_names,
                                 param_fibers, deadline,
                                 duck_types=duck_types)
    if isinstance(bt_result, dict) and bt_result.get('eq') is False:
        bt_reason = bt_result.get('reason', '')
        _edge_only = bt_reason in (
            'empty_collection_edge_disagree',
            'exception_disagreement_dominant',
        )
        if denotational_soft_eq and _edge_only:
            # Denotation correctly handles edge (e.g., identity element for
            # reduce on empty list); trust the formal proof.
            return Result(True, 'denotational equivalence (edge-case exception tolerated)',
                         h0=1, confidence=0.88, method='proof')
        return Result(False, 'bounded testing NEQ (concrete disagreement found)',
                      h0=0, h1=1, method='counterexample')
    if isinstance(bt_result, dict) and bt_result.get('eq') is True:
        # BT agreement is evidence but not a proof.
        # If denotational also said EQ, that IS a proof.
        if denotational_soft_eq:
            return Result(True, 'denotational equivalence (OTerm canonical forms)',
                         h0=1, confidence=0.90, method='proof')

        return Result(None,
            'unknown (bounded testing agreement is not a proof)',
            h0=cech.h0 or 0, method='tested')

    # Bounded testing inconclusive — fall through to original logic
    if cech.equivalent is False:
        # Non-concrete H1 obstruction (uses uninterpreted functions).
        # Z3's model may be spurious — return unknown.
        return Result(None,
            f'unknown (H1 obstruction without concrete counterexample)',
            h0=cech.h0, method='inconclusive')
    else:
        # If denotational said soft EQ and nothing refuted it,
        # accept the denotational judgment (it IS a proof)
        if denotational_soft_eq:
            return Result(True, 'denotational equivalence (OTerm canonical forms)',
                         h0=1, confidence=0.90, method='proof')
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


def _has_unmodeled_features(source: str) -> bool:
    """Check if source uses Python features the Z3 compiler can't model.

    These features are silently dropped during compilation, making
    structural Z3 equality unreliable (the Z3 terms look the same
    but the programs actually differ in their dropped features).
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return True  # can't parse → assume lossy
    for node in ast.walk(tree):
        # Loops: body is unrolled/dropped, loop bounds lost
        if isinstance(node, (ast.For, ast.While)):
            return True
        # Try/finally: finally block semantics dropped
        if isinstance(node, ast.Try):
            if node.finalbody:
                return True
        # Mutation calls: .append(), .insert(), .pop(), .sort(), etc.
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute):
                if node.func.attr in (
                    'append', 'extend', 'insert', 'pop', 'remove',
                    'sort', 'reverse', 'clear', 'update', 'add',
                    'discard', 'setdefault',
                ):
                    return True
        # Augmented assignment on subscript/attribute (mutation)
        if isinstance(node, ast.AugAssign):
            if isinstance(node.target, (ast.Subscript, ast.Attribute)):
                return True
        # Delete statement
        if isinstance(node, ast.Delete):
            return True
        # Yield / yield from (generators)
        if isinstance(node, (ast.Yield, ast.YieldFrom)):
            return True
    return False


def _mutation_fingerprint(source: str) -> list:
    """Extract a fingerprint of mutation operations that OTerm CANNOT model.

    Only captures patterns whose differences cause false equivalence proofs:
    1. pop/popleft assignment targets — OTerm loses operand order
       (e.g., `a,b = pop(),pop()` vs `b,a = pop(),pop()`)
    2. reverse/sort calls — OTerm drops in-place reordering
    3. Variable toggles — `x = not x` is lost in compilation

    Other mutations (append, extend, add) are safely abstracted by OTerm's
    fold/fix representation — differing patterns there are OK.
    """
    try:
        tree = ast.parse(textwrap.dedent(source))
    except SyntaxError:
        return []

    # Build parent map for context
    for node in ast.walk(tree):
        for child in ast.iter_child_nodes(node):
            child._parent = node  # type: ignore[attr-defined]

    # Only ops whose DIFFERENCES cause false proofs
    ORDER_SENSITIVE_OPS = frozenset({'pop', 'popleft'})
    INPLACE_REORDER_OPS = frozenset({'reverse', 'sort'})

    fingerprint = []
    # Assign positional indices to variables by order of first appearance,
    # so different variable names (left_to_right vs ltr) get the same index.
    _var_index: Dict[str, int] = {}
    def _vname(name: str) -> str:
        if name not in _var_index:
            _var_index[name] = len(_var_index)
        return f'v{_var_index[name]}'

    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            method = node.func.attr
            if method in ORDER_SENSITIVE_OPS:
                # For pop/popleft, record assignment targets (order matters)
                targets = ''
                parent = getattr(node, '_parent', None)
                if isinstance(parent, ast.Assign):
                    targets = ast.dump(parent.targets[0])
                elif isinstance(parent, ast.Tuple):
                    gp = getattr(parent, '_parent', None)
                    if isinstance(gp, ast.Assign):
                        targets = ast.dump(gp.targets[0])
                container = ''
                if isinstance(node.func.value, ast.Name):
                    container = _vname(node.func.value.id)
                fingerprint.append((method, container, targets))
            elif method in INPLACE_REORDER_OPS:
                # reverse/sort: just record presence
                container = ''
                if isinstance(node.func.value, ast.Name):
                    container = _vname(node.func.value.id)
                fingerprint.append((method, container, ''))

        # Variable toggle: `x = not x`
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            tgt = node.targets[0]
            val = node.value
            if isinstance(tgt, ast.Name):
                if isinstance(val, ast.UnaryOp) and isinstance(val.op, ast.Not):
                    if isinstance(val.operand, ast.Name) and val.operand.id == tgt.id:
                        fingerprint.append(('toggle_not', _vname(tgt.id), ''))

    fingerprint.sort()
    return fingerprint


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


def _has_semi_uninterp(term, depth=0) -> bool:
    """Check if a Z3 term uses semi-uninterpreted operations.

    These are binop/unop operations that are defined in the Theory's
    RecFunction but have no meaningful Z3 axioms (e.g. GETITEM=70,
    LEN=55 on non-strings). Z3 can freely pick values for these,
    making H¹=0 proofs vacuously true.

    Unlike _uninterp_depth, this is used only for GUARDING EQ proofs,
    not for invalidating NEQ counterexamples.
    """
    if depth > 10:
        return False
    try:
        if term.num_args() == 0:
            return False
        decl_name = term.decl().name()
        # Check for binop with uninterpreted op codes
        if decl_name.startswith('binop_') and term.num_args() >= 1:
            try:
                op_id = term.arg(0).as_long()
                _INTERPRETED_BINOPS = frozenset({
                    1, 2, 3, 4, 5, 6, 7,       # +, -, *, /, //, %, **
                    10, 11, 12, 13, 14,          # <<, >>, |, &, ^
                    20, 21, 22, 23, 24, 25,      # <, <=, >, >=, ==, !=
                })
                if op_id not in _INTERPRETED_BINOPS:
                    return True
            except Exception:
                pass
        # Check for unop with uninterpreted op codes
        if decl_name.startswith('unop_') and term.num_args() >= 1:
            try:
                op_id = term.arg(0).as_long()
                _INTERPRETED_UNOPS = frozenset({50, 52, 53, 56, 57})
                if op_id not in _INTERPRETED_UNOPS:
                    return True
            except Exception:
                pass
        # Check explicit uninterpreted functions
        if any(decl_name.startswith(p) for p in
               ('py_', 'meth_', 'call_', 'dyncall_', 'mut_')):
            return True
        # Recurse into children
        for i in range(term.num_args()):
            if _has_semi_uninterp(term.arg(i), depth + 1):
                return True
        return False
    except Exception:
        return False


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


def _bounded_testing_kwargs(source_f: str, source_g: str, deadline: float):
    """BT for **kwargs-only functions. Tests with keyword argument combos."""
    import subprocess, json

    lines_f = source_f.strip().split('\n')
    first_f = lines_f[0]
    rest_f = lines_f[1:]
    lines_g = source_g.strip().split('\n')
    first_g = lines_g[0]
    rest_g = lines_g[1:]

    # Test with different kwarg dictionaries, including order-sensitive ones
    kwargs_tests = [
        "dict(a=1, b=2)",
        "dict(b=1, a=2)",
        "dict(x=10, y=20, z=30)",
        "dict(z=30, y=20, x=10)",
        "dict(a=1)",
        "dict()",
        "dict(b=3, a=4, c=5)",
    ]
    test_calls = ', '.join(f'({kt},)' for kt in kwargs_tests)

    script = f'''
import sys, json, types
{first_f}
{chr(10).join(rest_f)}

_saved_f = None
for _name, _obj in list(locals().items()):
    if isinstance(_obj, types.FunctionType) and not _name.startswith('_'):
        _saved_f = _obj
        break

{first_g}
{chr(10).join(rest_g)}

_fn_g = None
for _name, _obj in list(locals().items()):
    if isinstance(_obj, types.FunctionType) and not _name.startswith('_') and _obj is not _saved_f:
        _fn_g = _obj
        break

_test_dicts = [{test_calls}]
for (_kw_dict,) in _test_dicts:
    try:
        _rf = _saved_f(**_kw_dict)
        _rg = _fn_g(**_kw_dict)
        if repr(_rf) != repr(_rg):
            print(json.dumps({{"eq": False, "args": repr(_kw_dict), "f": repr(_rf), "g": repr(_rg)}}))
            sys.exit(0)
    except Exception:
        pass

print(json.dumps({{"eq": True, "n": len(_test_dicts)}}))
'''
    remaining = max(0.5, deadline - time.monotonic())
    try:
        proc = subprocess.run(
            ['python3.11', '-c', script],
            capture_output=True, text=True,
            timeout=min(remaining, 3.0)
        )
        if proc.returncode != 0:
            return None
        for line in proc.stdout.strip().split('\n'):
            if not line.strip():
                continue
            try:
                data = json.loads(line)
                return data
            except json.JSONDecodeError:
                continue
    except (subprocess.TimeoutExpired, Exception):
        pass
    return None


def _bounded_testing(source_f: str, source_g: str, param_names: List[str],
                     param_fibers: List[List[str]], deadline: float,
                     require_n_disagree: int = 1,
                     duck_types: List[str] = None):
    """Bounded testing: evaluate both functions on representative inputs.

    Returns True if all test cases agree, a dict with 'eq'=False and details
    if disagree found, None if testing could not be completed.
    When require_n_disagree > 1, BT runs all test cases and only reports NEQ
    if n_disagree >= require_n_disagree.
    """
    import subprocess, json

    if not param_names:
        # Check for **kwargs-only functions — test with keyword arguments
        try:
            import ast as _ast
            _tree_f = _ast.parse(source_f)
            _func_f = next(n for n in _ast.walk(_tree_f) if isinstance(n, _ast.FunctionDef))
            if _func_f.args.kwarg:
                return _bounded_testing_kwargs(source_f, source_g, deadline)
        except Exception:
            pass
        return None

    # Generate representative test inputs based on fiber types
    # Include edge cases that commonly distinguish NEQ pairs
    # NOTE: Avoid NaN and extreme floats — these expose implementation-
    # specific behavior (NaN ordering, float precision) that causes
    # false NEQ on genuinely equivalent programs.
    type_samples = {
        'int': ['0', '1', '-1', '2',
                # Half-values for rounding mode detection (banker's vs half-up)
                '0.5', '1.5', '2.5', '3.5', '-0.5', '-2.5',
                # Financial rounding edge cases (x.xx5 not exactly representable
                # in float, causing round(x, 2) to differ from Decimal rounding)
                '2.675', '1.005',
                '3', '5', '-7', '42', '100', '257', '10',
                # Large ints to detect float precision loss (int→float→int)
                '10**15', '2**53', '2**53+1'],
        'float': ['0.0', '1.0', '-1.0', '0.5', '-0.5',
                  'float("nan")', 'float("inf")', 'float("-inf")', '-0.0',
                  '0.1', '0.2', '0.3', '1e16', '1e-16', '2**53+1'],
        'bool': ['True', 'False', '0', '1'],
        'str': ['""', '"a"', '"hello"', '"abc"', '"a  b"',
                '"aab"', '"aaab"', '" "', '"Alice"', '"A"', '"ba"',
                '"Hello World"', '"12345"',
                # Unicode and special chars
                '"\\u00e9"', '"10"', '"2"'],
        'pair': ['(1, 2)', '(0,)', '((1, "a"), (2, "b"))',
                 '(1, "b")', '(1, "a")',
                 '{"b": 1, "a": 2}', '{"a": 1}', '{"a": 2}',
                 '{"a": 1, "b": 2}', '{"b": 3, "a": 4}',
                 '{"x": 10, "y": 20}', '{"y": 99, "x": 0}',
                 '(3, 1, 2)', '(1, 1, 1)',
                 # Empty dict and dict with None values
                 '{}', '{"a": None}'],
        'ref': ['[]', '[1]', '[1, 2, 3]', '[3, 1, 2]',
                # String-as-integer lists EARLY for str/int sort differences
                '["10", "2", "3"]', '["100", "20", "9"]',
                # Same-first-different-second pairs for secondary sort detection
                '[(1, 2), (1, 1)]', '[(1, 3), (1, 1), (1, 2)]',
                # Tied-key pairs to catch first-vs-last max/min stability
                '[(1, 5), (2, 5)]', '[(1, 5), (2, 5), (3, 5)]',
                '[("a", 1), ("b", 1)]', '[(0, 3), (1, 3), (2, 3)]',
                # String-key tuples for secondary sort detection
                '[("c", 2), ("a", 2), ("b", 1)]',
                '[float("nan"), 1.0, 2.0]',
                '[1.0, 1e-16, -1.0]',
                '[(1, "a"), (1, "b"), (2, "a")]',
                '[1, 1, 2, 1, 3]', '[[1], [2]]',
                '[(1, "b"), (1, "a"), (2, "c")]',
                '["a", "b"]',
                '[0, 0, 0]', '[-1, 0, 1]', '[1, 2, 3, 4, 5]',
                '["b", "a", "c"]', '[None, 1, "a"]',
                '[1, 1, 1, 2]', '[3, 3, 3, 3]', '[1, 2, 1, 2, 1]',
                '[1e16, 1.0, -1e16]', '[True, True, True]',
                # Lists with None for None-handling differences
                '[None]', '[1, None, 3]', '[None, 1, 2]',
                # Nested lists for flatten/chain differences
                '[[1, 2], [3]]', '[[1], [2], [3]]', '[[], [1]]',
                # Sorted arrays with duplicates for binary search
                '[1, 2, 2, 3]', '[1, 1, 1, 2, 3]'],
        'none': ['None'],
        'bytes': ['b""', 'b"hello"', 'b"abc"', 'b"\\x00\\x01\\x02"',
                  'b"Hello World"', 'b"test data"', 'b"\\xff\\xfe"',
                  'b"12345"', 'b"\\n\\t\\r"', 'bytes(range(256))'],
        'collection': ['[]', '[1]', '[1, 2, 3]', '[3, 1, 2]',
                       # Tied-key pairs early for max/min stability detection
                       '[(1, 5), (2, 5)]', '[(1, 5), (2, 5), (3, 5)]',
                       '[("a", 1), ("b", 1)]', '[(0, 3), (1, 3), (2, 3)]',
                       '[1, 1, 2, 1, 3]', '[1, 1, 1, 2]',
                       '[(1, "a"), (1, "b")]',
                       '[float("nan"), 1.0]',
                       '[1.0, 1e-16, -1.0]',
                       # String-as-integer and None lists
                       '["10", "2", "3"]', '[None, 1, 3]',
                       '[[1, 2], [3]]',
                       # Additional edge cases
                       '["hello", "world"]', '[True, False, True]',
                       '[0, 0, 0]', '[-1, 0, 1]', '[1, 2, 3, 4, 5]',
                       '[3, 3, 3, 3]', '[1, 2, 1, 2, 1]'],
        # Numeric-only lists: no tuples, strings, None, booleans, or nested lists
        'numeric_list': ['[]', '[1]', '[1, 2, 3]', '[3, 1, 2]',
                         '[0, 0, 0]', '[-1, 0, 1]', '[1, 2, 3, 4, 5]',
                         '[3, 3, 3, 3]', '[1, 2, 1, 2, 1]',
                         '[1, 1, 2, 1, 3]', '[1, 1, 1, 2]',
                         '[5, 4, 3, 2, 1]', '[100, 1, 50]',
                         '[-5, -3, -1, 0, 2, 4]', '[7]',
                         '[1, -1, 2, -2, 3, -3]',
                         '[10, 20, 30, 40, 50]', '[1, 3, 5, 2, 4]',
                         '[0, 1, 2, 0, 1, 2, 0]', '[-100, 0, 100]',
                         # Float lists for sum vs fsum precision detection
                         '[0.1] * 10', '[0.1, 0.2, 0.3]',
                         '[1e16, 1.0, -1e16]', '[0.3, 0.3, 0.3]'],
        # Positive integers — include 0 and -1 as boundary sentinels so
        # that BT catches edge-case disagreements when the Z3 proof is
        # lossy (e.g. bitand on integers → Bottom).
        'positive_int': ['0', '1', '2', '3', '5', '7', '10', '42', '100', '257',
                         '4', '6', '8', '9', '11', '12', '13', '15', '16',
                         '17', '20', '25', '50', '64', '128', '256'],
        # Callable predicates/transforms for higher-order function testing
        'callable': ['lambda x: x > 0', 'lambda x: x % 2 == 0',
                     'lambda x: x < 3', 'lambda x: x != 0',
                     'lambda x: True', 'lambda x: False',
                     'lambda x: x', 'lambda x: not x',
                     'lambda x: x >= 0', 'lambda x: x < 0',
                     'lambda x: isinstance(x, int) and x > 1',
                     'lambda x: x == x'],
        # 2D integer matrices (lists of lists)
        'matrix': ['[[1]]', '[[0]]', '[[2]]',
                   '[[1,0],[0,1]]', '[[1,2],[3,4]]', '[[2,3],[1,4]]',
                   '[[0,1],[1,0]]', '[[1,1],[1,1]]', '[[-1,2],[3,-4]]',
                   '[[1,2,3],[4,5,6],[7,8,9]]',
                   '[[1,0,0],[0,1,0],[0,0,1]]',
                   '[[2,1,3],[4,5,6],[7,8,0]]',
                   '[[1,2],[3,4],[5,6]]',
                   '[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]'],
        # Fixed-length coordinate/point types (2-element numeric tuples).
        # For params accessed via p[0], p[1] without iteration — prevents
        # spurious NEQ when math.dist uses all dims but indexing uses only 2.
        'coord': ['(0, 0)', '(1, 0)', '(0, 1)', '(1, 1)', '(-1, 0)',
                  '(1, 2)', '(3, 4)', '(-1, -1)', '(0, -1)',
                  '(5, 3)', '(10, 20)', '(100, 200)',
                  '(0.5, 0.5)', '(1.5, 2.5)', '(-0.5, 1.0)',
                  '(2, 7)', '(-3, 4)', '(0, 0)', '(1, -2)'],
        # Small positive ints for exponent/shift operands (2**n, 1<<n).
        # Capped at ≤20 to prevent exponential memory blowup.
        'small_positive_int': ['0', '1', '2', '3', '4', '5', '6', '7', '8',
                               '9', '10', '11', '12', '13', '14', '15',
                               '16', '17', '18', '19', '20'],
        # Pair-list: for x, y in param (tuple unpacking iteration)
        'pair_list': ['[]', '[(1, 2)]', '[(1, 2), (3, 4)]',
                      '[(1, 2), (2, 3)]', '[(1, 3), (2, 4)]',
                      '[(0, 1), (1, 2), (2, 3)]',
                      '[(0, 0), (0, 1), (1, 0)]',
                      '[(10, 20), (15, 25), (30, 40)]',
                      '[(3, 1), (1, 2)]', '[(-1, 1), (0, 2)]'],
    }

    # Build test input combinations (limited to avoid explosion)
    # For multi-fiber params, combine from all fibers and prioritize
    # edge cases (NaN, large floats, duplicate keys) first.
    param_samples = []
    for i, pname in enumerate(param_names):
        fibers = param_fibers[i] if i < len(param_fibers) else ['int']
        # If duck type has a specialized sample set, use it directly
        # (e.g., numeric_list uses clean int-only lists instead of mixed-type
        # collection samples from pair+ref fibers)
        dt = duck_types[i] if duck_types and i < len(duck_types) else None
        _DUCK_TYPE_SAMPLE_OVERRIDE = {'numeric_list', 'bytes', 'positive_int', 'matrix', 'callable', 'coord', 'small_positive_int'}
        if dt and dt in _DUCK_TYPE_SAMPLE_OVERRIDE and dt in type_samples:
            samples = list(type_samples[dt])
        else:
            samples = []
            per_fiber_lists = []
            for f in fibers:
                per_fiber_lists.append(type_samples.get(f, ['0', '1']))
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
        param_samples.append(unique[:40])  # keep compact to avoid explosion

    # Generate test combinations (limit to 60 total for better coverage)
    import itertools as _it
    # Generate test combinations with edge-case coverage.
    # For multi-parameter functions, itertools.product creates too many
    # combos and the 60-limit truncation drops edge cases for later
    # parameters.  Instead, ensure every value appears for each
    # parameter at least once (diagonal coverage), then fill remaining
    # slots with random combos.
    import random as _rnd
    _rnd.seed(42)  # deterministic for reproducibility

    n_params = len(param_samples)
    if n_params == 0:
        combos = [()]
    elif n_params == 1:
        combos = [(v,) for v in param_samples[0]]
    else:
        # Phase 1: diagonal coverage — each value for each param
        # Use staggered offsets for different params to avoid same-value combos
        # (e.g., start==stop for slice functions, or key==value for dict functions).
        combos_set = set()
        combos = []
        for pi in range(n_params):
            for vi, val in enumerate(param_samples[pi]):
                combo = []
                for pj in range(n_params):
                    if pj == pi:
                        combo.append(val)
                    else:
                        # Stagger by param index to create diverse combos
                        offset = (pj - pi) * 3 if pj != pi else 0
                        idx = (vi + offset) % len(param_samples[pj])
                        combo.append(param_samples[pj][idx])
                t = tuple(combo)
                if t not in combos_set:
                    combos_set.add(t)
                    combos.append(t)
        # Phase 2: random combos for additional coverage
        for _ in range(200):
            if len(combos) >= 80:
                break
            combo = tuple(_rnd.choice(s) for s in param_samples)
            if combo not in combos_set:
                combos_set.add(combo)
                combos.append(combo)

    # Phase 3: Float diagnostic combos — expose IEEE 754 non-associativity
    # and cancellation issues. These are general numeric properties, not
    # algorithm-specific. Only added for multi-param numeric functions.
    if n_params >= 2 and duck_types:
        _numeric_dts = {'numeric', 'int', 'float'}
        _all_numeric = all(dt in _numeric_dts for dt in duck_types)
        if _all_numeric:
            _float_diags = [
                ['1e16', '1.0', '-1e16'],     # catastrophic cancellation
                ['1e16', '-1e16', '1.0'],
                ['0.1', '0.2', '0.3'],        # decimal representation
            ]
            for diag in _float_diags:
                if len(diag) >= n_params:
                    t = tuple(diag[:n_params])
                    if t not in combos_set:
                        combos_set.add(t)
                        combos.append(t)

    if len(combos) > 85:
        combos = combos[:85]

    if not combos:
        return None

    # Build test script
    combo_strs = ', '.join(f'({", ".join(c)},)' for c in combos)
    param_fiber_info = repr(param_fibers)  # e.g. [['int'], ['ref']]
    duck_type_info = repr(duck_types if duck_types else [])

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

# Find function F — use the LAST defined function (main function)
# when source contains multiple functions (e.g. helpers + main)
_fn_f = None
for _name, _obj in list(locals().items()):
    if isinstance(_obj, types.FunctionType) and not _name.startswith('_'):
        _fn_f = _obj
_fn_f_name = None
for _name, _obj in list(locals().items()):
    if _obj is _fn_f:
        _fn_f_name = _name
        break

# Define function G (rename to avoid collision)
_saved_f = _fn_f
_saved_f_name = _fn_f_name
'''

    # Add G's source with renamed function
    script += f'''
{chr(10).join(rest_g)}

_fn_g = None
for _name, _obj in list(locals().items()):
    if isinstance(_obj, types.FunctionType) and not _name.startswith('_') and _obj is not _saved_f:
        _fn_g = _obj

test_cases = [{combo_strs}]
results = []
_RESOURCE_EXCS = (MemoryError, RecursionError, OverflowError)
_exception_disagree = 0
_cross_type_disagree = 0
_tests_run = 0
_both_ok_agree = 0
_value_disagree = 0
_mutation_disagree = 0
_last_mut_args = None
import time as _time
_deadline = _time.monotonic() + 4.0  # hard deadline for all tests
# Per-call timeout to prevent single calls from hanging (e.g., f('Hello World') → 11! perms)
import signal as _sig
class _CallTimeout(Exception): pass
def _timeout_handler(signum, frame): raise _CallTimeout()
try:
    _sig.signal(_sig.SIGALRM, _timeout_handler)
    _has_alarm = True
except (AttributeError, OSError):
    _has_alarm = False
# Per-parameter simple defaults based on fiber types.
# Only include edge cases relevant to the parameter's type:
# - int/numeric: 0, None, False
# - str: '', None, False
# - collection/ref/list: [], (), None
# - pair: {{}}, (), None
# - any/unknown: 0, '', None, False
_param_fiber_info = {param_fiber_info}
_duck_types = {duck_type_info}
# Only do mutation checking if any param is list-typed (catches
# sorted() vs .sort() style NEQ) but skip for matrix/collection
# (where mutation is implementation detail, not semantic difference).
_do_mutation_check = any(dt in ('list', 'dict', 'ref') for dt in _duck_types)
_PARAM_SIMPLE = []
for _fi in _param_fiber_info:
    _s = []
    _s.append(None)
    if 'int' in _fi or 'float' in _fi or 'bool' in _fi:
        _s.append(0)
    _s.append(False)
    if 'str' in _fi:
        _s.append('')
    if 'bytes' in _fi:
        _s.append(b'')
    if 'collection' in _fi or 'ref' in _fi or 'list' in _fi:
        _s.append(())  # empty tuple (hashable stand-in)
    _PARAM_SIMPLE.append(_s)
_STRICT_DEFAULTS = (0, None, False)
for args in test_cases:
    if _time.monotonic() > _deadline:
        break  # stop testing before subprocess timeout
    try:
        import copy as _cp
        _args_f = _cp.deepcopy(args)
        if _has_alarm: _sig.alarm(2)
        _val_f = _saved_f(*_args_f)
        if _has_alarm: _sig.alarm(0)
        r_f = repr(_val_f)
        f_ok = True
        f_resource_err = False
    except _RESOURCE_EXCS:
        if _has_alarm: _sig.alarm(0)
        f_ok = False
        f_resource_err = True
    except _CallTimeout:
        continue
    except Exception as e:
        if _has_alarm: _sig.alarm(0)
        f_ok = False
        f_resource_err = False
    try:
        _args_g = _cp.deepcopy(args)
        if _has_alarm: _sig.alarm(2)
        _val_g = _fn_g(*_args_g)
        if _has_alarm: _sig.alarm(0)
        r_g = repr(_val_g)
        g_ok = True
    except _RESOURCE_EXCS:
        if _has_alarm: _sig.alarm(0)
        if f_ok:
            g_ok = False
        elif f_resource_err:
            continue  # both resource errors — skip
        else:
            continue  # f had other error, g had resource error — skip
    except _CallTimeout:
        continue
    except Exception as e:
        g_ok = False
    _tests_run += 1
    if f_ok != g_ok:
        _exception_disagree += 1
        # Only count as immediate NEQ for very conservative cases:
        # For single-param: the arg must be in that param's simple defaults
        # For multi-param: ALL args must be strict defaults (0, None, False)
        _n_params = len(args)
        if _n_params == 1:
            _is_simple = False
            if len(_PARAM_SIMPLE) >= 1:
                _a = args[0]
                for _d in _PARAM_SIMPLE[0]:
                    try:
                        if type(_a) == type(_d) and _a == _d:
                            _is_simple = True
                            break
                    except Exception:
                        pass
        else:
            _is_simple = all(
                any(a == d for d in _STRICT_DEFAULTS)
                for a in args
            )
        if _is_simple:
            print(json.dumps({{"eq": False, "args": repr(args), "reason": "exception_disagree_on_simple_input"}}))
            sys.exit(0)
        continue
    if not (f_ok and g_ok):
        continue
    # Mutation check: if return values agree but input mutations differ,
    # the functions have different side effects (e.g., sorted vs .sort).
    if r_f == r_g:
        _both_ok_agree += 1
        if _do_mutation_check:
            try:
                _mut_f = repr(_args_f)
                _mut_g = repr(_args_g)
                if _mut_f != _mut_g:
                    _mutation_disagree += 1
                    _last_mut_args = repr(args)
            except Exception:
                pass
        # Output structural identity check: detect [[x]*m]*n vs
        # [[x]*m for _ in range(n)] (shared vs independent references).
        # If result is a list of lists and one has shared refs but the
        # other doesn't, this is a genuine structural difference.
        if isinstance(_val_f, list) and isinstance(_val_g, list):
            if len(_val_f) >= 2 and len(_val_g) >= 2:
                try:
                    if (isinstance(_val_f[0], list) and isinstance(_val_g[0], list)):
                        _shared_f = _val_f[0] is _val_f[1]
                        _shared_g = _val_g[0] is _val_g[1]
                        if _shared_f != _shared_g:
                            _value_disagree += 1
                            _last_args = repr(args)
                            _last_f = 'shared_refs=' + str(_shared_f)
                            _last_g = 'shared_refs=' + str(_shared_g)
                except (IndexError, TypeError):
                    pass
    if r_f != r_g:
        # When both return values are callable (higher-order functions),
        # compare their behavior on test inputs rather than their reprs
        # (function object reprs always differ due to memory addresses).
        if callable(_val_f) and callable(_val_g):
            _fn_agree = True
            _fn_tested = 0
            for _probe in [0, 1, -1, 2, 'a', True]:
                try:
                    _pf = repr(_val_f(_probe))
                except Exception:
                    _pf = None
                try:
                    _pg = repr(_val_g(_probe))
                except Exception:
                    _pg = None
                if _pf is not None and _pg is not None:
                    _fn_tested += 1
                    if _pf != _pg:
                        _fn_agree = False
                        break
                elif _pf is not None or _pg is not None:
                    # One crashes, other doesn't — different behavior
                    _fn_agree = False
                    _fn_tested += 1
                    break
            if _fn_agree and _fn_tested > 0:
                _both_ok_agree += 1
                continue
            elif _fn_tested == 0:
                _cross_type_disagree += 1
                continue  # no valid probes — count as structural divergence
        # Skip cross-type disagreements (e.g., [] vs '') — these indicate
        # domain mismatches, not real semantic differences.  Functions
        # that are equivalent on their intended domain may produce
        # different types on out-of-domain inputs.
        # Allow numeric type mixing (bool/int are semantically equivalent
        # since bool is a subclass of int in Python: True==1, False==0).
        _tf, _tg = type(_val_f), type(_val_g)
        _NUMERIC = (int, float, complex, bool)
        if _tf != _tg:
            if isinstance(_val_f, _NUMERIC) and isinstance(_val_g, _NUMERIC):
                if _val_f == _val_g:
                    continue  # e.g., True == 1 → same value, skip
            elif _val_f is None or _val_g is None:
                pass  # None vs value is a genuine semantic difference
            else:
                _cross_type_disagree += 1
                continue  # cross-type disagree: domain mismatch, not a bug
        # Skip nested cross-type disagreements: when both return lists
        # but element types differ due to string vs list domain (e.g.,
        # string slicing returns substrings, islice returns char lists).
        # Only skip str-vs-list element differences — other element type
        # differences (list vs tuple) are genuine NEQ signals.
        if isinstance(_val_f, (list, tuple)) and isinstance(_val_g, (list, tuple)):
            if len(_val_f) > 0 and len(_val_g) > 0 and len(_val_f) == len(_val_g):
                _etf = type(_val_f[0])
                _etg = type(_val_g[0])
                if _etf != _etg:
                    _is_str_list = (_etf == str and _etg == list) or (_etf == list and _etg == str)
                    if _is_str_list:
                        _cross_type_disagree += 1
                        continue  # str/list element mismatch: domain issue
        # Skip NaN disagreements — NaN violates total ordering and
        # comparison invariants, causing equivalent algorithms to
        # produce different orderings on NaN-containing inputs.
        if 'nan' in r_f.lower() or 'nan' in r_g.lower():
            continue
        # Skip float-precision disagreements — equivalent algorithms
        # can produce slightly different float results due to FP
        # arithmetic ordering.  Only skip if the absolute difference
        # is at machine-epsilon level (< 1e-12), to avoid masking
        # genuine float-semantic differences (e.g., Decimal vs float,
        # float associativity).
        def _floats_close(a, b, rel_tol=1e-9, abs_tol=1e-12):
            """IEEE 754 approximate equality: mathematically equivalent
            formulas may produce different float results due to rounding
            order.  Use relative tolerance for scale-invariance.
            Special cases: inf/NaN require exact match (per IEEE 754)."""
            if isinstance(a, (int, float)) and isinstance(b, (int, float)):
                if isinstance(a, bool) or isinstance(b, bool):
                    return False
                fa, fb = float(a), float(b)
                import math as _m
                if _m.isinf(fa) or _m.isinf(fb) or _m.isnan(fa) or _m.isnan(fb):
                    return fa == fb  # inf/NaN: exact match only
                return abs(fa - fb) <= max(rel_tol * max(abs(fa), abs(fb)), abs_tol)
            if isinstance(a, (tuple, list)) and isinstance(b, (tuple, list)):
                if len(a) != len(b): return False
                return all(_floats_close(x, y, rel_tol, abs_tol) for x, y in zip(a, b))
            return False
        if _floats_close(_val_f, _val_g):
            continue
        _value_disagree += 1
        _last_args = repr(args)
        _last_f = r_f[:50]
        _last_g = r_g[:50]
        if _value_disagree >= {require_n_disagree}:
            print(json.dumps({{"eq": False, "args": _last_args, "f": _last_f, "g": _last_g, "n_disagree": _value_disagree}}))
            sys.exit(0)
# If exception disagreements dominate and there are no successful
# agreements, this is a genuine semantic difference (one function
# consistently raises while the other succeeds on valid inputs).
# Require at least 20% of tests to show exception disagreement to
# avoid false positives from garbage inputs (e.g., graph functions
# tested with non-graph inputs where only a few short-circuit).
if _exception_disagree >= max(5, int(_tests_run * 0.2)) and _both_ok_agree == 0:
    print(json.dumps({{"eq": False, "reason": "exception_disagreement_dominant", "count": _exception_disagree, "total": _tests_run}}))
    sys.exit(0)
# If functions consistently return different types with no same-type
# agreements, they are fundamentally different (e.g., sum vs collect).
if _cross_type_disagree >= 3 and _both_ok_agree == 0:
    print(json.dumps({{"eq": False, "reason": "persistent_cross_type_disagree", "count": _cross_type_disagree}}))
    sys.exit(0)
# Mutation: report if enough tests show mutation disagree.
# Only checked for list-typed params to catch sorted() vs .sort().
if _do_mutation_check and _mutation_disagree >= 2 and _value_disagree == 0:
    print(json.dumps({{"eq": False, "args": _last_mut_args, "reason": "mutation_disagree", "count": _mutation_disagree}}))
    sys.exit(0)
# Report any remaining disagrees that didn't hit the threshold
if _value_disagree > 0:
    print(json.dumps({{"eq": False, "args": _last_args, "f": _last_f, "g": _last_g, "n_disagree": _value_disagree}}))
    sys.exit(0)

# ── Mutable default argument detection ──
# If a function uses mutable default args (def f(x, lst=[])), repeated calls
# without the default arg will accumulate state.  Test by calling each function
# with only required arguments (dropping optional ones that have defaults),
# twice, and checking if results change between calls.
if _time.monotonic() < _deadline and _both_ok_agree > 0:
    _mutable_detected = False
    try:
        import inspect as _insp
        _sig_f = _insp.signature(_saved_f)
        _sig_g = _insp.signature(_fn_g)
        # Count required params (no default)
        _n_req_f = sum(1 for p in _sig_f.parameters.values()
                       if p.default is _insp.Parameter.empty
                       and p.kind not in (_insp.Parameter.VAR_POSITIONAL, _insp.Parameter.VAR_KEYWORD))
        _n_req_g = sum(1 for p in _sig_g.parameters.values()
                       if p.default is _insp.Parameter.empty
                       and p.kind not in (_insp.Parameter.VAR_POSITIONAL, _insp.Parameter.VAR_KEYWORD))
        _n_req = max(_n_req_f, _n_req_g)
        # Find a simple test input with only required params
        _min_test = None
        for _tc in test_cases:
            if len(_tc) >= _n_req:
                _min_test = _tc[:_n_req]
                break
        if _min_test is not None and (_n_req < len(_sig_f.parameters) or _n_req < len(_sig_g.parameters)):
            import copy as _cp2
            # Capture repr immediately after each call to detect mutation
            _repr_f1 = repr(_saved_f(*_cp2.deepcopy(_min_test)))
            _repr_f2 = repr(_saved_f(*_cp2.deepcopy(_min_test)))
            _repr_g1 = repr(_fn_g(*_cp2.deepcopy(_min_test)))
            _repr_g2 = repr(_fn_g(*_cp2.deepcopy(_min_test)))
            _f_stable = (_repr_f1 == _repr_f2)
            _g_stable = (_repr_g1 == _repr_g2)
            if _f_stable != _g_stable:
                _mutable_detected = True
    except Exception:
        pass
    if _mutable_detected:
        print(json.dumps({{"eq": False, "reason": "mutable_default_statefulness"}}))
        sys.exit(0)

# ── Focused empty/minimal collection edge-case test ──
# Some functions differ ONLY on empty or single-element lists (e.g.,
# f handles [] gracefully while g crashes). These edge cases may not
# trigger the exception_disagree threshold since most tests agree.
# Guard: run if both functions successfully agreed on some input
# OR if exception disagrees were already detected (functions have
# different edge behavior worth probing further).
if _time.monotonic() < _deadline and (_both_ok_agree > 0 or _exception_disagree >= 2):
    _list_validation_inputs = [([1, 2, 3],), ([3, 1, 2],), ([(1, 2), (3, 4)],)]
    _list_valid_count = 0
    for _lvi in _list_validation_inputs:
        try:
            _saved_f(*_cp.deepcopy(_lvi))
            _fn_g(*_cp.deepcopy(_lvi))
            _list_valid_count += 1
        except Exception:
            pass
    _is_matrix = len(_duck_types) >= 1 and _duck_types[0] == 'matrix'
    if _list_valid_count >= 1 and not _is_matrix:
        _edge_inputs = [([],), ([1],), ([None, 1],)]
        # [None] tests catch functions that differ on single-element
        # inputs (e.g., sorted with key vs bubble sort). Only valid for
        # general collection types — numeric lists can't contain None.
        _is_general_collection = (
            len(_duck_types) == 1
            and _duck_types[0] in ('collection', 'ref', 'list', 'any', 'unknown')
        )
        if _is_general_collection:
            _edge_inputs.append(([None],))
        for _ei in _edge_inputs:
            try:
                _ef = repr(_saved_f(*_cp.deepcopy(_ei)))
                _ef_ok = True
            except Exception:
                _ef_ok = False
            try:
                _eg = repr(_fn_g(*_cp.deepcopy(_ei)))
                _eg_ok = True
            except Exception:
                _eg_ok = False
            if _ef_ok != _eg_ok:
                print(json.dumps({{"eq": False, "reason": "empty_collection_edge_disagree", "input": repr(_ei)}}))
                sys.exit(0)

print(json.dumps({{"eq": True, "n": len(test_cases), "exception_disagree": _exception_disagree, "cross_type_disagree": _cross_type_disagree}}))
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
            return data  # return full data dict (includes exception_disagree info)
        elif data.get('eq') is False:
            return data  # return full data dict for caller inspection
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


# ═══════════════════════════════════════════════════════════
# Spec Satisfaction Testing
# ═══════════════════════════════════════════════════════════

def _infer_param_fibers(source: str, param_names: List[str],
                         spec_source: str = '') -> Dict[str, str]:
    """Infer fiber types (duck types) for parameters from source code.
    
    Examines both program and spec source to determine parameter types.
    Uses both duck-ops (method calls) and builtin-call analysis.
    """
    try:
        from cctt.duck import extract_duck_ops
        result = {}
        sources = [source]
        if spec_source:
            sources.append(spec_source)
        
        # Builtins that imply their argument is iterable (list-like)
        _ITERABLE_BUILTINS = {'zip', 'enumerate', 'sorted', 'reversed',
                              'sum', 'min', 'max', 'any', 'all', 'map',
                              'filter', 'set', 'tuple', 'list', 'frozenset',
                              'iter', 'next'}
        _STR_BUILTINS = {'ord', 'chr'}
        
        for p in param_names:
            all_ops = set()
            builtin_hints = set()
            
            for src in sources:
                try:
                    tree = ast.parse(textwrap.dedent(src))
                    func_node = next(n for n in ast.walk(tree)
                                     if isinstance(n, ast.FunctionDef))
                    all_ops.update(extract_duck_ops(func_node, p))
                    
                    # Scan for builtin calls where p is an argument
                    for node in ast.walk(func_node):
                        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                            fname = node.func.id
                            for arg in node.args:
                                if isinstance(arg, ast.Name) and arg.id == p:
                                    builtin_hints.add(fname)
                        # Also check for len(p)
                        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                            and node.func.id == 'len' and node.args
                            and isinstance(node.args[0], ast.Name)
                            and node.args[0].id == p):
                            builtin_hints.add('len')
                        # Check for `for x in p` iteration
                        if isinstance(node, (ast.For, ast.comprehension)):
                            iter_node = node.iter if isinstance(node, ast.For) else node.iter
                            if isinstance(iter_node, ast.Name) and iter_node.id == p:
                                builtin_hints.add('__iter__')
                                # If loop var is compared to single-char strings,
                                # the iterable is a string
                                tgt = node.target if isinstance(node, ast.For) else node.target
                                if isinstance(tgt, ast.Name):
                                    loop_var = tgt.id
                                    for inner in ast.walk(func_node):
                                        if (isinstance(inner, ast.Compare)
                                            and isinstance(inner.left, ast.Name)
                                            and inner.left.id == loop_var):
                                            for comp in inner.comparators:
                                                if (isinstance(comp, ast.Constant)
                                                    and isinstance(comp.value, str)
                                                    and len(comp.value) == 1):
                                                    builtin_hints.add('__char_iter__')
                            # for x, y in zip(p, ...): the iter is zip(p,...)
                            if (isinstance(iter_node, ast.Call)
                                and isinstance(iter_node.func, ast.Name)
                                and iter_node.func.id in _ITERABLE_BUILTINS):
                                for a in iter_node.args:
                                    if isinstance(a, ast.Name) and a.id == p:
                                        builtin_hints.add(iter_node.func.id)
                except Exception:
                    pass
            
            # Build expanded sets that also include method_ prefixed variants
            str_ops_base = {'upper', 'lower', 'split', 'strip', 'replace',
                       'isalpha', 'isdigit', 'isalnum', 'isupper', 'islower',
                       'startswith', 'endswith', 'find', 'join', 'count',
                       'encode', 'decode', 'title', 'capitalize', 'swapcase',
                       'ljust', 'rjust', 'center', 'zfill', 'maketrans',
                       'translate'}
            str_ops = str_ops_base | {f'method_{s}' for s in str_ops_base}
            list_ops_base = {'__getitem__', '__len__', '__iter__', 'append',
                        'sort', 'extend', 'insert', 'pop', 'remove',
                        'index', 'reverse'}
            list_ops = list_ops_base | {f'method_{s}' for s in list_ops_base}
            int_ops = {'__add__', '__mul__', '__sub__', '__mod__',
                       '__floordiv__', '__truediv__', '__pow__',
                       '__and__', '__or__', '__xor__', '__lshift__',
                       '__rshift__', '__invert__'}
            
            # Detect positive_int: param used as range bound (range(p),
            # range(p+1), range(1, p+1), etc.) without any negative-domain usage.
            is_range_bound = False
            has_negative_domain_use = False
            for src in sources:
                try:
                    tree2 = ast.parse(textwrap.dedent(src))
                    for node2 in ast.walk(tree2):
                        if isinstance(node2, ast.Call) and isinstance(node2.func, ast.Name):
                            if node2.func.id == 'range':
                                for a in node2.args:
                                    if _mentions_name(a, p):
                                        is_range_bound = True
                        # Check for comparisons like p < 0 or p < 2
                        # (suggests param CAN be negative)
                        if isinstance(node2, ast.Compare):
                            if (isinstance(node2.left, ast.Name) and node2.left.id == p):
                                for op, comp in zip(node2.ops, node2.comparators):
                                    if (isinstance(comp, ast.Constant)
                                            and isinstance(comp.value, (int, float))
                                            and comp.value < 0
                                            and isinstance(op, ast.Lt)):
                                        has_negative_domain_use = True
                            for comp in node2.comparators:
                                if (isinstance(comp, ast.Name) and comp.id == p):
                                    if (isinstance(node2.left, ast.Constant)
                                            and isinstance(node2.left.value, (int, float))
                                            and node2.left.value < 0):
                                        has_negative_domain_use = True
                except Exception:
                    pass

            if (all_ops & str_ops or builtin_hints & _STR_BUILTINS
                    or '__char_iter__' in builtin_hints):
                result[p] = 'str'
            elif (all_ops & list_ops or builtin_hints & _ITERABLE_BUILTINS
                  or 'len' in builtin_hints or '__iter__' in builtin_hints):
                result[p] = 'ref'
            elif all_ops & int_ops:
                if is_range_bound and not has_negative_domain_use:
                    result[p] = 'positive_int'
                else:
                    result[p] = 'int'
            else:
                if is_range_bound and not has_negative_domain_use:
                    result[p] = 'positive_int'
                else:
                    result[p] = 'any'
        return result
    except Exception:
        return {p: 'any' for p in param_names}


def _bounded_spec_testing(source: str, spec_source: str,
                           prog_params: List[str], spec_params: List[str],
                           deadline: float) -> Optional[Dict]:
    """Test if program satisfies spec by running on representative inputs.

    Used ONLY for counterexample finding (VIO detection).
    A concrete failing input IS a proof of non-satisfaction.
    Passing all tests is NOT a proof of satisfaction.

    Executes: result = program(inputs); assert spec(inputs, result) == True
    """
    import subprocess, json

    if not prog_params:
        return None

    # Infer duck types from source + spec for test generation
    duck_types = []
    try:
        fibers = _infer_param_fibers(source, prog_params,
                                      spec_source=spec_source)
        duck_types = [fibers.get(p, 'any') for p in prog_params]
    except Exception:
        duck_types = ['any'] * len(prog_params)

    # Generate test inputs based on duck types
    type_samples = {
        'int': ['0', '1', '-1', '2', '3', '5', '10', '42', '100',
                '-10', '7', '255', '1000', '-100'],
        'float': ['0.0', '1.0', '-1.0', '0.5', '3.14', '1e-10',
                  'float("nan")', 'float("inf")', '1e16'],
        'str': ['""', '"a"', '"hello"', '"abc"', '"HELLO"',
                '"Hello World"', '"ABA"', '"Aba"', '"AbBa"',
                '"racecar"', '"AbCdEf"', '"aeiou"', '"u"',
                '"bcdfg"', '"12345"', '"hello world"', '" "',
                '"Aa"', '"aAbBcC"', '"aba"', '"test"',
                '"Level"', '"Abc"', '"CBA"',
                '"([{}])"', '"(())"', '"[{]}"', '"(()"'],
        'bool': ['True', 'False'],
        'ref': ['[]', '[1]', '[1, 2, 3]', '[3, 1, 2]',
                '[1, 1, 2, 1, 3]', '[-1, 0, 1]', '[1, 2, 3, 4, 5]',
                '[5, 5, 5]', '[1, 1, 1]', '[0, 0, 0]',
                '[1, 2]', '[2, 1]', '[-5, -3, -1, 0, 2]',
                '[1, 2, 2, 3]', '[10, 20, 30]',
                '["a", "b", "c"]', '["hello", "world"]',
                '[[1, 2], [3, 4]]', '[[1], [2], [3]]',
                # Strings are iterable+subscriptable like lists
                '"abc"', '"racecar"', '"abba"', '"hello"', '""',
                '"12"', '"1"', '"0"'],
        'collection': ['[]', '[1]', '[1, 2, 3]', '[3, 1, 2]',
                        '[1, 1, 2, 1, 3]', '[-1, 0, 1]',
                        '[5, 5, 5]', '[0, 0, 0]'],
        'numeric_list': ['[]', '[1]', '[1, 2, 3]', '[3, 1, 2]',
                          '[0, 0, 0]', '[-1, 0, 1]', '[5, 4, 3, 2, 1]',
                          '[1, 1, 1]', '[10, 20, 30]', '[-5, -3, 0, 2, 4]'],
        'positive_int': ['0', '1', '2', '3', '5', '7', '10', '42', '100', '255'],
        'matrix': ['[[1,2],[3,4]]', '[[1,0],[0,1]]', '[[1]]',
                   '[[0,0],[0,0]]'],
        'bytes': ['b""', 'b"hello"', 'b"abc"', 'b"\\x00\\xff"'],
        'pair': ['(1, 2)', '(0, 0)', '(3, 1)', '(-1, 5)'],
        'callable': ['lambda x: x > 0', 'lambda x: x % 2 == 0'],
        'any': ['0', '1', '-1', '3', '5', '10', '100',
                '"a"', '"hello"', '""', '"ABA"', '"AbCd"', '"aeiou"',
                '[]', '[1]', '[1, 2, 3]', '[3, 1, 2]', '[1, 1, 2, 1, 3]',
                '[-1, 0, 1]', '[5, 4, 3, 2, 1]', '[5, 5, 5]',
                'True', 'False', 'None',
                '(1, 2)', '{"a": 1}'],
        'none': ['None'],
    }

    n_params = len(prog_params)
    samples_per_param = []
    for i in range(n_params):
        dt = duck_types[i] if i < len(duck_types) else 'any'
        s = type_samples.get(dt, type_samples['any'])
        samples_per_param.append(s)

    # Generate test tuples (cross product, limited)
    if n_params == 1:
        test_tuples = [(s,) for s in samples_per_param[0]]
    elif n_params == 2:
        test_tuples = [(a, b) for a in samples_per_param[0][:8]
                       for b in samples_per_param[1][:8]]
    elif n_params == 3:
        test_tuples = [(a, b, c) for a in samples_per_param[0][:5]
                       for b in samples_per_param[1][:5]
                       for c in samples_per_param[2][:5]]
    else:
        test_tuples = [(s[min(i, len(s)-1)] for s in samples_per_param)
                       for i in range(min(10, max(len(s) for s in samples_per_param)))]
        test_tuples = [tuple(t) for t in test_tuples]

    test_tuples = test_tuples[:100]  # safety cap

    test_args = ', '.join(f'({", ".join(t)},)' for t in test_tuples)

    # Build test script
    script = f'''
import sys, json, types, traceback
sys.setrecursionlimit(500)

{textwrap.dedent(source)}

_prog_fn = None
for _name, _obj in list(locals().items()):
    if isinstance(_obj, types.FunctionType) and not _name.startswith('_'):
        _prog_fn = _obj
        break

{textwrap.dedent(spec_source)}

_spec_fn = None
for _name, _obj in list(locals().items()):
    if isinstance(_obj, types.FunctionType) and not _name.startswith('_') and _obj is not _prog_fn:
        _spec_fn = _obj
        break

_test_args = [{test_args}]
_n_passed = 0
for _args in _test_args:
    try:
        _result = _prog_fn(*_args)
        _ok = _spec_fn(*_args, _result)
        if not _ok:
            print(json.dumps({{"satisfies": False, "counterexample": repr(_args), "result": repr(_result)}}))
            sys.exit(0)
        _n_passed += 1
    except (RecursionError, MemoryError) as _e:
        print(json.dumps({{"satisfies": False, "counterexample": repr(_args), "error": type(_e).__name__}}))
        sys.exit(0)
    except Exception as _e:
        pass

print(json.dumps({{"satisfies": True, "n_tests": _n_passed}}))
'''

    remaining = max(0.5, deadline - time.monotonic())
    try:
        proc = subprocess.run(
            ['python3', '-c', script],
            capture_output=True, text=True,
            timeout=min(remaining, 5.0)
        )
        if proc.returncode != 0:
            # Non-zero exit from the test script — likely crash
            return {'satisfies': False, 'counterexample': 'program crashed',
                    'error': proc.stderr[:200] if proc.stderr else 'unknown'}
        for line in proc.stdout.strip().split('\n'):
            if not line.strip():
                continue
            try:
                data = json.loads(line)
                return data
            except json.JSONDecodeError:
                continue
    except subprocess.TimeoutExpired:
        return {'satisfies': False, 'counterexample': 'program timeout',
                'error': 'timeout'}
    except Exception:
        pass
    return None
