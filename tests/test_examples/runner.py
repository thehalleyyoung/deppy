#!/usr/bin/env python3
"""Runner for the 100 advanced algorithm verification examples.

Each example is a standalone .py file that exports:
  CORRECT: str          — correct implementation source
  BUGGY: str            — subtly buggy implementation source
  SPEC: Callable        — spec(input_params..., result) -> bool
  BUG_DESC: str         — description of the bug
  INPUT_OVERRIDES: dict  — {param_name: generator_callable}

Run:  PYTHONPATH=deppy/src python deppy/tests/test_examples/runner.py [-v]
"""
from __future__ import annotations

import importlib
import os
import sys
import time
import traceback
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'src'))

from deppy.render.predicate_refine import SheafSpecVerifier


@dataclass
class AlgoCase:
    name: str
    correct: str
    buggy: str
    spec: Callable
    bug_desc: str
    input_overrides: Optional[Dict[str, Callable]] = None


@dataclass
class AlgoResult:
    name: str
    correct_verdict: bool
    buggy_verdict: bool
    detected: bool
    false_positive: bool
    false_negative: bool
    elapsed_ms: float
    error: str = ""
    n_vcs: int = 0
    cech_eliminated: int = 0
    n_z3_proofs: int = 0
    n_z3_refutations: int = 0
    n_structural: int = 0
    n_sheaf_transfers: int = 0
    n_impl_section: int = 0
    correct_refuted: bool = False
    buggy_refuted: bool = False


def discover_examples() -> List[AlgoCase]:
    """Discover all example files in this directory."""
    examples_dir = os.path.dirname(os.path.abspath(__file__))
    cases = []
    for fname in sorted(os.listdir(examples_dir)):
        if not fname.endswith('.py'):
            continue
        if fname in ('__init__.py', 'runner.py', 'helpers.py'):
            continue
        modname = fname[:-3]
        try:
            mod = importlib.import_module(f'test_examples.{modname}')
            case = AlgoCase(
                name=modname,
                correct=mod.CORRECT,
                buggy=mod.BUGGY,
                spec=mod.SPEC,
                bug_desc=mod.BUG_DESC,
                input_overrides=getattr(mod, 'INPUT_OVERRIDES', None),
            )
            cases.append(case)
        except Exception as e:
            print(f"  WARNING: Failed to load {fname}: {e}")
    return cases


def run_one(algo: AlgoCase, verifier: SheafSpecVerifier,
            verbose: bool = False) -> AlgoResult:
    t0 = time.time()
    error = ""
    n_vcs = cech_elim = 0
    n_z3_proofs = n_z3_refutations = n_structural = 0
    n_sheaf_transfers = n_impl_section = 0
    correct_refuted = buggy_refuted = False

    try:
        # Don't pass reference_source when verifying correct —
        # comparative analysis is asymmetric and would cause FPs
        r_correct = verifier.verify(
            algo.correct, algo.spec,
            input_overrides=algo.input_overrides,
        )
        # Pass correct as reference when verifying buggy
        r_buggy = verifier.verify(
            algo.buggy, algo.spec,
            input_overrides=algo.input_overrides,
            reference_source=algo.correct,
        )
        correct_verdict = r_correct.correct
        buggy_verdict = r_buggy.correct
        correct_refuted = r_correct.refuted
        buggy_refuted = r_buggy.refuted
        n_vcs = r_correct.n_vcs_total + r_buggy.n_vcs_total
        cech_elim = r_correct.n_vcs_eliminated + r_buggy.n_vcs_eliminated
        n_z3_proofs = r_correct.n_z3_proofs + r_buggy.n_z3_proofs
        n_z3_refutations = r_correct.n_z3_refutations + r_buggy.n_z3_refutations
        n_structural = r_correct.n_structural_proofs + r_buggy.n_structural_proofs
        n_sheaf_transfers = r_correct.n_sheaf_transfers + r_buggy.n_sheaf_transfers
        n_impl_section = r_correct.n_impl_section_proofs + r_buggy.n_impl_section_proofs

        if verbose:
            print(f"       Correct: {r_correct.correct} (proved={r_correct.n_vcs_proved}, "
                  f"refuted={r_correct.n_vcs_refuted}, inconc={r_correct.n_vcs_inconclusive})")
            print(f"       Buggy:   {r_buggy.correct} (proved={r_buggy.n_vcs_proved}, "
                  f"refuted={r_buggy.n_vcs_refuted}, inconc={r_buggy.n_vcs_inconclusive})")
            for line in r_buggy.proof_log[-3:]:
                print(f"       [buggy]   {line}")

    except Exception as e:
        correct_verdict = False
        buggy_verdict = False
        error = f"{type(e).__name__}: {e}"
        if verbose:
            traceback.print_exc()

    elapsed = (time.time() - t0) * 1000
    detected = correct_verdict and not buggy_verdict
    false_pos = not correct_verdict and not error
    false_neg = buggy_verdict if buggy_verdict else False

    return AlgoResult(
        name=algo.name,
        correct_verdict=correct_verdict,
        buggy_verdict=buggy_verdict,
        detected=detected,
        false_positive=false_pos,
        false_negative=false_neg,
        elapsed_ms=elapsed,
        error=error,
        n_vcs=n_vcs,
        cech_eliminated=cech_elim,
        n_z3_proofs=n_z3_proofs,
        n_z3_refutations=n_z3_refutations,
        n_structural=n_structural,
        n_sheaf_transfers=n_sheaf_transfers,
        n_impl_section=n_impl_section,
        correct_refuted=correct_refuted,
        buggy_refuted=buggy_refuted,
    )


def run_all(verbose: bool = False) -> List[AlgoResult]:
    verifier = SheafSpecVerifier(z3_timeout_ms=3000.0)
    algorithms = discover_examples()

    print(f"{'=' * 90}", flush=True)
    print(f"  Sheaf Descent Proof Engine — {len(algorithms)} Advanced Algorithm Suite", flush=True)
    print(f"  (Pure proofs: Z3 + structural + Čech cohomology — no concrete testing)", flush=True)
    print(f"{'=' * 90}", flush=True)
    print(f"  {'#':>3}  {'Algorithm':<35} {'Correct':>8} {'Buggy':>8} {'Detect':>8} "
          f"{'Time':>8}", flush=True)
    print(f"  {'─' * 3}  {'─' * 35} {'─' * 8} {'─' * 8} {'─' * 8} "
          f"{'─' * 8}", flush=True)

    results = []
    for i, algo in enumerate(algorithms):
        print(f"  [{i + 1:>3}/{len(algorithms)}] {algo.name}...", end="", flush=True)
        r = run_one(algo, verifier, verbose)
        results.append(r)

        c_mark = "PROVED" if r.correct_verdict else ("REFUTED" if r.correct_refuted else "INCONC")
        b_mark = "REFUTED" if r.buggy_refuted else ("PASS" if r.buggy_verdict else "INCONC")
        d_mark = "CAUGHT" if r.detected else (
            "FP" if r.false_positive else ("FN" if r.false_negative else "---"))

        c_col = "\033[32m" if r.correct_verdict else "\033[31m"
        b_col = "\033[32m" if (r.buggy_refuted or not r.buggy_verdict) else "\033[31m"
        d_col = "\033[32m" if r.detected else "\033[33m"

        print(f"\r  {i + 1:>3}  {algo.name:<35} "
              f"{c_col}{c_mark:>8}\033[0m "
              f"{b_col}{b_mark:>8}\033[0m "
              f"{d_col}{d_mark:>8}\033[0m "
              f"{r.elapsed_ms:>6.0f}ms", flush=True)

        if r.error and verbose:
            print(f"       ERROR: {r.error}", flush=True)

    n = len(results)
    n_detected = sum(1 for r in results if r.detected)
    n_fp = sum(1 for r in results if r.false_positive)
    n_fn = sum(1 for r in results if r.false_negative)
    n_err = sum(1 for r in results if r.error)
    total_time = sum(r.elapsed_ms for r in results)

    print(f"\n{'=' * 90}")
    print(f"  PROOF SUMMARY")
    print(f"{'=' * 90}")
    print(f"  Algorithms verified:      {n}")
    print(f"  Bugs detected (proved):   {n_detected}/{n} ({100 * n_detected / n:.1f}%)" if n else "")
    print(f"  False positives:          {n_fp}")
    print(f"  False negatives:          {n_fn}")
    print(f"  Errors:                   {n_err}")
    print(f"  Total time:               {total_time:.0f}ms ({total_time / 1000:.1f}s)")
    print(f"{'=' * 90}")

    if n_fn > 0:
        print(f"\n  False Negatives (buggy code not refuted):")
        for r in results:
            if r.false_negative:
                algo = next(a for a in algorithms if a.name == r.name)
                print(f"    - {r.name}: {algo.bug_desc}")

    if n_fp > 0:
        print(f"\n  False Positives (correct code refuted):")
        for r in results:
            if r.false_positive:
                print(f"    - {r.name}")

    return results


if __name__ == '__main__':
    verbose = '--verbose' in sys.argv or '-v' in sys.argv
    run_all(verbose=verbose)
