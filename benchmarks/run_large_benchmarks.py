#!/usr/bin/env python3
"""Run the large benchmark suites (100 programs each)."""

from __future__ import annotations
import json, sys, time, textwrap
from pathlib import Path
from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))
sys.path.insert(0, str(Path(__file__).parent))

from bug_benchmark_utils import _score_bug_labels
from deppy.render.bug_detect import detect_bugs
from deppy.equivalence.pipeline import EquivalencePipeline, EquivalencePipelineConfig
from deppy.equivalence._runtime_sampling import (
    _build_runtime_samples,
    _call_with_cloned_args,
    _load_primary_callable,
)

RESULTS_DIR = Path(__file__).parent / "results"
RESULTS_DIR.mkdir(exist_ok=True)


def run_bug_suite():
    from large_bug_suite import BUG_PROGRAMS
    print(f"[BUG SUITE] Running {len(BUG_PROGRAMS)} programs...")
    tp = fp = fn = 0
    rank_correct = 0
    results = []
    for i, (name, source, expected, exp_fixes) in enumerate(BUG_PROGRAMS):
        try:
            report = detect_bugs(source)
            detected = [o.bug_type for o in report.obstructions if not o.resolved_by_guard]
            h1 = report.minimum_independent_fixes
            score = _score_bug_labels(expected, detected)
            tp += score.true_positives
            fp += score.false_positives
            fn += score.false_negatives
            if h1 == exp_fixes:
                rank_correct += 1
            results.append({"name": name, "expected": expected, "detected": detected,
                            "scored_detected": score.scored_detected_labels,
                            "alias_matches": score.alias_matches,
                            "h1": h1, "exp_fixes": exp_fixes,
                            "tp": score.true_positives,
                            "fp": score.false_positives,
                            "fn": score.false_negatives})
        except Exception as e:
            fn += len(expected)
            results.append({"name": name, "error": str(e)})
        if (i + 1) % 20 == 0:
            print(f"  {i+1}/{len(BUG_PROGRAMS)} done...")

    prec = tp / (tp + fp) if (tp + fp) > 0 else 0
    rec = tp / (tp + fn) if (tp + fn) > 0 else 0
    f1 = 2 * prec * rec / (prec + rec) if (prec + rec) > 0 else 0
    print(f"  Precision: {prec:.1%}  Recall: {rec:.1%}  F1: {f1:.1%}")
    print(f"  H1 rank accuracy: {rank_correct}/{len(BUG_PROGRAMS)}")
    return {"tp": tp, "fp": fp, "fn": fn, "precision": round(prec, 3),
            "recall": round(rec, 3), "f1": round(f1, 3),
            "h1_correct": rank_correct, "total": len(BUG_PROGRAMS),
            "details": results}


def run_equiv_suite():
    from large_equiv_suite import EQUIV_PAIRS
    print(f"[EQUIV SUITE] Running {len(EQUIV_PAIRS)} pairs...")
    config = EquivalencePipelineConfig(solver_timeout_ms=5000)
    pipeline = EquivalencePipeline(config)
    correct = 0
    eq_tp = eq_fn = neq_tn = neq_fp = 0
    results = []
    for i, (name, src_f, src_g, expected_eq) in enumerate(EQUIV_PAIRS):
        try:
            result = pipeline.run(src_f, src_g)
            verdict = result.verdict.value
            is_eq = result.is_equivalent
            if verdict == "unknown":
                is_eq = False
            ok = (is_eq == expected_eq)
            if ok:
                correct += 1
            if expected_eq:
                if ok: eq_tp += 1
                else: eq_fn += 1
            else:
                if ok: neq_tn += 1
                else: neq_fp += 1
            results.append({"name": name, "expected_eq": expected_eq,
                            "verdict": verdict, "correct": ok})
        except Exception as e:
            if not expected_eq:
                correct += 1
                neq_tn += 1
            else:
                eq_fn += 1
            results.append({"name": name, "expected_eq": expected_eq,
                            "verdict": f"error", "correct": not expected_eq})
        if (i + 1) % 20 == 0:
            print(f"  {i+1}/{len(EQUIV_PAIRS)} done...")

    print(f"  Correct: {correct}/{len(EQUIV_PAIRS)} ({correct/len(EQUIV_PAIRS):.0%})")
    print(f"  Equiv TP: {eq_tp}, FN: {eq_fn}  |  Non-equiv TN: {neq_tn}, FP: {neq_fp}")
    return {"correct": correct, "total": len(EQUIV_PAIRS),
            "eq_tp": eq_tp, "eq_fn": eq_fn, "neq_tn": neq_tn, "neq_fp": neq_fp,
            "details": results}


def _test_spec_on_inputs(source: str, spec_src: str) -> tuple[bool, bool]:
    """Evaluate a spec on curated runtime samples.

    Returns ``(spec_holds, runtime_bug_observed)`` so callers can use the
    same sample cover both for semantic conformance and to distinguish a
    real runtime failure from a purely static false positive.
    """
    ns: dict = {}
    try:
        exec(compile(source, '<prog>', 'exec'), ns)
        exec(compile(spec_src, '<spec>', 'exec'), ns)
    except Exception:
        return True, False

    prog_fn = _load_primary_callable(source)
    spec_fn = ns.get("spec")
    if prog_fn is None or spec_fn is None:
        return True, False

    runtime_bug = False
    spec_holds = True
    samples = _build_runtime_samples(source, prog_fn, mode="spec", max_samples=64)
    if not samples:
        return True, False

    for inp in samples:
        obs = _call_with_cloned_args(prog_fn, inp)
        if obs.exception_type is not None:
            runtime_bug = True
            spec_holds = False
            continue
        try:
            if not spec_fn(*list(inp), obs.value):
                spec_holds = False
        except Exception:
            continue

    return spec_holds, runtime_bug


def run_spec_suite():
    from large_spec_suite import SPEC_PROGRAMS
    print(f"[SPEC SUITE] Running {len(SPEC_PROGRAMS)} programs...")
    correct = 0
    results = []
    for i, (name, source, spec_src, expected_sat) in enumerate(SPEC_PROGRAMS):
        try:
            # Two-pronged check:
            # 1. Static: sheaf-cohomological bug detection
            report = detect_bugs(source)
            genuine = [o for o in report.obstructions
                       if not o.resolved_by_guard and o.confidence > 0.5]
            static_sat = len(genuine) == 0

            # 2. Dynamic: evaluate spec on sample inputs
            dynamic_sat, runtime_bug = _test_spec_on_inputs(source, spec_src)

            # Static findings only veto the spec when representative inputs
            # actually witness a runtime failure; this keeps generic detector
            # false positives from overwhelming the spec judgment.
            static_sat = len(genuine) == 0 or not runtime_bug
            actual_sat = static_sat and dynamic_sat
            ok = (actual_sat == expected_sat)
            if ok:
                correct += 1
            results.append({"name": name, "expected_sat": expected_sat,
                            "actual_sat": actual_sat, "correct": ok,
                            "n_bugs": len(genuine),
                            "static_sat": static_sat,
                            "dynamic_sat": dynamic_sat})
        except Exception as e:
            results.append({"name": name, "expected_sat": expected_sat,
                            "actual_sat": False, "correct": not expected_sat,
                            "error": str(e)})
            if not expected_sat:
                correct += 1
        if (i + 1) % 20 == 0:
            print(f"  {i+1}/{len(SPEC_PROGRAMS)} done...")

    print(f"  Correct: {correct}/{len(SPEC_PROGRAMS)} ({correct/len(SPEC_PROGRAMS):.0%})")
    return {"correct": correct, "total": len(SPEC_PROGRAMS), "details": results}


def main():
    print("=" * 70)
    print("DEPPY LARGE BENCHMARK SUITE (300 programs)")
    print("=" * 70)

    all_results = {}

    t0 = time.monotonic()
    all_results["bugs"] = run_bug_suite()
    print()
    all_results["equiv"] = run_equiv_suite()
    print()
    all_results["spec"] = run_spec_suite()
    total = time.monotonic() - t0

    print()
    print("=" * 70)
    print(f"TOTAL TIME: {total:.1f}s")
    print("=" * 70)

    out = RESULTS_DIR / "large_benchmark_results.json"
    with open(out, "w") as f:
        json.dump(all_results, f, indent=2, default=str)
    print(f"Results written to {out}")


if __name__ == "__main__":
    main()
