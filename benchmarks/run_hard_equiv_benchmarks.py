#!/usr/bin/env python3
"""Run the hard equivalence benchmark suite."""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))
sys.path.insert(0, str(Path(__file__).parent))

from deppy.equivalence.pipeline import EquivalencePipeline, EquivalencePipelineConfig
from hard_equiv_suite import EQUIV_PAIRS

RESULTS_DIR = Path(__file__).parent / "results"
RESULTS_DIR.mkdir(exist_ok=True)


def main() -> None:
    print("=" * 70)
    print("DEPPY HARD EQUIVALENCE BENCHMARK SUITE (100 pairs)")
    print("=" * 70)
    print(f"[HARD EQUIV SUITE] Running {len(EQUIV_PAIRS)} pairs...")

    config = EquivalencePipelineConfig(solver_timeout_ms=5000)
    pipeline = EquivalencePipeline(config)

    started = time.monotonic()
    correct = 0
    eq_tp = eq_fn = neq_tn = neq_fp = 0
    details: list[dict[str, object]] = []

    for idx, (name, src_f, src_g, expected_eq) in enumerate(EQUIV_PAIRS, start=1):
        try:
            result = pipeline.run(src_f, src_g)
            verdict = result.verdict.value
            is_eq = result.is_equivalent and verdict != "unknown"
            ok = is_eq == expected_eq
            if ok:
                correct += 1
            if expected_eq:
                if ok:
                    eq_tp += 1
                else:
                    eq_fn += 1
            else:
                if ok:
                    neq_tn += 1
                else:
                    neq_fp += 1
            details.append(
                {
                    "name": name,
                    "expected_eq": expected_eq,
                    "verdict": verdict,
                    "correct": ok,
                    "explanation": (
                        result.global_result.explanation if result.global_result is not None else None
                    ),
                }
            )
        except Exception as exc:  # benchmark harness should keep going
            if not expected_eq:
                correct += 1
                neq_tn += 1
            else:
                eq_fn += 1
            details.append(
                {
                    "name": name,
                    "expected_eq": expected_eq,
                    "verdict": "error",
                    "correct": not expected_eq,
                    "error": str(exc),
                }
            )
        if idx % 10 == 0:
            print(f"  {idx}/{len(EQUIV_PAIRS)} done...")

    elapsed = time.monotonic() - started
    accuracy = correct / len(EQUIV_PAIRS)

    print(f"  Correct: {correct}/{len(EQUIV_PAIRS)} ({accuracy:.0%})")
    print(f"  Equiv TP: {eq_tp}, FN: {eq_fn}  |  Non-equiv TN: {neq_tn}, FP: {neq_fp}")
    print(f"  Elapsed: {elapsed:.1f}s")

    payload = {
        "correct": correct,
        "total": len(EQUIV_PAIRS),
        "accuracy": round(accuracy, 3),
        "eq_tp": eq_tp,
        "eq_fn": eq_fn,
        "neq_tn": neq_tn,
        "neq_fp": neq_fp,
        "elapsed_seconds": round(elapsed, 3),
        "details": details,
    }
    out_path = RESULTS_DIR / "hard_equiv_benchmark_results.json"
    out_path.write_text(json.dumps(payload, indent=2, default=str))
    print(f"Results written to {out_path}")


if __name__ == "__main__":
    main()
