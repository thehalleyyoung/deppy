#!/usr/bin/env python3
"""Runner for the 9 bug-type detection test suite.

Each example file exports:
  EXAMPLES: list of (name, buggy_src, safe_src, desc) tuples
  BUG_TYPE: str  — expected bug type code from BUG_SPECS
  BUG_DESC: str  — overall description

Run: PYTHONPATH=deppy/src:deppy/tests python3 deppy/tests/test_bug_types/runner.py [-v]
"""
from __future__ import annotations

import importlib
import os
import sys
import time
from dataclasses import dataclass
from typing import List

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'src'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from deppy.render.bug_detect import detect_bugs


@dataclass
class CaseResult:
    bug_type: str
    example_name: str
    buggy_detected: bool
    safe_clean: bool
    elapsed_ms: float
    error: str = ""


def _has_bug(source: str, bug_type: str) -> bool:
    """Check if detect_bugs finds the given bug type in source."""
    try:
        report = detect_bugs(source, bug_types={bug_type})
        return any(o.confidence > 0 and o.bug_type == bug_type
                   for o in report.obstructions)
    except Exception:
        return False


def discover_and_run(verbose: bool = False) -> List[CaseResult]:
    examples_dir = os.path.dirname(os.path.abspath(__file__))
    results: List[CaseResult] = []
    modules = []

    for fname in sorted(os.listdir(examples_dir)):
        if not fname.endswith('.py') or fname in ('__init__.py', 'runner.py'):
            continue
        modname = fname[:-3]
        try:
            mod = importlib.import_module(f'test_bug_types.{modname}')
            modules.append((modname, mod))
        except Exception as e:
            print(f"  WARNING: Failed to load {fname}: {e}")

    total_examples = sum(len(m.EXAMPLES) for _, m in modules)
    print(f"{'=' * 100}")
    print(f"  Sheaf Bug Detector — 9 Bug Types × {total_examples} Examples")
    print(f"{'=' * 100}")
    print(f"  {'Bug Type':<20} {'Example':<25} {'Buggy':>8} {'Safe':>8} {'Time':>8}")
    print(f"  {'─' * 20} {'─' * 25} {'─' * 8} {'─' * 8} {'─' * 8}")

    for modname, mod in modules:
        bug_type = mod.BUG_TYPE
        for ex_name, buggy_src, safe_src, desc in mod.EXAMPLES:
            t0 = time.time()
            buggy_found = _has_bug(buggy_src, bug_type)
            safe_found = _has_bug(safe_src, bug_type)
            elapsed = (time.time() - t0) * 1000

            r = CaseResult(
                bug_type=bug_type,
                example_name=ex_name,
                buggy_detected=buggy_found,
                safe_clean=not safe_found,
                elapsed_ms=elapsed,
            )
            results.append(r)

            b_col = "\033[32m" if r.buggy_detected else "\033[31m"
            s_col = "\033[32m" if r.safe_clean else "\033[31m"
            b_mark = "FOUND" if r.buggy_detected else "MISS"
            s_mark = "CLEAN" if r.safe_clean else "FP"
            print(f"  {bug_type:<20} {ex_name:<25} "
                  f"{b_col}{b_mark:>8}\033[0m "
                  f"{s_col}{s_mark:>8}\033[0m "
                  f"{elapsed:>6.0f}ms")

    # Summary by bug type
    bug_types_seen = []
    for _, m in modules:
        if m.BUG_TYPE not in [b for b, _ in bug_types_seen]:
            bug_types_seen.append((m.BUG_TYPE, m.BUG_DESC))

    print(f"\n{'=' * 100}")
    print(f"  PER-TYPE SUMMARY")
    print(f"{'=' * 100}")
    print(f"  {'Bug Type':<20} {'TP':>4} {'TN':>4} {'FP':>4} {'FN':>4} {'F1':>8}")
    print(f"  {'─' * 20} {'─' * 4} {'─' * 4} {'─' * 4} {'─' * 4} {'─' * 8}")

    total_tp = total_tn = total_fp = total_fn = 0
    for bt, desc in bug_types_seen:
        bt_results = [r for r in results if r.bug_type == bt]
        tp = sum(1 for r in bt_results if r.buggy_detected)
        fn = sum(1 for r in bt_results if not r.buggy_detected)
        tn = sum(1 for r in bt_results if r.safe_clean)
        fp = sum(1 for r in bt_results if not r.safe_clean)
        total_tp += tp; total_tn += tn; total_fp += fp; total_fn += fn
        prec = tp / (tp + fp) if (tp + fp) > 0 else 0
        rec = tp / (tp + fn) if (tp + fn) > 0 else 0
        f1 = 2 * prec * rec / (prec + rec) if (prec + rec) > 0 else 0
        print(f"  {bt:<20} {tp:>4} {tn:>4} {fp:>4} {fn:>4} {f1:>8.2f}")

    print(f"  {'─' * 20} {'─' * 4} {'─' * 4} {'─' * 4} {'─' * 4} {'─' * 8}")
    n = len(results)
    prec = total_tp / (total_tp + total_fp) if (total_tp + total_fp) > 0 else 0
    rec = total_tp / (total_tp + total_fn) if (total_tp + total_fn) > 0 else 0
    f1 = 2 * prec * rec / (prec + rec) if (prec + rec) > 0 else 0
    print(f"  {'TOTAL':<20} {total_tp:>4} {total_tn:>4} {total_fp:>4} {total_fn:>4} {f1:>8.2f}")
    total_time = sum(r.elapsed_ms for r in results)
    print(f"\n  Precision: {prec:.1%}  Recall: {rec:.1%}  F1: {f1:.1%}  Time: {total_time:.0f}ms")
    print(f"{'=' * 100}")

    return results


if __name__ == '__main__':
    verbose = '--verbose' in sys.argv or '-v' in sys.argv
    discover_and_run(verbose=verbose)
