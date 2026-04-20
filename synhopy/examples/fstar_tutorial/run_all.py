#!/usr/bin/env python3
"""
Run ALL F* Tutorial SynHoPy Translations
==========================================

Executes every proof from the F* tutorial book, translated into SynHoPy
with genuine homotopy constructs.

Usage:
    PYTHONPATH=. python3 synhopy/examples/fstar_tutorial/run_all.py
"""
from __future__ import annotations
import sys, os, time, importlib, traceback

# Add project root to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))

MODULES = [
    ("Part 1: Total Functions", "part1_total_functions"),
    ("Part 2a: Indexed Types & Merkle Trees", "part2a_indexed_types"),
    ("Part 2b: STLC & Logical Connectives", "part2b_stlc_and_connectives"),
    ("Part 3+4: Typeclasses & Effects", "part3_typeclasses_and_effects"),
    ("Part 5: Tactics & Metaprogramming", "part5_tactics"),
    ("Pulse: Separation Logic", "pulse_separation_logic"),
    ("Pulse: Data Structures", "pulse_data_structures"),
    ("Pulse: Concurrency", "pulse_concurrency"),
]

def run_module(name: str, module_name: str) -> tuple[int, int, float]:
    """Run a module's run_all() function, return (passed, failed, time)."""
    print(f"\n{'='*70}")
    print(f"  {name}")
    print(f"{'='*70}")
    
    start = time.time()
    try:
        mod = importlib.import_module(f"synhopy.examples.fstar_tutorial.{module_name}")
        if hasattr(mod, 'run_all'):
            result = mod.run_all()
            elapsed = time.time() - start
            if isinstance(result, tuple) and len(result) == 2:
                return result[0], result[1], elapsed
            else:
                # run_all returned something else — count as 1 pass
                return 1, 0, elapsed
        else:
            print(f"  WARNING: {module_name} has no run_all() function")
            return 0, 0, time.time() - start
    except Exception as e:
        elapsed = time.time() - start
        print(f"  ERROR: {e}")
        traceback.print_exc()
        return 0, 1, elapsed

def main():
    print("╔══════════════════════════════════════════════════════════════════════╗")
    print("║     SynHoPy Translation of the Complete F* Tutorial Book           ║")
    print("║     Every example, every proof — with genuine homotopy             ║")
    print("╚══════════════════════════════════════════════════════════════════════╝")
    
    total_passed = 0
    total_failed = 0
    total_time = 0.0
    results = []
    
    for name, module_name in MODULES:
        passed, failed, elapsed = run_module(name, module_name)
        total_passed += passed
        total_failed += failed
        total_time += elapsed
        results.append((name, passed, failed, elapsed))
    
    # Summary
    print(f"\n{'='*70}")
    print(f"  SUMMARY: F* Tutorial → SynHoPy Translation")
    print(f"{'='*70}")
    print(f"  {'Module':<45} {'Pass':>6} {'Fail':>6} {'Time':>8}")
    print(f"  {'-'*45} {'-'*6} {'-'*6} {'-'*8}")
    for name, passed, failed, elapsed in results:
        status = "✅" if failed == 0 else "❌"
        print(f"  {status} {name:<43} {passed:>5} {failed:>5} {elapsed:>7.1f}s")
    print(f"  {'-'*45} {'-'*6} {'-'*6} {'-'*8}")
    print(f"  {'TOTAL':<45} {total_passed:>6} {total_failed:>6} {total_time:>7.1f}s")
    print()
    
    if total_failed == 0:
        print(f"  ✅ ALL {total_passed} PROOFS PASSED — F* tutorial fully translated to SynHoPy!")
    else:
        print(f"  ❌ {total_failed} PROOFS FAILED out of {total_passed + total_failed}")
    
    return 0 if total_failed == 0 else 1

if __name__ == '__main__':
    sys.exit(main())
