#!/usr/bin/env python3
"""Evaluate deppy's sheaf-theoretic bug detector on the synthetic suite.

Runs all 40 functions (20 bug types × {buggy, safe}) through:
  1. deppy's sheaf detector (types-as-sheaf-objects, gluing obstructions)
  2. a3-python's analyzer (if available)

Reports per-bug-type accuracy and a head-to-head comparison.

Metrics:
  - TRUE POSITIVE:  buggy variant flagged as having obstruction(s)
  - TRUE NEGATIVE:  safe variant has NO obstructions (all resolved by guards)
  - FALSE POSITIVE: safe variant falsely flagged
  - FALSE NEGATIVE: buggy variant missed (no obstructions found)
"""

from __future__ import annotations

import inspect
import json
import sys
import textwrap
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

# Add deppy to path
sys.path.insert(0, str(Path(__file__).parent / "src"))

from deppy.render.bug_detect import detect_bugs, format_bug_report, SheafBugReport

# Import the synthetic suite
sys.path.insert(0, str(Path(__file__).parent / "tests"))
from synthetic_bug_suite import SUITE


# ═══════════════════════════════════════════════════════════════════════════════
# Result types
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class CaseResult:
    """Result of running one function through the detector."""
    bug_type: str
    variant: str  # "buggy" or "safe"
    function_name: str
    # Sheaf detector
    sheaf_bugs_found: int = 0
    sheaf_matching_bugs: int = 0  # bugs matching the expected type
    sheaf_all_types: List[str] = field(default_factory=list)
    sheaf_resolved: int = 0
    sheaf_spurious: int = 0
    sheaf_elapsed_ms: float = 0.0
    sheaf_n_sites: int = 0
    sheaf_n_overlaps: int = 0
    # a3-python
    a3_bugs_found: int = 0
    a3_matching_bugs: int = 0
    a3_all_types: List[str] = field(default_factory=list)
    a3_elapsed_ms: float = 0.0
    # Classification
    correct: bool = False
    classification: str = ""  # TP, TN, FP, FN


@dataclass
class EvalSummary:
    """Aggregate evaluation results."""
    total_cases: int = 0
    sheaf_tp: int = 0
    sheaf_tn: int = 0
    sheaf_fp: int = 0
    sheaf_fn: int = 0
    a3_tp: int = 0
    a3_tn: int = 0
    a3_fp: int = 0
    a3_fn: int = 0
    per_type: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    case_results: List[CaseResult] = field(default_factory=list)
    total_elapsed_ms: float = 0.0


# ═══════════════════════════════════════════════════════════════════════════════
# a3-python integration
# ═══════════════════════════════════════════════════════════════════════════════

def _make_triggering_call(bug_type: str, func_name: str, source: str) -> Optional[str]:
    """Return a module-level call expression (no newline) that triggers bug_type.

    a3-python detects bugs via concrete symbolic execution of module-level code.
    Each buggy function must be called with arguments that actually reach the
    buggy site so a3 can observe the exception / unsafe state.

    Returns None when we do not know how to trigger the bug type concretely
    (e.g. non-termination, deadlock, memory leak) — in those cases a3's
    function-level analysis may still find something.
    """
    b = bug_type

    if b == "DIV_ZERO":
        if "modulus" in source:
            return f"{func_name}(1, 0)"             # modulus = 0
        if ": list" in source and "values" in source:
            return f"{func_name}([])"               # len([]) == 0
        return f"{func_name}(10, 0)"                # count = 0

    if b == "NULL_PTR":
        if "re.search" in source:
            return f"{func_name}('hello', 'XYZNOPATTERN123!@#')"  # no match → None
        return f"{func_name}({{}}, 'missing_key_xyz123')"         # .get() → None

    if b == "INDEX_OOB":
        if "-(n + 1)" in source or "(n + 1)" in source:
            return f"{func_name}([1], 1)"           # [1][-(1+1)] = [1][-2] → OOB
        if "(items: list)" in source and "n" not in source.split("(")[1].split(")")[0]:
            return f"{func_name}([])"               # items[0] on empty list
        return f"{func_name}([], 0)"                # items=[], position=0

    if b == "KEY_ERROR":
        return f"{func_name}({{}}, 'missing_key_xyz123')"         # {} ['x'] → KeyError

    if b == "TYPE_ERROR":
        if "join" in source:
            return f"{func_name}([1, 'hello'])"     # int in join → TypeError
        if "len" in source:
            return f"{func_name}(42)"               # len(42) → TypeError
        return f"{func_name}('Alice', 30)"           # str + int → TypeError

    if b == "ASSERT_FAIL":
        if "ratio" in source:
            return f"{func_name}(2.0)"              # ratio > 1 → assert fails
        if "isinstance" in source and "int" in source:
            return f"{func_name}('not_an_int')"     # isinstance fails
        return f"{func_name}([])"                   # assert len([]) > 0 fails

    if b == "UNBOUND_VAR":
        if "mode" in source:
            return f"{func_name}('unrecognized_mode_xyz')"  # no branch taken
        if "range" in source and "last" in source:
            return f"{func_name}(0)"                # range(0) → loop never runs
        return f"{func_name}(False)"                # flag=False → x not assigned

    if b == "INTEGER_OVERFLOW":
        if "shift" in source:
            return f"{func_name}(1, 31)"            # 1 << 31 > int32 max
        if "(a: int, b: int)" in source or "a + b" in source:
            return f"{func_name}(2**30, 2**30)"     # sum = 2**31 > int32 max
        return f"{func_name}(2**31)"                # value = 2**31 → pack fails

    if b == "OVERFLOW":
        if "n_bits" in source or "shift" in source:
            return f"{func_name}(1, 63)"            # 1 << 63 = 2**63 > int64 max
        if ": list" in source and "values" in source:
            return f"{func_name}([2**30, 2**30, 2**30])"  # sum > int32 max
        return f"{func_name}(2**32, 2**32)"         # product = 2**64 > int64 max

    if b == "TYPE_CONFUSION":
        # list(42) → TypeError: 'int' object is not iterable
        # len(42)  → TypeError: object of type 'int' has no len()
        # sorted(42) → TypeError: 'int' object is not iterable
        return f"{func_name}(42)"

    if b == "BOUNDS":
        if "buf" in source or "bytearray" in source:
            return f"{func_name}(bytearray(3), 10, 1)"  # index 10 on 3-byte buf
        return f"{func_name}([1, 2, 3], 0, 10)"    # range(10) → [3], [4].. IndexError

    return None  # Don't know a concrete trigger for this bug type


def _try_a3_analyze(source: str, bug_type: str) -> Tuple[int, int, List[str], float]:
    """Try to analyze source with a3-python. Returns (total, matching, types, ms).

    a3-python detects bugs via concrete module-level execution (its symbolic VM
    explores the executed code path and checks unsafe predicates).  A plain
    function definition with no call produces no execution trace and no findings.

    Strategy: write the function source, then append a crash-triggering call
    for bug types where we know the right arguments.  The call uses arguments
    that reach the buggy site so a3 can observe the resulting exception/state.
    For bug types where we cannot reliably trigger the crash concretely
    (NON_TERMINATION, DEADLOCK, etc.), we omit the call and rely on a3's
    function-level entry-point analysis, which may still find the bug.
    """
    import tempfile
    import os
    try:
        from a3_python.analyzer import analyze_file as a3_analyze_file_fn
    except ImportError:
        return 0, 0, ["a3-python not installed"], 0.0

    tmp = None
    try:
        # Extract first function name
        func_name: Optional[str] = None
        for line in source.split('\n'):
            stripped = line.strip()
            if stripped.startswith('def ') and '(' in stripped:
                func_name = stripped[4:stripped.index('(')]
                break

        # Build source: function definition + bug-triggering module-level call
        call_expr = _make_triggering_call(bug_type, func_name, source) if func_name else None
        if call_expr:
            full_source = source + f"\n{call_expr}\n"
        else:
            full_source = source

        tmp = tempfile.NamedTemporaryFile(
            mode='w', suffix='.py', prefix='a3_eval_', delete=False
        )
        tmp.write(full_source)
        tmp.flush()
        tmp.close()

        t0 = time.perf_counter()

        file_result = a3_analyze_file_fn(
            tmp.name,
            full_source,
            max_paths=2000,
            max_depth=5000,
        )

        elapsed = (time.perf_counter() - t0) * 1000

        all_types: List[str] = []
        matching = 0

        for bug in file_result.bugs:
            all_types.append(bug.bug_type)
            if _bug_types_match(bug.bug_type, bug_type):
                matching += 1

        total = len(file_result.bugs)
        return total, matching, all_types, elapsed

    except Exception as e:
        return 0, 0, [f"error: {type(e).__name__}: {e}"], 0.0
    finally:
        if tmp and os.path.exists(tmp.name):
            os.unlink(tmp.name)


def _bug_types_match(found: str, expected: str) -> bool:
    """Check if a3's bug type matches our expected bug type.

    a3-python classifies bugs using its own naming scheme that differs from
    the suite's canonical names.  Key mappings based on a3's unsafe/registry.py:

      a3 reports  → suite expects
      ─────────────────────────────────────────────────────────────────
      BOUNDS       ← INDEX_OOB  (IndexError classified as BOUNDS)
      BOUNDS       ← KEY_ERROR  (KeyError classified as BOUNDS)
      TYPE_CONFUSION ← TYPE_ERROR  (TypeError classified as TYPE_CONFUSION)
      NAME_ERROR / UNBOUND_LOCAL ← UNBOUND_VAR
      STACK_OVERFLOW ← RUNTIME_ERROR  (RecursionError → STACK_OVERFLOW)
      INTEGER_OVERFLOW ← OVERFLOW  (OverflowError → INTEGER_OVERFLOW)
    """
    found_lower = found.lower().replace('_', '').replace('-', '')
    expected_lower = expected.lower().replace('_', '').replace('-', '')

    if found_lower == expected_lower:
        return True

    # Each canonical name maps to the set of a3 bug-type strings that mean it.
    _ALIASES: Dict[str, Set[str]] = {
        "divzero":          {"zerodivisionerror", "divisionbyzero", "divzero"},
        "nullptr":          {"nullderef", "nonederef", "nullptr", "attributeerror",
                             "nonetype", "nonemisuse"},
        # a3 classifies IndexError → BOUNDS; also accept INDEX_OOB directly
        "indexoob":         {"indexerror", "indexoob", "indexoutofbounds",
                             "outofbounds", "bounds", "boundsviolation"},
        # a3 classifies KeyError → BOUNDS
        "keyerror":         {"keyerror", "missingkey", "bounds", "lookuperror",
                             "lookup"},
        # a3 classifies TypeError → TYPE_CONFUSION
        "typeerror":        {"typeerror", "typemismatch", "carriermismatch",
                             "typeconfusion"},
        "assertfail":       {"assertionerror", "assertfail", "assertionfailure"},
        # a3 classifies NameError → NAME_ERROR, UnboundLocalError → UNBOUND_LOCAL
        "unboundvar":       {"unboundlocalerror", "unboundvar", "nameerror",
                             "unbound", "namelocalerror", "nameerror",
                             "unbound", "unboundlocal"},
        "integeroverflow":  {"integeroverflow", "overflowerror", "overflow"},
        "nontermination":   {"nontermination", "infiniteloop", "nonterminating",
                             "nontermination"},
        "memoryleak":       {"memoryleak", "resourceleak", "unclosedresource"},
        "useafterfree":     {"useafterfree", "useafterclose"},
        "doublefree":       {"doublefree", "doubleclose"},
        "datarace":         {"datarace", "racecondition", "toctou"},
        "deadlock":         {"deadlock", "lockorder"},
        "timingchannel":    {"timingchannel", "timingsidewindow", "timingleak"},
        "infoleak":         {"infoleak", "informationleak", "informationdisclosure"},
        "bounds":           {"bounds", "boundscheck", "outofbounds", "boundsviolation"},
        # a3 classifies RecursionError → STACK_OVERFLOW
        "runtimeerror":     {"runtimeerror", "recursionerror", "stackoverflow",
                             "stackoverflowerror", "recursionerror"},
        "typeconfusion":    {"typeconfusion", "typeerror", "attributeerror"},
        # a3 classifies OverflowError → INTEGER_OVERFLOW
        "overflow":         {"overflow", "integeroverflow", "arithmeticoverflow",
                             "overflowerror"},
    }

    for canonical, aliases in _ALIASES.items():
        if found_lower in aliases and expected_lower in aliases:
            return True
        if expected_lower == canonical and found_lower in aliases:
            return True
        if found_lower == canonical and expected_lower in aliases:
            return True

    # Substring match as last resort
    if found_lower in expected_lower or expected_lower in found_lower:
        return True

    return False


# ═══════════════════════════════════════════════════════════════════════════════
# Run evaluation
# ═══════════════════════════════════════════════════════════════════════════════

def evaluate_case(
    bug_type: str,
    func: Any,
    variant: str,
    description: str,
) -> CaseResult:
    """Evaluate a single function."""
    source = textwrap.dedent(inspect.getsource(func))
    result = CaseResult(
        bug_type=bug_type,
        variant=variant,
        function_name=func.__name__,
    )

    # Run sheaf detector
    report = detect_bugs(
        source,
        function_name=func.__name__,
        bug_types={bug_type},
    )
    result.sheaf_bugs_found = report.genuine_obstructions
    result.sheaf_matching_bugs = sum(
        1 for o in report.findings if o.bug_type == bug_type
    )
    result.sheaf_all_types = [o.bug_type for o in report.findings]
    result.sheaf_resolved = report.resolved_obstructions
    result.sheaf_spurious = report.spurious_obstructions
    result.sheaf_elapsed_ms = report.elapsed_ms
    result.sheaf_n_sites = report.n_sites
    result.sheaf_n_overlaps = report.n_overlaps

    # Run a3-python
    a3_total, a3_match, a3_types, a3_ms = _try_a3_analyze(source, bug_type)
    result.a3_bugs_found = a3_total
    result.a3_matching_bugs = a3_match
    result.a3_all_types = a3_types
    result.a3_elapsed_ms = a3_ms

    # Classify
    if variant == "buggy":
        if result.sheaf_matching_bugs > 0:
            result.classification = "TP"
            result.correct = True
        else:
            result.classification = "FN"
            result.correct = False
    else:  # safe
        if result.sheaf_matching_bugs == 0:
            result.classification = "TN"
            result.correct = True
        else:
            result.classification = "FP"
            result.correct = False

    return result


def run_evaluation() -> EvalSummary:
    """Run the full evaluation suite."""
    summary = EvalSummary()
    t0 = time.perf_counter()

    for bug_type, buggy_func, safe_func, description in SUITE:
        # Test buggy variant
        buggy_result = evaluate_case(bug_type, buggy_func, "buggy", description)
        summary.case_results.append(buggy_result)
        summary.total_cases += 1

        # Test safe variant
        safe_result = evaluate_case(bug_type, safe_func, "safe", description)
        summary.case_results.append(safe_result)
        summary.total_cases += 1

        # Aggregate sheaf results
        if buggy_result.classification == "TP":
            summary.sheaf_tp += 1
        elif buggy_result.classification == "FN":
            summary.sheaf_fn += 1
        if safe_result.classification == "TN":
            summary.sheaf_tn += 1
        elif safe_result.classification == "FP":
            summary.sheaf_fp += 1

        # Aggregate a3 results
        if buggy_result.a3_matching_bugs > 0:
            summary.a3_tp += 1
        else:
            summary.a3_fn += 1
        if safe_result.a3_matching_bugs == 0:
            summary.a3_tn += 1
        else:
            summary.a3_fp += 1

        # Per-type: keyed by (bug_type, buggy_func_name) to support multiple pairs
        key = f"{bug_type}:{buggy_func.__name__}"
        summary.per_type[key] = {
            "bug_type": bug_type,
            "description": description,
            "sheaf_buggy_detected": buggy_result.sheaf_matching_bugs > 0,
            "sheaf_safe_clear": safe_result.sheaf_matching_bugs == 0,
            "sheaf_buggy_detail": buggy_result.classification,
            "sheaf_safe_detail": safe_result.classification,
            "a3_buggy_detected": buggy_result.a3_matching_bugs > 0,
            "a3_safe_clear": safe_result.a3_matching_bugs == 0,
            "sheaf_buggy_bugs": buggy_result.sheaf_all_types,
            "sheaf_safe_bugs": safe_result.sheaf_all_types,
            "sheaf_safe_resolved": safe_result.sheaf_resolved,
        }

    summary.total_elapsed_ms = (time.perf_counter() - t0) * 1000
    return summary


# ═══════════════════════════════════════════════════════════════════════════════
# Output formatting
# ═══════════════════════════════════════════════════════════════════════════════

def format_results(summary: EvalSummary) -> str:
    """Format evaluation results as a readable report."""
    lines = []
    lines.append("=" * 100)
    lines.append("SHEAF-THEORETIC BUG DETECTION: SYNTHETIC SUITE EVALUATION")
    lines.append("Types as sheaf objects | Bugs as gluing obstructions | Guards as restriction maps")
    lines.append(f"Suite: {len(SUITE)} pairs × 2 variants = {len(SUITE) * 2} test cases")
    lines.append("=" * 100)
    lines.append("")

    # Per-case results table
    lines.append(f"{'Pair':<36} {'Sheaf':^13} {'a3-python':^13} {'Notes'}")
    lines.append(f"{'':─<36} {'buggy safe':─^13} {'buggy safe':─^13} {'':─<30}")

    for bug_type, buggy_func, safe_func, desc in SUITE:
        key = f"{bug_type}:{buggy_func.__name__}"
        info = summary.per_type[key]

        sb_mark = " [+]" if info["sheaf_buggy_detected"] else " [-]"
        ss_mark = " [+]" if info["sheaf_safe_clear"] else " [!]"
        ab_mark = " [+]" if info["a3_buggy_detected"] else " [-]"
        as_mark = " [+]" if info["a3_safe_clear"] else " [!]"

        pair_label = f"{bug_type} ({buggy_func.__name__})"
        lines.append(
            f"{pair_label:<36} {sb_mark} {ss_mark}     {ab_mark} {as_mark}    {desc}"
        )

    lines.append("")
    lines.append("─" * 100)

    # Summary statistics
    n_pairs = len(SUITE)
    lines.append("")
    lines.append("SUMMARY")
    lines.append("─" * 60)
    lines.append(f"  Total pairs: {n_pairs}  (3 × 20 bug types × 2 variants = {n_pairs * 2} cases)")
    lines.append(f"                    {'Sheaf Detector':>16}  {'a3-python':>12}")
    lines.append(f"  True Positives:   {summary.sheaf_tp:>16}  {summary.a3_tp:>12}")
    lines.append(f"  True Negatives:   {summary.sheaf_tn:>16}  {summary.a3_tn:>12}")
    lines.append(f"  False Positives:  {summary.sheaf_fp:>16}  {summary.a3_fp:>12}")
    lines.append(f"  False Negatives:  {summary.sheaf_fn:>16}  {summary.a3_fn:>12}")
    lines.append(f"  ─────────────────────────────────────────────────────────")

    sheaf_total = summary.sheaf_tp + summary.sheaf_tn + summary.sheaf_fp + summary.sheaf_fn
    a3_total = summary.a3_tp + summary.a3_tn + summary.a3_fp + summary.a3_fn
    sheaf_acc = (summary.sheaf_tp + summary.sheaf_tn) / sheaf_total if sheaf_total else 0
    a3_acc = (summary.a3_tp + summary.a3_tn) / a3_total if a3_total else 0
    sheaf_prec = summary.sheaf_tp / (summary.sheaf_tp + summary.sheaf_fp) if (summary.sheaf_tp + summary.sheaf_fp) else 0
    sheaf_rec = summary.sheaf_tp / (summary.sheaf_tp + summary.sheaf_fn) if (summary.sheaf_tp + summary.sheaf_fn) else 0
    a3_prec = summary.a3_tp / (summary.a3_tp + summary.a3_fp) if (summary.a3_tp + summary.a3_fp) else 0
    a3_rec = summary.a3_tp / (summary.a3_tp + summary.a3_fn) if (summary.a3_tp + summary.a3_fn) else 0

    lines.append(f"  Accuracy:         {sheaf_acc:>15.0%}  {a3_acc:>12.0%}")
    lines.append(f"  Precision:        {sheaf_prec:>15.0%}  {a3_prec:>12.0%}")
    lines.append(f"  Recall (TP rate): {sheaf_rec:>15.0%}  {a3_rec:>12.0%}")

    sheaf_f1 = 2 * sheaf_prec * sheaf_rec / (sheaf_prec + sheaf_rec) if (sheaf_prec + sheaf_rec) else 0
    a3_f1 = 2 * a3_prec * a3_rec / (a3_prec + a3_rec) if (a3_prec + a3_rec) else 0
    lines.append(f"  F1 Score:         {sheaf_f1:>15.0%}  {a3_f1:>12.0%}")
    lines.append("")
    lines.append(f"  Total time: {summary.total_elapsed_ms:.0f}ms")
    lines.append("")

    # Detailed per-case results
    lines.append("DETAILED RESULTS")
    lines.append("─" * 100)
    for cr in summary.case_results:
        marker = {"TP": "[+]", "TN": "[+]", "FP": "[!]", "FN": "[-]"}.get(cr.classification, "[?]")
        found_str = f"found={cr.sheaf_matching_bugs}"
        resolved_str = f"resolved={cr.sheaf_resolved}"
        time_str = f"{cr.sheaf_elapsed_ms:.1f}ms"
        cover_str = f"sites={cr.sheaf_n_sites},overlaps={cr.sheaf_n_overlaps}"
        a3_str = f"a3={cr.a3_all_types[0] if cr.a3_all_types else 'none'}"
        lines.append(
            f"  {marker} {cr.bug_type:<22} {cr.function_name:<30} {cr.variant:<6} "
            f"{cr.classification:<4} {found_str:<10} {resolved_str:<12} {time_str:<10} "
            f"{cover_str}  {a3_str}"
        )

    lines.append("")
    lines.append("Legend: [+] = correct, [-] = missed (FN), [!] = false alarm (FP)")
    lines.append("")

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("Running sheaf-theoretic bug detection evaluation on synthetic suite...")
    print(f"Suite: {len(SUITE)} pairs × 2 variants = {len(SUITE) * 2} test cases")
    print()

    summary = run_evaluation()

    # Print formatted report
    report = format_results(summary)
    print(report)

    # Save results
    results_path = Path(__file__).parent / "eval_synthetic_results.json"
    results_data = {
        "total_cases": summary.total_cases,
        "n_pairs": len(SUITE),
        "sheaf": {
            "tp": summary.sheaf_tp,
            "tn": summary.sheaf_tn,
            "fp": summary.sheaf_fp,
            "fn": summary.sheaf_fn,
            "accuracy": (summary.sheaf_tp + summary.sheaf_tn) / summary.total_cases if summary.total_cases else 0,
        },
        "a3": {
            "tp": summary.a3_tp,
            "tn": summary.a3_tn,
            "fp": summary.a3_fp,
            "fn": summary.a3_fn,
            "accuracy": (summary.a3_tp + summary.a3_tn) / summary.total_cases if summary.total_cases else 0,
        },
        "per_type": summary.per_type,
        "elapsed_ms": summary.total_elapsed_ms,
    }
    results_path.write_text(json.dumps(results_data, indent=2, default=str))
    print(f"\nResults saved to: {results_path}")

    # Save text report
    report_path = Path(__file__).parent / "eval_synthetic_report.txt"
    report_path.write_text(report)
    print(f"Report saved to: {report_path}")
