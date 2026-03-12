#!/usr/bin/env python3
"""BugsInPy evaluation harness: compare sheaf-theoretic bug detection vs a3-python.

For each BugsInPy bug:
  1. Parse the bug patch to extract the buggy file and relevant code
  2. Classify the bug type from the patch (heuristic)
  3. Run deppy sheaf detector on the buggy code
  4. Run a3-python analyzer on the buggy code
  5. Compare detection results

Usage:
    python eval_bugsinpy.py [--bugsinpy-dir /tmp/BugsInPy] [--max-bugs 50]
"""

from __future__ import annotations

import ast
import json
import os
import re
import sys
import textwrap
import time
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

# Add deppy to path
sys.path.insert(0, str(Path(__file__).parent / "src"))

from deppy.render.bug_detect import detect_bugs, detect_bugs_in_file, format_bug_report, BUG_SPECS


# ═══════════════════════════════════════════════════════════════════════════════
# Bug type classification from patches
# ═══════════════════════════════════════════════════════════════════════════════

# Map keywords in patches to a3-python bug type codes
PATCH_BUG_CLASSIFIERS: List[Tuple[str, str, float]] = [
    # (pattern_in_patch, bug_type_code, confidence)
    # Division by zero
    (r"ZeroDivisionError", "DIV_ZERO", 0.95),
    (r"division by zero", "DIV_ZERO", 0.90),
    (r"/ 0\b|/0\b|== 0.*[/]", "DIV_ZERO", 0.60),

    # None dereference
    (r"AttributeError.*None", "NULL_PTR", 0.90),
    (r"NoneType.*has no attribute", "NULL_PTR", 0.95),
    (r"is not None|is None|!= None|== None", "NULL_PTR", 0.50),
    (r"if .+ is None", "NULL_PTR", 0.60),

    # Index out of bounds
    (r"IndexError", "INDEX_OOB", 0.95),
    (r"index out of (range|bounds)", "INDEX_OOB", 0.90),
    (r"list index out of range", "INDEX_OOB", 0.95),

    # Key error
    (r"KeyError", "KEY_ERROR", 0.95),
    (r"key.*not found|missing key", "KEY_ERROR", 0.80),

    # Type error
    (r"TypeError", "TYPE_ERROR", 0.90),
    (r"type.*mismatch|unexpected type|wrong type", "TYPE_ERROR", 0.70),
    (r"isinstance\(", "TYPE_ERROR", 0.40),

    # Value error
    (r"ValueError", "VALUE_ERROR", 0.90),
    (r"invalid (value|literal|argument)", "VALUE_ERROR", 0.70),

    # Runtime error
    (r"RuntimeError", "RUNTIME_ERROR", 0.85),

    # File not found
    (r"FileNotFoundError", "FILE_NOT_FOUND", 0.95),
    (r"No such file or directory", "FILE_NOT_FOUND", 0.90),

    # Import error
    (r"ImportError|ModuleNotFoundError", "IMPORT_ERROR", 0.90),

    # Assertion failure
    (r"AssertionError", "ASSERT_FAIL", 0.90),
    (r"assert\s+", "ASSERT_FAIL", 0.30),

    # Overflow
    (r"OverflowError", "OVERFLOW", 0.90),
    (r"overflow", "OVERFLOW", 0.50),

    # Unbound variable
    (r"NameError|UnboundLocalError", "UNBOUND_VAR", 0.90),

    # Connection/timeout
    (r"ConnectionError|TimeoutError", "CONNECTION_ERROR", 0.85),
    (r"timeout", "TIMEOUT_ERROR", 0.50),

    # Permission
    (r"PermissionError", "PERMISSION_ERROR", 0.90),

    # Unicode
    (r"UnicodeError|UnicodeDecodeError|UnicodeEncodeError", "UNICODE_ERROR", 0.90),
]


def classify_bug_from_patch(patch_text: str, test_text: str = "") -> List[Tuple[str, float]]:
    """Classify the bug type from the patch text and test file.

    Returns a list of (bug_type_code, confidence) tuples, sorted by confidence.
    """
    combined = patch_text + "\n" + test_text
    matches: List[Tuple[str, float]] = []
    seen = set()

    for pattern, bug_code, base_conf in PATCH_BUG_CLASSIFIERS:
        if bug_code in seen:
            continue
        hits = len(re.findall(pattern, combined, re.IGNORECASE))
        if hits > 0:
            # Boost confidence with more matches
            conf = min(base_conf + 0.05 * (hits - 1), 0.99)
            matches.append((bug_code, conf))
            seen.add(bug_code)

    matches.sort(key=lambda x: -x[1])
    return matches


# ═══════════════════════════════════════════════════════════════════════════════
# Patch parsing: extract buggy code from unified diffs
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class PatchInfo:
    """Parsed information from a BugsInPy bug patch."""
    project: str
    bug_id: int
    files_changed: List[str]
    # Lines removed in the fix (= the buggy lines)
    buggy_lines: Dict[str, List[str]]
    # Lines added in the fix
    fix_lines: Dict[str, List[str]]
    # Full patch text
    raw_patch: str
    # Test file path
    test_file: str = ""
    python_version: str = ""


def parse_patch(patch_path: Path, info_path: Path) -> PatchInfo:
    """Parse a BugsInPy bug patch and info file."""
    raw = patch_path.read_text(errors="replace")
    info_text = info_path.read_text(errors="replace") if info_path.exists() else ""

    # Parse info
    test_file = ""
    python_version = ""
    for line in info_text.splitlines():
        if line.startswith("test_file="):
            test_file = line.split("=", 1)[1].strip().strip('"')
        if line.startswith("python_version="):
            python_version = line.split("=", 1)[1].strip().strip('"')

    # Parse diff
    files_changed: List[str] = []
    buggy_lines: Dict[str, List[str]] = defaultdict(list)
    fix_lines: Dict[str, List[str]] = defaultdict(list)
    current_file = ""

    for line in raw.splitlines():
        if line.startswith("diff --git"):
            parts = line.split()
            if len(parts) >= 4:
                current_file = parts[3].lstrip("b/")
                files_changed.append(current_file)
        elif line.startswith("-") and not line.startswith("---"):
            buggy_lines[current_file].append(line[1:])
        elif line.startswith("+") and not line.startswith("+++"):
            fix_lines[current_file].append(line[1:])

    project = patch_path.parent.parent.parent.name

    return PatchInfo(
        project=project,
        bug_id=int(patch_path.parent.name),
        files_changed=files_changed,
        buggy_lines=dict(buggy_lines),
        fix_lines=dict(fix_lines),
        raw_patch=raw,
        test_file=test_file,
        python_version=python_version,
    )


def extract_buggy_functions_from_patch(patch: PatchInfo) -> List[Tuple[str, str]]:
    """Extract function-sized code snippets around the buggy lines.

    Returns list of (function_name, source_code) tuples.
    Since we don't have the full source, we construct minimal synthetic
    functions from the patch context.
    """
    functions: List[Tuple[str, str]] = []
    seen_names: Set[str] = set()

    # Parse the patch into per-file hunks
    hunks = _parse_hunks(patch.raw_patch)

    for file_path, hunk_lines_list in hunks.items():
        if not file_path.endswith(".py"):
            continue

        for hunk_lines in hunk_lines_list:
            # Build buggy version: context + removed lines (skip added lines)
            buggy_lines = []
            for line in hunk_lines:
                if line.startswith(" "):
                    buggy_lines.append(line[1:])
                elif line.startswith("-"):
                    buggy_lines.append(line[1:])
                # Skip "+" lines (those are the fix)

            if not buggy_lines:
                continue

            snippet = "\n".join(buggy_lines)

            # Strategy 1: parse as-is and extract functions
            try:
                tree = ast.parse(snippet)
                for node in ast.walk(tree):
                    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        if node.name not in seen_names:
                            func_src = ast.unparse(node)
                            functions.append((node.name, func_src))
                            seen_names.add(node.name)
                continue
            except SyntaxError:
                pass

            # Strategy 2: dedent and try again
            try:
                dedented = textwrap.dedent(snippet)
                tree = ast.parse(dedented)
                for node in ast.walk(tree):
                    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        if node.name not in seen_names:
                            func_src = ast.unparse(node)
                            functions.append((node.name, func_src))
                            seen_names.add(node.name)
                continue
            except SyntaxError:
                pass

            # Strategy 3: wrap non-function code in synthetic function
            buggy_body = "\n".join(buggy_lines)
            try:
                indented = textwrap.indent(textwrap.dedent(buggy_body), "    ")
                func = f"def _buggy_{len(functions)}():\n{indented}"
                tree = ast.parse(func)
                name = f"_buggy_{len(functions)}"
                if name not in seen_names:
                    functions.append((name, func))
                    seen_names.add(name)
            except SyntaxError:
                pass

    return functions


def _parse_hunks(raw_patch: str) -> Dict[str, List[List[str]]]:
    """Parse a unified diff into per-file hunks."""
    result: Dict[str, List[List[str]]] = defaultdict(list)
    current_file = ""
    current_hunk: List[str] = []

    for line in raw_patch.splitlines():
        if line.startswith("diff --git"):
            if current_hunk and current_file:
                result[current_file].append(current_hunk)
            current_hunk = []
            parts = line.split()
            if len(parts) >= 4:
                current_file = parts[3].lstrip("b/")
        elif line.startswith("@@"):
            if current_hunk and current_file:
                result[current_file].append(current_hunk)
            current_hunk = []
        elif line.startswith(("---", "+++")):
            continue
        elif line.startswith((" ", "-", "+")):
            current_hunk.append(line)

    if current_hunk and current_file:
        result[current_file].append(current_hunk)

    return dict(result)


# ═══════════════════════════════════════════════════════════════════════════════
# Run a3-python analyzer
# ═══════════════════════════════════════════════════════════════════════════════

def run_a3_on_source(source: str, filepath: str = "/tmp/_sheaf_eval.py") -> Dict[str, Any]:
    """Run a3-python on a source string, return results."""
    try:
        from a3_python.analyzer import Analyzer
    except ImportError:
        return {"error": "a3-python not installed", "bugs": []}

    # Write source to temp file
    p = Path(filepath)
    p.write_text(source)

    try:
        analyzer = Analyzer(
            max_paths=500,
            max_depth=500,
            timeout_ms=5000,
            verbose=False,
        )
        result = analyzer.analyze_all_functions(p)
        return result
    except Exception as e:
        return {"error": str(e), "bugs": []}
    finally:
        if p.exists():
            p.unlink()


# ═══════════════════════════════════════════════════════════════════════════════
# Comparison logic
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class BugEvalResult:
    """Result of evaluating one BugsInPy bug with both tools."""
    project: str
    bug_id: int
    classified_type: str
    classified_confidence: float
    # Sheaf detector
    sheaf_detected: bool
    sheaf_bug_types: List[str]
    sheaf_n_findings: int
    sheaf_ms: float
    # a3-python
    a3_detected: bool
    a3_bug_types: List[str]
    a3_n_findings: int
    # Metadata
    n_functions: int
    patch_files: List[str]


@dataclass
class EvalSummary:
    """Summary of evaluation across all bugs."""
    total_bugs: int = 0
    classifiable_bugs: int = 0  # Bugs whose type we could identify
    # Per-tool detection counts
    sheaf_true_positive: int = 0
    sheaf_false_negative: int = 0
    a3_true_positive: int = 0
    a3_false_negative: int = 0
    # Both
    both_detected: int = 0
    neither_detected: int = 0
    sheaf_only: int = 0
    a3_only: int = 0
    # By bug type
    by_type: Dict[str, Dict[str, int]] = field(default_factory=lambda: defaultdict(lambda: {
        "total": 0, "sheaf_tp": 0, "a3_tp": 0
    }))
    # Timing
    sheaf_total_ms: float = 0.0
    a3_total_ms: float = 0.0


def evaluate_bug(
    patch: PatchInfo,
    bug_type: str,
    confidence: float,
) -> BugEvalResult:
    """Evaluate a single BugsInPy bug with both detectors."""
    functions = extract_buggy_functions_from_patch(patch)

    sheaf_detected = False
    sheaf_types: List[str] = []
    sheaf_findings = 0
    sheaf_ms = 0.0

    a3_detected = False
    a3_types: List[str] = []
    a3_findings = 0

    for func_name, func_source in functions:
        # Run sheaf detector
        try:
            report = detect_bugs(func_source, function_name=func_name)
            sheaf_ms += report.elapsed_ms
            for finding in report.findings:
                sheaf_findings += 1
                sheaf_types.append(finding.bug_type)
                if finding.bug_type == bug_type:
                    sheaf_detected = True
        except Exception:
            pass

        # Run a3-python
        try:
            a3_result = run_a3_on_source(func_source)
            if isinstance(a3_result, dict):
                for fr in a3_result.get("function_results", []):
                    if isinstance(fr, dict):
                        v = fr.get("verdict", "")
                        bt = fr.get("bug_type", "")
                        if v == "BUG" and bt:
                            a3_findings += 1
                            a3_types.append(bt)
                            if bt == bug_type:
                                a3_detected = True
        except Exception:
            pass

    return BugEvalResult(
        project=patch.project,
        bug_id=patch.bug_id,
        classified_type=bug_type,
        classified_confidence=confidence,
        sheaf_detected=sheaf_detected,
        sheaf_bug_types=sheaf_types,
        sheaf_n_findings=sheaf_findings,
        sheaf_ms=sheaf_ms,
        a3_detected=a3_detected,
        a3_bug_types=a3_types,
        a3_n_findings=a3_findings,
        n_functions=len(functions),
        patch_files=patch.files_changed,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Main evaluation loop
# ═══════════════════════════════════════════════════════════════════════════════

def run_evaluation(
    bugsinpy_dir: str = "/tmp/BugsInPy",
    max_bugs: int = 100,
    min_classify_confidence: float = 0.5,
) -> Tuple[List[BugEvalResult], EvalSummary]:
    """Run the full evaluation on BugsInPy."""
    bp = Path(bugsinpy_dir)
    if not bp.exists():
        print(f"BugsInPy not found at {bp}. Clone it:")
        print(f"  git clone https://github.com/soarsmu/BugsInPy {bp}")
        return [], EvalSummary()

    projects_dir = bp / "projects"
    results: List[BugEvalResult] = []
    summary = EvalSummary()
    bugs_processed = 0

    # Collect all bugs
    all_bugs: List[Tuple[Path, Path]] = []
    for project_dir in sorted(projects_dir.iterdir()):
        if not project_dir.is_dir():
            continue
        bugs_dir = project_dir / "bugs"
        if not bugs_dir.exists():
            continue
        for bug_dir in sorted(bugs_dir.iterdir(), key=lambda p: int(p.name) if p.name.isdigit() else 0):
            if not bug_dir.is_dir():
                continue
            patch_path = bug_dir / "bug_patch.txt"
            info_path = bug_dir / "bug.info"
            if patch_path.exists() and info_path.exists():
                all_bugs.append((patch_path, info_path))

    print(f"Found {len(all_bugs)} bugs in BugsInPy")
    print(f"Evaluating up to {max_bugs} classifiable bugs...")
    print()

    # Filter to a3-compatible bug types
    a3_compatible = set(BUG_SPECS.keys())

    for patch_path, info_path in all_bugs:
        if bugs_processed >= max_bugs:
            break

        summary.total_bugs += 1

        # Parse patch
        try:
            patch = parse_patch(patch_path, info_path)
        except Exception:
            continue

        # Classify bug type from patch
        # Also try to read test file for classification hints
        test_text = ""
        test_path = patch_path.parent / "run_test.sh"
        if test_path.exists():
            test_text = test_path.read_text(errors="replace")

        classifications = classify_bug_from_patch(patch.raw_patch, test_text)
        # Filter to a3-compatible types
        classifications = [(bt, c) for bt, c in classifications if bt in a3_compatible]

        if not classifications or classifications[0][1] < min_classify_confidence:
            continue

        bug_type, confidence = classifications[0]
        summary.classifiable_bugs += 1

        # Evaluate
        try:
            result = evaluate_bug(patch, bug_type, confidence)
            results.append(result)
            bugs_processed += 1

            # Update summary
            summary.sheaf_total_ms += result.sheaf_ms
            bt_stats = summary.by_type[bug_type]
            bt_stats["total"] = bt_stats.get("total", 0) + 1

            if result.sheaf_detected and result.a3_detected:
                summary.both_detected += 1
                summary.sheaf_true_positive += 1
                summary.a3_true_positive += 1
                bt_stats["sheaf_tp"] = bt_stats.get("sheaf_tp", 0) + 1
                bt_stats["a3_tp"] = bt_stats.get("a3_tp", 0) + 1
            elif result.sheaf_detected:
                summary.sheaf_only += 1
                summary.sheaf_true_positive += 1
                summary.a3_false_negative += 1
                bt_stats["sheaf_tp"] = bt_stats.get("sheaf_tp", 0) + 1
            elif result.a3_detected:
                summary.a3_only += 1
                summary.a3_true_positive += 1
                summary.sheaf_false_negative += 1
                bt_stats["a3_tp"] = bt_stats.get("a3_tp", 0) + 1
            else:
                summary.neither_detected += 1
                summary.sheaf_false_negative += 1
                summary.a3_false_negative += 1

            # Progress
            status = "BOTH" if result.sheaf_detected and result.a3_detected else \
                     "sheaf" if result.sheaf_detected else \
                     "a3" if result.a3_detected else "MISS"
            print(f"  [{bugs_processed:3d}/{max_bugs}] {patch.project}/{patch.bug_id:3d} "
                  f"({bug_type:15s} conf={confidence:.0%}) → {status:5s} "
                  f"| sheaf: {result.sheaf_n_findings} findings, "
                  f"a3: {result.a3_n_findings} findings "
                  f"({result.sheaf_ms:.0f}ms)")

        except Exception as e:
            print(f"  ERROR on {patch.project}/{patch.bug_id}: {e}")
            continue

    return results, summary


def print_summary(summary: EvalSummary, results: List[BugEvalResult]):
    """Print a formatted evaluation summary."""
    print()
    print("=" * 72)
    print("EVALUATION SUMMARY: Sheaf Type-Section Detector vs a3-python")
    print("=" * 72)
    print()
    print(f"Total BugsInPy bugs scanned:     {summary.total_bugs}")
    print(f"Classifiable (a3-compatible):     {summary.classifiable_bugs}")
    n = summary.classifiable_bugs or 1
    print()
    print("Detection results:")
    print(f"  Both detected:                  {summary.both_detected:4d}  ({summary.both_detected/n:.1%})")
    print(f"  Sheaf-only detected:            {summary.sheaf_only:4d}  ({summary.sheaf_only/n:.1%})")
    print(f"  a3-only detected:               {summary.a3_only:4d}  ({summary.a3_only/n:.1%})")
    print(f"  Neither detected:               {summary.neither_detected:4d}  ({summary.neither_detected/n:.1%})")
    print()
    print(f"Sheaf detector recall:            {summary.sheaf_true_positive}/{n} = {summary.sheaf_true_positive/n:.1%}")
    print(f"a3-python recall:                 {summary.a3_true_positive}/{n} = {summary.a3_true_positive/n:.1%}")
    print()
    print(f"Sheaf total time:                 {summary.sheaf_total_ms:.0f}ms")
    if results:
        print(f"Sheaf avg time/bug:               {summary.sheaf_total_ms/len(results):.1f}ms")
    print()

    if summary.by_type:
        print("Detection by bug type:")
        print(f"  {'Bug Type':<25s} {'Total':>6s} {'Sheaf':>6s} {'a3':>6s}")
        print(f"  {'─'*25} {'─'*6} {'─'*6} {'─'*6}")
        for bt in sorted(summary.by_type.keys()):
            stats = summary.by_type[bt]
            total = stats.get("total", 0)
            sheaf_tp = stats.get("sheaf_tp", 0)
            a3_tp = stats.get("a3_tp", 0)
            print(f"  {bt:<25s} {total:>6d} {sheaf_tp:>6d} {a3_tp:>6d}")
        print()


# ═══════════════════════════════════════════════════════════════════════════════
# Quick demo: run on a few hand-picked examples
# ═══════════════════════════════════════════════════════════════════════════════

def run_demo():
    """Run the sheaf detector on hand-crafted examples and show output."""
    examples = [
        ("Division by zero (unguarded)", """
def average(items):
    total = sum(items)
    count = len(items)
    return total / count
"""),
        ("Division by zero (guarded)", """
def safe_average(items):
    total = sum(items)
    count = len(items)
    if count == 0:
        return 0.0
    return total / count
"""),
        ("None dereference (unguarded)", """
def process(data):
    result = data.get("key")
    return result.strip()
"""),
        ("None dereference (guarded)", """
def process_safe(data):
    result = data.get("key")
    if result is not None:
        return result.strip()
    return ""
"""),
        ("Index out of bounds", """
def get_last(items, n):
    return items[n - 1]
"""),
        ("SQL injection", """
def search_user(cursor, username):
    query = f"SELECT * FROM users WHERE name = '{username}'"
    cursor.execute(query)
    return cursor.fetchall()
"""),
        ("Command injection", """
def run_tool(user_input):
    import os
    os.system("process " + user_input)
"""),
        ("Unsafe deserialization", """
def load_data(raw_bytes):
    import pickle
    return pickle.loads(raw_bytes)
"""),
        ("Multiple bugs", """
def fragile(data, idx, divisor):
    item = data[idx]
    result = item / divisor
    obj = data.get("nested")
    return obj.value + result
"""),
    ]

    print("=" * 72)
    print("SHEAF TYPE-SECTION BUG DETECTION — DEMO")
    print("Types as sheaf objects, bugs as gluing obstructions")
    print("=" * 72)
    print()

    for title, source in examples:
        print(f"── {title} {'─' * (60 - len(title))}")
        print()

        report = detect_bugs(source)
        print(format_bug_report(report))
        print()


# ═══════════════════════════════════════════════════════════════════════════════
# Entry point
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="BugsInPy evaluation harness")
    parser.add_argument("--bugsinpy-dir", default="/tmp/BugsInPy",
                        help="Path to BugsInPy clone")
    parser.add_argument("--max-bugs", type=int, default=50,
                        help="Maximum number of bugs to evaluate")
    parser.add_argument("--demo", action="store_true",
                        help="Run demo on hand-crafted examples")
    parser.add_argument("--min-confidence", type=float, default=0.5,
                        help="Minimum classification confidence")
    args = parser.parse_args()

    if args.demo:
        run_demo()
    else:
        # First show demo
        run_demo()

        # Then run BugsInPy evaluation
        print()
        print("=" * 72)
        print("BUGSINPY EVALUATION")
        print("=" * 72)
        print()

        results, summary = run_evaluation(
            bugsinpy_dir=args.bugsinpy_dir,
            max_bugs=args.max_bugs,
            min_classify_confidence=args.min_confidence,
        )

        print_summary(summary, results)

        # Save results
        out_path = Path(__file__).parent / "eval_results.json"
        out_data = {
            "summary": {
                "total_bugs": summary.total_bugs,
                "classifiable": summary.classifiable_bugs,
                "sheaf_tp": summary.sheaf_true_positive,
                "a3_tp": summary.a3_true_positive,
                "both": summary.both_detected,
                "neither": summary.neither_detected,
                "sheaf_only": summary.sheaf_only,
                "a3_only": summary.a3_only,
            },
            "by_type": dict(summary.by_type),
            "results": [
                {
                    "project": r.project,
                    "bug_id": r.bug_id,
                    "type": r.classified_type,
                    "sheaf": r.sheaf_detected,
                    "a3": r.a3_detected,
                    "sheaf_types": r.sheaf_bug_types,
                    "a3_types": r.a3_bug_types,
                }
                for r in results
            ],
        }
        out_path.write_text(json.dumps(out_data, indent=2, default=str))
        print(f"Results saved to {out_path}")
