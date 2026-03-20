#!/usr/bin/env python3
"""Scan open-source Python packages for bugs using deppy's sheaf-cohomological analysis.

This scanner finds interesting bugs in real-world Python code that traditional
type checkers (mypy, pyright) miss because they require type annotations.

Usage:
    python github_scanner.py --packages requests flask numpy
    python github_scanner.py --file path/to/module.py
    python github_scanner.py --dir path/to/project/

Results are written to benchmarks/results/github_scan_results.json
"""

from __future__ import annotations

import ast
import json
import os
import sys
import textwrap
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from deppy.render.bug_detect import detect_bugs, SheafBugReport, GluingObstruction

RESULTS_DIR = Path(__file__).parent / "results"
RESULTS_DIR.mkdir(exist_ok=True)


@dataclass
class FunctionScanResult:
    """Result of scanning a single function."""
    file_path: str
    function_name: str
    line_start: int
    line_end: int
    n_sites: int = 0
    n_obstructions: int = 0
    genuine_bugs: int = 0
    bug_types: List[str] = field(default_factory=list)
    h1_rank: int = 0
    descriptions: List[str] = field(default_factory=list)
    elapsed_ms: float = 0.0


@dataclass
class PackageScanResult:
    """Result of scanning a package."""
    package_name: str
    files_scanned: int = 0
    functions_scanned: int = 0
    total_bugs_found: int = 0
    bug_type_counts: Dict[str, int] = field(default_factory=dict)
    interesting_findings: List[FunctionScanResult] = field(default_factory=list)
    elapsed_ms: float = 0.0


# ============================================================================
# Built-in test corpus: common patterns from popular Python packages
# ============================================================================

BUILTIN_CORPUS: List[Tuple[str, str, str]] = [
    # --- requests-like patterns ---
    ("requests_pattern", "response_handling", textwrap.dedent("""\
        def get_json(response):
            data = response.json()
            return data['results'][0]['id']
    """)),

    ("requests_pattern", "timeout_handling", textwrap.dedent("""\
        def fetch_with_retry(url, max_retries=3):
            for attempt in range(max_retries):
                response = requests.get(url, timeout=5)
                if response.status_code == 200:
                    return response.json()
            return None
    """)),

    # --- flask-like patterns ---
    ("flask_pattern", "route_handler", textwrap.dedent("""\
        def get_user(user_id):
            user = db.query(User).filter_by(id=user_id).first()
            return {'name': user.name, 'email': user.email}
    """)),

    ("flask_pattern", "form_processing", textwrap.dedent("""\
        def process_form(request):
            name = request.form['name']
            age = int(request.form['age'])
            email = request.form.get('email')
            return {'name': name, 'age': age, 'email': email.lower()}
    """)),

    # --- numpy-like patterns ---
    ("numpy_pattern", "array_division", textwrap.dedent("""\
        def normalize_array(arr):
            total = arr.sum()
            return arr / total
    """)),

    ("numpy_pattern", "shape_mismatch", textwrap.dedent("""\
        def weighted_sum(weights, values):
            return (weights * values).sum()
    """)),

    # --- pandas-like patterns ---
    ("pandas_pattern", "column_access", textwrap.dedent("""\
        def process_dataframe(df):
            ages = df['age']
            avg_age = ages.mean()
            return df[df['age'] > avg_age]
    """)),

    ("pandas_pattern", "groupby_agg", textwrap.dedent("""\
        def aggregate_sales(df):
            grouped = df.groupby('region')
            totals = grouped['revenue'].sum()
            return totals / totals.sum()
    """)),

    # --- data processing patterns ---
    ("data_pattern", "csv_processing", textwrap.dedent("""\
        def parse_csv_row(row):
            name, age, score = row.split(',')
            return {'name': name.strip(), 'age': int(age), 'score': float(score)}
    """)),

    ("data_pattern", "json_traversal", textwrap.dedent("""\
        def extract_nested(data, keys):
            current = data
            for key in keys:
                current = current[key]
            return current
    """)),

    ("data_pattern", "safe_division", textwrap.dedent("""\
        def percentage(part, whole):
            return (part / whole) * 100
    """)),

    ("data_pattern", "list_aggregation", textwrap.dedent("""\
        def average(values):
            return sum(values) / len(values)
    """)),

    # --- ML/torch-like patterns ---
    ("ml_pattern", "batch_processing", textwrap.dedent("""\
        def process_batch(batch, model):
            inputs = batch['input_ids']
            labels = batch['labels']
            outputs = model(inputs)
            loss = criterion(outputs, labels)
            return loss.item()
    """)),

    ("ml_pattern", "gradient_update", textwrap.dedent("""\
        def train_step(model, optimizer, batch):
            optimizer.zero_grad()
            loss = model(batch)
            loss.backward()
            optimizer.step()
            return loss.item()
    """)),

    # --- file handling patterns ---
    ("file_pattern", "read_config", textwrap.dedent("""\
        def load_config(path):
            f = open(path)
            data = json.load(f)
            f.close()
            return data['settings']
    """)),

    ("file_pattern", "safe_read", textwrap.dedent("""\
        def safe_load(path):
            with open(path) as f:
                return json.load(f)
    """)),

    # --- algorithm patterns ---
    ("algorithm_pattern", "quicksort_partition", textwrap.dedent("""\
        def partition(arr, low, high):
            pivot = arr[high]
            i = low - 1
            for j in range(low, high):
                if arr[j] <= pivot:
                    i += 1
                    arr[i], arr[j] = arr[j], arr[i]
            arr[i + 1], arr[high] = arr[high], arr[i + 1]
            return i + 1
    """)),

    ("algorithm_pattern", "dijkstra_extract", textwrap.dedent("""\
        def extract_min(dist, visited):
            min_dist = float('inf')
            min_node = None
            for node, d in dist.items():
                if node not in visited and d < min_dist:
                    min_dist = d
                    min_node = node
            return min_node
    """)),

    ("algorithm_pattern", "stack_operations", textwrap.dedent("""\
        def evaluate_rpn(tokens):
            stack = []
            for token in tokens:
                if token in '+-*/':
                    b = stack.pop()
                    a = stack.pop()
                    if token == '+': stack.append(a + b)
                    elif token == '-': stack.append(a - b)
                    elif token == '*': stack.append(a * b)
                    elif token == '/': stack.append(a / b)
                else:
                    stack.append(float(token))
            return stack[0]
    """)),
]


def scan_source(source: str, file_path: str = "<inline>",
                function_name: str = "") -> List[FunctionScanResult]:
    """Scan a Python source string for bugs."""
    results = []

    # Parse to find all functions
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return results

    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue

        func_source = ast.get_source_segment(source, node)
        if func_source is None:
            continue

        start = time.monotonic()
        try:
            report = detect_bugs(func_source, function_name=node.name)
            genuine = [o for o in report.obstructions
                       if not o.resolved_by_guard and o.confidence > 0.5]
            elapsed = (time.monotonic() - start) * 1000

            if genuine:  # Only record functions with findings
                results.append(FunctionScanResult(
                    file_path=file_path,
                    function_name=node.name,
                    line_start=node.lineno,
                    line_end=getattr(node, 'end_lineno', node.lineno),
                    n_sites=report.n_sites,
                    n_obstructions=len(report.obstructions),
                    genuine_bugs=len(genuine),
                    bug_types=[o.bug_type for o in genuine],
                    h1_rank=report.minimum_independent_fixes,
                    descriptions=[o.description for o in genuine[:3]],
                    elapsed_ms=elapsed,
                ))
        except Exception:
            pass

    return results


def scan_file(file_path: str) -> List[FunctionScanResult]:
    """Scan a Python file for bugs."""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            source = f.read()
    except (IOError, OSError):
        return []
    return scan_source(source, file_path=file_path)


def scan_directory(dir_path: str, max_files: int = 100) -> PackageScanResult:
    """Scan all Python files in a directory."""
    result = PackageScanResult(package_name=os.path.basename(dir_path))
    start = time.monotonic()

    py_files = []
    for root, dirs, files in os.walk(dir_path):
        # Skip common non-source directories
        dirs[:] = [d for d in dirs if d not in {
            '__pycache__', '.git', '.tox', 'node_modules', '.eggs',
            'build', 'dist', '.mypy_cache', '.pytest_cache', 'venv',
            'env', '.venv', '.env',
        }]
        for f in files:
            if f.endswith('.py') and not f.startswith('test_'):
                py_files.append(os.path.join(root, f))
                if len(py_files) >= max_files:
                    break

    for fp in py_files:
        findings = scan_file(fp)
        result.files_scanned += 1
        result.functions_scanned += 1  # approximate
        for finding in findings:
            result.total_bugs_found += finding.genuine_bugs
            for bt in finding.bug_types:
                result.bug_type_counts[bt] = result.bug_type_counts.get(bt, 0) + 1
            result.interesting_findings.append(finding)

    result.elapsed_ms = (time.monotonic() - start) * 1000
    return result


def scan_builtin_corpus() -> PackageScanResult:
    """Scan the built-in corpus of common Python patterns."""
    result = PackageScanResult(package_name="builtin_corpus")
    start = time.monotonic()

    for pkg, func_name, source in BUILTIN_CORPUS:
        findings = scan_source(source, file_path=f"{pkg}/{func_name}.py")
        result.functions_scanned += 1
        for finding in findings:
            result.total_bugs_found += finding.genuine_bugs
            for bt in finding.bug_types:
                result.bug_type_counts[bt] = result.bug_type_counts.get(bt, 0) + 1
            result.interesting_findings.append(finding)

    result.files_scanned = len(BUILTIN_CORPUS)
    result.elapsed_ms = (time.monotonic() - start) * 1000
    return result


def format_findings(result: PackageScanResult) -> str:
    """Format scan results as a human-readable report."""
    lines = []
    lines.append(f"Package: {result.package_name}")
    lines.append(f"Files scanned: {result.files_scanned}")
    lines.append(f"Functions with bugs: {len(result.interesting_findings)}")
    lines.append(f"Total bugs found: {result.total_bugs_found}")
    lines.append(f"Time: {result.elapsed_ms:.0f}ms")
    lines.append("")

    if result.bug_type_counts:
        lines.append("Bug type distribution:")
        for bt, count in sorted(result.bug_type_counts.items(), key=lambda x: -x[1]):
            lines.append(f"  {bt}: {count}")
        lines.append("")

    if result.interesting_findings:
        lines.append("Interesting findings:")
        for f in result.interesting_findings[:20]:
            lines.append(f"  {f.file_path}:{f.function_name}() L{f.line_start}")
            for desc in f.descriptions:
                lines.append(f"    - {desc}")
            lines.append(f"    H1 rank: {f.h1_rank}, types: {', '.join(f.bug_types)}")
            lines.append("")

    return "\n".join(lines)


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Scan Python code for bugs using deppy")
    parser.add_argument("--dir", help="Directory to scan")
    parser.add_argument("--file", help="Single file to scan")
    parser.add_argument("--builtin", action="store_true", help="Scan built-in corpus")
    parser.add_argument("--max-files", type=int, default=100, help="Max files to scan")
    args = parser.parse_args()

    if args.dir:
        result = scan_directory(args.dir, max_files=args.max_files)
    elif args.file:
        findings = scan_file(args.file)
        result = PackageScanResult(
            package_name=os.path.basename(args.file),
            files_scanned=1,
            functions_scanned=len(findings),
            total_bugs_found=sum(f.genuine_bugs for f in findings),
            interesting_findings=findings,
        )
    else:
        result = scan_builtin_corpus()

    print(format_findings(result))

    # Save results
    out_file = RESULTS_DIR / "github_scan_results.json"
    with open(out_file, 'w') as f:
        json.dump(asdict(result), f, indent=2, default=str)
    print(f"Results saved to {out_file}")


if __name__ == "__main__":
    main()
