#!/usr/bin/env python3
"""Full sympy proof run via CCTT Orchestrator.

Usage:
    # Fast baseline (no LLM, AST+template specs only):
    PYTHONPATH=src python3 run_sympy_proof.py

    # With LLM-generated intent specs (requires copilot CLI):
    PYTHONPATH=src python3 run_sympy_proof.py --llm

    # LLM on a subset (e.g. core only):
    PYTHONPATH=src python3 run_sympy_proof.py --llm --subpackage core --max-files 20
"""
from __future__ import annotations

import argparse
import logging
import json
import sys

logging.basicConfig(level=logging.WARNING)

from cctt.proof_theory.library_proof_orchestrator import Orchestrator

parser = argparse.ArgumentParser(description="CCTT sympy proof runner")
parser.add_argument("--llm", action="store_true",
                    help="Use copilot CLI to generate LLM intent specs")
parser.add_argument("--max-files", type=int, default=0,
                    help="Max files to process (0 = all)")
parser.add_argument("--subpackage", type=str, default="",
                    help="Only process this subpackage")
parser.add_argument("--workers", type=int, default=8)
args = parser.parse_args()

orc = Orchestrator(
    library_name="sympy",
    output_dir="examples/sympy_full_proof",
    use_copilot=args.llm,
    workers=args.workers,
    max_files=args.max_files,
    subpackage=args.subpackage,
)
report = orc.run()
summary = report.summary()
print(summary)

# Save structured stats for the report
stats = {
    "n_files": report.n_files,
    "n_definitions": report.n_definitions,
    "n_proved": report.n_proved,
    "pass_rate": report.pass_rate,
    "trust_boundary": report.trust_boundary,
}

# Collect trust domains
trust_domains: dict = {}
for fr in report.file_reports.values():
    for r in fr.results:
        if r.annotation:
            for ref in r.annotation.trust:
                domain = ref.split(".")[0] if "." in ref else ref
                trust_domains[domain] = trust_domains.get(domain, 0) + 1

stats["trust_domains"] = trust_domains

with open("examples/sympy_full_proof/run_stats.json", "w") as f:
    json.dump(stats, f, indent=2, default=str)

print(f"\nStats saved to examples/sympy_full_proof/run_stats.json")
print(f"Trust domains found: {sorted(trust_domains.keys())}")

# Verify no sympy.* in trust refs
sympy_refs = [d for d in trust_domains if d == "sympy"]
if sympy_refs:
    print(f"\nWARNING: sympy.* trust refs found! {sympy_refs}")
    sys.exit(1)
else:
    print("\nOK: No sympy.* circular trust refs found in trust domains.")
