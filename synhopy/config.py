"""
synhopy.config — Configuration for SynHoPy verification.
"""
from __future__ import annotations
from dataclasses import dataclass, field


@dataclass
class SynHoPyConfig:
    """Global configuration for SynHoPy verification."""
    z3_timeout: int = 5000          # Z3 timeout in milliseconds
    z3_rlimit: int = 10_000_000     # Z3 resource limit
    trust_level: str = "Z3_PROVEN"  # minimum trust level
    parallel: bool = True           # enable parallel verification
    cache_proofs: bool = True       # cache proof terms
    verbose: bool = False           # verbose output
    lean_export: bool = False       # export to Lean
    coverage_gate: float = 0.0      # CI coverage gate (0-100%)
    strategies: list = field(default_factory=lambda: ["homotopy", "z3", "manual"])
