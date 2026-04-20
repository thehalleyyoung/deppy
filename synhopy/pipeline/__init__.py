"""SynHoPy pipeline — end-to-end verification, scalability, caching."""
from __future__ import annotations

# Lazy imports to avoid circular dependencies and optional Z3
__all__ = [
    "VerificationPipeline",
    "AbstractInterpreter", "StratifiedVerifier", "ObligationResolver",
    "Z3BatchContext", "ModuleBatchVerifier",
    "EffectPruningPipeline", "EffectAnalyzer",
    "IncrementalVerifier", "VerificationCache",
    "AutoSpecGenerator",
    "ParallelScheduler", "VerificationGraph",
    "GradualChecker", "GradualReport", "VerificationCoverage",
    "CounterexampleFinder", "CounterexampleResult",
    "PropertyTester", "HypothesisBridge",
    "DiagnosticEngine", "Diagnosis",
    "BoundaryAnalyzer", "BoundaryViolation",
]
