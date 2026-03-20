# CLAUDE.md — Instructions for Claude Code / Claude Sonnet

## Project: deppy — Hybrid Dependent Type System for Verified Python

### What you MUST do when writing code in this project:

1. **Every public function gets `@guarantee("...")`** describing its postcondition in natural language. deppy will decompose this into structural (Z3-checkable) and semantic (oracle-judgeable) predicates.

2. **Every precondition uses `assume("...")`**. These become proof obligations for callers.

3. **Complex logic can use `hole("description")`** — deppy synthesizes and verifies the implementation.

4. **Import deppy surface syntax**: `from deppy.hybrid import guarantee, spec, hole, assume, check, given`

5. **Use `from __future__ import annotations`** in every file.

6. **Guard Z3**: `try: from z3 import *; _HAS_Z3 = True; except: _HAS_Z3 = False`

7. **Use TYPE_CHECKING guards** for cross-module imports to avoid circular dependencies.

### The Mathematical Foundation (not a metaphor):

- **Programs are sheaves** over a site category. Type assignments are presheaf sections.
- **Bugs are H¹ cohomology classes** — obstructions to gluing local type assignments.
- **LLM outputs inhabit hybrid types** = structural (Z3) ∧ semantic (oracle) predicates.
- **Hallucination = type inhabitation failure**. Fabricated APIs = structural. Wrong behavior = semantic.
- **Every verified artifact is a Σ-type**: code paired with its proof certificate.
- **The oracle monad T_O** wraps semantic judgments: `T_O(A) = A × TrustLevel × Confidence × Provenance`

### Running tests:
```bash
PYTHONPATH=src python3 -m pytest tests/test_hybrid/ -v --timeout=30
```

### Key files:
- `src/deppy/hybrid/core/types.py` — HybridType as product presheaf section
- `src/deppy/hybrid/core/algebraic_geometry.py` — Čech cohomology, Mayer-Vietoris
- `src/deppy/hybrid/core/oracle_theory.py` — Oracle monad, decidability stratification
- `src/deppy/hybrid/core/checker.py` — Bidirectional type checker with cache
- `src/deppy/hybrid/mixed_mode/syntax.py` — Surface language forms
- `agent/orchestrator.py` — Autonomous agent brain
- `agent/intent_oracle.py` — LLM-as-human-intent-oracle

### When generating code with the agent:
The agent at `agent/` takes a natural language prompt and generates a verified codebase:
```python
from agent import run
result = run("write me a financial trading app", llm_fn=my_llm)
```
Every generated function uses deppy's surface syntax and is verified through the full pipeline.
