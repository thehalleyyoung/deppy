# Copilot Instructions for deppy

## What is deppy?

deppy is a **hybrid dependent type system** for Python that uses algebraic geometry (sheaf cohomology), dependent type theory, and LLM-as-controlled-oracle to produce formally verified software.

## When writing code in this repository:

1. **Always use deppy's surface syntax** on public functions:
   ```python
   from deppy.hybrid import guarantee, spec, hole, assume, check, given

   @guarantee("returns a sorted list with no duplicates")
   def unique_sorted(lst: list[int]) -> list[int]:
       ...
   ```

2. **Use `@guarantee` on every public function** — this is the postcondition that deppy verifies.

3. **Use `assume()` for preconditions** — these generate proof obligations for callers.

4. **Use `check()` for internal invariants** — these are verified structurally (Z3) or semantically (oracle).

5. **Use `hole("description")` for complex logic** — deppy will synthesize code that satisfies the surrounding type context.

6. **Use `@spec("description")` for functions whose entire body should be synthesized** from the NL description.

7. **Use `given("theorem or axiom")` to import domain knowledge** (regulatory requirements, paper theorems, etc.)

8. **All monetary values use `Decimal`, never `float`.**

9. **Guard Z3 imports**: `try: from z3 import *; _HAS_Z3 = True; except: _HAS_Z3 = False`

10. **Use `from __future__ import annotations`** in every file.

## Verification levels:
- 🟢 **LEAN_VERIFIED** — machine-checked by Lean's kernel
- 🟡 **Z3_PROVEN** — proved by Z3 solver
- 🟠 **LLM_JUDGED** — oracle says correct with confidence ≥ threshold
- 🔴 **UNTRUSTED** — no verification yet

## Running verification:
```bash
PYTHONPATH=src python3 -m pytest tests/test_hybrid/ -v
deppy hybrid verify <file.py>
deppy hybrid check <file.py>
```

## Architecture:
- `src/deppy/hybrid/core/` — type system, trust topos, oracle monad, AG computation
- `src/deppy/hybrid/mixed_mode/` — surface language (hole/spec/guarantee/assume/check)
- `src/deppy/hybrid/lean_translation/` — Python → Lean translation
- `src/deppy/hybrid/nl_spec/` — NL → HybridSpec parsing
- `src/deppy/hybrid/anti_hallucination/` — hallucination detection as type error
- `src/deppy/hybrid/discharge/` — Z3 + LLM → Lean proof discharge
- `src/deppy/hybrid/pipeline/` — end-to-end verification pipeline
- `src/deppy/hybrid/theory_library/` — per-library type theories
- `agent/` — autonomous verified code generation agent
