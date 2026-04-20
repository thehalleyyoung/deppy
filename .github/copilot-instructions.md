# Copilot Instructions for deppy

## What is deppy?

deppy is a **proof-oriented programming system** for Python that uses synthetic homotopy type theory, cubical paths, Čech cohomology, and Lean 4 discharge to produce formally verified software — directly from idiomatic Python.

## When writing code in this repository:

1. **Always use deppy's surface syntax** on public functions:
   ```python
   from deppy import guarantee, requires, verify, compile_to_lean

   @guarantee("result >= 0")
   def square(x: int) -> int:
       return x * x
   ```

2. **Use `@guarantee` on every public function** — this is the postcondition that deppy verifies.

3. **Use `@requires` for preconditions** — these generate proof obligations for callers.

4. **Use `verify()` for runtime/static verification** — checks guarantees hold.

5. **Use `compile_to_lean()` for Lean 4 export** — produces machine-checkable proofs.

6. **All monetary values use `Decimal`, never `float`.**

7. **Guard Z3 imports**: `try: from z3 import *; _HAS_Z3 = True; except: _HAS_Z3 = False`

8. **Use `from __future__ import annotations`** in every file.

## Verification levels:
- 🟢 **LEAN_VERIFIED** — machine-checked by Lean's kernel (0 sorry)
- 🟡 **Z3_PROVEN** — proved by Z3 solver
- 🟠 **LEAN_EXPORTED** — exported to Lean but has sorry obligations
- 🔴 **UNTRUSTED** — no verification yet

## Running verification:
```bash
PYTHONPATH=. python3 -m pytest deppy/tests/ -v
PYTHONPATH=. python3 -m pytest deppy/lean/ -v
```

## Architecture:
- `deppy/` — main package
  - `deppy/core/` — type checker, kernel, path engine, Z3 bridge
  - `deppy/proofs/` — sugar decorators (guarantee/requires/verify), tactics, sidecar specs
  - `deppy/hott/` — HoTT types, cubical paths, fibrations
  - `deppy/lean/` — Python → Lean 4 translation, spec translator, proof translator, compiler
  - `deppy/pipeline/` — verification pipeline, incremental checking, batch Z3
  - `deppy/semantics/` — Python denotational semantics, AST compiler
  - `deppy/axioms/` — formal axiom library, library axioms
  - `deppy/runtime/` — runtime monitor
  - `deppy/effects/` — effect types
  - `deppy/tests/` — 358 unit tests
  - `deppy/lean/test_*.py` — 159 Lean discharge tests
- `docs/` — tutorial website (thehalleyyoung.github.io/deppy)
