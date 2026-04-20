# Deppy: Python with Dependent Types

Deppy brings formal verification to Python. Write ordinary Python, annotate functions with `@guarantee` and `@requires`, and Deppy verifies correctness — via Z3 SMT solving, homotopy type theory, or export to Lean 4 with machine-checked proofs.

```python
from deppy import guarantee, requires, compile_to_lean

@requires("n > 0")
@guarantee("result > 0")
def double_pos(n: int) -> int:
    return n * 2

# Verify at import time
from deppy import verify
verify(double_pos)

# Export to Lean 4 with a real proof (no sorry)
cert = compile_to_lean(double_pos)
print(cert.render())
# theorem double_pos_guarantee (n : Int) (h : 0 < n) : 0 < (double_pos n) :=
#   by unfold double_pos; omega
```

## Quick Start

```bash
pip install z3-solver
git clone https://github.com/thehalleyyoung/deppy.git
cd deppy
PYTHONPATH=. python3 -c "from deppy import guarantee, verify; print('ready')"
```

## Features

| Feature | Description |
|---|---|
| `@guarantee(spec)` | Postcondition — what the function promises |
| `@requires(spec)` | Precondition — what the caller must provide |
| `@ensures(pred)` | Formal postcondition as a callable predicate |
| `verify(fn)` | Check guarantees hold (Z3 + runtime) |
| `compile_to_lean(fn)` | Export to Lean 4 with proofs |
| `@decreases(measure)` | Termination measure for recursive functions |
| Sidecar proofs | Verify libraries without modifying their source |
| Duck typing paths | Homotopy proofs for structural subtyping |

## Verification Levels

- 🟢 **LEAN_VERIFIED** — Lean 4 kernel fully checks the proof (0 sorry)
- 🟡 **Z3_PROVEN** — Z3 SMT solver proves the spec
- 🟠 **LEAN_EXPORTED** — Exported to Lean but has `sorry` obligations
- 🔴 **UNTRUSTED** — No verification yet

## Lean 4 Export

Deppy translates Python functions to Lean 4 definitions and generates proofs. Arithmetic specs (`result >= 0`, `result > n`) get real proofs via `omega`. Complex specs are exported with clear `sorry` obligations:

```python
@guarantee("result >= 0")
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    return -x

cert = compile_to_lean(abs_val)
print(cert.trust_level)   # LEAN_VERIFIED
print(cert.obligations)   # []
```

## Project Structure

```
deppy/              Python package
  core/             Type checker, kernel, path engine, Z3 bridge
  proofs/           Decorators (guarantee, requires, verify), tactics
  hott/             HoTT types, cubical paths, fibrations
  lean/             Python → Lean 4 compiler, spec & proof translators
  pipeline/         Verification pipeline, incremental checking
  semantics/        Python denotational semantics
  axioms/           Formal axiom library for external libraries
  runtime/          Runtime monitor
  tests/            Unit tests (358 tests)
  lean/test_*.py    Lean discharge tests (159 tests)
docs/               Tutorial book (thehalleyyoung.github.io/deppy)
```

## Running Tests

```bash
PYTHONPATH=. python3 -m pytest deppy/tests/ deppy/lean/ -q
# 517 passed
```

## Tutorial Book

The full tutorial is at **[thehalleyyoung.github.io/deppy](https://thehalleyyoung.github.io/deppy)** — covering refinement types, termination proofs, sidecar verification of libraries, homotopy methods, separation logic, and Lean 4 export.

## License

MIT
