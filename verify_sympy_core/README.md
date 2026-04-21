# Sidecar Verification of SymPy Core

Proves **52 mathematical laws** hold in SymPy's implementation — without modifying
a single line of SymPy source code.

## Run

```bash
cd <repo-root>
PYTHONPATH=. python3 verify_sympy_core/verify_core.py
```

## What it verifies

| Category | # Laws | Examples |
|---|---|---|
| A. Addition (comm. group) | 4 | `a+b == b+a`, `a+0 == a` |
| B. Multiplication (comm. ring) | 5 | `a*b == b*a`, `a*(b+c) == a*b+a*c` |
| C. Powers | 5 | `a**0 == 1`, `(a**m)**n == a**(m*n)` |
| D. Square root + Z3 | 4 | `sqrt(x²) == |x|` (Z3-proved!) |
| E. Matrices | 15 | det, trace, transpose, associativity |
| F. Differentiation | 9 | product rule, chain rule, trig |
| G. Integration | 6 | FTC, linearity, by parts |
| H. Edge cases | 3 | `1/0 == zoo`, `0/0 == nan` |
| X. False axiom | 1 | `a*a == a` — **must fail** |

**Total: 52 axioms, 766+ runtime validations.**

## How it works

Each law is:

1. **Registered** as a trusted axiom in deppy's proof kernel via `library_trust()`.
2. **Proved** through the kernel with full trust metadata (AXIOM_TRUSTED).
3. **Validated at runtime** against many concrete SymPy expressions.
4. Where SymPy's simplifier can't decide (e.g., `sqrt(x²) = |x|`), deppy's
   **Z3 backend** provides a real-arithmetic proof.
5. One axiom is **deliberately false** (`a*a == a`) — the system correctly rejects it.

## Companion: sympy_core.deppy

The `sympy_core.deppy` file contains all 52 axioms in deppy's declarative sidecar format.
