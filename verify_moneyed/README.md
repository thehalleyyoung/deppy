# Deppy × py-moneyed: Sidecar Verification of a Production Finance Library

This directory verifies **28 mathematical and safety properties** of
[py-moneyed](https://github.com/py-moneyed/py-moneyed) (1.2k+ GitHub
stars, used in Django/Saleor e-commerce) — **without modifying a single
line of py-moneyed's source code**.

## What is verified

| Category | Properties | Method |
|----------|-----------|--------|
| A. Currency safety | Addition never silently mixes currencies | Kernel + runtime |
| B. Subtraction safety | Cross-currency subtraction raises TypeError | Kernel + runtime |
| C. Abelian group | Commutativity, associativity, identity, inverse | Kernel + runtime |
| D. Scalar multiplication | Currency preservation, distributivity | Kernel + runtime |
| E. Comparison | Total order within same currency | Kernel + runtime |
| F. Absolute value | Non-negative, currency-preserving | Kernel + runtime |
| G. Bool/zero detection | bool(Money(0)) == False | Kernel + runtime |
| H. Finance functions | Discount, tax, fees, bill splitting | **Z3 proof** |
| X. Deliberate false axiom | Must fail (sanity check) | Expected failure |

## Running

```bash
pip install py-moneyed
cd <repo-root>
PYTHONPATH=. python3 verify_moneyed/verify_moneyed.py
```

## Files

- `moneyed.deppy` — Declarative sidecar specification (28 axioms)
- `verify_moneyed.py` — Companion verification script
- `README.md` — This file

## Why this matters

Python is the #1 language in fintech, yet no widely-used money library
has formal verification.  Deppy bridges this gap by providing:

1. **Sidecar specs** — declare properties of external libraries without
   modifying their source code
2. **Z3 proofs** — machine-checked verification of arithmetic invariants
3. **Bug detection** — Z3 counterexamples catch off-by-one errors with
   concrete inputs
4. **Lean 4 export** — verified properties can be exported to
   machine-checkable Lean proofs
