# Sidecar Verification of SymPy's Geometry Module

This example demonstrates **deppy's sidecar verification** —
proving properties of an existing library (*without modifying it*)
using external `.deppy` spec files and computational validation.

## What's verified

24 classical theorems of Euclidean geometry, checked against
SymPy's `sympy.geometry` implementation:

| Category | Theorems | What's proved |
|----------|----------|---------------|
| **A. Distance** | 4 | Non-negativity, symmetry, identity, triangle inequality |
| **B. Area** | 4 | Cross-product formula, Heron's formula, medial ¼ theorem, orientation |
| **C. Euler Line** | 6 | Circumcenter equidistance, R = abc/4A, centroid averaging, Euler collinearity, OG:GH = 1:2, incenter equidistance |
| **D. Nine-Point Circle** | 4 | Center = midpoint(O,H), radius = R/2, passes through midpoints, passes through altitude feet |
| **E. Circle** | 2 | Area = πr², circumference = 2πr |
| **F. Similarity** | 3 | Angle-preserving similarity, side-preserving congruence, circumcircle |
| **G. Soundness** | 1 | **FALSE axiom** ("every triangle is equilateral") — correctly **refuted** |

### Soundness check

Category G includes a deliberately false axiom to verify the system
doesn't rubber-stamp everything. The kernel accepts it as a trusted axiom,
but the runtime validation layer catches the contradiction — exactly the
behavior a verified system should have.

## How it works

```
sympy_geometry.deppy          verify_triangle.py
┌──────────────────┐          ┌──────────────────────────┐
│ spec Triangle.area│          │ 1. Install axioms        │
│   guarantee: ...  │──parse──▶│ 2. Prove via kernel      │
│   axiom heron:... │          │ 3. Validate on 8 exact   │
│                   │          │    triangle families      │
│ proof euler_proof:│          │ 4. Report pass/fail      │
│   by: axiom ...   │          └──────────────────────────┘
└──────────────────┘                    │
                                        ▼
                               23/23 kernel proofs ✓
                               182/182 runtime checks ✓
                               1/1 expected failure ✓
```

**Key design decisions:**

- All coordinates use exact arithmetic (`Rational`, `sqrt`) — never floats
- 8 diverse triangle families (right, isosceles, equilateral, scalene,
  rational, negative, obtuse) provide broad coverage
- `Abs(area)` is used where orientation matters (SymPy's area is signed)
- Equilateral triangles are skipped for Euler-line ratio tests
  (all centers coincide, ratio is 0/0)

## Running

```bash
cd <repo-root>
PYTHONPATH=. python3 verify_sympy_geometry/verify_triangle.py
```

Expected output:
```
Kernel proofs:         23/23 passed  (+1 expected failure)
Runtime validations:   182/182
Unexpected failures:   0
```

## Files

| File | Purpose |
|------|---------|
| `sympy_geometry.deppy` | Sidecar spec: 28 axioms, 14 specs, 5 proof obligations |
| `verify_triangle.py` | Verification script: installs axioms, proves theorems, runs 182 runtime checks |
| `README.md` | This file |

## Trust model

Deppy uses a layered trust model:

1. **AXIOM_TRUSTED** — The axiom is declared and accepted by the kernel.
   This is analogous to `axiom` in Lean or `Axiom` in Coq: it extends
   the trusted base.

2. **Runtime validation** — Each axiom is also checked computationally
   against concrete SymPy instances using exact arithmetic. This is not
   a proof, but it builds confidence that the axiom is consistent with
   the library's actual behavior.

3. **Soundness check** — The deliberately false axiom shows that while
   the kernel trusts axioms, the computational layer catches contradictions.
   In a production workflow, you would either remove the axiom or
   investigate the discrepancy.
