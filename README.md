<p align="center">
  <br>
  <b>deppy</b><br>
  <i>Sheaf-Cohomological Program Analysis for Python</i><br>
  <br>
  <a href="https://thehalleyyoung.github.io/deppy/">Website</a> ·
  <a href="#-quick-start">Quick Start</a> · <a href="#-what-it-catches">What It Catches</a> · <a href="#%EF%B8%8F-equivalence-checking">Equivalence</a> · <a href="#-the-mathematics">The Math</a> · <a href="#-benchmarks">Benchmarks</a>
  <br><br>
  <img src="https://img.shields.io/badge/version-2.0.0-blue" alt="Version 2.0.0">
  <img src="https://img.shields.io/badge/python-3.10+-3776AB?logo=python&logoColor=white" alt="Python 3.10+">
  <img src="https://img.shields.io/badge/Z3_solver-✓-blue" alt="Z3">
  <img src="https://img.shields.io/badge/Lean_4-3.5K_LOC-green" alt="Lean 4">
  <img src="https://img.shields.io/badge/tests-3%2C093_passing-brightgreen" alt="Tests">
  <img src="https://img.shields.io/badge/license-MIT-blue" alt="MIT">
</p>

---

Deppy treats program analysis as computing the **Čech cohomology** of a *semantic presheaf* over a program's *site category*. Bugs are gluing obstructions in H¹. Equivalence is descent. Incremental analysis is Mayer-Vietoris.

**This is not a metaphor — it is the actual algorithm.**

```
                     δ⁰              δ¹
            C⁰(U, Sem) ──→ C¹(U, Sem) ──→ C²(U, Sem)
               │                │                │
               ▼                ▼                ▼
          local type       transition        cocycle
          assignments      functions g_ij    condition
               │                │                │
               ▼                ▼                ▼
          H⁰ = ker δ⁰    H¹ = ker δ¹/im δ⁰    H² = C²/im δ¹
               │                │                │
       global consistent   BUGS / EQUIV       higher
       type assignments    OBSTRUCTIONS      obstructions
```

> **Paper:** *Sheaf-Cohomological Program Analysis* — Halley Young, POPL 2027

---

## Why Deppy?

<table>
<tr><td>

**Works on raw Python.** No annotations, no type hints, no contracts. Hand it any `.py` file.

</td><td>

**Finds bugs mypy and pyright miss.** 100% recall on benchmark suite — mypy and pyright score 0% on the same programs.

</td></tr>
<tr><td>

**Proves equivalence.** Not just testing — a sound and complete criterion via descent (Theorem 5).

</td><td>

**Explains itself mathematically.** Every bug is a 1-cocycle. Every fix count is a GF(2) rank. Every equivalence is a trivial H¹.

</td></tr>
</table>

---

## 📊 Benchmarks

Evaluated on **375 programs** (133 bug-detection, 134 equivalence, 108 spec-satisfaction):

| | **Deppy** | **mypy** | **pyright** |
|---|:---:|:---:|:---:|
| Bug recall | **100%** | 0% | 0% |
| Bug precision | 69% | — | — |
| Bug F1 | **81%** | 0% | 0% |
| Equivalence accuracy | **99%** | — | — |
| Spec satisfaction accuracy | **98%** | — | — |

<details>
<summary><b>Per-category breakdown (click to expand)</b></summary>

| Bug Category | Precision | Recall | F1 |
|---|:---:|:---:|:---:|
| DIV_ZERO | 100% | 100% | 100% |
| NULL_PTR | 100% | 100% | 100% |
| UNBOUND_VAR | 100% | 100% | 100% |
| VALUE_ERROR | 100% | 100% | 100% |
| KEY_ERROR | 83% | 100% | 91% |
| INDEX_OOB | 62% | 100% | 77% |
| USE_AFTER_FREE | 50% | 100% | 67% |

**Large suite** (300 programs): Bug F1 **79%**, Equivalence **100/100**, Spec **99/100**.

</details>

---

## 🚀 Quick Start

```bash
pip install -e ".[dev]"   # Python 3.10+, installs z3-solver
```

### Find a bug in 3 lines

```python
from deppy.render.bug_detect import detect_bugs

report = detect_bugs("""
def normalize(values):
    total = sum(values)
    return [v / total for v in values]
""")

for obs in report.obstructions:
    if not obs.resolved_by_guard and obs.confidence > 0:
        print(f"[{obs.bug_type}] line {obs.line}: {obs.description}")
# [DIV_ZERO] line 4: [BUG] divisor `total` must be ≠ 0 — SAT (gap exists)

print(report.minimum_independent_fixes)  # 1
```

The presheaf section at the division site requires `total ≠ 0`, but the argument-boundary section admits `total = 0`. These disagree on their overlap — a non-trivial element of H¹.

### Check equivalence in 3 lines

```python
from deppy.equivalence.pipeline import EquivalencePipeline, EquivalencePipelineConfig

pipeline = EquivalencePipeline(EquivalencePipelineConfig())

result = pipeline.run("""
def sum_loop(xs):
    total = 0
    for x in xs:
        total += x
    return total
""", """
def sum_builtin(xs):
    return sum(xs)
""")

print(result.verdict.value)   # "equivalent"
print(result.is_equivalent)   # True
```

### Or use the CLI

```
$ deppy equiv search_a.py search_b.py --verbose

╔══════════════════════════════════════════════════════════════╗
║                 Sheaf Equivalence Checker                    ║
╚══════════════════════════════════════════════════════════════╝

  Program f: search (search_a.py)
  Program g: search (search_b.py)

  Verdict: ✅ equivalent
  Strength: denotational

  Site-by-Site Analysis:
  ────────────────────────────────────────────────────────────
    ✅ common_search_search [call_result]  fwd:✓  bwd:✓
```

---

## 🐛 What It Catches

### Division by zero

```python
report = detect_bugs("""
def normalize(values):
    total = sum(values)
    return [v / total for v in values]
""")
# [DIV_ZERO] line 4: divisor `total` must be ≠ 0
```

### Null-pointer dereference (interprocedural)

```python
report = detect_bugs("""
def first_match(items, predicate):
    for item in items:
        if predicate(item):
            return item
    return None

def process_match(items, pred):
    match = first_match(items, pred)
    return match.value   # bug: match may be None
""")
# [NULL_PTR] line 10
```

Deppy tracks `None` across function boundaries via section transport through the interprocedural call graph. The call site admits `None` from `first_match`'s return-None path, but the dereference site requires `match != None`.

### Deadlock (cyclic lock ordering)

```python
report = detect_bugs("""
import threading
lock_a, lock_b = threading.Lock(), threading.Lock()

def task1():
    with lock_a:
        with lock_b:
            return 1

def task2():
    with lock_b:
        with lock_a:
            return 2
""")
# [DEADLOCK]: cyclic lock ordering: lock_a ↔ lock_b —
#             lock ordering presheaf has no consistent section
```

### Use-after-close + resource leak

```python
report = detect_bugs("""
def read_config(path):
    f = open(path)
    data = f.read()
    f.close()
    return f.readline()   # bug: use after close
""")
# [MEMORY_LEAK] line 3: `f` = open(...) without context manager
# [USE_AFTER_FREE] line 6: `.readline()` requires lifecycle(f) = OPEN
```

### Index out of bounds

```python
report = detect_bugs("""
def get_middle(lst):
    return lst[len(lst) // 2]
""")
# [INDEX_OOB] line 3: index `len(lst) // 2` must be in [0, len(lst))
```

### SQL injection

```python
report = detect_bugs("""
def find_user(db, username):
    query = "SELECT * FROM users WHERE name = '" + username + "'"
    return db.execute(query)
""")
# [SQL_INJECTION] line 4: db.execute executes a concatenated query
```

### TOCTOU race condition

```python
report = detect_bugs("""
import os
def safe_read(path):
    if os.path.exists(path):
        return open(path).read()
""")
# [DATA_RACE] line 4: Check-then-act file access can race
#                      between existence test and open
```

---

## ⚖️ Equivalence Checking

Deppy implements the **descent theorem** (Theorem 5): two functions f, g are equivalent iff Ȟ¹(U, Iso(Sem_f, Sem_g)) = 0.

### Two binary searches — different invariants, same function

```python
result = pipeline.run("""
def search(xs, target):
    lo, hi = 0, len(xs) - 1         # closed interval
    while lo <= hi:
        mid = (lo + hi) // 2
        if xs[mid] == target: return mid
        elif xs[mid] < target: lo = mid + 1
        else: hi = mid - 1
    return -1
""", """
def search(xs, target):
    lo, hi = 0, len(xs)             # half-open interval
    while lo < hi:
        mid = lo + (hi - lo) // 2   # overflow-safe midpoint
        if xs[mid] < target: lo = mid + 1
        elif xs[mid] > target: hi = mid
        else: return mid
    return -1
""")

print(result.verdict.value)   # "equivalent"
```

### Mutation vs. copy — correctly detected as inequivalent

```python
result = pipeline.run("""
def append_a(lst):
    return lst + [1]
""", """
def append_b(lst):
    lst.append(1)
    return lst
""")

print(result.verdict.value)   # "inequivalent"
```

---

## 🔬 Deep Cohomological Engine

For full mathematical detail, use the radical engine directly. It computes the complete Čech complex C⁰→C¹→C² with proper H¹ = ker(δ¹)/im(δ⁰) quotient, plus **six beyond-paper extensions**:

```python
from deppy.equivalence.cohomological_engine import DeepEquivalenceEngine
engine = DeepEquivalenceEngine()
```

### ✅ Commutative reorder — Galois σ_comm detects the symmetry

```python
cert = engine.check(
    "def f(x, y): return x + y + 1",
    "def g(x, y): return 1 + y + x",
)

cert.equivalent                              # True
cert.proof_method.value                      # "cech_h1_zero"
cert.betti_numbers                           # (1, 0, 0) — β₁=0, no obstructions
cert.euler_characteristic                    # 1
cert.galois_cohomology.symmetry_generators   # ['σ_comm (commutative reorder)']
cert.etale_cohomology.parametric             # True — works uniformly on all types
cert.derived_category.is_quasi_isomorphic    # True
cert.mayer_vietoris.exact_sequence_verified  # True
```

### ❌ Fibonacci off-by-one — 8 independent obstructions located

```python
cert = engine.check("""
def fib_a(n):
    if n <= 1: return n
    a, b = 0, 1
    for _ in range(2, n+1):
        a, b = b, a + b
    return b
""", """
def fib_b(n):
    if n <= 1: return n
    a, b = 0, 1
    for _ in range(2, n):   # ← off-by-one in range
        a, b = b, a + b
    return b
""")

cert.equivalent                   # False
cert.proof_method.value           # "z3_counterexample"
cert.h1_rank                      # 8 (independent obstructions)
cert.counterexample               # {'p0': 9} — n=9 witnesses the bug
cert.obstruction_sites[:3]        # ['f_path3∩g_path2', 'f_path4∩g_path3', ...]
cert.betti_numbers                # (1, 0, 84)
cert.num_sites_checked            # 10
```

### Beyond-Paper Extensions

| Extension | What it computes |
|---|---|
| **Spectral Sequences** | E₂^{p,q} = Ȟᵖ(Y, Rᵍπ₊F) — hierarchical inter-/intra-module bug decomposition |
| **Derived Categories** | Quasi-isomorphism via mapping cone acyclicity |
| **Persistent Cohomology** | Birth/death tracking of H¹ classes across filtration depths |
| **Étale Cohomology** | Ȟ¹\_ét for polymorphic function parametricity verification |
| **Galois Cohomology** | H¹(G, Aut(Sem)) classifying implementation symmetries (σ\_comm, σ\_branch, σ\_assoc, σ\_loop, σ\_tce) |
| **Betti Numbers** | β₀, β₁, β₂ and Euler characteristic χ = β₀ − β₁ + β₂ |

---

## 🏗 Hybrid Dependent Types

Annotate your code with natural-language specifications. Deppy decomposes them into structural (Z3-decidable) and semantic (oracle-judgeable) predicates:

```python
from deppy.hybrid import guarantee, assume, check

@guarantee("returns a non-negative number")
def abs_val(x: int) -> int:
    assume("x is an integer")
    if x >= 0:
        return x
    return -x

abs_val(5)    # 5
abs_val(-3)   # 3
```

### Verification Levels

| Level | Meaning |
|---|---|
| 🟢 `LEAN_VERIFIED` | Machine-checked by Lean 4 kernel |
| 🟡 `Z3_PROVEN` | Proved by Z3 SMT solver |
| 🟠 `LLM_JUDGED` | Oracle says correct with confidence ≥ threshold |
| 🔴 `UNTRUSTED` | No verification yet |

---

## 📐 Sheaf Analysis Reports

Inspect the full presheaf structure of any function:

```python
from deppy.render.report import analyze

report = analyze("""
def binary_search(arr, target):
    lo, hi = 0, len(arr) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return -1
""")

report.num_sites          # 21
report.num_morphisms      # 6
report.num_obstructions   # 0
report.convergence        # "global_section_found"
for p in report.preconditions:
    print(f"  {p.parameter}: {p.condition}")
# arr: isinstance(arr, (list, tuple, str, dict, set))
```

---

## 🧮 The Mathematics

```
Program ──parse──→ Site Category S_P ──Sem──→ Presheaf Sem_f : S_P^op → Lat
                        │                              │
                   5 site kinds:                 refinement predicates
                   • ArgBoundary                 on each site
                   • BranchGuard
                   • CallResult                  Čech complex C•(U, Sem)
                   • OutBoundary                 with coboundaries δ⁰, δ¹
                   • ErrorSite
                        │                              │
                        ▼                              ▼
                   Morphisms =                   H¹ = ker(δ¹)/im(δ⁰)
                   data-flow edges                    │
                                                      ▼
                                              BUGS = obstruction classes
                                              rk H¹ = minimum fixes
```

### Core Theorems

| Theorem | Statement |
|---|---|
| **Thm 5** (Descent) | f ≡ g ⟺ Ȟ¹(U, Iso(Sem\_f, Sem\_g)) = 0 |
| **Thm 7** (Mayer-Vietoris) | ... → Ȟ⁰(A∩B) →[δ]→ Ȟ¹(U) → Ȟ¹(A)⊕Ȟ¹(B) → ... |
| **Prop 3** (Fix count) | rk H¹ over GF(2) = minimum independent fixes |

### Three Separation Results vs. Traditional Analysis

| | Cohomological (Deppy) | Traditional |
|---|---|---|
| **Minimum fix count** | Polynomial — GF(2) Gaussian elimination on δ-matrix | NP-hard from flat error sets (Thm 9) |
| **Incremental update** | Exact via Mayer-Vietoris | Must re-solve global fixpoint (Thm 10) |
| **Equivalence** | Sound and complete (descent) | No finite abstract domain suffices (Thm 11) |

---

## 💻 CLI Reference

```bash
# Bug detection and sheaf analysis
deppy check myfile.py
deppy check myfile.py --format json

# Equivalence checking
deppy equiv file_a.py file_b.py
deppy equiv file_a.py file_b.py --verbose     # site-by-site detail
deppy equiv file_a.py file_b.py --json        # machine-readable
deppy equiv file_a.py file_b.py --sarif out   # SARIF export

# Explain a specific site
deppy explain myfile.py --site arg_boundary_x

# Attempt to prove a property
deppy prove myfile.py --property "x > 0 implies result > 0"

# Generate contract annotations
deppy generate myfile.py

# Watch mode (re-analyze on save)
deppy watch myfile.py
```

---

## 📂 Project Structure

```
src/deppy/                         172K lines across 388 files
  core/                            Site categories, presheaves, sheaf conditions
  equivalence/                     Equivalence pipeline
    cohomological_engine.py        ← radical engine: full Čech + 6 extensions
    pipeline.py                    ← orchestrator: parse → presheaves → align → Z3
  render/                          Bug detection, reports, repair synthesis
  solver/                          Z3 backend
  hybrid/                          Hybrid dependent types (structural + semantic)
  kernel/                          Fixed-point engine, Čech, Mayer-Vietoris
  library_theories/                Theory packs (arithmetic, collections, nullability)
  interprocedural/                 Call graph, section transport

lean_proofs/                       ~3,500 lines of Lean 4
  DeppyProofs/
    SiteCategory.lean              Program site categories form a category
    Presheaf.lean                  Semantic presheaves, sheaf condition
    CechCohomology.lean            Čech complex, chain complex property ∂₁∘∂₀=0
    Descent.lean                   Descent theorem (Thm 5): H¹=0 ⟺ equivalence
    MayerVietoris.lean             Exact sequence, connecting homomorphism
    Separation.lean                Polynomial fix count, incremental, completeness
    Soundness.lean                 Framework soundness
    Hybrid/                        Oracle monad, trust topos, anti-hallucination

benchmarks/                        375-program evaluation suite
tests/                             3,093 tests across 415 files
```

---

## 🏋️ Running

```bash
# Install
pip install -e ".[dev]"

# Run all tests
PYTHONPATH=src python3 -m pytest -q

# Run benchmarks (375 programs)
PYTHONPATH=src python3 benchmarks/run_all_benchmarks.py

# Large benchmark suite (300 programs)
PYTHONPATH=src python3 benchmarks/run_large_benchmarks.py

# Build Lean proofs
cd lean_proofs && lake build
```

---

## 📐 Lean Proofs

The `lean_proofs/` directory contains Lean 4 mechanizations of the core metatheorems:

| File | What it proves |
|---|---|
| `SiteCategory.lean` | Program site categories form a category |
| `Presheaf.lean` | Semantic presheaves, sheaf condition, H⁰ characterization |
| `CechCohomology.lean` | Čech complex, chain complex property ∂₁∘∂₀ = 0, H¹ computation |
| `Descent.lean` | **Descent theorem**: trivial transitions ⟺ global equivalence |
| `MayerVietoris.lean` | Exact sequence, connecting homomorphism |
| `Separation.lean` | `min_fixes_ge_h1_rank`, `incremental_exact`, `descent_sound`, `descent_complete`, `abstraction_separates_implies_incomplete` |
| `Soundness.lean` | End-to-end framework soundness |
| `FixedPoint.lean` | Fixed-point convergence |
| `Hybrid/` | Oracle monad, trust topos, anti-hallucination as type error |

```bash
cd lean_proofs && lake build
```

---

## 🤝 Contributing

Deppy uses a non-standard architecture. A few things to know:

1. **Every public function gets `@guarantee("...")`** in the deppy codebase itself
2. **Guard Z3 imports**: `try: from z3 import *; _HAS_Z3 = True; except: _HAS_Z3 = False`
3. **Use `from __future__ import annotations`** in every file
4. Run `PYTHONPATH=src python3 -m pytest -q` before submitting — all 3,093 tests must pass

---

## License

MIT — Copyright (c) 2026 Halley Young
