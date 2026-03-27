# Deppy: Sheaf-Cohomological Program Analysis

**Bug finding, equivalence checking, and specification verification for Python — via Cech cohomology.**

Deppy treats program analysis as computing the cohomology of a *semantic presheaf* over a program's *site category*. Bugs are gluing obstructions in H^1. Equivalence is descent. Incremental analysis is Mayer-Vietoris. This is not a metaphor — it is the actual algorithm.

## Highlights

- **100% bug-detection recall** on 133 benchmark programs (zero missed bugs)
- **Zero false equivalences** across 134 equivalence pairs
- **Zero false spec satisfactions** across 108 specification checks
- Works on **unannotated Python** — no type hints required
- Key metatheorems mechanized in **Lean 4**

## Installation

```bash
pip install -e ".[dev]"
```

Requires Python 3.10+ and Z3 (`pip install z3-solver`).

## Quick Start

### Bug Detection

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
# [DIV_ZERO] line 4: divisor `total` must be != 0

print(f"Minimum independent fixes: {report.minimum_independent_fixes}")
# Minimum independent fixes: 1
```

### Equivalence Checking

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

### Sheaf Analysis Report

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

print(f"Sites: {report.num_sites}")
print(f"Obstructions: {report.num_obstructions}")
print(f"Preconditions inferred:")
for p in report.preconditions:
    print(f"  {p.parameter}: {p.condition}")
```

## Longer Examples

### Interprocedural Null-Pointer Detection

Deppy tracks nullable return values across function boundaries:

```python
from deppy.render.bug_detect import detect_bugs

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

for obs in report.obstructions:
    if not obs.resolved_by_guard and obs.confidence > 0:
        print(f"[{obs.bug_type}] line {obs.line}")
# [NULL_PTR] line 10
```

The presheaf section at the call site admits `None` (from `first_match`'s return-None path), but the dereference site requires `match != None`. These sections disagree on their overlap — a non-trivial 1-cocycle in H^1.

### Deadlock Detection

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

for obs in report.obstructions:
    if not obs.resolved_by_guard and obs.confidence > 0:
        print(f"[{obs.bug_type}] line {obs.line}: {obs.description}")
# [DEADLOCK] line 3: task1 calls task2 while both acquire the same lock
```

### Equivalence: Two Binary Search Implementations

```python
pipeline = EquivalencePipeline(EquivalencePipelineConfig())

result = pipeline.run("""
def search(xs, target):
    lo, hi = 0, len(xs) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if xs[mid] == target: return mid
        elif xs[mid] < target: lo = mid + 1
        else: hi = mid - 1
    return -1
""", """
def search(xs, target):
    lo, hi = 0, len(xs)
    while lo < hi:
        mid = lo + (hi - lo) // 2
        if xs[mid] < target: lo = mid + 1
        elif xs[mid] > target: hi = mid
        else: return mid
    return -1
""")

print(result.verdict.value)  # "equivalent"
```

These use different loop invariants (closed vs. half-open interval), different midpoint formulas, and different branch structures — but compute the same function.

### Detecting Mutation vs. Copy

```python
result = pipeline.run("""
def append_a(lst):
    return lst + [1]
""", """
def append_b(lst):
    lst.append(1)
    return lst
""")

print(result.verdict.value)  # "inequivalent"
```

`append_a` creates a new list; `append_b` mutates the original. Deppy's runtime sampling with input-state tracking detects the side-effect difference.

## The Math

Programs are **presheaves** over a **site category**. Each observation point (argument boundary, branch guard, call result, error site) is a site. Data-flow edges are morphisms. The presheaf assigns refinement-type information to each site.

- **H^0** = globally consistent type assignments (compatible families that glue)
- **H^1** = gluing obstructions (bugs, type errors, equivalence failures)
- **rk H^1 over GF(2)** = minimum number of independent fixes needed
- **H^1(U, Iso) = 0** iff two programs are equivalent (descent theorem)
- **Mayer-Vietoris** gives compositional, incremental obstruction counting

Three **separation results** vs. traditional analysis:
1. Minimum-fix count is polynomial via Gaussian elimination on the coboundary matrix (NP-hard from flat error sets)
2. Mayer-Vietoris gives exact incremental updates (abstract interpretation must re-solve the global fixpoint)
3. Descent gives a complete equivalence criterion (no finite abstract domain can)

## Project Structure

```
src/deppy/
  core/              # Site categories, presheaves, sheaf conditions
  equivalence/       # Equivalence pipeline (descent, runtime sampling, Z3)
  render/            # Bug detection, analysis reports, repair synthesis
  solver/            # Z3 backend
  hybrid/            # Hybrid type system (structural + semantic)
  kernel/            # Fixed-point engine
  library_theories/  # Theory packs (arithmetic, collections, nullability)
  interprocedural/   # Call graph, section transport

benchmarks/          # 375-program evaluation suite
lean_proofs/         # Lean 4 mechanization of key metatheorems
tests/               # Test suite
```

## Running the Benchmarks

```bash
# Full benchmark suite (375 programs)
PYTHONPATH=src python3 benchmarks/run_all_benchmarks.py
PYTHONPATH=src python3 benchmarks/run_large_benchmarks.py
```

## Running Tests

```bash
PYTHONPATH=src python3 -m pytest tests/test_hybrid/ -v --timeout=30
```

## Lean Proofs

The `lean_proofs/` directory contains Lean 4 mechanizations:

- `SiteCategory.lean` — program site categories form a category
- `Presheaf.lean` — semantic presheaves, sheaf condition, H^0 characterization
- `Separation.lean` — three separation results (polynomial fix count, exact incremental update, complete equivalence)

```bash
cd lean_proofs && lake build
```

## Paper

The accompanying paper is `programcohomology.tex`:

> **Sheaf-Cohomological Program Analysis: Unifying Bug Finding, Equivalence, and Verification via Cech Cohomology**
>
> Halley Young (Microsoft Research)

## License

MIT
