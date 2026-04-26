# Deppy: Python with Dependent Types

Deppy is an experimental formal verification harness for Python.  You write ordinary Python, annotate functions with `@guarantee` / `@requires`, and Deppy dispatches the proof obligations to Z3, a small cubical-flavoured proof kernel, or a Lean 4 source emitter.

```python
from deppy import guarantee, requires, compile_to_lean

@requires("n > 0")
@guarantee("result > 0")
def double_pos(n: int) -> int:
    return n * 2

# Attempt to discharge each @guarantee through Z3.  The result is
# recorded on double_pos._deppy_verification — inspect trust_level.
from deppy import verify
verify(double_pos)

# Emit Lean 4 source.  This does NOT invoke Lean by default —
# `cert.trust_level` will be "LEAN_SYNTAX_COMPLETE" if no sorry was
# emitted, not "LEAN_KERNEL_VERIFIED".
cert = compile_to_lean(double_pos)

# To get LEAN_KERNEL_VERIFIED, run Lean yourself:
cert = cert.verify_with_lean()   # requires `lean` on PATH
assert cert.is_kernel_verified   # True iff Lean accepted the file
```

## Quick Start

```bash
# Install from GitHub
pip install git+https://github.com/thehalleyyoung/deppy.git

# — or — clone and install in editable mode (for development)
git clone https://github.com/thehalleyyoung/deppy.git
cd deppy
pip install -e .

# Optional: Z3 for SMT-backed verification
pip install z3-solver
# Optional: Lean 4 + lake for kernel-checked proofs
#   https://leanprover.github.io/lean4/doc/setup.html
```

Verify the install:

```python
from deppy import guarantee, verify
print('ready')
```

## Features

| Feature | What it does | What it does NOT do |
|---|---|---|
| `@guarantee(spec)` | Records a postcondition as metadata and feeds it to `verify`/`compile_to_lean` | Does not enforce the spec at decoration time |
| `@requires(spec)` | Records a precondition | Does not enforce it at call time |
| `@ensures(pred)` | Records a formal predicate callback | — |
| `verify(fn)` | Attempts Z3 discharge per-guarantee, falls back to structural if Z3 rejects | Does not raise on failure unless you pass `raise_on_failure=True` |
| `compile_to_lean(fn)` | Emits Lean 4 source for each guarantee | Does not invoke the Lean compiler — call `cert.verify_with_lean()` for that |
| `check_equiv(f, g)` | Proves (via Z3) or finds counterexamples (via property testing) | Testing-based results are `equivalent=None` with a confidence score — never `True`; `True` is reserved for proofs |
| `@decreases(measure)` | Marks a termination measure; consumed by the safety pipeline | Does not itself prove termination — the pipeline does |
| Sidecar proofs | Attach specs to external library functions via `.deppy` files | — |

## Verification Levels

The verification level records *how* a claim was discharged, not just that it was:

- 🟢 **LEAN_KERNEL_VERIFIED** — `compile_to_lean(fn).verify_with_lean()` ran Lean and Lean accepted the file
- 🟢 **Z3_VERIFIED** — Z3 proved the formula (via `verify(fn)`, `by_z3`, or `check_equiv`)
- 🟡 **LEAN_SYNTAX_COMPLETE** — Lean source emitted, no `sorry`, but Lean has not been invoked
- 🟡 **KERNEL** — kernel rules only (refl / trans / cong / ListInduction …)
- 🟠 **AXIOM_TRUSTED** — cites code-derived axioms; trustworthy iff the axioms faithfully represent the source
- 🟠 **STRUCTURAL_CHAIN** — proof assembled but contains an unchecked leaf (a `Structural` pinky-promise) — **not** a substitute for verification
- 🟠 **LEAN_EXPORTED** — Lean source emitted but contains `sorry`
- 🟠 **ASSUMPTION_DEPENDENT** — Lean file declares raw axioms; any proof routing through them inherits the assumption
- 🔴 **LLM_CHECKED** / **EFFECT_ASSUMED** / **UNTRUSTED** — no real check

For code-derived theorems, the `ProofCertificate.kernel_verified` property is True iff `success` and no `Structural` leaf appears in the proof tree — that is the gate to use when deciding "is this proof actually true".

## Lean 4 Export

Deppy translates Python functions to Lean 4 definitions and emits proof skeletons.  Arithmetic specs (`result >= 0`, `result > n`) get `omega`-backed proofs.  Anything Deppy can't prove is emitted as a `sorry` with a tracked obligation.

```python
@guarantee("result >= 0")
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    return -x

cert = compile_to_lean(abs_val)
print(cert.trust_level)   # LEAN_SYNTAX_COMPLETE   — no sorry, but Lean not run
cert.verify_with_lean()   # runs `lean` on the rendered file (requires the binary on PATH)
print(cert.trust_level)   # LEAN_KERNEL_VERIFIED if Lean accepts it, LEAN_REJECTED otherwise
print(cert.obligations)   # []
```

## Architecture

For a full walk-through of the system — the trusted kernel, cubical/HoTT layer, pipeline stages, verification-level taxonomy, and a map of what is / isn't yet implemented — see **[`ARCHITECTURE.md`](./ARCHITECTURE.md)**.

## Project Structure

```
deppy/              Python package
  core/             Type checker, proof kernel, Z3 bridge
  proofs/           Decorators, tactic DSL, cubical proof pipeline
                    (the production entry points are here)
  hott/             Cubical interval + PathType re-export
  lean/             Python → Lean 4 compiler, proof translators, runner
  pipeline/         Safety pipeline, gradual verification, abstract interp
  effects/          Effect-type framework
  semantics/        Python denotational semantics
  axioms/           Formal axiom library for external libraries
  runtime/          Runtime monitor
  tests/            Unit + integration tests
  examples/         Runnable demo scripts (print-based)
docs/               Tutorial book
```

A handful of top-level modules (`deppy/tactics.py`, `deppy/sidecar.py`, `deppy/concurrency.py`, `deppy/async_verify.py`, `deppy/classical.py`, `deppy/ghost.py`, `deppy/separation.py`, `deppy/heap.py`, `deppy/homotopy.py`, `deppy/patching.py`) are **metadata-only re-exports** kept for backward compatibility with tutorial code; their header docstrings state this explicitly.  For real proof/verification use the submodules listed above.

## Running Tests

```bash
python3 -m pytest deppy/tests/ deppy/lean/ -q
```

Actual counts shift as the test suite evolves; `pytest --collect-only -q | tail -3` is the source of truth.

## Tutorial Book

The full tutorial is at **[thehalleyyoung.github.io/deppy](https://thehalleyyoung.github.io/deppy)** — covering refinement types, termination proofs, sidecar verification of libraries, homotopy methods, separation logic, and Lean 4 export.

## License

MIT
