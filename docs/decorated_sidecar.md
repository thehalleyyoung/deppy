# Decorator-based sidecar — proof annotations inline with Python

Deppy supports two equivalent forms for the proof-relevant metadata
attached to a module:

  * `.deppy` **sidecar files** — separate-file YAML-shaped form for
    when you are *retrofitting proof obligations onto code you didn't
    write* (sympy, numpy, …).  See `sympy_geometry.deppy` for an
    example.
  * **Decorators inside a Python module** — when you are *writing
    the module yourself* and want the proof metadata to live next
    to the implementation it constrains.

Both produce a `SidecarModule` and feed the **same** verify
pipeline.

## Quick start

```python
# my_module.py
from deppy.proofs.sidecar_decorators import (
    foundation, axiom, verify, spec, lemma,
    psdl_proof, by_lean, code_type, predicate, constant,
    lean_import, lean_preamble,
)


@foundation
def Real_sqrt_nonneg():
    """sqrt(x) >= 0 when x >= 0"""


@axiom(
    target="my_module.Point.distance",
    statement="Point.distance(p, q) >= 0",
)
def dist_nonneg():
    """Distance is non-negative."""


@spec(
    # guarantees must be Python expressions, ``lean: ...``, or
    # ``smt: ...`` — natural language is rejected by
    # ``_validate_formal`` in ``deppy/proofs/sidecar_decorators.py``.
    guarantees=["Point.distance(p, q) >= 0"],
    axioms=["dist_nonneg"],
)
class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    @verify(
        property="Point.distance(p, q) >= 0",
        via="foundation Real_sqrt_nonneg",
        binders={"p": "Point", "q": "Point"},
    )
    @psdl_proof("""
if isinstance(other, Point):
    inline(Point.distance, sqrt(sum_zip_sub_sq(self, other)))
    apply(Real_sqrt_nonneg)
    assert sum_zip_sub_sq(self, other) >= 0, "z3"
else:
    raise NotImplementedError
""")
    def distance(self, other):
        from math import sqrt
        return sqrt((self.x - other.x) ** 2 + (self.y - other.y) ** 2)
```

Run:

```bash
python -m deppy.pipeline.run_verify --from-module my_module
```

Or programmatically:

```python
import my_module
from deppy.proofs.sidecar_decorators import extract_sidecar_module
sm = extract_sidecar_module(my_module)

from deppy.lean.sidecar_runner import _run_with_module
from pathlib import Path
rr = _run_with_module(
    sm,
    out_path=Path("my_module.lean"),
    sidecar_path=Path(my_module.__file__),
)
print(rr.certified)  # True / False
```

## Decorator reference

| Decorator | Target | What it records | `.deppy` equivalent |
|---|---|---|---|
| `@foundation` | function | A generic mathematical fact. Statement comes from docstring or the function's return value. | `foundation NAME: "stmt"` |
| `@axiom(target=, statement=, ...)` | function | A claim about the library's behaviour. | `axiom NAME: target: ...` |
| `@verify(property=, via=, binders=, ...)` | function | A property of *this* function — the verify pipeline kernel-checks it. | `verify NAME: function: ... property: ... via: ...` |
| `@psdl_proof("...")` | function (after `@verify`) | A PSDL proof body (Python-syntax tactics). | `psdl_proof: \|` block |
| `@by_lean("...")` | function | Raw Lean tactic for the verify block. | `by_lean: \|` block |
| `@spec(guarantees=, axioms=, ...)` | class | A spec block listing guarantees + cited axioms. | `spec target: ...` |
| `@lemma(name=, statement=, by=, lean_proof=, ...)` | function | A local lemma the certificate can cite. | `lemma NAME: ...` |
| `@code_type(name, signature)` | (call form) | A Lean type signature for a function name. | `code_types: \|` line |
| `predicate(name, body)` | (call form) | Custom predicate definition. | `predicate NAME: ...` |
| `constant(name, body)` | (call form) | Symbolic constant. | `constant NAME: ...` |
| `lean_import(line)` | (call form) | A top-level Lean import. | `lean_imports: \|` line |
| `lean_preamble(text)` | (call form) | Append to top-level Lean preamble. | `lean_preamble: \|` block |

## How extraction works

Each decorator stamps the function (or class) with a `__deppy_*__`
attribute carrying the metadata as a dict.  At extraction time,
`extract_sidecar_module(module)` walks the module's members
(including methods of classes) and reassembles a `SidecarModule`
with the same fields a parsed `.deppy` file would produce.

The pipeline that runs after extraction is **identical**:

  1. Foundation Z3 discharge.
  2. Mechanization to concrete Lean Props.
  3. Per-method body translation.
  4. Per-verify-block kernel verification + counterexample search.
  5. PSDL compilation when `@psdl_proof` is set.
  6. Lean certificate emission + `lean_runner` round-trip.
  7. JSON sidecar emission.
  8. `certify_or_die` verdict.

## When to use which form

| Workflow | Use |
|---|---|
| Verifying an *imported* library (`sympy`, `numpy`, `requests`, …) you don't control | `.deppy` sidecar |
| Writing a *new* module and proving its properties as you go | Decorators |
| Mixed: some claims about `sympy` + some about your own helpers | Both — the decorator form imports your code; the `.deppy` form adds external claims; merge via `import other.deppy` and `--from-module` together (run twice and diff JSON if you need rigorous separation) |

The decorator form is best when:
  * The function being verified IS the function carrying the
    `@verify` decorator.
  * You want refactors to keep the proof metadata aligned with the
    implementation (renaming the function automatically renames the
    verify block's `function:` target via `__qualname__`).
  * You want the proof obligations to be discoverable via `dir(mod)`.

The `.deppy` form is best when:
  * The module being verified is read-only (third-party library).
  * Multiple `.deppy` files compose via `import` (one per
    sub-module of a large library).
  * You want to publish the proof metadata as a separate artefact
    (audit log, reproducibility manifest).

## Composition with `.deppy`

A module may use *both*: decorators inline define one piece of the
sidecar; a separate `.deppy` file describes external dependencies.
The two are union'd at extraction time.

```python
# my_module.py
@foundation
def MyFact():
    """x + 0 == x"""
```

```yaml
# my_module.deppy
import generic_arith.deppy   # external foundations

axiom external_claim:
  target: third_party.lib
  statement: "..."
```

```bash
# Run both — decorator form adds the inline foundations; .deppy
# adds the external claims.
python -m deppy.pipeline.run_verify --from-module my_module
python -m deppy.pipeline.run_verify my_module.deppy
```

## See also

- `examples/decorated_geometry.py` — full worked example.
- `deppy/proofs/sidecar_decorators.py` — implementation.
- `deppy/lean/sidecar_runner.py` — the `--from-module` CLI hook.
- `docs/psdl_treatise/` — the long-form treatise on the verification
  pipeline as a whole (uses the `.deppy` form throughout).
