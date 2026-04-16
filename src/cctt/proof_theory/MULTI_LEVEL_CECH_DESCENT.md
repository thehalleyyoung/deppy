# Multi-Level Čech Descent: How Refinement-Type Fibers Transform Proof ↔ Code

## The Core Thesis

Conventional proof systems treat proofs and programs as separate artifacts that
happen to be connected by a soundness theorem. Multi-level Čech descent makes
them **the same data structure seen from two angles**: the computation tree IS
the proof skeleton, and the proof skeleton IS the computation tree.

The critical innovation: fibers are not just types (`int` vs `float`) — they
are **refinement types** (`{x : int | x > 0}` vs `{x : int | x ≤ 0}`), and
those refinements can reference **arbitrary library operations**:

```python
{t : torch.Tensor | t.mean() == 0}               # zero-mean tensors
{e : sympy.Expr | sympy.expand(e) == e}           # already-expanded expressions
{A : np.ndarray | A.shape[0] == A.shape[1]}       # square matrices
{d : dict | 'port' in d and isinstance(d['port'], int)}  # typed config dicts
```

This is not a metaphor. It is a structural identity that enables both directions
of the F*-style bidirectional extraction, with proof obligations that are as
precise as the library semantics allow.

## Refinement-Type Fibers: Beyond Type-Level Splits

### Old: Type-Level Fibers (Structural/Duck-Type)

Previous Čech descent decomposes parameters by type:
```
Fiber int:    {..., add, sub, mul, lt, ...}    (duck ops)
Fiber float:  {..., add, sub, mul, truediv, ...}
Fiber str:    {..., add, getitem, split, ...}
```

This is *capability-level* decomposition — it tells you what operations
a value supports, but not what *predicates* it satisfies.

### New: Refinement-Type Fibers (Predicate-Level)

Refinement fibers decompose by **logical predicates** on the same type:

```
Fiber positive:  {x : int | x > 0}
Fiber zero:      {x : int | x == 0}
Fiber negative:  {x : int | x < 0}
```

This is *predicate-level* decomposition — it tells you what properties
hold in each fiber, and each property can be used as a hypothesis in
the fiber's proof.

### Arbitrarily Refined: Library-Aware Predicates

The predicate language is open-ended. Any Python expression that
references library operations is a valid predicate:

```python
# Tensor predicates (torch library)
{t : Tensor | t.mean() == 0}          # zero-mean
{t : Tensor | t.norm() <= 1.0}        # bounded
{t : Tensor | len(t.shape) == 2}      # matrix
{t : Tensor | t.shape[0] == t.shape[1]}  # square

# Expression predicates (sympy library)
{e : Expr | sympy.expand(e) == e}     # expanded form
{e : Expr | sympy.is_polynomial(e)}   # polynomial
{e : Expr | sympy.degree(e) <= n}     # bounded degree

# Array predicates (numpy library)
{A : ndarray | np.linalg.det(A) != 0} # invertible
{A : ndarray | np.allclose(A, A.T)}   # symmetric
{A : ndarray | all(np.linalg.eigvals(A) > 0)}  # positive definite

# Dict predicates (structural)
{d : dict | 'port' in d and isinstance(d['port'], int) and d['port'] > 0}
```

Each predicate has a **decidability level** that determines the proof strategy:

| Level | Examples | Strategy |
|---|---|---|
| Z3 | `x > 0`, `x + y == z` | Z3 solver decides |
| STRUCTURAL | `isinstance(x, int)`, `x is None` | AST pattern match |
| LIBRARY | `x.mean() == 0`, `sympy.expand(e) == e` | Library axiom |
| ORACLE | `"x represents a valid email"` | LLM judgment |

## What's Wrong with Single-Level Checking

Current CCTT applies Čech descent at ONE level: the **input guard level**.
The checker decomposes parameters by duck-type fiber (is `x` an int? a float?
a list?), checks equivalence per fiber, and glues via H¹ = 0.

This is powerful but shallow. It misses structure WITHIN the computation:

```python
def f(xs):
    result = 0
    for x in xs:
        if x > 0:        result += x * 2       # CASE A
        elif x == 0:      pass                   # CASE B
        else:             result += abs(x)       # CASE C
    return result

def g(xs):
    result = 0
    for x in xs:
        if x >= 0:        result += x * 2       # Different decomposition!
        else:             result += -x           # But same on each piece
    return result
```

With refinement fibers, we decompose the iteration domain into three
refinement-type regions:
- `{x : int | x > 0}` — both compute `acc + x * 2` ✓
- `{x : int | x == 0}` — f computes `acc + 0`, g computes `acc + 0 * 2 = acc` ✓
- `{x : int | x < 0}` — f computes `acc + abs(x)`, g computes `acc + (-x)` ✓

Each fiber's proof can USE its predicate as a hypothesis. In the negative
fiber, we use `x < 0` to prove `abs(x) == -x`. This is what makes refinement
fibers strictly more powerful than type-level fibers.

## The Multi-Level Tower with Refinement Fibers

Instead of one cover at the top, build a **tower of refinement covers**
at every node of the computation tree:

```
Stratum 0: Input type refinements
           {xs : list[int] | len(xs) > 0}
           {xs : list[int] | len(xs) == 0}

Stratum 1: Top-level branch refinements
           {xs | len(xs) <= 1}
           {xs | len(xs) > 1}

Stratum 2: Fold body iteration refinements
           {x : int | x > 0}
           {x : int | x == 0}
           {x : int | x < 0}

Stratum 3: Nested branch refinements
           {(x, depth) | depth < max_depth}
           {(x, depth) | depth >= max_depth}

Stratum 4: Dict key refinements
           {d | 'mode' in d and d['mode'] == 'fast'}
           {d | 'mode' in d and d['mode'] == 'safe'}

Stratum 5: Exception path refinements
           {args | preconditions_hold(args)}      → normal path
           {args | not preconditions_hold(args)}  → exception path

Stratum 6: Library call refinements
           {x | x satisfies library.func.precondition}
           → post: {result | library.func.postcondition(x, result)}
```

At each stratum:
1. Decompose into refinement-type regions (the Čech cover)
2. Verify per region UNDER the refinement hypothesis
3. Verify overlaps under the intersection hypothesis
4. Glue if H¹ = 0

## How Refinement Fibers Make Proving EASIER

### 1. Each fiber proof gets a free hypothesis

With type-level fibers, the fiber proof is "prove lhs ≡ rhs when x is an int."
The proof gets no useful hypothesis — just the structural type.

With refinement fibers, the fiber proof is "prove lhs ≡ rhs when x > 0."
The proof gets `x > 0` AS A HYPOTHESIS — it can use this fact in Z3 queries,
library axiom applications, and arithmetic simplifications.

This turns many hard proofs into trivial ones: `abs(x) == x` is hard globally,
but trivial under the hypothesis `x > 0`.

### 2. Z3 handles exhaustiveness automatically

For Z3-decidable predicates, the cover's exhaustiveness is checked
automatically:

```python
cover = RefinementCover.from_predicates("int", "x", [
    ("positive", "x > 0"),
    ("zero",     "x == 0"),
    ("negative", "x < 0"),
])
# Z3 proves: (x > 0) ∨ (x == 0) ∨ (x < 0) is valid ✓
# Z3 proves: (x > 0) ∧ (x < 0) is unsat ✓  (empty overlap)
# Z3 proves: (x > 0) ∧ (x == 0) is unsat ✓  (empty overlap)
```

Empty overlaps need NO compatibility proof — the system detects them
automatically.

### 3. Library predicates connect types to library axioms

A predicate like `sympy.expand(e) == e` connects the type system to
the library axiom system. When proving a property of a function that
calls `sympy.expand()`, the proof can:

1. Split into fibers: "already expanded" vs "not yet expanded"
2. In the "already expanded" fiber, use `sympy.expand(e) == e` as
   a hypothesis — this IS the library axiom applied at the type level
3. In the "not yet expanded" fiber, apply the library axiom to show
   that `expand()` produces an expanded expression

This is bidirectional: the type carries the library invariant, and
the library axiom justifies the type.

### 4. Proof search decomposes along the refinement lattice

The refinement lattice gives proof search a natural decomposition:
- For each predicate, try Z3 first
- If Z3 fails, check if a library axiom matches
- If no axiom, fall back to oracle
- Each fiber search is independent — parallelizable

## How Refinement Fibers Make Code Generation EASIER

### 5. Refinement predicates map to guards

When extracting code from a proof, refinement predicates become guards:

```python
# From refinement fiber {x : int | x > 0}
if x > 0:
    ...  # extracted from the "positive" fiber proof

# From refinement fiber {d : dict | 'mode' in d and d['mode'] == 'fast'}
if 'mode' in d and d['mode'] == 'fast':
    ...  # extracted from the "fast" fiber proof
```

The proof structure generates the code's guard conditions — more precise
than type-level extraction, which can only generate `isinstance()` checks.

### 6. Library invariants propagate through extraction

When a fiber predicate is `sympy.expand(e) == e`, the extracted code
knows that `e` is already expanded — it can skip the `expand()` call.
This is optimization by proof: the proof tells the code what invariants
hold, and the code exploits them.

### 7. Missing fibers become typed holes

If a cover is exhaustive but a fiber proof is missing, the extraction
engine generates a typed hole:

```python
# hole: need proof for {x : Tensor | x.mean() != 0}
# must satisfy: normalize(x) == x / x.mean()
raise NotImplementedError("handle non-zero-mean tensor")
```

The hole carries the refinement predicate AND the obligation — a future
developer (or LLM) knows exactly what to implement.

## Theoretical Foundation

In the monograph's language, multi-level refinement descent computes a
**spectral sequence** E_r^{p,q} over the refinement lattice:

- p = stratum depth (0 = input, 1 = top-level case, 2 = fold body, ...)
- q = cohomological degree (0 = sections, 1 = obstructions)
- E_0 = local cohomology at computation-tree leaves, under leaf refinements
- E_1 = cohomology of case/branch regions after leaf gluing
- E_r+1 = cohomology after gluing at stratum r

The refinement lattice enriches each stratum with predicate-level
information that type-level fibers miss.  The spectral sequence
converges to the global H¹ and gives a strictly finer partition
than the type-level version at every page.

**Key theorem**: If E_r^{p,1} = 0 for all p at page r, then the global
equivalence holds, and we can stop early. Refinement fibers make this
convergence faster because:
- More fibers → finer partition → easier per-fiber proofs
- Z3-empty overlaps → fewer compatibility obligations
- Library hypotheses in fibers → stronger local reasoning

## Implementation

- `predicates.py` — Predicate AST (Pred), parsing, Z3 compilation,
  decidability analysis, RefinementFiber, RefinementCover, cover algebra.

- `pythonic_types.py` — `Refinement` type uses `Pred`; `refine()` and
  `cover_from_predicates()` convenience constructors; `CType.refinement_cover()`
  method on Nullable, PyUnion, DependentDict, ExceptionEffect, PyLibType.

- `terms.py` — `RefinementDescent` proof term with arbitrary predicates,
  per-fiber proofs checked under refinement hypothesis, Z3-verified
  exhaustiveness.

- `checker.py` — `_check_refinement_descent` adds refinement predicates
  as context assumptions, checks overlap proofs under conjunction, auto-skips
  Z3-empty overlaps.

- `sugar.py` — `refinement_split()` tactic for Pythonic proof DSL.

- `bidi_extraction.py` — `ProofObligation.refinement` carries predicates.

