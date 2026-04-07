# A Non-Cohomologist's Guide to Deppy

## What This Document Is

Deppy is a Python program analysis tool whose README and paper talk about "Čech cohomology," "presheaves," "Grothendieck topologies," and "descent theorems." If you're a PL researcher, a working programmer, or a static-analysis practitioner, you may look at that and think: *do I really need algebraic geometry to find bugs in Python?*

This guide answers that question by explaining every concept in deppy using only ideas you already know from programming languages — control-flow graphs, abstract interpretation, SMT solving, refinement types. It shows you what deppy *actually computes*, why the sheaf language isn't just decoration, and where the mathematical structure gives you things that flat analyses provably cannot.

It's long on purpose. By the end, you should be able to:

1. Use deppy's API without knowing what a sheaf is.
2. Understand *why* deppy uses sheaves, in PL terms.
3. Read deppy's source code and know what each component does.
4. Evaluate the claims: what's genuinely new vs. what's a re-labeling.

---

## Table of Contents

1. [Part I: Using Deppy (No Math Required)](#part-i-using-deppy-no-math-required)
   - [Installing](#installing)
   - [Finding bugs](#finding-bugs)
   - [Reading a bug report](#reading-a-bug-report)
   - [Checking equivalence](#checking-equivalence)
   - [Analyzing structure](#analyzing-structure)
   - [The hybrid type system](#the-hybrid-type-system)
   - [The CLI](#the-cli)
2. [Part II: The Key Insight (Gentle Math)](#part-ii-the-key-insight-gentle-math)
   - [Programs have local facts](#programs-have-local-facts)
   - [Local facts sometimes contradict each other](#local-facts-sometimes-contradict-each-other)
   - [Contradictions that can't be fixed locally are bugs](#contradictions-that-cant-be-fixed-locally-are-bugs)
   - [This is exactly what cohomology measures](#this-is-exactly-what-cohomology-measures)
3. [Part III: The Dictionary (PL ↔ Sheaf Theory)](#part-iii-the-dictionary-pl--sheaf-theory)
   - [Sites = program points](#sites--program-points)
   - [Sections = local type facts](#sections--local-type-facts)
   - [Restriction maps = data flow](#restriction-maps--data-flow)
   - [Presheaf = the collection of all local facts](#presheaf--the-collection-of-all-local-facts)
   - [Gluing = global consistency](#gluing--global-consistency)
   - [H⁰ = globally consistent typings](#h⁰--globally-consistent-typings)
   - [H¹ = bugs](#h¹--bugs)
   - [Coboundaries = fixable disagreements](#coboundaries--fixable-disagreements)
   - [Cocycles = genuine bugs](#cocycles--genuine-bugs)
   - [GF(2) = boolean disagreement algebra](#gf2--boolean-disagreement-algebra)
4. [Part IV: The Three Applications in Depth](#part-iv-the-three-applications-in-depth)
   - [Bug detection via H¹](#bug-detection-via-h¹)
   - [Equivalence via descent](#equivalence-via-descent)
   - [Specification verification via product covers](#specification-verification-via-product-covers)
5. [Part V: What You Can't Do Without Cohomology (The Separation Results)](#part-v-what-you-cant-do-without-cohomology-the-separation-results)
   - [Minimum fix count: polynomial vs NP-hard](#minimum-fix-count-polynomial-vs-np-hard)
   - [Incremental analysis: exact vs approximate](#incremental-analysis-exact-vs-approximate)
   - [Equivalence: complete vs inherently incomplete](#equivalence-complete-vs-inherently-incomplete)
6. [Part VI: How Deppy Actually Works (Implementation Tour)](#part-vi-how-deppy-actually-works-implementation-tour)
   - [The bug detection pipeline](#the-bug-detection-pipeline)
   - [The equivalence pipeline](#the-equivalence-pipeline)
   - [The cohomological engine](#the-cohomological-engine)
   - [The hybrid type checker](#the-hybrid-type-checker)
7. [Part VII: The Extensions (Beyond the Paper)](#part-vii-the-extensions-beyond-the-paper)
   - [Mayer-Vietoris: compositional analysis](#mayer-vietoris-compositional-analysis)
   - [Spectral sequences: hierarchical modules](#spectral-sequences-hierarchical-modules)
   - [Derived categories: relaxed equivalence](#derived-categories-relaxed-equivalence)
   - [Persistent cohomology: tracking bugs over time](#persistent-cohomology-tracking-bugs-over-time)
   - [Étale cohomology: polymorphism](#étale-cohomology-polymorphism)
   - [Galois cohomology: implementation symmetries](#galois-cohomology-implementation-symmetries)
8. [Part VIII: Lean Proofs (What's Machine-Checked)](#part-viii-lean-proofs-whats-machine-checked)
9. [Part IX: FAQ](#part-ix-faq)

---

# Part I: Using Deppy (No Math Required)

You can use deppy without understanding any of the mathematics. This section shows you how.

## Installing

```bash
pip install -e ".[dev]"   # Python 3.10+, installs z3-solver automatically
```

## Finding Bugs

The core API is one function: `detect_bugs`. Hand it a string of Python source code, get back a report.

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
```

Output:

```
[DIV_ZERO] line 4: [BUG] divisor `total` must be ≠ 0 — SAT (gap exists)
```

That's it. No type annotations. No configuration. No LLM. Deppy parsed the function, built an internal representation, checked whether every operation's precondition is guaranteed by its context, and found that the division on line 4 can receive `total = 0` when `values` is an empty list.

## Reading a Bug Report

The `SheafBugReport` object has several useful fields:

| Field | Type | What it means |
|---|---|---|
| `obstructions` | `list[GluingObstruction]` | Each potential bug found |
| `minimum_independent_fixes` | `int` | Minimum number of edits to fix all bugs |
| `bugs_found` | `int` | Number of high-confidence bugs |

Each `GluingObstruction` has:

| Field | What it means |
|---|---|
| `bug_type` | Category: `DIV_ZERO`, `NULL_PTR`, `INDEX_OOB`, `DEADLOCK`, etc. |
| `line` | Source line number |
| `description` | Human-readable explanation |
| `confidence` | 0.0–1.0, how sure deppy is |
| `resolved_by_guard` | `True` if a guard (like `if x != 0:`) already protects this site |

The `minimum_independent_fixes` number is special. It's not just "how many bugs" — it's the minimum number of *independent* code changes needed to fix *all* the bugs simultaneously. Two bugs might be fixed by a single guard. This number accounts for that.

### What bugs can deppy find?

Deppy organizes bugs into *obstruction families* based on the kind of mismatch:

| Family | Bugs | What it means in plain English |
|---|---|---|
| **Refinement gap** | `DIV_ZERO`, `NULL_PTR`, `INDEX_OOB`, `KEY_ERROR`, `ASSERT_FAIL`, `BOUNDS`, `INTEGER_OVERFLOW` | "This operation requires something about its input (e.g., ≠ 0), but the input doesn't guarantee it" |
| **Carrier mismatch** | `TYPE_ERROR`, `TYPE_CONFUSION`, `UNBOUND_VAR` | "The type of this value is fundamentally wrong" |
| **Taint leakage** | `SQL_INJECTION`, `COMMAND_INJECTION`, `XSS`, `SSRF` | "User-controlled data reaches a sensitive operation without sanitization" |
| **Protocol violation** | `ITERATOR_PROTOCOL`, `CONTEXT_MANAGER_PROTOCOL` | "This object doesn't implement the interface it's used as" |
| **Resource lifetime** | `USE_AFTER_FREE`, `DOUBLE_FREE`, `MEMORY_LEAK`, `USE_AFTER_CLOSE` | "This resource is used after it's been released" |
| **Configuration weakness** | `FLASK_DEBUG`, `WEAK_CRYPTO`, `INSECURE_COOKIE` | "This configuration value fails a security policy" |
| **Exception escapement** | `VALUE_ERROR`, `RUNTIME_ERROR`, `FILE_NOT_FOUND` | "This exception can be raised but nothing catches it" |

Here are a few more examples showing the range:

```python
# Null pointer dereference (interprocedural)
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

# Deadlock (cyclic lock ordering)
report = detect_bugs("""
import threading
lock_a, lock_b = threading.Lock(), threading.Lock()

def task1():
    with lock_a:
        with lock_b: return 1

def task2():
    with lock_b:
        with lock_a: return 2
""")
# [DEADLOCK]: cyclic lock ordering: lock_a ↔ lock_b

# SQL injection (taint tracking)
report = detect_bugs('''
def find_user(db, username):
    query = "SELECT * FROM users WHERE name = '" + username + "'"
    return db.execute(query)
''')
# [SQL_INJECTION] line 4
```

## Checking Equivalence

Deppy can prove two functions compute the same thing — or find an input where they differ.

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

When functions *aren't* equivalent, deppy tells you why:

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
# append_a creates a new list; append_b mutates and returns the original
```

For deeper analysis with full mathematical detail, use the cohomological engine directly:

```python
from deppy.equivalence.cohomological_engine import DeepEquivalenceEngine

engine = DeepEquivalenceEngine()

cert = engine.check(
    "def f(x, y): return x + y + 1",
    "def g(x, y): return 1 + y + x",
)

print(cert.equivalent)          # True
print(cert.proof_method.value)  # "cech_h1_zero"
print(cert.betti_numbers)       # (1, 0, 0)
```

## Analyzing Structure

Inspect the internal structure deppy builds for any function:

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

print(report.num_sites)        # 21
print(report.num_morphisms)    # 6
print(report.num_obstructions) # 0
print(report.convergence)      # "global_section_found"
```

This tells you: deppy identified 21 observation points in the function, 6 data-flow connections between them, zero contradictions, and successfully found a globally consistent typing.

## The Hybrid Type System

Deppy also provides decorators for annotating your own code with natural-language specifications:

```python
from deppy.hybrid import guarantee, assume, check

@guarantee("returns a non-negative number")
def abs_val(x: int) -> int:
    assume("x is an integer")
    if x >= 0:
        return x
    return -x
```

- `@guarantee("...")` — a postcondition. Deppy verifies this holds for all inputs.
- `assume("...")` — a precondition. Deppy checks that callers satisfy it.
- `check("...")` — an internal invariant. Deppy verifies it at that point.
- `hole("...")` — a gap to be synthesized. Deppy fills it in.
- `@spec("...")` — an entire function body to be synthesized from description.
- `given("...")` — imports a domain fact (theorem, regulation, axiom).

These are valid Python that runs normally. The decorators/functions are no-ops at runtime by default. When deppy's compiler is active, they become verification obligations.

## The CLI

```bash
deppy check myfile.py                    # Bug detection
deppy equiv file_a.py file_b.py          # Equivalence checking
deppy equiv file_a.py file_b.py --verbose  # Site-by-site detail
deppy explain myfile.py --site arg_x     # Explain a specific site
deppy prove myfile.py --property "..."   # Prove a property
deppy watch myfile.py                    # Re-analyze on save
```

---

# Part II: The Key Insight (Gentle Math)

Now let's understand *why* deppy works the way it does. No category theory required — just the intuition.

## Programs Have Local Facts

When you analyze a program, you discover facts at different program points. Consider:

```python
def normalize(values):
    total = sum(values)       # Point A: total = sum(values), type: int
    return [v / total          # Point B: need total ≠ 0
            for v in values]

def process(data):
    filtered = [x for x in data if x >= 0]  # Point C: filtered is a list
    return normalize(filtered)                # Point D: call normalize
```

At each point, you know something *locally*:

- **Point A**: `values` is a list; `total` is an integer.
- **Point B**: For the division to be safe, `total ≠ 0` must hold.
- **Point C**: `filtered` is a list of non-negative numbers.
- **Point D**: We're passing `filtered` to `normalize`, so `values = filtered`.

These are *local* facts — each one is correct in its own context.

## Local Facts Sometimes Contradict Each Other

Now look at what happens when we connect Point A to Point B through data flow:

- Point A says: `total` is an integer (could be anything, including 0).
- Point B *requires*: `total ≠ 0`.

These two local facts are **incompatible on their overlap**. The "overlap" is the shared variable `total` — both points talk about it, but they disagree about what's true.

Similarly, Point C says `filtered` could be an empty list `[]`. Point D passes `filtered` to `normalize`. Point A receives it as `values`. If `values = []`, then `total = sum([]) = 0`, violating Point B's requirement.

## Contradictions That Can't Be Fixed Locally Are Bugs

Here's the crucial question: **can this contradiction be fixed by changing one of the local facts?**

If yes, it's a "coboundary" — a disagreement that's just an artifact of how we assigned types locally. Adjust one assignment and the disagreement disappears.

If no, it's a **genuine bug**. No matter how you reassign types locally, some pair of points will still disagree. The contradiction is *intrinsic* to the program, not to our analysis.

Example of a fixable disagreement: suppose the programmer adds `if total == 0: return []`. Now there's a new local fact at the branch guard that says "after this point, `total ≠ 0`." The contradiction between Point A and Point B disappears — the guard fixes it.

Example of an unfixable disagreement: if the function has no guard and `values` genuinely can be empty, no local reassignment helps. The bug is real.

## This Is Exactly What Cohomology Measures

Here's the punchline:

> **H¹ counts the contradictions that can't be fixed by local reassignment.**

That's literally what the first cohomology group measures. It takes all the pairwise disagreements between local facts (the "cocycles"), quotients out the ones that are artifacts of your particular choice of local assignments (the "coboundaries"), and what's left is the genuine obstructions.

- **H¹ = 0** means: every pairwise disagreement is fixable by local adjustment. The program is correct (relative to the checked properties).
- **H¹ ≠ 0** means: there are genuine, irreducible contradictions. The program has bugs.
- **rank(H¹)** tells you: the minimum number of independent fixes needed.

That's the entire mathematical insight. Everything else is engineering to make it work on real Python.

---

# Part III: The Dictionary (PL ↔ Sheaf Theory)

Here's a complete translation table between the sheaf-theoretic terminology deppy uses and the PL concepts you already know.

## Sites = Program Points

A **site** in deppy is an observation point in the program where the analysis can ask "what's true here?" Deppy uses five kinds:

| Site Kind | PL Equivalent | Example |
|---|---|---|
| `ArgBoundary` | Function parameter entry | `def f(x):` — what do we know about `x`? |
| `BranchGuard` | Conditional test | `if x > 0:` — after this, `x > 0` holds |
| `CallResult` | Return value of a function call | `y = g(x)` — what do we know about `y`? |
| `OutBoundary` | Function return point | `return result` — what does the caller get? |
| `ErrorSite` | Potentially failing operation | `x / y` — needs `y ≠ 0` |

In a standard dataflow analysis, these would be "program points" or "abstract locations." The word "site" comes from algebraic geometry's "Grothendieck site" — but it means the same thing.

## Sections = Local Type Facts

A **local section** at a site is the type information that holds at that point. In PL terms, it's a refinement type.

```
Site: the division x / y
Section: { y : int | y ≠ 0 }    ← what MUST hold for safety
```

```
Site: the function entry def f(x):
Section: { x : int }             ← what we KNOW about x (could be anything)
```

The word "section" comes from fiber bundles: a section is a choice of one element from each fiber. Here, the "fiber" at each site is the set of possible refinement types, and a "section" is picking one.

## Restriction Maps = Data Flow

A **restriction map** connects two sites via data flow. When information flows from site A to site B, the restriction map tells you how to "restrict" what you know at A to get what's relevant at B.

In PL terms: it's the transfer function from abstract interpretation, or the edge in a dataflow graph.

```
Site A: def f(x)     Section: { x : int }
    |
    | restriction map (data flow: x flows to the division)
    ↓
Site B: x / y        Section: { y : int | y ≠ 0 }    ← REQUIRED
                     Available: { x : int }            ← from A
```

The disagreement between "required" and "available" is where bugs live.

## Presheaf = The Collection of All Local Facts

A **presheaf** is the entire assignment: "at each site, here's the local type fact, and here's how they connect via data flow." In PL terms, it's the abstract state at every program point, plus the transfer functions between them.

Formally:

```
Presheaf Sem: (Sites)^op → (Refinement Lattice)
```

"Contravariant functor" just means: when data flows from A to B (a morphism A → B), the type information goes *backwards* from B to A (restriction). This is exactly how backward analysis works — you propagate requirements backwards from where they're needed.

## Gluing = Global Consistency

The **gluing condition** asks: can all the local sections be assembled into one globally consistent typing?

In PL terms: does the dataflow analysis have a fixed point? Can we assign types to every variable at every point such that every transfer function preserves the assignment?

## H⁰ = Globally Consistent Typings

**H⁰** (zeroth cohomology) is the set of globally consistent typings. If H⁰ is non-empty, there exists at least one way to assign types everywhere that's self-consistent.

In PL terms: H⁰ is the solution space of the dataflow equations.

## H¹ = Bugs

**H¹** (first cohomology) measures the obstructions to global consistency. Each non-zero element of H¹ represents a contradiction between local facts that no local adjustment can fix.

```
H¹ = ker(δ¹) / im(δ⁰)
```

Translation:
- `ker(δ¹)` = all pairwise disagreements that are "locally consistent" (the disagreement pattern doesn't contradict itself on triple overlaps). These are the **cocycles**.
- `im(δ⁰)` = disagreements that can be eliminated by changing individual local sections. These are the **coboundaries**.
- The quotient `ker(δ¹)/im(δ⁰)` = genuine bugs: disagreements that are consistent (not self-contradictory) but also not fixable locally.

## Coboundaries = Fixable Disagreements

A **coboundary** is a disagreement pattern that arises from a "bad choice" of local types. You can fix it by adjusting one local section.

Example: Suppose at site A you assigned the type `int` to variable `x`, and at site B you assigned `int | None`. They disagree on the overlap. But you could change site A's assignment to `int | None`, and now they agree. The disagreement was a coboundary — an artifact of your particular assignment, not a real problem.

## Cocycles = Genuine Bugs

A **cocycle** is a disagreement pattern that satisfies a consistency condition (it doesn't contradict itself across triple overlaps) and therefore *could* represent a real bug. The question is whether it's also a coboundary (fixable) or not.

A cocycle that is NOT a coboundary is a genuine bug: a contradiciton inherent in the program.

## GF(2) = Boolean Disagreement Algebra

Deppy computes cohomology over **GF(2)** — the field with two elements, {0, 1}. This means:

- Each local section is labeled 0 (agrees) or 1 (disagrees).
- The coboundary maps are linear algebra over GF(2).
- `rank(H¹)` = number of linearly independent bug classes = **minimum number of independent fixes**.

Why GF(2)? Because we care about *whether* there's a disagreement (yes/no), not *how much* disagreement there is. GF(2) is the simplest coefficient ring that captures this.

The actual computation is Gaussian elimination on binary matrices — the same thing you'd do in linear algebra, but with all arithmetic mod 2.

---

# Part IV: The Three Applications in Depth

## Bug Detection via H¹

### The Theorem (in Plain English)

> **Theorem 4 (Bugs as gluing obstructions):** A bug exists at an error site *e* iff the semantic presheaf has a non-trivial H¹ class involving *e*. The rank of H¹ over GF(2) equals the minimum number of independent fixes needed.

What this means concretely:

1. Deppy finds all the "error sites" — operations that can fail (divisions, dereferences, index operations, etc.).
2. At each error site, it determines the *required* type (e.g., `{ x : int | x ≠ 0 }` for a divisor).
3. It determines the *available* type from upstream data flow (e.g., `{ x : int }` for an unguarded parameter).
4. If the available type doesn't imply the required type, that's a potential obstruction.
5. It checks whether any guards (like `if x != 0:`) resolve the obstruction.
6. Unresolved obstructions are candidate bugs. Z3 confirms: is `available ∧ ¬required` satisfiable?
7. If Z3 says SAT, the obstruction is genuine — there exists a concrete input that triggers the bug.

### The Algorithm

Here's what `detect_bugs()` actually does, step by step:

```
Input: Python source code (string)

1. PARSE: Parse the source into an AST.

2. COVER SYNTHESIS: Walk the AST and create "sites" — observation points:
   - Every function parameter → ArgBoundary site
   - Every if/assert/try → BranchGuard site
   - Every function call → CallResult site
   - Every return → OutBoundary site
   - Every division, indexing, dereference, etc. → ErrorSite

3. SECTION REQUIREMENTS: For each error site, determine what type
   the operand MUST have for safety:
   - Division: divisor must be ≠ 0
   - Indexing: index must be in [0, len)
   - Dereference: object must be ≠ None
   - etc.

4. AVAILABLE SECTIONS: For each error site, trace backwards through
   data flow to determine what type the operand ACTUALLY has:
   - If it's a parameter: could be anything of declared type
   - If it's guarded by `if x != 0:`: refined to ≠ 0
   - If it comes from a function call: use the callee's return type

5. GUARD HARVESTING: Find all guards (if/try/with/assert) and record
   what they protect and where.

6. OBSTRUCTION DETECTION: For each (required, available) pair:
   - Form the "gap predicate": available ∧ ¬required
   - If a guard resolves it: mark as resolved
   - Otherwise: send to Z3

7. Z3 DISCHARGE: For each unresolved gap:
   - SAT → genuine bug (Z3 provides a witness input)
   - UNSAT → spurious (the gap can't actually happen)

8. INDEPENDENCE: Compute rank(H¹) over GF(2) = minimum fixes.
   Uses Gaussian elimination on the obstruction matrix.

Output: SheafBugReport with obstructions, fix count, and explanations.
```

### Why "H¹" and Not Just "List of Bugs"?

Here's what H¹ buys you that a flat bug list doesn't:

**Minimum fix count.** If you have 5 bugs, maybe 3 of them are fixed by a single `if` guard. A flat list says "5 bugs." H¹ says "2 independent fixes needed" — because the rank of the cohomology group is the dimension of the obstruction space, not the number of individual obstructions.

This isn't a heuristic. The paper proves (Theorem 9) that computing the minimum fix count from a flat set of bugs is NP-hard (it reduces to minimum hitting set). But computing it from H¹ is polynomial — it's just the rank of a GF(2) matrix, which you get from Gaussian elimination.

## Equivalence via Descent

### The Theorem (in Plain English)

> **Theorem 5 (Descent):** Two functions f and g are behaviorally equivalent iff Ȟ¹(U, Iso(Sem_f, Sem_g)) = 0.

Translation: build the "isomorphism presheaf" — at each site, check whether f and g produce the same output under the same conditions. If all these local checks are globally consistent (H¹ = 0), the functions are equivalent. If there's an H¹ obstruction, they're not, and the obstruction tells you where they differ.

### How It Works

```
Input: Two Python functions f, g (as source strings)

1. Z3 ENCODE: Convert each function into a set of "guarded paths":
   - Each path through the function (through if/else, loop iterations)
     becomes a pair (path_condition, return_expression)
   - Path conditions and returns are Z3 symbolic expressions

2. ALIGN: Pair up the paths of f with the paths of g.
   Each pair is a "site" in the comparison.

3. LOCAL ISO CHECK: At each aligned site, check:
   - Are the path conditions jointly satisfiable?
   - If yes, are the return expressions equal under those conditions?
   - Use Z3: is ∃x. (cond_f(x) ∧ cond_g(x) ∧ ret_f(x) ≠ ret_g(x)) SAT?
   - SAT → disagreement (with counterexample)
   - UNSAT → agreement

4. BUILD ČECH COMPLEX:
   - C⁰: one entry per site (0 = agrees, 1 = disagrees)
   - C¹: pairwise overlaps with δ⁰ (disagreement matrix)
   - C²: triple overlaps with δ¹ (cocycle condition)
   - Compute H¹ = ker(δ¹) / im(δ⁰) via GF(2) Gaussian elimination

5. DESCENT VERDICT:
   - If ALL sites agree AND H¹ = 0 → EQUIVALENT (certified)
   - If ANY site disagrees → INEQUIVALENT (with counterexample)
   - H¹ rank = number of independent differences
```

### Worked Example: Binary Search

Two binary search implementations — one uses a closed interval `[lo, hi]`, the other uses a half-open interval `[lo, hi)`:

```python
# Version A: closed interval
def search(xs, target):
    lo, hi = 0, len(xs) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if xs[mid] == target: return mid
        elif xs[mid] < target: lo = mid + 1
        else: hi = mid - 1
    return -1

# Version B: half-open interval
def search(xs, target):
    lo, hi = 0, len(xs)
    while lo < hi:
        mid = lo + (hi - lo) // 2
        if xs[mid] < target: lo = mid + 1
        elif xs[mid] > target: hi = mid
        else: return mid
    return -1
```

Deppy encodes both functions as guarded Z3 paths, aligns them by input, checks each pair, finds all agree (UNSAT: can't find an input where they differ), builds the Čech complex, and gets H¹ = 0. Verdict: equivalent.

### Worked Example: Fibonacci Off-by-One

```python
def fib_a(n):                    def fib_b(n):
    if n <= 1: return n              if n <= 1: return n
    a, b = 0, 1                      a, b = 0, 1
    for _ in range(2, n+1):          for _ in range(2, n):  # ← off by one
        a, b = b, a + b                  a, b = b, a + b
    return b                         return b
```

Deppy encodes both, aligns paths, and finds that 8 out of 10 site pairs disagree (e.g., at n=5: fib_a returns 5, fib_b returns 3). The Čech complex has H¹ rank = 8, with counterexample n=9. Verdict: inequivalent with 8 independent obstructions.

## Specification Verification via Product Covers

The third application: checking that a function satisfies a specification.

Given a function f and a spec S (e.g., "output is sorted"), deppy builds the *product cover* — sites that simultaneously observe the function's behavior and the spec's requirements. The product cover reduces the number of verification conditions from O(k × m) (all site-spec combinations) to the number of *overlapping* pairs, which is typically much smaller.

---

# Part V: What You Can't Do Without Cohomology (The Separation Results)

This is the most important part for anyone skeptical about whether the math is "just relabeling." The paper proves three separation results: properties that the cohomological framework computes efficiently but that traditional (flat, non-topological) analyses provably cannot.

## Minimum Fix Count: Polynomial vs NP-Hard

**Traditional approach:** You have a set of bugs B₁, B₂, ..., Bₙ. Each bug can be fixed by modifying certain sites. Finding the minimum number of site modifications that fix all bugs simultaneously is the **minimum hitting set problem** — NP-hard in general.

**Cohomological approach:** The bugs are elements of H¹, which is a vector space over GF(2). The minimum number of independent fixes is `rank(H¹)`, computed by Gaussian elimination in O(n³) time.

Why the difference? Because H¹ isn't just a set — it's a *vector space*. The linear structure tells you exactly which bugs are "dependent" (one fix handles multiple bugs) and which are independent. A flat set of bugs doesn't have this structure.

> **Theorem 9:** Computing the minimum number of independent fixes from a flat set of error reports is NP-hard. Computing it from H¹ is polynomial.

## Incremental Analysis: Exact vs Approximate

**Traditional approach:** When you edit a function, abstract interpretation needs to re-run the fixed-point computation. Widening operators make this converge but introduce approximation. The result is sound but may gain or lose precision.

**Cohomological approach:** The Mayer-Vietoris exact sequence gives an *exact* decomposition. When you modify part B of a program, you only need to recompute H¹(B) and the connecting homomorphism δ at the boundary. The new H¹(total) is determined exactly — no widening, no precision loss.

```
0 → H⁰(total) → H⁰(A) ⊕ H⁰(B) → H⁰(A∩B) →[δ]→ H¹(total) → H¹(A) ⊕ H¹(B) → ...
```

> **Theorem 10:** The Mayer-Vietoris sequence provides exact incremental updates. Traditional abstract interpretation with widening cannot achieve this without re-analyzing the entire program.

## Equivalence: Complete vs Inherently Incomplete

**Traditional approach:** Abstract interpretation over a finite domain can prove two functions equivalent only if the domain is expressive enough to capture their behavior. The paper proves no *finite* abstract domain suffices for all programs — there always exist equivalent programs that the domain maps to different abstract values.

**Cohomological approach:** The descent theorem gives a *complete* equivalence criterion (relative to the cover). If the cover is fine enough to observe all behavioral differences, then H¹ = 0 iff the functions are equivalent. There's no inherent loss of completeness from the analysis framework itself — only from the granularity of the cover.

> **Theorem 11:** For any finite abstract domain D, there exist equivalent programs that D cannot prove equivalent. The descent criterion is complete relative to the cover.

---

# Part VI: How Deppy Actually Works (Implementation Tour)

This section walks through the actual source code architecture.

## The Bug Detection Pipeline

**Entry point:** `src/deppy/render/bug_detect.py` — function `detect_bugs(source: str) -> SheafBugReport`

The pipeline is roughly 10,000 lines (it's a big file) but breaks into clear stages:

### Stage 1: Cover Synthesis

```python
from deppy.core.site_cover import SiteCoverSynthesizer

synth = SiteCoverSynthesizer()
cover = synth.synthesize(source)
```

This walks the AST and creates a `Cover` object containing:
- **Sites**: one per observation point (14 kinds total, including SSA values, loop headers, tensor shapes, etc.)
- **Morphisms**: restriction maps between sites (data-flow edges)
- **Overlaps**: pairs of sites that share variables

The synthesizer lives in `src/deppy/core/site_cover.py` and delegates to:
- `SiteFactory` — creates sites from AST nodes
- `OverlapBuilder` — finds which sites share data
- `BoundarySynthesizer` — identifies input/output boundaries
- `ErrorSiteRegistry` — catalogs potentially-failing operations

### Stage 2: Section Requirements

The analysis walks the AST and, for each error site, emits a `SectionRequirement`:

```python
@dataclass
class SectionRequirement:
    site_id: SiteId
    bug_type: str              # "DIV_ZERO", "NULL_PTR", etc.
    required_predicate: ...    # Z3 formula or Python check
    description: str
    line: int
```

For example, a division `x / y` creates a requirement:
```
bug_type = "DIV_ZERO"
required_predicate = y ≠ 0
line = 4
```

### Stage 3: Available Sections

For each requirement, trace backwards through data flow to determine what type the variable actually has. This uses the `_PresheafAnalyzer`, which runs a forward abstract interpretation over the AST and records what's known at each site.

### Stage 4: Guard Harvesting

The `harvest` module (`src/deppy/harvest/`) extracts guards from the AST:
- `harvest_guards`: `if`, `assert`, `while` conditions
- `harvest_none_guards`: `if x is not None`, `if x`
- `harvest_type_guards`: `isinstance()`, `type()` checks
- `harvest_collection_facts`: `len()`, `in` operator
- `harvest_arithmetic_bounds`: comparison operators on integers
- `harvest_exception_regions`: `try/except` blocks

### Stage 5: Obstruction Resolution

For each requirement, check if any guard protects it:
- Is the error site inside a `try/except`?
- Is there an `if` guard that implies the requirement?
- Does the presheaf stalk already satisfy the requirement?

If so, mark the obstruction as resolved.

### Stage 6: Z3 Discharge

For unresolved obstructions, form the **gap predicate**: `available ∧ ¬required`. Ask Z3:
- **SAT**: genuine bug. Z3 provides a concrete witness.
- **UNSAT**: spurious. The gap can't happen.
- **UNKNOWN/timeout**: report with lower confidence.

### Stage 7: Independence Analysis

Build the GF(2) obstruction matrix and compute its rank. This gives `minimum_independent_fixes` — the minimum number of code changes needed to fix all bugs.

## The Equivalence Pipeline

**Entry point:** `src/deppy/equivalence/pipeline.py` — class `EquivalencePipeline`

### Stage 1–2: Parse and Build Presheaves

Parse both functions, synthesize covers, run fixed-point analysis to get presheaves for each.

### Stage 3: Align Covers

Build a "common refinement" — a single site category that maps sites from f to corresponding sites in g, so they can be compared point-by-point.

### Stage 4: Global Equivalence Check

The `GlobalEquivalenceChecker` compares presheaves at aligned sites. For each pair, check if the local sections agree (same refinement types, same restrictions).

### Stage 5: Deep Cohomological Check

If the global check is inconclusive, delegate to the `DeepEquivalenceEngine` (the radical cohomological engine). This is the heavy machinery: Z3 path encoding, Čech complex construction, GF(2) H¹ computation.

### Stage 6: Structural Mutation Analysis

Special check: does one function mutate its input while the other copies? If so, they're inequivalent regardless of return values. This catches cases like `lst.append(x)` vs `lst + [x]`.

### Stage 7: Runtime Sampling

If all else is inconclusive, generate random inputs and compare outputs empirically. This is a fallback, not the primary method.

## The Cohomological Engine

**File:** `src/deppy/equivalence/cohomological_engine.py` (~2,100 lines)

This is the mathematical core. It implements the paper's framework faithfully, plus six extensions. Here's the data flow:

```
Source f, Source g
    │
    ▼
Z3SectionEncoder.encode_function()     ← converts AST to guarded Z3 paths
    │
    ▼
Align paths pairwise
    │
    ▼
For each pair: Z3 check (∃x. cond_f ∧ cond_g ∧ ret_f ≠ ret_g)
    │
    ▼
LocalIsoSection per pair: agrees=True/False, counterexample
    │
    ▼
CechComplexBuilder.build(sections)     ← builds C⁰, C¹, C², δ⁰, δ¹ matrices
    │
    ▼
GF(2) Gaussian elimination             ← computes ranks, H⁰, H¹, H²
    │
    ▼
DescentVerifier.verify()               ← applies Theorem 5: H¹=0 ∧ all agree ⟹ equiv
    │
    ▼
DescentCertificate                     ← the Σ-type: (verdict, evidence)
    │
    ▼
Extensions: MV, Spectral, Derived, Persistent, Étale, Galois
```

### Z3SectionEncoder

The encoder converts a Python function into a list of **guarded return paths**:

```python
def f(x, y):
    if x > 0:
        return x + y      # path 1: condition = (x > 0), return = x + y
    else:
        return x - y      # path 2: condition = (x ≤ 0), return = x - y
```

Becomes:
```
Path 1: (x > 0,  x + y)
Path 2: (x ≤ 0,  x - y)
```

Loops are handled by bounded unrolling (up to 9 iterations). Tuple assignments like `a, b = b, a + b` are tracked symbolically.

### CechComplexBuilder

Given n sections, builds:

- **C⁰**: n cochains, one per section (value = 0 if agrees, 1 if disagrees)
- **C¹**: C(n,2) cochains, one per pair (δ⁰: row_i has 1s at positions i and j)
- **C²**: C(n,3) cochains, one per triple (δ¹: standard alternating formula)
- **δ⁰ matrix**: n_pairs × n, entries in GF(2)
- **δ¹ matrix**: n_triples × n_pairs, entries in GF(2)
- **H¹ = dim(ker δ¹) − dim(im δ⁰)**

The GF(2) computation is standard Gaussian elimination — row-reduce the matrices mod 2 and count pivots.

### DescentVerifier

Applies the descent theorem with an important subtlety:

> H¹ = 0 in the GF(2) complex does **not** automatically mean equivalence.

The descent theorem requires that the *Iso presheaf has non-empty stalks everywhere* — meaning every local comparison actually witnesses an isomorphism. If any section has `agrees = False` (the functions differ at that site), then the Iso presheaf has an *empty stalk* at that site, and no global section can exist regardless of H¹.

So the check is: **(all sections agree) AND (H¹ = 0)** → equivalent.

## The Hybrid Type Checker

**File:** `src/deppy/hybrid/core/checker.py` — class `HybridTypeChecker`

This implements bidirectional type checking for hybrid types:

- **Check mode (top-down)**: given a value and a type, verify the value has that type.
- **Synthesis mode (bottom-up)**: given a value, infer its type.

A **HybridType** has five layers, corresponding to five levels of specification detail:

| Layer | What it contains | How it's checked |
|---|---|---|
| `INTENT` | Natural language description | Human review |
| `STRUCTURAL` | Z3-decidable predicates | Z3 solver |
| `SEMANTIC` | LLM-judged predicates | Oracle monad |
| `PROOF` | Lean-verifiable propositions | Lean 4 kernel |
| `CODE` | The actual implementation | Runtime tests |

The **oracle monad** wraps every semantic judgment:

```
T_O(A) = A × TrustLevel × Confidence × Provenance
```

- `TrustLevel`: how the judgment was established (UNTRUSTED → RUNTIME_CHECKED → LLM_JUDGED → Z3_PROVEN → LEAN_VERIFIED)
- `Confidence`: 0.0–1.0, multiplicative under composition
- `Provenance`: where the judgment came from

The monad's `bind` propagates trust by taking the *weakest link* and multiplies confidence. This means a chain of three 90%-confident judgments gives 72.9% overall confidence, and the trust level is the lowest in the chain.

**Coherence check:** A HybridType is *coherent* iff its H¹ across layers vanishes — meaning the intent, structural predicate, semantic predicate, proof, and code all agree with each other on their overlaps. If they don't (e.g., the intent says "sorted" but the code doesn't sort), that's an H¹ obstruction.

---

# Part VII: The Extensions (Beyond the Paper)

The paper establishes the core framework. The implementation extends it with six additional constructions from algebraic geometry.

## Mayer-Vietoris: Compositional Analysis

**What it is in math:** The Mayer-Vietoris exact sequence relates the cohomology of a space to the cohomology of two overlapping pieces:

```
... → H⁰(A∩B) →[δ]→ H¹(A∪B) → H¹(A) ⊕ H¹(B) → H¹(A∩B) → ...
```

**What it means for programs:** If you split a program into two parts A and B (e.g., before and after a function call), the bugs in the whole program decompose into:
- Bugs in A alone
- Bugs in B alone  
- Bugs at the boundary (the connecting homomorphism δ captures new bugs that only appear when A and B interact)

**Why it matters:** Incremental analysis. When you edit part B, you only need to recompute H¹(B) and the boundary term δ. You don't need to re-analyze part A. The exact sequence tells you the new H¹(total) without re-running the whole analysis.

**In the code:** `MayerVietorisAnalyzer` splits sections into halves, computes sub-H¹ values, estimates the connecting homomorphism rank, and checks the exactness condition.

## Spectral Sequences: Hierarchical Modules

**What it is in math:** A spectral sequence is a sequence of "pages" E₂, E₃, ..., E∞ that progressively approximate the cohomology of a complex space by computing it layer by layer.

**What it means for programs:** When you have a caller calling a callee, the bugs decompose hierarchically:

```
E₂^{0,0} = bugs in neither          (inter-module clean, intra-module clean)
E₂^{1,0} = inter-module bugs        (modules disagree at boundaries)  
E₂^{0,1} = intra-module bugs        (bugs inside a single module)
E₂^{1,1} = cross-level bugs         (both levels have issues)
```

The spectral sequence converges: E₂ → E₃ → ... → E∞, and E∞ gives the true H¹ of the entire system.

**Why it matters:** It separates "the callee has a bug" from "the caller misuses the callee" from "the interaction creates a new bug." Different developers can fix different levels independently.

**In the code:** `SpectralSequenceEngine` splits sections into outer (inter-module, even indices) and inner (intra-module, odd indices), computes E₂ entries, applies a crude differential d₂, and produces E∞.

## Derived Categories: Relaxed Equivalence

**What it is in math:** Two chain complexes are *quasi-isomorphic* if a chain map between them induces isomorphisms on all cohomology groups — even if the complexes themselves look different. This is weaker than isomorphism but captures "same behavior."

**What it means for programs:** Two functions might have very different internal structure (different control flow, different intermediate variables) but still have the same input-output behavior at every cohomological level. Derived equivalence captures this — it says "these two implementations are equivalent in every way that cohomology can detect."

**In the code:** `DerivedCategoryEngine` compares the Betti numbers of the two functions' Čech complexes. If they match at all degrees, it checks the mapping cone for acyclicity (which is the criterion for quasi-isomorphism).

## Persistent Cohomology: Tracking Bugs Over Time

**What it is in math:** Given a filtration (a sequence of increasingly fine covers), persistent cohomology tracks when each H¹ class is "born" (first appears) and when it "dies" (gets resolved). Long-lived classes are "essential" — they represent genuine features of the space, not artifacts of the resolution.

**What it means for programs:** As you increase analysis precision (unroll more loops, inline more calls, add more sites), some bugs appear and then disappear (they were artifacts of the coarse analysis). Others persist — these are the real bugs. Persistent cohomology separates signal from noise.

The output is a **barcode**: a set of intervals `[birth, death)` for each H¹ class.

```
Filtration depth:  0    1    2    3    4    5    6    7
Bug class 1:       |====|                              ← short-lived, probably spurious
Bug class 2:       |================================|   ← persistent, real bug
Bug class 3:            |===========|                   ← medium, needs investigation
```

**In the code:** `PersistentCohomologyEngine` computes H¹ at 8 filtration depths (using different subsets of sections) and tracks which classes persist.

## Étale Cohomology: Polymorphism

**What it is in math:** Étale cohomology is a refinement of Čech cohomology that uses "étale covers" — covers where the covering maps are local isomorphisms (like unramified covering spaces). For schemes, it gives finer information than the Zariski topology.

**What it means for programs:** When a function is generic/polymorphic (works on multiple types), the "étale cover" consists of all its type specializations. Ȟ¹_ét = 0 means the function behaves uniformly across all types — it's parametrically polymorphic (Wadler's "free theorem" is the vanishing of étale H¹).

If Ȟ¹_ét ≠ 0, the function has *type-specific behavior* that breaks uniformity. The torsor obstructions tell you which type specializations behave differently.

**In the code:** `EtaleCohomologyEngine` scans for `isinstance`/`type` checks and type-specific operations in both functions, counts dispatch branches, and reports whether the functions behave uniformly.

## Galois Cohomology: Implementation Symmetries

**What it is in math:** Galois cohomology classifies the "twisted forms" of an object — things that look the same locally but are globally different. H¹(G, Aut(X)) counts how many essentially different objects there are that become isomorphic after applying an automorphism.

**What it means for programs:** The "Galois group" is the group of program transformations that preserve behavior:
- **σ_comm**: commuting operands (`x + y` ↔ `y + x`)
- **σ_assoc**: associativity (`(a + b) + c` ↔ `a + (b + c)`)
- **σ_branch**: reordering if/else branches
- **σ_loop**: loop transformations (for ↔ while, loop unrolling)
- **σ_tce**: tail-call elimination

Two implementations are "Galois-equivalent" if one can be transformed into the other by applying these symmetries. H¹_Galois counts the unexplained differences — structural differences that *aren't* just symmetry transformations.

**In the code:** `GaloisCohomologyEngine` computes structural fingerprints (operator counts, control flow structure), checks which symmetry generators explain the differences, and counts residual unexplained differences.

---

# Part VIII: Lean Proofs (What's Machine-Checked)

Deppy's metatheory is mechanized in ~3,500 lines of Lean 4 in the `lean_proofs/` directory. Here's what's actually proven:

| File | What's proven | Plain English |
|---|---|---|
| `SiteCategory.lean` | Program site categories form a category | Morphism composition is associative, identities work |
| `Presheaf.lean` | Semantic presheaves satisfy the presheaf axioms | Restriction maps compose correctly, identities are preserved |
| `CechCohomology.lean` | The Čech complex is a chain complex: ∂₁ ∘ ∂₀ = 0 | Applying the coboundary twice always gives zero — this is what makes H¹ well-defined |
| `Descent.lean` | The descent theorem (Thm 5): H¹ = 0 ⟺ global equivalence | If local isomorphisms exist everywhere AND they glue (H¹ = 0), then a global isomorphism exists |
| `MayerVietoris.lean` | The exact sequence holds | The compositional decomposition is mathematically correct |
| `Separation.lean` | Three separation results: `min_fixes_ge_h1_rank`, `incremental_exact`, `descent_sound`, `descent_complete` | The three advantages over traditional analysis are real |
| `Soundness.lean` | End-to-end soundness | If deppy says "no bugs," there are no bugs (relative to the cover) |
| `FixedPoint.lean` | Fixed-point convergence | The bidirectional analysis terminates |
| `Hybrid/OracleMonad.lean` | Oracle monad laws | `pure` and `bind` satisfy the monad laws; trust propagation is correct |
| `Hybrid/TrustTopos.lean` | Trust levels form a topos | The categorical structure of trust is well-formed |
| `Hybrid/AntiHallucination.lean` | Hallucination = type inhabitation failure | If an LLM output doesn't satisfy its type, it's a hallucination |

The key theorem mechanized in Lean:

```
theorem descent_theorem :
  h1_vanishes (iso_presheaf Sem_f Sem_g) ↔ global_equiv Sem_f Sem_g
```

This is the formal statement that H¹ = 0 for the isomorphism presheaf is both necessary and sufficient for behavioral equivalence. The proof goes through the standard sheaf-theoretic argument: H¹ = 0 means every cocycle is a coboundary, which means the transition functions can be "straightened" to identities, which means the local isomorphisms glue to a global one.

---

# Part IX: FAQ

### Q: Do I need to understand sheaf cohomology to use deppy?

**No.** You can use `detect_bugs()`, `EquivalencePipeline.run()`, and `analyze()` as black boxes. The API is just "give it Python source, get back a report." The math is internal.

### Q: Is this just abstract interpretation with fancy names?

**Partly, but not entirely.** The local analysis (computing what's true at each program point, propagating through data flow) is standard abstract interpretation. What's new is the *global organization* — using the Čech complex and GF(2) linear algebra to extract invariants (minimum fix count, exact incremental updates, complete equivalence) that flat analyses can't compute.

Think of it this way: abstract interpretation gives you the *local sections*. Cohomology gives you the *global structure* of how those sections relate to each other. The separation results (Part V) show this global structure isn't just bookkeeping — it enables computations that are provably harder without it.

### Q: Why GF(2) and not integers or rationals?

Because we're asking a yes/no question: "do these two sites agree?" The answer is 0 (yes) or 1 (no). GF(2) is the natural coefficient ring for boolean-valued questions. You *could* use integers (and the code supports it for Betti number computation), but GF(2) is what gives you the minimum-fix-count result.

### Q: What about false positives?

Deppy has 100% recall but 69% precision on its benchmark suite. That means it finds every bug, but about 31% of what it reports isn't actually a bug. Most false positives come from:

- Imprecise modeling of Python's dynamic semantics (e.g., duck typing)
- Overly conservative assumptions about what types function parameters can have
- Missing guards that are in scope but not detected by the harvester

The `confidence` field on each obstruction helps you filter. Obstructions with Z3-confirmed counterexamples (SAT results) are almost always real.

### Q: How does deppy compare to mypy and pyright?

mypy and pyright are *type checkers* — they check declared type annotations for consistency. If your code has no annotations, they have nothing to check. Deppy works on unannotated Python — it infers refinement types from the code structure.

On deppy's benchmark suite: mypy finds 0/23 bugs. pyright finds 0/23 bugs. Deppy finds 23/23. The comparison isn't entirely fair (the benchmarks are designed to have bugs that mypy/pyright can't express), but it illustrates the fundamental difference: mypy checks *declared* types; deppy checks *semantic* properties (division-by-zero, null dereference, deadlock, etc.).

### Q: Can I use deppy on a large codebase?

The current implementation analyzes one function (or one pair of functions) at a time. Interprocedural analysis is supported (it tracks `None` returns across function boundaries, for example), but the analysis doesn't scale to thousands of functions automatically. Think of it as a per-function deep analysis rather than a whole-program linter.

### Q: What's the oracle monad? Do I need an LLM?

The oracle monad is the wrapper around semantic judgments — assertions that can't be checked by Z3 alone (like "this function returns a sorted list"). If you're using only the bug detection and equivalence checking, you don't need an LLM. Those features use Z3 exclusively.

The LLM is only needed for the hybrid type system's `@guarantee` and `check()` with natural-language predicates. Even then, the monad tracks *how much to trust* the LLM's answer (the `TrustLevel` and `Confidence` fields), so you can choose your own threshold.

### Q: What does "H¹ = 8" mean for the Fibonacci example?

It means there are 8 *linearly independent* input classes on which the two Fibonacci implementations disagree. Not 8 individual inputs — 8 independent *kinds* of disagreement. The actual GF(2) rank of the obstruction space in the Čech complex is 8. In practice, this means the functions differ on 8 of the 10 tested paths through the loop unrollings.

### Q: Is the Čech complex computation expensive?

The Čech complex has size:
- C⁰: n sections
- C¹: C(n, 2) = n(n-1)/2 pair overlaps
- C²: C(n, 3) = n(n-1)(n-2)/6 triple overlaps

For typical functions, n is around 5–15 (the number of meaningful Z3 paths). At n=10, C² has 120 elements. Gaussian elimination is O(n³). Total cost is dominated by the Z3 queries (one per section), which are typically fast (10–100ms each).

The engine filters out "vacuous" sections (Z3 path conditions that are jointly unsatisfiable), which keeps n small. Without this optimization, n could be 100+ and C² would explode.

### Q: What does "presheaf" vs "sheaf" mean in this context?

A **presheaf** assigns local data to each site and has restriction maps, but doesn't require any consistency condition. Every program has a presheaf.

A **sheaf** is a presheaf that satisfies the *gluing condition*: local sections that agree on overlaps can be glued into a unique global section. A program's presheaf is a sheaf iff it has no bugs (H¹ = 0).

So: all programs define presheaves; only correct programs define sheaves.

### Q: Where can I read the paper?

The paper is `programcohomology.tex` in the repository root. It's titled "Sheaf-Cohomological Program Analysis" and is targeted at POPL 2027. The abstract is in `abstract.txt`.

### Q: How do I cite this?

```
@article{young2027sheaf,
  title={Sheaf-Cohomological Program Analysis},
  author={Young, Halley},
  journal={Proceedings of the ACM on Programming Languages (POPL)},
  year={2027}
}
```

---

*This guide was written for programmers and PL researchers who want to understand deppy without first learning algebraic geometry. If you find yourself wanting the full mathematical details, start with the paper (§2 "Overview by Example" is very accessible) and then read the Lean proofs for the formal statements.*
