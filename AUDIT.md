# Deppy `.deppy` — gaps remaining for a Turing-expressive sidecar proof format

## What "Turing-expressive sidecar proof format" means

A `.deppy` file is a **sidecar specification + proof script** for arbitrary Python code.  The format is *Turing-expressive* iff:

1. **Any property** that a human (or LLM) can formally state about Python code is expressible.
2. **Any proof** a human or LLM can write — by hand, by tactic, or by appealing to external libraries — is expressible.
3. The format **compiles to a Lean proof** that Lean's own kernel type-checks.  The trust chain bottoms at *Lean's elaboration of user-written or LLM-written tactics*, not at "deppy's kernel admitted an opaque axiom".
4. The pipeline can run on **any** Python code; nothing is library-specific.

Goal: **a human or LLM, looking at the goal state, can supply a tactic that closes it; the format accepts that**.  Whether the tactic is `by ring`, `by exact some_lemma`, or 200 lines of custom proof, the format embeds it and Lean checks it.

---

## The strong proof language: **PSDL** (Python-Semantic Deppy Language)

The naive escape hatch — "user pastes raw Lean text" — works but loses every advantage of deppy's metatheory.  The strong language makes deppy's existing **cubical / cohomological / duck-typed / effect-modal** view of Python *the primitive vocabulary* of the proof language.  Each PSDL tactic compiles to (a) a deppy ``ProofTerm`` the kernel checks and (b) a Lean tactic the Lean kernel checks.

### PSDL design

PSDL appears inside a `verify` block as a `psdl_proof: |` indented block.

#### Cubical / control-flow primitives (deppy.pipeline.cubical_ast + cubical_effects)

| PSDL tactic | Compiles to ProofTerm | Compiles to Lean | Semantics |
|---|---|---|---|
| `branch_value: <body>` | `EffectWitness(effect="value")` | `-- value fibre` | Take the happy-path face of the cubical set |
| `branch_raise <Exc>: <body>` | `ConditionalEffectWitness(precondition="raises " + Exc, effect="exception")` | `· -- raises Exc` | Take the exception-fibre face for `Exc` |
| `kan_fill axis_<n> eps_<e>: <body>` | `KanFill(dimension=<n>, faces=…)` | `-- Kan-fill axis n eps e` | Reconstruct a missing face from peers |
| `pure_assume:` | adds `□A` modality to context | `-- pure` | Assert function is in `□` (no effects) |
| `c0_local <fn>: <body>` | `Cocycle(level=0, components=[…])` | `theorem deppy_c0_<fn>` | Per-function safety bundle |
| `c1_propagate <caller> → <callee>: <body>` | `Cocycle(level=1, …)` | `theorem deppy_c1_<edge>` | Call-site precondition propagation |

#### Type-dispatch / duck-typing (deppy.core.path_engine + DuckPath)

| `case_isinstance x : T: <body>` | `Fiber(scrutinee=x, type_branches=[(T, …)])` | `by_cases h : x.is(T)` | Verify under `isinstance(x, T)` |
| `else_case: <body>` | (paired with `case_isinstance`) | `· -- ¬isinstance` | Complement fibre |
| `dispatch_getattr x.<attr>: <body>` | `DuckPath` via `getattr` | `match x.<attr> with` | Method-resolution path |
| `dispatch_protocol x : <Proto>: <body>` | `FiberedLookup` | `Σ-projection on attribute` | Run-time protocol check |

#### Path / homotopy / dependent (deppy.core.path_engine + path_dependent_specs)

| `transport_along <path>: <body>` | `TransportProof(type_family, path_proof, base_proof)` | (custom Lean) | Transport a proof along a path |
| `path_compose <p> ∘ <q>` | `PathComp(p, q)` | `Eq.trans` | Path composition |
| `cong <f>: <body>` | `Cong(f, …)` | `congr` | Congruence under f |
| `funext: <body>` | `FunExt(var, body)` | `funext` | Function extensionality |
| `univalence A ≃ B: <body>` | `Univalence(equiv_proof, …)` | (custom) | Equivalent types are equal |

#### Standard logical tactics (deppy.core.kernel)

| `apply <F>` | `AxiomInvocation(F)` | `exact F` | Cite a foundation |
| `unfold <X>` | `Unfold(X, …)` | `unfold X` | Unfold a definition |
| `rfl` | `Refl` | `rfl` | Reflexivity |
| `sym <p>` | `Sym(p)` | `Eq.symm p` | Symmetry |
| `trans <p> <q>` | `Trans(p, q)` | `Eq.trans p q` | Transitivity |
| `rewrite <L>: <body>` | `Rewrite(L, …)` | `rw [L]` | Rewrite using a lemma |
| `induction xs: nil := …, cons := …` | `ListInduction(var=xs, …)` | `induction xs with …` | List induction |
| `nat_induction n: zero := …, succ := …` | `NatInduction(var=n, …)` | `induction n with …` | Nat induction |
| `cases x: …` | `Cases(scrutinee=x, …)` | `cases x with …` | Case analysis |
| `assume h : T := <proof>` | `Cut(hyp_name=h, hyp_type=T, …)` | `have h : T := …` | Local hypothesis |
| `z3 <formula>` | `Z3Proof(formula)` | `omega` (best-effort) | Z3 discharge |

#### Body-translation primitives (deppy.lean.body_translation)

| `unfold_body <fn>: <expected_lean>` | `Unfold(<fn>) + Refl-check` | `show <expected_lean>` | Assert the body translates to expected |
| `unfold_value_fibre <fn>: <expr>` | `Unfold` of just the value-fibre face | (Lean comment + show) | Unfold only the happy-path branch |

#### Top-level / structural

| `lemma_local L : <stmt> := <proof>` | `Cut(L, T, lemma_proof, body)` | `have L : <stmt> := <proof>` | Local lemma |
| `vacuous "<reason>"` | `Structural(reason)` (gated) | `exact absurd …` | Branch is vacuous |
| `lean { <raw> }` | `LeanProof(theorem, proof_script)` | `<raw>` | Raw Lean escape hatch |
| `hint "<text>"` | annotation only | `-- hint` | LLM-iteration hint |
| `show_goal` | annotation only | `show?` | Print current goal state |
| `show_term` | annotation only | `-- term: <repr>` | Print constructed ProofTerm |

### Example PSDL proof

Proving `Point.distance(p, q) >= 0` using deppy's cubical+effect+fibration view:

```
verify dist_nonneg_psdl:
  function: sympy.geometry.point.Point.distance
  property: "Point.distance(p, q) >= 0"
  with_binders: p: Point, q: Point
  psdl_proof: |
    -- Sympy.distance branches on isinstance(other, Point);
    -- the value-fibre returns sqrt(sum_sq), the exception-fibre raises.
    case_isinstance other : Point:
      -- value-fibre: under isinstance(other, Point), the body
      -- returns sqrt(sum_sq).  Unfold to that:
      unfold_value_fibre Point.distance: sqrt(sum_zip_sub_sq(self, other))
      -- sqrt is non-negative for non-negative argument:
      apply Real_sqrt_nonneg
      -- side condition: sum_zip_sub_sq(...) >= 0
      assume h_nonneg : "sum_zip_sub_sq(self, other) >= 0" := z3
    else_case:
      -- exception-fibre: a TypeError is raised; this branch never
      -- reaches a return value, so the claim is vacuous.
      branch_raise TypeError:
        vacuous "value-fibre handles Points; this raises before returning"
```

This proof:

* Uses `case_isinstance` (FibrationVerifier) → kernel `Fiber`, Lean `by_cases`.
* Uses `unfold_value_fibre` (cubical_effects) → kernel `Unfold` of the value-face only.
* Uses `apply` (kernel `AxiomInvocation`) for the foundation citation.
* Uses `assume … := z3` (Cut + Z3Proof) for the side condition.
* Uses `branch_raise` (cubical_effects modal) to inhabit the exception fibre.
* Uses `vacuous` (Structural, gated) to dismiss it.

The compiled deppy ProofTerm:

```
Fiber(scrutinee=Var("other"),
      type_branches=[
        (PointType, Cut(
            hyp_name="h_nonneg",
            hyp_type=RefinementType(predicate="sum_zip_sub_sq >= 0"),
            lemma_proof=Z3Proof("sum_zip_sub_sq(self, other) >= 0"),
            body_proof=Unfold("Point_distance",
                AxiomInvocation("Real_sqrt_nonneg")))),
        (else_branch, Structural("value-fibre handles Points")),
      ])
```

The compiled Lean tactic:

```lean
by
  by_cases h : isinstance other Point
  · -- value-fibre
    unfold Point_distance
    apply Foundation_Real_sqrt_nonneg
    -- side goal: sum_zip_sub_sq self other >= 0
    omega
  · -- exception-fibre, value-fibre handles Points
    sorry
```

Both are emitted; deppy's kernel checks the ProofTerm; Lean's kernel checks the tactic.

---

## **THE GAP**: opaque Props block PSDL's Lean tactics from elaborating

PSDL emits a tactic like:

```lean
by_cases h : isinstance other Point
· unfold Point.distance
  exact Foundation_Real_sqrt_nonneg
  have h_n : sum_zip_sub_sq self other ≥ 0 := by omega
· exact absurd ‹_› (by simp)
```

This is *correct in spirit* — exactly what a human or LLM would write.  But Lean's elaborator rejects it because the surrounding declarations are **opaque**:

```lean
opaque Verified_dist_nonneg_psdl_property : Prop          -- ← opaque!
opaque Sidecar_dist_pythagoras_prop : Prop                -- ← opaque!
opaque Foundation_Real_sqrt_nonneg_prop : Prop            -- ← opaque!
axiom Point_distance : Int → Int → Int                    -- ← Int, not Point!
```

Lean can't `by_cases h : isinstance other Point` because there's no `Point` type; can't `unfold Point.distance` because it's an `axiom`, not a `def`; can't `exact Foundation_Real_sqrt_nonneg` because the foundation's type is an opaque Prop, not the inequality the goal expects.

The fix: **drive Lean declarations from the .deppy annotations**.  Every `verify` block already names:
- the function (`function: sympy.geometry.point.Point.distance`)
- the property (`property: "Point.distance(p, q) >= 0"`)
- the binders (`binders: p: Point, q: Point`)

These suffice to generate **concrete** Lean:

```lean
-- Generated from binders: p: Point, q: Point
axiom Point : Type

-- Generated from function: sympy.geometry.point.Point.distance + signature inference
axiom Point.distance : Point → Point → Int

-- Generated from foundation Real_sqrt_nonneg's *typed* statement
axiom Foundation_Real_sqrt_nonneg : ∀ (x : Int), x ≥ 0 → Real_sqrt x ≥ 0

-- Property compiled from "Point.distance(p, q) >= 0" + binders
def Verified_dist_nonneg_psdl_property : Prop := 
  ∀ (p q : Point), Point.distance p q ≥ 0

-- PSDL-emitted Lean tactic now actually elaborates:
theorem Verified_dist_nonneg_psdl : Verified_dist_nonneg_psdl_property := by
  intros p q
  -- PSDL: if isinstance(other, Point):
  ...
```

The `Sidecar_X_prop` / `Foundation_X_prop` / `Verified_X_property` definitions become **concrete Lean Props** assembled from:
1. `binders:` → declared `axiom <T> : Type` per unique binder type
2. `function:` → declared method signature (parameter types from binders, return type inferred)
3. `property:` → translated to a Lean Prop using the binder + function context
4. `via: foundation X` → the foundation's typed signature, derived from its statement parsed under the property's type context

A new top-level `.deppy` directive `code_types: |` lets the user supply typed signatures for any sympy method PSDL references (`sqrt: Int → Int`, `sum_zip_sub_sq: Point → Point → Int`, etc.), so the Lean preamble has them in scope.

This is **the** gap.  Once Props are concrete, the trust chain shifts from "deppy admitted opaque X" to "Lean's kernel checked the user's PSDL tactic against a concrete claim".

### What annotations drive concretisation

| .deppy field | Drives in Lean preamble |
|---|---|
| `binders: p: Point, q: Point` | `axiom Point : Type`; `intros p q` |
| `function: sympy.geometry.point.Point.distance` | `axiom Point.distance : Point → Point → Int` |
| `property: "Point.distance(p, q) >= 0"` | `def …_property : Prop := ∀ (p q : Point), Point.distance p q ≥ 0` |
| `via: foundation Real_sqrt_nonneg` | the foundation's statement compiled into a typed Prop |
| `code_types: \| sqrt: Int → Int` (NEW) | `axiom sqrt : Int → Int` |
| `code_types: \| sum_zip_sub_sq: Point → Point → Int` (NEW) | `axiom sum_zip_sub_sq : Point → Point → Int` |
| `requires: "p != q"` | `intros _h_pre` after introducing the hypothesis |
| `ensures: ...` | augmented Prop body |

### Why this is the linchpin

Every other "Lean compiles `exit 0`" success up to now has been because the certificate's theorems are tautological wrappers around opaque Props (`theorem T : Sidecar_X_prop := Sidecar_X` — kernel-trivial).  Lean accepts *because* the type doesn't reduce.  With concrete Props:

- Lean's elaborator must actually unify the proof body with the goal type.
- `by_cases h : isinstance other Point` works because `Point` is declared.
- `unfold Point.distance` works because it's a `def`.
- `exact Foundation_Real_sqrt_nonneg` works because the foundation has a concrete Prop type that unifies with a sub-goal of the proof.

Failures become *real* failures (LLM iteration target), not "yes this opaque Prop is inhabited because we said it is".

---

## What is *still* missing for full Turing-expressivity (beyond PSDL + concrete Props)

PSDL closes the proof-language gap.  Concrete Props (this round) close the Lean-elaboration gap.  These remain:

### B. Type-system expressiveness  `[hard]`
- Universe polymorphism / polymorphic foundations
- Refinement types `{x : Int // x ≥ 0}`
- Sigma / Pi (dependent) types
- Higher-order quantifiers
- Inductive type declarations
- Coinductive / corecursive specs

### E. Class / OOP  `[fixable in PSDL]`
- Class invariant declarations
- Inheritance
- Method preconditions on `self`

### F. Advanced cubical / homotopy  `[partially fixable in PSDL]`
- Higher inductive types
- Path-equivalence between two implementations
- Cubical structure declarations beyond axis_n/eps_e

### G. Module structure  `[fixable]`
- Namespaces, re-exports, conditional imports, versioned imports

### H. Test / example / counterexample  `[fixable]`
- Concrete examples
- Property-based-test directives
- Counterexample minimization

### I. Verification quality  `[fixable]`
- Confidence levels per axiom
- Provenance metadata
- Deprecation

### J. Dynamic / generative  `[hard]`
- Schematic axioms / proof templates
- Spec generation from examples
- LLM directive hints

### K. LLM iteration affordances  `[partially fixable in PSDL]`
- Goal state output  ✓ via `show_goal` in PSDL
- Partial-proof credit
- Tactic suggestion mode
- Counterexample-to-obligation

### L. Multi-target  `[fixable]`
- Coq / Agda / Idris targets
- Z3-only target
- No-target dry run

---

## This pass implements

| ID | Feature |
|---|---|
| **A.1** | `lemma X:` accepts multi-line `lean_proof:` text |
| **A.2** | `foundation X:` accepts `lean_proof:` text |
| **A.3** | `axiom X:` (in spec block) accepts `lean_proof:` |
| **A.4** | `verify X:` accepts `lean_signature:` + multi-line `by_lean: \|` |
| **A.5** | Top-level `lean_imports: \|` injected into certificate |
| **A.6** | Top-level `lean_preamble: \|` injected into certificate |
| **A.7** | Goal state surfaced when Lean rejects (machine-readable) |
| **PSDL** | Full Python-Semantic Deppy Language: parser, ProofTerm compiler, Lean tactic compiler |
| **CONCRETE-PROPS** | Annotation-driven concrete Lean Props — replaces opaque `Sidecar_X_prop` / `Foundation_X_prop` / `Verified_X_property` with concrete Lean propositions assembled from `.deppy` `binders:` / `function:` / `property:` / `code_types:` annotations.  PSDL-emitted Lean tactics now actually elaborate. |
| **CODE-TYPES** | New top-level `code_types: \|` block where the user lists typed signatures for any sympy method / helper PSDL references.  Drives concrete `axiom <name> : <signature>` declarations in the Lean preamble. |

Items B, E, F, G, H, I, J, K, L are noted but not yet implemented; the PSDL escape hatch (`lean { ... }`) covers them in practice for proofs the user/LLM can write directly in Lean.
