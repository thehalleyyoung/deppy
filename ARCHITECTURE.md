# Deppy — Architecture

This is the canonical map of the system: what each module does, how the pieces fit together, what is actually implemented vs. what is a deliberate placeholder, and how a verification goal flows through the pipeline.

Keep this document honest.  If you change behaviour, change the claim here too.

---

## 1. One-paragraph summary

Deppy is a formal verification harness for Python.  You write ordinary Python, annotate with `@guarantee` / `@requires`, and Deppy discharges the resulting proof obligations through a small cubical-flavoured proof kernel that can delegate to Z3, run a pattern-based rewriter, or emit Lean 4.  The system is layered: a trusted **kernel** in `deppy/core/kernel.py` that checks proof terms; a **language** layer in `deppy/proofs/language.py` that turns Python ASTs into kernel axioms; a **pipeline** in `deppy/pipeline/` that stages the obligations; and a **cubical / HoTT** layer in `deppy/core/path_engine.py`, `deppy/core/path_compression.py`, `deppy/core/hott_equality.py`, `deppy/core/cubical_effects.py`, `deppy/core/type_checker.py` that gives equality its homotopy-type-theoretic structure.

---

## 2. Layer diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                         USER SURFACE                             │
│   @guarantee / @requires / @ensures / @verify                    │
│   compile_to_lean  •  check_equiv  •  ProofScript.verify         │
└──────────────────────────────┬───────────────────────────────────┘
                               │
┌──────────────────────────────▼───────────────────────────────────┐
│                     PIPELINE LAYER                               │
│   deppy/pipeline/*       staged obligation handling              │
│     safety_pipeline      ←  per-function safety verdict          │
│     auto_spec_obligations← inferred drafts                       │
│     abstract_interp      ← cheap early pruning                   │
│     batch_z3             ← batched Z3 discharge                  │
│     effect_pruning       ← drop read-only obligations            │
│     cache / recovery     ← incremental + fallback                │
└──────────────────────────────┬───────────────────────────────────┘
                               │
┌──────────────────────────────▼───────────────────────────────────┐
│                     PROOF LANGUAGE LAYER                         │
│   deppy/proofs/language.py   AST → axioms, Tactic DSL            │
│   deppy/proofs/pipeline.py   AxiomRegistry, ProofCertificate,    │
│                              ProofScript round-trip              │
│   deppy/proofs/sugar.py      @guarantee / Proof builder          │
│   deppy/proofs/tactics.py    ProofBuilder (imperative interface) │
│   deppy/proofs/sidecar.py    External-library sidecar specs      │
└──────────────────────────────┬───────────────────────────────────┘
                               │
┌──────────────────────────────▼───────────────────────────────────┐
│                   CUBICAL / HoTT LAYER                           │
│   deppy/core/path_engine.py  PathConstructor, CechDecomposer,    │
│                              FibrationVerifier, UnivalenceEngine │
│                              + 4 search strategies               │
│   deppy/core/path_compression.py  branch/loop compression        │
│   deppy/core/hott_equality.py   BehavioralEquivalenceAnalyzer    │
│                              + 12 real pattern matchers          │
│   deppy/core/cubical_effects.py  effect transport over paths     │
│   deppy/core/type_checker.py  bidirectional checker              │
│                              + real Kan composition              │
│   deppy/core/hott_equality.py  univalence engine                 │
│   deppy/hott/cubical.py      Interval re-export                  │
└──────────────────────────────┬───────────────────────────────────┘
                               │
┌──────────────────────────────▼───────────────────────────────────┐
│                       TRUSTED KERNEL                             │
│   deppy/core/kernel.py         ProofKernel, VerificationResult   │
│     proof terms: Refl / Sym / Trans / Cong / Ap / FunExt /       │
│                  ListInduction / NatInduction / Cases /          │
│                  TransportProof / PathComp / DuckPath / Fiber /  │
│                  CechGlue / Univalence / AxiomInvocation /       │
│                  Z3Proof / Structural / Rewrite / Ext            │
│   deppy/core/formal_ops.py     Op / OpCall / FormalAxiomEntry    │
│   deppy/core/types.py          SynType / SynTerm / PathType /    │
│                                PathAbs / PathApp / Transport /   │
│                                Comp / PiType / GlueType / ...    │
│   deppy/core/z3_bridge.py      Z3 context + encoding             │
└──────────────────────────────────────────────────────────────────┘
```

---

## 3. Trusted vs. untrusted

The **trusted computing base (TCB)** is exactly:

* `deppy/core/kernel.py` — `ProofKernel.verify` and every `_verify_*` method
* `deppy/core/formal_ops.py` — `FormalAxiomEntry`, `formal_eq`
* `deppy/core/types.py` — the syntactic representation (data only; no logic)

Everything else is untrusted helper code.  A soundness bug outside the TCB makes Deppy emit proofs the kernel rejects; a soundness bug **inside** the TCB makes Deppy emit proofs the kernel wrongly accepts.  Changes to the TCB deserve extreme care.

### Trust-level taxonomy (`TrustLevel`)

| Level | Meaning | Where it's issued |
|---|---|---|
| `KERNEL` | Every sub-proof went through kernel rules | Refl / Sym / Trans / Cong / PathAbs / PathApp / well-formedness |
| `Z3_VERIFIED` | Z3 returned `unsat` on the negation | `_verify_z3` on valid formulas |
| `STRUCTURAL_CHAIN` | Kernel checked the structure; at least one leaf is Structural | Trans with inferred middle, DuckPath with coverage gaps (no longer — now fails), Structural proof terms |
| `LLM_CHECKED` | LLM proposed, kernel verified structure | `@verify` when LLM backs a claim |
| `AXIOM_TRUSTED` | The claim routes through a registered axiom | `AxiomInvocation`, `_verify_axiom` |
| `EFFECT_ASSUMED` | Effect witness accepted | `EffectWitness` / weaker combiners |
| `UNTRUSTED` | Nothing was actually checked | Failure outputs, missing verifiers, empty modules |

**The correct soundness gate is `ProofCertificate.kernel_verified`**, which walks the proof tree and refuses the label if any leaf is `Structural`.  `success == True` alone is not a soundness gate — a proof whose only step is `Structural("trust me")` has `success == True`.

---

## 4. Cubical / HoTT layer in depth

Deppy implements a slice of cubical HoTT suited to real-world Python verification tasks.  The following is the state of each piece.

### 4.1 `deppy/core/types.py` — syntactic cubical types

* `PathType(base_type, left, right)` — a HoTT path `a =_A b`; treated as a 1-cell.
* `PathAbs(ivar, body)` — path abstraction `λ(i:I). body(i)`; verified by `_verify_path_abs` which substitutes `0` and `1` and checks well-formedness.  **Fully implemented.**
* `PathApp(path, arg)` — path application `p @ r`.  Verified by `_verify_path_app`.  **Fully implemented.**
* `Transport(type_family, path, base)` — cubical transport.  Verified by `_verify_transport` which calls the real `_type_family_consistent` check (Section 4.2).  **Fully implemented.**
* `Comp(type_, face, partial_term, base)` — Kan composition.  Type-synthesised by `_synth_comp` which evaluates the face formula, checks the partial section under an interval-extended context, and emits a compatibility obligation `u(0) = u₀` when the face is indeterminate.  **Fully implemented.**
* `IntervalType` — the interval `I` with endpoints `0`, `1`.
* `GlueType(base_type, face, equiv_type)` — glue type for univalence.  Verified but underused; richer uses via `UnivalenceEngine`.
* `PiType`, `SigmaType`, `RefinementType`, `UnionType`, `OptionalType`, `UniverseType`, `ProtocolType` — the ambient type grammar.

### 4.2 `deppy/core/kernel.py` — cubical verifiers

The kernel's `_type_family_consistent` (for transport) now performs five real checks:

1. **Kind** — rejects `Literal`, `Pair`, `Fst`, `Snd` as motives.
2. **Domain match** — a `Lam(param_type=A)` must have `A` compatible with the path's `base_type`.  Compatibility allows the PyObj top-type, numeric tower, and Union/Optional alternatives.
3. **Body shape** — the lambda body must not be a value literal; it must be a term that can evaluate to a `SynType`.
4. **Scope hygiene** — the body's free variables are the motive parameter plus what the outer context binds.
5. **Arity** — a curried `λx.λy.body` motive is rejected against a 1-dimensional path.

Tests: `deppy/tests/test_core.py` `test_transport_rejects_literal_motive`, `test_transport_rejects_motive_with_wrong_domain`, `test_transport_rejects_motive_with_value_literal_body`, `test_transport_rejects_escaping_free_variable`, `test_transport_rejects_curried_binary_motive`, `test_transport_accepts_well_formed_motive`, `test_transport_accepts_pyobj_motive_against_typed_path`.

Other cubical verifiers with honest behaviour:

* `_verify_fiber` — rejects non-exhaustive `Fiber` dispatch over a `UnionType`.  (Was: downgraded to STRUCTURAL; now: fails with code `E003e`.)
* `_verify_duck_path` — rejects a `DuckPath` with missing protocol methods.  (Was: downgraded; now: fails with code `E003f`.)
* `_verify_structural` — returns `STRUCTURAL_CHAIN` and carries an "unchecked by kernel" message.  Downstream gates must use `ProofCertificate.kernel_verified`.
* `_verify_unfold` without a sub-proof returns `UNTRUSTED` rather than silent STRUCTURAL_CHAIN.

### 4.3 `deppy/core/path_engine.py` — path-construction + proof search

* **`PathConstructor`** — refl, sym, transitivity (Kan composition), congruence (`ap`), duck-type path, function path.  Core primitives used throughout the HoTT layer.
* **`CechDecomposer`** — Čech-cohomology decomposition of branching functions.  Real implementation: extracts branches, verifies each locally, checks the cocycle condition.
* **`FibrationVerifier`** — isinstance-dispatch fibration.  Real implementation: extracts fibers, verifies per-fiber, combines.
* **`UnivalenceEngine`** — protocol-level equivalence.  `check_equivalence(A, B, protocol)` returns an `EquivalenceProof` wrapping a `PathAbs` + duck-type path.
* **`TransportEngine`** — wraps `PathConstructor` to move proofs along paths.
* **`HomotopyContext`** — one-stop bundle.  Holds the kernel, constructor, decomposer, verifier, engines.
* **`_ReflexivityStrategy`**, **`_SymmetryStrategy`**, **`_CongruenceStrategy`** — existing, real search strategies.
* **`_TransitivityStrategy`** — real: scans `kernel.formal_axiom_registry` for bridging axioms.
* **`_CechStrategy`** — real: recognises `IfThenElse` terms and dispatches to `CechDecomposer.verify_locally` + cocycle check.
* **`_FibrationStrategy`** — real: detects isinstance condition and dispatches to `FibrationVerifier.verify_per_fiber`.
* **`_DuckTypeStrategy`** — real: finds shared protocol methods between two `ProtocolType` contexts and runs `UnivalenceEngine.check_equivalence`.

Tests: `deppy/tests/test_cubical_expansions.py` `test_transitivity_strategy_uses_registered_axioms`, `test_cech_strategy_dispatches_on_if_then_else`, `test_fibration_strategy_only_fires_on_isinstance`, `test_duck_type_strategy_finds_shared_protocol_methods`.

### 4.4 `deppy/core/path_compression.py` — control-flow compression

Two compression angles, both now real:

* **Homotopy-equivalent branches** (`_branches_homotopy_equivalent`) — no longer a 70% variable-overlap heuristic.  Requires:
  (a) equal footprint arity (|read|, |written|),
  (b) pairwise AST kind match,
  (c) a concretely-constructible path via `_try_build_homotopy_path` (reflexivity or `PathConstructor.function_path` over shared names).
* **Loop-invariant preservation** (`_loop_preserves_invariant`) — no longer "loop variable unmodified".  Runs a real Hoare-triple check via Z3 when available (`_loop_invariant_by_z3`); falls back to a conservative rule: invariant preserved only if *no variable mentioned in the invariant* is written by the body.

Tests: `test_branches_homotopy_equivalent_requires_real_path`, `test_branches_homotopy_equivalent_rejects_mismatched_ast_kinds`, `test_loop_invariant_syntactic_fallback_detects_write`, `test_loop_invariant_preserved_when_invariant_untouched`.

### 4.5 `deppy/core/hott_equality.py` — equivalence patterns

`BehavioralEquivalenceAnalyzer._build_equivalence_patterns()` now returns **12 real pattern matchers** recognising:

| Pattern | Matches |
|---|---|
| `add-right-identity` | `x + 0 = x` |
| `add-left-identity` | `0 + x = x` |
| `mul-right-identity` | `x * 1 = x` |
| `mul-left-identity` | `1 * x = x` |
| `double-negation` | `-(-x) = x` |
| `double-logical-not` | `not not x = x` |
| `reverse-reverse` | `reversed(reversed(xs)) = xs` |
| `sort-idempotent` | `sorted(sorted(xs)) = sorted(xs)` |
| `add-commute` | `a + b = b + a` |
| `mul-commute` | `a * b = b * a` |
| `add-associate` | `(a + b) + c = a + (b + c)` |
| `mul-associate` | `(a * b) * c = a * (b * c)` |
| `recursive-vs-iterative` | same function computed two ways |

Each matcher is an AST inspector.  A successful match is a *claim* — the caller discharges the resulting `EquivalenceProof` through the kernel.

Tests: `test_equivalence_pattern_*`.

### 4.6 `deppy/core/cubical_effects.py` — effect transport

`CubicalEffectVerifier.transport_effect_proof(source, target, equivalence_path, claimed_effect)` constructs a real kernel `TransportProof` that:

1. Checks source/target analysed effects are each subsumed by `claimed_effect` (early fail with E-CE-SRC / E-CE-TGT).
2. Builds a `PathAbs` motive over the interval.
3. Wraps the user's equivalence path in `_PathProof`.
4. Wraps a base witness in `Structural` carrying the effect signature.
5. Submits to `kernel.verify` — the kernel's real `_verify_transport` runs.

Tests: `test_effect_transport_passes_when_signatures_match`, `test_effect_transport_rejects_source_with_extra_effects`.

### 4.7 `deppy/core/type_checker.py` — Kan composition

`_synth_comp` now:

* Recognises `φ ≡ 0` (no partial data → reduces to base).
* Recognises `φ ≡ 1` (face total → reduces to `u(1)`).
* For indeterminate `φ`, type-checks the partial section under an interval-extended context with the face hypothesis, then emits a compatibility obligation `u(0) = u₀` for downstream Z3/kernel discharge.

Tests: `test_synth_comp_phi_zero_reduces_to_base`, `test_synth_comp_emits_compatibility_obligation_when_face_indeterminate`.

---

## 5. Module-composition verifier

`deppy/core/module_composition.py` — `ModuleCechDecomposer` verifies patches with real checks replacing the former STRUCTURAL placeholders:

* `_verify_patch_interfaces` — fails if any public function has an unsuccessful verdict or any advertised function is missing from the verdict map.  Aggregate trust is the weakest per-function trust.
* `_verify_function_in_context` — computes a SHA256 digest of the function source, looks up `@guarantee` specs via `_deppy_spec` metadata, and discharges each through `kernel.verify` with a `Structural` witness.  Returns `UNTRUSTED` if no specs exist (honest gap signal).
* `_verify_compositions_in_patch` — rejects any `FUNCTION_CALL` dependency whose target has no recorded verdict.

Tests: `test_module_composition_interface_fails_on_unverified_function`.

---

## 6. Proof DSL

### 6.1 `deppy/proofs/language.py`

* AST → axioms via `function_to_axioms` / `class_to_axioms`.
* Tactic DSL: `T.refl / sym / trans / cong / unfold / axiom / z3 / transport / ext / simp / structural`.
* `T.path_intro(ivar, term)` — **real** cubical path abstraction.  Produces a `_PathProof` wrapping a `PathAbs` that the kernel verifies at `KERNEL` trust.
* Axiom grammar constants (`AXIOM_SUFFIX_DEF`, `_CASE`, `_INIT`, `_FOLD`, `_INDUCTION`, `_PROPERTY`, `_INHERITED`) are the single source of truth consumed by both emitters and citers.

### 6.2 `deppy/proofs/pipeline.py`

Five-stage pipeline:

1. `axiomize` — deep AST→axioms (multi-stmt, for-loop → fold, class + inheritance, @property).
2. `AxiomRegistry` — dedup, LHS-head index, syntactic conflict detection (documented as purely syntactic — see `AxiomRegistry.conflicts` docstring for limitations).
3. `Tactics` — extended surface (`cases`, `induction`, `first`, `repeat`, `simp_with`, `intro`).  `Tactics.induction` builds a real `ListInduction` kernel term via `pb.by_list_induction`.
4. `ProofTreeNode` — printable tactic tree with Lean-4 export.
5. `ProofCertificate` — kernel-checked receipt.  `.kernel_verified` returns True iff `success` AND no `structural` leaf in the tree.  `.content_hash` includes a `source_fingerprint` so stale proofs against updated code can't masquerade.  `ProofScript.verify(kernel)` re-runs a serialized proof (this is the operation that realises "check a third-party proof").

### 6.3 `deppy/proofs/sugar.py`

`@verify` now runs through `by_z3` first, falls back to `by_structural`.  With `raise_on_failure=True` it becomes a hard gate that raises `VerificationError`.

---

## 7. Pipeline layer

`deppy/pipeline/` is the orchestration layer — it takes user source, extracts obligations, dispatches to the right discharger, and aggregates verdicts.

Key honesty fixes you can rely on today:

* `verifier.py` — empty modules return `verified=False` with a warning, not silent pass.
* `incremental.py` — when no `verify_fn` is supplied, `_stub_verify` returns `fail`, not silent success.
* `safety_pipeline.py` — recovery paths (auto-spec failure, effect propagation failure) set `module_safe=False` and record notes instead of silently papering over.
* `safety_predicates.py`:
  * OVERFLOW requires `isinstance(a, int) and isinstance(b, int)` (not hardcoded `True`).
  * `TYPE_ERROR` on builtin calls narrows per-function: `len(x)` needs `__len__`, `int(x)` needs numeric-or-parseable, `sorted(x)` needs `__iter__`, etc.
  * `ATTRIBUTE_ERROR` on methods narrows per type: string methods require `isinstance(obj, str)`, list methods require `isinstance(obj, list)`, etc.
* `abstract_interp.py`:
  * `resolve_type_check` requires a bounded interval or a concrete type tag — having *any* interval is no longer enough.
  * `resolve_safe_access` for subscripts requires `0 <= idx.lo AND idx.hi < seq.size.lo`, not only nullability.
* `progress.py` — now counts succeeded vs failed separately; reports both.

---

## 8. Lean 4 export

`deppy/lean/compiler.py` — `compile_to_lean` emits Lean source *without* running Lean.  Trust labels:

| Label | Meaning |
|---|---|
| `LEAN_EXPORTED` | Source emitted; may have `sorry`; Lean NOT run |
| `LEAN_SYNTAX_COMPLETE` | No `sorry`, no raw `axiom`s; Lean NOT run |
| `LEAN_KERNEL_VERIFIED` | `cert.verify_with_lean()` succeeded |
| `LEAN_REJECTED` | `cert.verify_with_lean()` failed; see `lean_check_stderr` |
| `LEAN_UNAVAILABLE` | `lean` binary not on PATH |
| `ASSUMPTION_DEPENDENT` | Raw `axiom` declarations present |

The former `LEAN_VERIFIED` label (which was assigned based solely on `sorry_count == 0`) has been retired.  Users who want a real Lean-kernel gate must call `cert.verify_with_lean()` explicitly.

---

## 9. Equivalence engine

`deppy/equivalence.py` distinguishes proof from evidence:

* `equivalent is True` — only when a proof (Z3 or refl) discharges the claim.
* `equivalent is None` — unknown; check `confidence` for evidence strength.  Testing-based checks always return `None` (testing cannot prove ∀).
* `equivalent is False` — witnessed counterexample.

`EquivResult.likely_equivalent` is the property to use for "candidate equivalence" ranking; never gate soundness on it.

Spec-matching (two functions with the same `@guarantee` string) also returns `None` with a `spec_info` payload: spec equivalence does NOT imply code equivalence.

---

## 10. How a goal flows

```
user code  +  @guarantee("result >= 0")
    │
    ▼
pipeline.safety_pipeline.verify_module_safety(src)
    │
    ├─ auto-spec inference  →  drafted_specs
    ├─ effect propagation   →  propagation graph
    ├─ coverage analysis    →  obligation list
    ▼
for each function:
    ├─ SemanticSafetyWitness(target, precondition, discharges, ...)
    │      ▲
    │      └─ each discharge tries: axiom / z3 / structural / transport
    ▼
kernel.verify(ctx, goal, witness)
    │
    ▼
VerificationResult(success, trust_level, message, sub_results)
    │
    ▼
FunctionVerdict(name, is_safe, trust, counterexamples, ...)
    │
    ▼
SafetyVerdict(module_safe, aggregate_trust, functions, ...)
```

Parallel path for user-authored proofs (the cubical pipeline):

```
user code  +  tactic script
    │
    ▼
deppy.proofs.pipeline.prove_certificate(theorem, kernel, goal, tactic)
    │   (or ProofScript.verify / verify_proof_script for replayable JSON)
    │
    ▼
tactic.compile(ProofBuilder) → ProofTerm
    │
    ▼
kernel.verify(ctx, formal_goal, proof_term)
    │
    ▼
ProofCertificate(
    success, trust_level, kernel_verified, axioms_used,
    content_hash, lean_export, ...
)
```

---

## 11. Testing

```bash
python3 -m pytest deppy/tests/ deppy/lean/ -q
```

Current headline counts (subject to change as the test suite grows):

* 750 unit + integration tests pass (including the 20-test cubical-expansion suite added in this ARCHITECTURE iteration)
* 6 pre-existing failures in `test_runtime_safety.py` covering paths outside the recent changes

Use `python3 -m pytest --collect-only -q | tail -3` for the exact current count.

---

## 12. What's still a placeholder

A short running list — update when you fix one.

* `deppy.tactics` (top-level) — inert data structures only.  Use `deppy.proofs.language.T` / `Tactics` instead.
* `deppy.sidecar`, `deppy.concurrency`, `deppy.async_verify`, `deppy.classical`, `deppy.ghost`, `deppy.patching`, `deppy.separation`, `deppy.heap`, `deppy.homotopy` — metadata or re-export shims.  Real behaviour lives in the corresponding core/proofs submodules.
* `deppy.core.cubical_effects._construct_effect_proof` / `_construct_cech_decomposition` — still return `Structural` witnesses.  These are secondary to `transport_effect_proof` (which is real).
* `deppy.core.oop_verification._check_specification_compatibility` — the Liskov check handles trivial cases (equal specs, parent-true, child-false) and rejects otherwise as incompatible.  Full predicate-logic Liskov awaits a proper pre/post Z3 encoding.
* `_TransitivityStrategy` requires exact repr-equality on endpoints; no alpha renaming or unification.  Matches code-derived axioms well but doesn't chase arbitrary lemma bases.

---

## 13. Where to look when

| I want to… | Start here |
|---|---|
| Understand proof-term types | `deppy/core/kernel.py` §"Proof Terms" |
| Add a new tactic | `deppy/proofs/language.py`, `Tactics` class in `deppy/proofs/pipeline.py` |
| Add a new cubical primitive | `deppy/core/types.py`, then its verifier in `deppy/core/kernel.py` |
| Add a new equivalence pattern | `deppy/core/hott_equality.py`, `_build_equivalence_patterns` |
| Add a new pipeline stage | `deppy/pipeline/`, wire from `safety_pipeline.py` |
| Check if a trust level is sound | `kernel_verified` property + this document §3 |
| Round-trip a proof through JSON | `ProofScript.to_json` / `verify_proof_script` |
| Export to Lean | `compile_to_lean` then `cert.verify_with_lean()` |
