# THE HOLY GRAIL OF TRUSTWORTHY SOFTWARE IN THE AGE OF LLMs

## Algebraic-Geometric Dependent Type Theory with Controlled Oracles

---

# PILLAR 10: TYPE EXPANSION — FROM SPEC TO 50K LOC VIA SHEAF REFINEMENT

## The Thesis

> A natural language specification is a *degenerate global section* of the presheaf
> HybridTy over the trivial cover {∗}. Type expansion is the process of replacing
> this trivial cover with a *fine enough* Čech cover U = {Uᵢ} such that:
>
> 1. Each local section Ty(Uᵢ) is **atomic** — small enough to generate directly
> 2. The cocycle condition holds: H¹(U, HybridTy) = 0 — no gaps or contradictions
> 3. The glued global section Γ(U, HybridTy) **refines** the original spec
>
> The expansion process is itself typed: it lives in the oracle monad T_O,
> meaning every decomposition decision carries trust metadata and can be audited.

## 10.0  Why Type Expansion Is the Right Abstraction

Current LLM code generation: `prompt → code`. One shot, no structure, no verification.

What we want: `spec → typed decomposition → verified assembly`. But how do you get
the decomposition? **You let the type theory tell you.**

The Curry-Howard-Lambek correspondence says:
- **Σ-types** (dependent pairs) ARE module decompositions
- **Π-types** (dependent functions) ARE API contracts between modules  
- **Refinement types** ({x:T | φ(x)}) ARE specifications/invariants
- **Identity types** (Id_A(a,b)) ARE integration compatibility proofs
- **Universe types** (Type_i) ARE abstraction/genericity boundaries

So: **expanding a type IS planning a codebase**. No separate "planning" step needed —
the plan *is* the fully-expanded type, and its well-formedness *is* plan coherence.

## 10.1  The Expansion Calculus

### 10.1.1  Judgment Forms

We define a type expansion judgment:

```
Γ ⊢ T ↝ᵣ T'    (T expands to T' via rule r in context Γ)
```

where r ∈ {Σ-expand, Π-expand, Refine, Identify, Universe-lift}.

**Σ-expansion** (module decomposition):
```
Γ ⊢ T : Type_INTENT
oracle(T) ⊢ [A₁, ..., Aₙ] : ModuleDecomp(T)    (oracle proposes decomposition)
∀i. Γ ⊢ Aᵢ : Type                                (each component is well-typed)
∀i<j. Γ ⊢ restrict(Aᵢ, Aⱼ) compatible           (overlaps agree — sheaf condition)
─────────────────────────────────────────────────
Γ ⊢ T ↝_Σ Σ(x₁:A₁). Σ(x₂:A₂(x₁)). ... Σ(xₙ:Aₙ(x₁,...,xₙ₋₁)). ⊤
```

Note the *dependency chain*: each Aᵢ can depend on all prior xⱼ (j < i).
This captures: "the API gateway module depends on the auth module's interface."

The oracle call is in T_O: trust = LLM_JUDGED, and the compatibility check is
either Z3-decidable (structural) or oracle-checked (semantic), never trusted blindly.

**Π-expansion** (API discovery):
```
Γ ⊢ M : ModuleType
oracle(M) ⊢ [(p₁,r₁), ..., (pₖ,rₖ)] : APISpec(M)    (oracle proposes functions)
∀i. Γ, pᵢ : InputType_i ⊢ rᵢ : OutputType_i(pᵢ)       (dependent return types)
─────────────────────────────────────────────────────
Γ ⊢ M ↝_Π Π(x₁:I₁).O₁(x₁) × ... × Π(xₖ:Iₖ).Oₖ(xₖ)
```

**Refinement-expansion** (constraint discovery):
```
Γ ⊢ f : Π(x:A).B(x)
oracle(f) ⊢ [φ₁,...,φₘ] : Constraints(f)
classify(φᵢ) = (φᵢ_d, φᵢ_s)    (decidable part, semantic part)
Z3.check(⋀ φᵢ_d) = SAT          (constraints are consistent)
────────────────────────────────────────────────
Γ ⊢ f ↝_R {x:A | ⋀φᵢ_d(x) ∧ ⋀φᵢ_s(x)} → {y:B(x) | ⋀ψⱼ(y)}
```

**Identity-expansion** (interface compatibility):
```
Γ ⊢ Mᵢ : ModuleType,  Γ ⊢ Mⱼ : ModuleType
interface(Mᵢ) ∩ interface(Mⱼ) = {f₁,...,fₖ}    (shared API surface)
∀l. Γ ⊢ Mᵢ.fₗ =_A Mⱼ.fₗ                       (types agree on overlap)
──────────────────────────────────────────────
Γ ⊢ (Mᵢ, Mⱼ) ↝_Id  (Mᵢ, Mⱼ, Id_{API}(Mᵢ.f, Mⱼ.f))
```

This is precisely the **cocycle condition** of sheaf theory:
on the overlap Uᵢ ∩ Uⱼ, the local sections must agree.
Identity-expansion DISCOVERS these cocycle conditions.

**Universe-expansion** (genericity):
```
Γ ⊢ f : A → B
oracle detects: f should work for any T satisfying P(T)
──────────────────────────────────────
Γ ⊢ f ↝_U  Π(T : Type_i). P(T) → (T → B'(T))
```

### 10.1.2  Expansion Termination

**Atomicity criterion** — a type T is *atomic* (needs no further expansion) when:
```
atomic(T) ⟺  σ-width(T) ≤ 1           (at most one Σ-component)
            ∧ π-arity(T) ≤ 5           (at most 5 function params)
            ∧ refine-decidable(T) ≥ 0.9 (90%+ of refinements are Z3-checkable)
            ∧ LOC-estimate(T) ≤ 300     (would be ≤ 300 lines of code)
```

**Termination theorem** (informal):
> If the oracle is well-behaved (each call reduces complexity by a measurable amount)
> and the atomicity criterion is satisfiable, then expansion terminates in
> O(log(target_LOC / atomic_threshold)) Σ-expansion steps.

In practice: a 50K LOC project needs ~5-7 levels of Σ-nesting, each level
multiplying by 3-10 components. 50000/300 ≈ 167 atomic leaves.

### 10.1.3  H¹ as Expansion Completeness

At every expansion step, we compute:
```
H¹(U_current, HybridTy) = ker(δ¹) / im(δ⁰)
```

where U_current = {current leaves of the expansion tree}.

- **dim H¹ = 0**: expansion is complete and coherent. Ship it.
- **dim H¹ > 0**: each generator corresponds to either:
  - A **missing component** (a gap in the cover — need more Σ-expansion)
  - An **interface mismatch** (cocycle failure — need Identity-expansion)
  - A **constraint conflict** (incompatible refinements — need Refinement relaxation)

The expansion loop: `while H¹ > 0 or non-atomic leaves exist: expand`.

## 10.2  The Controlled Oracle Protocol

Every expansion step invokes the LLM oracle. But we NEVER trust it blindly.

### 10.2.1  Oracle Call Typing

Each oracle call is typed in the oracle monad:
```
oracle_Σ : NLSpec → T_O(List[ComponentSpec])
oracle_Π : ComponentSpec → T_O(List[FunctionSpec])  
oracle_R : FunctionSpec → T_O(List[Constraint])
oracle_Id : (ComponentSpec, ComponentSpec) → T_O(List[IdentityConstraint])
```

Every result carries `(value, trust=LLM_JUDGED, confidence, provenance)`.

### 10.2.2  Oracle Validation Protocol

After each oracle call, we run a **validation cascade**:

```
Level 1 (Structural — free, instant):
  - JSON schema check on oracle output
  - Dependency graph acyclicity check
  - Name collision check
  - LOC budget check (sum of components ≈ parent estimate)

Level 2 (Z3 — cheap, decidable):
  - Constraint consistency (¬(φ₁ ∧ ... ∧ φₙ) is UNSAT → consistent)
  - Type compatibility (interface types match across modules)
  - Coverage (union of component specs ⊇ parent spec keywords)

Level 3 (Cross-oracle — moderate cost):
  - Ask a DIFFERENT oracle (or same oracle, different temperature) to verify
  - Compare decompositions: if significantly different, flag for human review
  - Confidence calibration: oracle's self-reported confidence vs actual

Level 4 (Human — expensive, reserved):
  - If levels 1-3 all pass with high confidence, skip human
  - If any level fails or confidence < threshold, present to human
  - Human judgment promotes trust to HUMAN_VERIFIED
```

### 10.2.3  Oracle Memoization (the "Semantic Cache")

The oracle monad supports memoization:
```
memo_oracle(key, call) = 
  if cache.has(key) and cache.trust(key) ≥ threshold:
    return cache.get(key)    — T_O with cached=True
  else:
    result = call()
    cache.put(key, result)
    return result
```

This is crucial for large-scale: a 50K LOC project might need 500+ oracle calls.
Memoization cuts this to ~100 unique calls (similar components share structure).

## 10.3  From Expanded Types to Code Generation Plan

### 10.3.1  The Curry-Howard-Lambek Direction

Given a fully expanded type tree T_expanded with H¹ = 0, we extract:

```
Σ-nodes at depth d  →  directories at nesting level d
Σ-leaves           →  Python modules (.py files)
Π-types in a leaf  →  functions/classes in that module
Refinements        →  docstrings + test cases + runtime checks
Identity types     →  integration tests between modules
```

This is a *functor* from the category of expanded types to the category of project layouts:
```
Layout : ExpType → ProjectStructure
Layout(Σ(x:A).B(x)) = Directory(Layout(A), Layout(B))
Layout(Π(x:A).B(x)) = Function(signature=A, body_spec=B)
Layout({x:A | φ})    = (Layout(A), TestCase(φ))
Layout(Id_A(a,b))    = IntegrationTest(a, b)
```

### 10.3.2  Generation Order = Σ-Elimination Order

The dependency structure of the Σ-type determines generation order:
```
Σ(x₁:A₁). Σ(x₂:A₂(x₁)). Σ(x₃:A₃(x₁,x₂)). ⊤
```
Generate A₁ first (no dependencies), then A₂ (depends on x₁), then A₃.
Within each level, independent components can be generated IN PARALLEL.

This gives us a **phase structure**:
```
Phase 1: {A₁}                    (foundation modules, no deps)
  Gate 1: structural + interface check
Phase 2: {A₂(x₁)}               (depends on phase 1)
  Gate 2: structural + semantic + integration
Phase 3: {A₃(x₁,x₂)}           (depends on phases 1+2)
  Gate 3: full verification + H¹ recheck
```

### 10.3.3  Verification Gates as Sheaf Conditions

Each gate checks the **local sheaf condition** for the newly generated sections:
```
Gate(phase_k):
  ∀ new artifact a ∈ phase_k:
    ∀ dependency d ∈ deps(a):
      restrict(section(a), overlap(a,d)) = restrict(section(d), overlap(a,d))
```

In code: "the API that module A calls on module D matches what module D exports."

## 10.4  CEGAR on the Plan Itself

When verification fails, we don't just regenerate code — we **refine the type**.

### 10.4.1  Plan-Level CEGAR Loop

```
while True:
    plan = compile(expand(spec))
    result = execute(plan)
    if result.all_verified:
        return result
    
    # Counterexample: the verification failure
    cex = result.first_failure
    
    # Refinement: modify the TYPE, not just the code
    if cex.type == STRUCTURAL:
        # Add the violated constraint as a refinement type
        plan.add_refinement(cex.artifact, cex.constraint)
    elif cex.type == SEMANTIC:
        # Narrow the semantic predicate with the counterexample
        plan.narrow_semantic(cex.artifact, cex.counterexample)
    elif cex.type == INTEGRATION:
        # Add identity constraint between the conflicting modules  
        plan.add_identity(cex.module_a, cex.module_b, cex.mismatch)
    elif cex.type == H1_NONZERO:
        # An H¹ generator = a missing piece. Add a new Σ-component.
        plan.add_sigma_component(cex.obstruction)
    
    # Re-expand and re-plan (only the affected subtree)
    plan = recompile_incremental(plan, affected_nodes)
```

### 10.4.2  Incremental Re-Expansion

Key efficiency: when CEGAR refines the plan, we don't re-expand everything.
We use the **sheaf locality** property: a change at node N only affects:
- N itself
- N's children (subtree)
- N's siblings that share an interface with N (cocycle neighbors)

Everything else is unchanged. This makes plan refinement O(affected) not O(total).

## 10.5  Implementation Files

### File 1: `type_expansion/expander.py` (~2500 lines)
- [ ] `ExpansionRule` ABC + 5 concrete rules (Σ, Π, Refine, Identity, Universe)
- [ ] `TypeNode` — node in the expansion tree with full sheaf metadata
- [ ] `ExpansionContext` — tracks H¹, nodes, expansion history
- [ ] `TypeExpander` — main engine: NL spec → fully expanded type tree
- [ ] `PatternBasedExpander` — heuristic fallback (no oracle needed)
- [ ] Oracle prompts with anti-hallucination validation cascade

### File 2: `type_expansion/codegen_plan.py` (~2000 lines)
- [ ] `CodeArtifact` — single code artifact with type provenance
- [ ] `CodeGenPlan` — DAG of artifacts with phases and verification gates
- [ ] `PlanCompiler` — Layout functor: expanded type → plan (Curry-Howard direction)
- [ ] `PromptGenerator` — type-structured prompts for each artifact
- [ ] `PlanExecutor` — phased execution with gate checking

### File 3: `type_expansion/large_scale.py` (~2000 lines)
- [ ] `LargeScaleGenerator` — end-to-end: NL spec → certified 50K LOC codebase
- [ ] `ProjectArchetype` — 8 archetypes with Σ-skeletons
- [ ] `IncrementalExpander` — expand-one-level-then-generate strategy
- [ ] `SpecAnalyzer` — complexity estimation and archetype detection
- [ ] Plan-level CEGAR loop with incremental re-expansion

### File 4: `type_expansion/demo.py` (~500 lines)
- [ ] End-to-end demo: "write me a financial trading app"
- [ ] Shows: spec → expansion tree → plan → (mock) generation → H¹ = 0
- [ ] Prints: ASCII tree, plan phases, LOC breakdown, trust certificate

### File 5: Tests `tests/test_hybrid/test_type_expansion.py` (~800 lines)
- [ ] Test expansion rules fire correctly
- [ ] Test H¹ computation detects gaps
- [ ] Test plan compilation preserves Σ-structure
- [ ] Test CEGAR loop converges
- [ ] Test archetype detection
- [ ] Test incremental re-expansion locality
- [ ] Integration: full pipeline on 3 example specs

## 10.6  The Payoff — What This Enables

With type expansion, the `deppy` command:
```bash
deppy "write me a financial trading app with risk management, 
       real-time market data, backtesting, and regulatory compliance"
```

produces NOT a single prompt to an LLM, but:

1. **Expansion tree** (17 modules, 89 functions, 43 refinements, 12 identity constraints)
2. **Code generation plan** (6 phases, 167 atomic artifacts, 5 verification gates)
3. **Parallel generation** (up to 10 artifacts simultaneously)
4. **Verified assembly** (H¹ = 0 certified, trust = PROPERTY_CHECKED)
5. **Trust certificate** (machine-readable, with full provenance chain)

Total: ~50K LOC, every module type-checked against its spec, every interface
verified compatible, every constraint either Z3-proven or oracle-judged with
confidence ≥ 0.9, all packaged with a certificate that says exactly what was
proven and what remains as oracle trust.

---

## 0. WHY EXISTING APPROACHES FAIL

**Static analysis** (Pylint, MyPy, Pyright): checks syntactic rules. Cannot express "this function returns a sorted list" or "this LLM output is grounded in the cited paper." Trust ceiling: SYNTACTIC.

**Testing** (pytest, property-based): checks finite samples. Cannot prove universal properties. An LLM can generate code that passes 1000 tests and fails on input 1001. Trust ceiling: RUNTIME_SAMPLED.

**Formal verification** (Dafny, F*, Lean): checks proofs. But requires the human to write the spec AND the proof. LLM-generated code has no spec — it has a *prompt*, which is natural language. Trust ceiling: LIMITED_BY_SPEC_AVAILABILITY.

**LLM-as-judge** (LMSYS, AlpacaEval): asks another LLM. But the judge can hallucinate too. There's no ground truth, no certificate, no way to know if the judgment is correct. Trust ceiling: LLM_JUDGED (circular).

**The gap**: No existing system can take a natural-language intent, an LLM-generated artifact, and produce a *machine-checked certificate* of correctness — or a *precise, localizable* explanation of what's wrong.

**This system closes the gap** by treating the problem as what it mathematically is: a *sheaf-cohomological obstruction* in a *dependent type theory* where LLMs are *controlled oracles* in a *trust topos*.

---

## I. THE MATHEMATICAL SUBSTRATE (not metaphors — executable math)

### I.A Programs as Sheaves over Sites

A Python program P defines a **site category** Site(P):

```
Objects:    observation points in P
            {arg_boundary, branch_guard, call_result, return_site, 
             error_handler, loop_entry, yield_point, attribute_access}

Morphisms:  data-flow edges with contravariant refinement projection
            s₁ →^f s₂  means data flows from s₁ to s₂,
            and f* : Ty(s₂) → Ty(s₁) is the pullback (type weakening)

Topology:   J = covering families
            {body sites} covers function; {module sites} covers module
            A family {sᵢ → s} is covering if the union of observations
            at the sᵢ determines the observation at s
```

A **type assignment** is a presheaf:

```
Ty : Site(P)^op → RefinementLattice
     s           ↦ {the refined type observable at s}
     (s₁ →^f s₂) ↦ f* : Ty(s₂) → Ty(s₁)   (restriction = weakening)
```

The presheaf Ty is a **sheaf** iff local sections that agree on overlaps glue uniquely. When they don't:

```
H¹(U, Ty) = ker(δ¹) / im(δ⁰)

where the Čech complex is:
  C⁰ = ∏ᵢ Ty(Uᵢ)                    — local type at each cover element
  C¹ = ∏ᵢⱼ Ty(Uᵢ ∩ Uⱼ)              — type at each overlap
  C² = ∏ᵢⱼₖ Ty(Uᵢ ∩ Uⱼ ∩ Uₖ)        — type at each triple overlap

  δ⁰(σ)ᵢⱼ = σⱼ|_{Uᵢ∩Uⱼ} - σᵢ|_{Uᵢ∩Uⱼ}    — disagreement on overlaps
  δ¹(τ)ᵢⱼₖ = τⱼₖ - τᵢₖ + τᵢⱼ                — cocycle condition
```

**Each independent generator of H¹ is an independent bug.** deppy already computes this over GF(2)-valued presheaves. The existing system achieves 87% F1 on 300 real programs.

### I.B The Product Site: Adding Layers of Trust

For the holy grail, we need types that track not just "what type does this value have" but "what type does this value have *at each layer of verification*." We define the **product site**:

```
ProductSite = Site(P) × Layer

Layer = (Obj = {INTENT, STRUCTURAL, SEMANTIC, PROOF, CODE},
         Mor = {10 restriction maps between layers})
```

The layer morphisms are the crucial innovation — they are **restriction maps** that translate between levels of formality:

```
ι₁ : INTENT → STRUCTURAL      "returns sorted list" → ∀i. a[i]≤a[i+1]
     (NL parsing: extract decidable claims from natural language)

ι₂ : INTENT → SEMANTIC        "returns sorted list" → O("is this sorted?")
     (NL parsing: extract undecidable claims as oracle queries)

σ₁ : STRUCTURAL → PROOF       ∀i. a[i]≤a[i+1] → Lean: ∀ i, a.get i ≤ a.get (i+1)
     (Z3 formula → Lean decidable proposition)

σ₂ : SEMANTIC → PROOF         O("is this sorted?") → Lean: Axiom trust_sorted
     (oracle judgment → Lean axiom with trust annotation)

π  : PROOF → CODE             Lean theorem → Python runtime assertion
     (proof extraction → executable check)

κ₁ : CODE → STRUCTURAL        Python AST → inferred Z3 constraints
     (abstract interpretation / type inference)

κ₂ : CODE → SEMANTIC          Python execution → LLM evaluation
     (run code, ask oracle about behavior)

κ₃ : CODE → INTENT            Python code → NL summary
     (LLM summarization — the reverse direction)

χ  : STRUCTURAL → CODE        Z3 model → test case / synthesized code
     (constraint solving → executable)

ω  : INTENT → CODE            NL spec → synthesized Python
     (LLM code generation — hole filling)
```

A **hybrid type** is a global section of the product presheaf:

```
HybridTy : (Site(P) × Layer)^op → RefinementLattice × TrustLattice

HybridTy(s, ℓ) = (refinement at site s in layer ℓ, trust level of that refinement)
```

### I.C The Cocycle Condition: What "No Gap" Means

For every triple of layers (ℓ₁, ℓ₂, ℓ₃), the transition maps must compose:

```
g_{ℓ₁ℓ₂} ∘ g_{ℓ₂ℓ₃} = g_{ℓ₁ℓ₃}    (cocycle condition)
```

When this fails, we have a **nontrivial cocycle** — an element of H¹(Layer, HybridTy) that represents a specific inconsistency:

```
INTENT →ι₁ STRUCTURAL →σ₁ PROOF  ≠  INTENT →(σ₁∘ι₁) PROOF
  ↕ means: formalizing NL via Z3 then Lean ≠ formalizing NL directly in Lean
  ↕ diagnosis: the Z3 encoding lost information, or the Lean encoding is too weak

CODE →κ₁ STRUCTURAL →σ₁ PROOF  ≠  CODE →(σ₁∘κ₁) PROOF
  ↕ means: analyzing code for Z3 then proving ≠ directly proving code properties
  ↕ diagnosis: the Z3 abstraction is incomplete

INTENT →ω CODE →κ₃ INTENT  ≠  id
  ↕ means: generating code from NL then summarizing ≠ original NL
  ↕ diagnosis: the LLM changed the intent during generation (HALLUCINATION!)
```

**The round-trip cocycle INTENT →ω CODE →κ₃ INTENT ≠ id is precisely hallucination.** The LLM was asked to implement X, produced code that does Y, and when summarized, the code says Y ≠ X. This is not a vague "the code doesn't look right" — it's a nonzero cohomology class with a specific obstruction.

### I.D JSON as Semi-Structured Refinement Lattice

JSON is the universal interchange format for LLM inputs/outputs. A JSON value is a term in a free algebra:

```
JSON ::= null | bool | number | string | [JSON, ...] | {string: JSON, ...}
```

A **JSON refinement type** is:

```
{v : JSON | schema(v) ∧ φ_d(v) ∧ φ_s(v)}

where:
  schema(v)  = JSON Schema validation (decidable, fast)
  φ_d(v)     = structural predicates on values (Z3-checkable)
               e.g., v.length ≥ 3, v.score ∈ [0,1], v.items ⊆ known_set
  φ_s(v)     = semantic predicates (oracle-judgeable)
               e.g., v.summary is_accurate_for(v.source), v.code is_correct_for(v.spec)
```

This is the refinement type from comet_verified.py, now embedded in the full hybrid type theory. Every LLM API call has a JSON refinement type:

```python
# The LLM call
response = llm.complete(prompt, schema=OutputSchema)

# Its hybrid type:
# Π(prompt : NLSpec). {v : OutputSchema | φ_d(v, prompt) ∧ φ_s(v, prompt)}
# 
# The return type DEPENDS on the prompt (Π-type!)
# The structural part is schema validation + decidable constraints
# The semantic part is "does the response actually answer the prompt correctly"
```

### I.E Descent: Equivalence as Isomorphism Sheaf Triviality

Two implementations f, g of the same spec are equivalent iff:

```
H¹(Site(P), Iso(HybridTy_f, HybridTy_g)) = 0
```

The isomorphism sheaf Iso(F, G) at site s is the set of local isomorphisms between F(s) and G(s). If these local isomorphisms don't glue (H¹ ≠ 0), the programs differ in a way that's observable at overlapping sites.

For an LLM-generated program g and a spec f: g is correct iff H¹(Iso) = 0. Each nonzero element of H¹(Iso) is a specific site where g deviates from f.

### I.F Mayer-Vietoris: Incremental Re-verification

When code changes (e.g., LLM re-generates one function), decompose the cover:

```
U = U_changed ∪ U_unchanged

→^δ H⁰(U_changed ∩ U_unchanged) →^δ H¹(U) → H¹(U_changed) ⊕ H¹(U_unchanged) → ...
```

Since U_unchanged was already verified (H¹(U_unchanged) = 0), we only need:
1. Re-verify U_changed (H¹(U_changed))
2. Check the boundary (H⁰(U_changed ∩ U_unchanged) → H¹(U))

The connecting homomorphism δ is the "boundary bug propagation" — a bug at the interface between changed and unchanged code.

---

## II. THE CONTROLLED ORACLE: LLMs IN THE TYPE THEORY

### II.A The Oracle Interface

An oracle is a typed function:

```
O : Π(φ : Prop). T_O(Judgment(φ))

where:
  Judgment(φ) = HOLDS | FAILS(counterexample) | UNKNOWN
  T_O(A) = A × TrustLevel × Confidence × ProvenanceChain
```

The oracle is **controlled** — it can only answer queries of the form "does φ hold?" where φ is a proposition in the hybrid type theory. It cannot:
- Generate arbitrary code (only fill typed holes)
- Make arbitrary claims (only judge typed propositions)
- Modify trust levels (only the system promotes/demotes based on evidence)

### II.B The Oracle Monad T_O

```
T_O(A) = A × TrustLevel × Confidence × Provenance

return : A → T_O(A)
return(a) = (a, LEAN_VERIFIED, 1.0, [Axiom])

bind : T_O(A) → (A → T_O(B)) → T_O(B)
bind((a, t₁, c₁, p₁), f) = 
  let (b, t₂, c₂, p₂) = f(a) in
  (b, min(t₁, t₂), c₁ × c₂, p₁ ++ p₂)
```

**Weakest-link trust**: composed judgments have the trust level of the weakest component.

**Multiplicative confidence**: if oracle A has 90% confidence and oracle B has 90% confidence, the composed judgment has 81% confidence (assuming independence).

**Provenance concatenation**: the full derivation chain is recorded for auditability.

The monad laws hold:
```
bind(return(a), f) = f(a)              — left identity
bind(m, return)    = m                  — right identity
bind(bind(m, f), g) = bind(m, λa. bind(f(a), g))  — associativity
```

### II.C The Decidability Stratification

Every predicate φ in the hybrid type theory is classified:

```
φ(x) = φ_d(x) ∧ φ_s(x)

φ_d ∈ Dec:     Z3 handles it. Sound AND complete for QF_LIA/QF_LRA/QF_BV.
               Trust level: Z3_PROVEN. Promotable to LEAN_VERIFIED.
               Examples: x > 0, len(arr) ≥ 3, arr[i] ≤ arr[i+1]

φ_s ∈ Oracle:  LLM handles it. Sound? Sometimes. Complete? Never.
               Trust level: LLM_JUDGED. Promotable if Lean-proved.
               Examples: "code is correct", "summary is accurate", "no hallucinations"
```

The **decidability classifier** maps NL predicates to this stratification:
- "at least 3 elements" → Dec: `z3.IntVal(len) >= 3`
- "sorted in ascending order" → Dec: `∀i. z3.Select(arr, i) <= z3.Select(arr, i+1)`
- "correctly implements binary search" → Oracle: prompt + rubric
- "grounded in the cited paper" → Oracle: prompt + citation check

### II.D The Trust Topos Sh(TrustSite, J_trust)

```
TrustSite objects (ordered):
  CONTRADICTED < UNTRUSTED < ASSUMED < LLM_JUDGED < RUNTIME_CHECKED < Z3_PROVEN < LEAN_VERIFIED

Topology:
  {LEAN_VERIFIED} covers every level (Lean is the final arbiter)
  {Z3_PROVEN, RUNTIME_CHECKED} covers LLM_JUDGED (Z3 + tests can confirm LLM)
  {LLM_JUDGED₁, LLM_JUDGED₂} covers LLM_JUDGED if oracles agree (consensus)
```

Promotion (restriction to higher level):
```
promote : TrustLevel × Evidence → TrustLevel
promote(LLM_JUDGED, z3_certificate) = Z3_PROVEN
promote(Z3_PROVEN, lean_proof)      = LEAN_VERIFIED
promote(UNTRUSTED, llm_judgment)    = LLM_JUDGED
promote(_, contradiction)           = CONTRADICTED
```

### II.E Anti-Hallucination as Type Inhabitation Failure

Given LLM output v and required hybrid type T:

```
v : T ⟺ 
  (v : T.base)                      — base type check (Python type)
  ∧ T.structural.φ_d(v) = ⊤         — Z3 says YES (decidable, certain)
  ∧ T.semantic.O(φ_s(v)) = ⊤        — Oracle says YES (judged, uncertain)
  ∧ T.proof ⊢ v satisfies spec      — Lean confirms (if available)
  ∧ T.code(v) agrees with T.intent  — round-trip coherence (H¹ = 0)
```

Hallucination taxonomy:
```
STRUCTURAL_HALLUCINATION:
  v fails φ_d(v) — definitive, no oracle needed
  Example: LLM says "use torch.nn.TransformerEncoder" but misspells as "TransfomerEncoder"
  Detection: API registry lookup, Z3 type check
  Trust impact: CONTRADICTED

SEMANTIC_HALLUCINATION:
  v fails O(φ_s(v)) — oracle-judged, confidence-weighted
  Example: LLM says "this sorts the list" but the code reverses it
  Detection: oracle prompt + rubric + test execution
  Trust impact: LLM_JUDGED → CONTRADICTED if confidence > threshold

FABRICATION:
  v references non-existent entities (APIs, papers, facts)
  Example: LLM cites "Smith et al., 2024, NeurIPS" — paper doesn't exist
  Detection: registry lookup, DOI/arXiv verification
  Trust impact: CONTRADICTED

INCONSISTENCY (= nontrivial cocycle):
  v contradicts earlier verified assertions
  Example: function docstring says O(n log n) but code is O(n²)
  Detection: H¹(Layer, HybridTy) ≠ 0
  Trust impact: CONTRADICTED for the inconsistent layer pair

DRIFT:
  v was correct but the spec changed (stale section in the presheaf)
  Example: API was updated, old code no longer valid
  Detection: DriftMonitor checks staleness of layer sections
  Trust impact: UNTRUSTED (needs re-verification)
```

### II.F Oracle Caching: The Token-Saving Optimization

```
cache_key = (predicate_name, content_hash(value))

Invariant: if content_hash(v₁) = content_hash(v₂), then O(φ(v₁)) = O(φ(v₂))
           (same content → same oracle judgment)

Algorithm:
  check_semantic(predicate, value):
    key = (predicate.name, hash(value))
    if key in cache and cache[key].age < max_age:
      return cache[key]  # HIT: no LLM call, saves $$$
    result = oracle.query(predicate, value)  # MISS: call LLM
    cache[key] = result
    return result
```

For incremental development: if you change one function, only that function's content hash changes. All other oracle judgments are cached. This turns O(n) LLM calls into O(1) for unchanged code.

---

## III. THE VERIFIED ARTIFACT: Σ-TYPE = CODE × PROOF

Every output of the system is a dependent pair:

```
VerifiedArtifact = Σ(code : Python). Σ(proof : Certificate). 
                   (code_satisfies_spec(code, spec) ∧ trust_level(proof) ≥ threshold)
```

The certificate records:
- Which properties are Z3_PROVEN (decidable, certain)
- Which properties are LLM_JUDGED (semantic, confident)  
- Which properties are LEAN_VERIFIED (machine-checked, absolute)
- Which properties are UNCHECKED (not yet verified)
- The trust level: min across all properties (weakest link)
- The provenance: full derivation chain from intent to code
- The cohomology: H¹(ProductSite, HybridTy) — should be 0

**The certificate is the second projection of the Σ-type.** You can always extract it, inspect it, and decide whether to trust the code.

---

## IV. THE SURFACE LANGUAGE: HALF CODE, HALF NL

```python
from deppy.hybrid import spec, hole, guarantee, assume, check, given

@guarantee("returns the k closest points to origin, sorted by distance")
def k_closest(points: list[tuple[float, float]], k: int) -> list[tuple[float, float]]:
    assume("k > 0 and k <= len(points)")          # → Z3: k > 0 ∧ k ≤ len(points)
    
    dists = hole("compute Euclidean distance for each point")   # → synthesis + verification
    
    import heapq
    result = heapq.nsmallest(k, points, key=lambda p: dists[points.index(p)])
    
    check("result has exactly k points")           # → Z3: len(result) = k
    check("all points in result are from input")   # → Z3: result ⊆ points  
    check("no closer point was excluded")          # → Oracle: optimality
    
    return result
```

After compilation:
```
STRUCTURAL (Z3_PROVEN):
  ✓ k > 0 ∧ k ≤ len(points)         (from assume)
  ✓ len(result) = k                   (from check)
  ✓ result ⊆ points                   (from check)

SEMANTIC (LLM_JUDGED, conf 0.92):
  ✓ "k closest to origin"             (from @guarantee)
  ✓ "sorted by distance"              (from @guarantee)
  ✓ "no closer point excluded"        (from check — oracle since optimality is undecidable in general)

HOLE FILLING:
  "compute Euclidean distance" → [math.sqrt(p[0]**2 + p[1]**2) for p in points]
  Verified: structural ✓, semantic ✓, 3 test cases ✓

LEAN:
  theorem k_closest_length : ∀ pts k, (k_closest pts k).length = k          → LEAN_VERIFIED
  theorem k_closest_subset : ∀ pts k p, p ∈ k_closest pts k → p ∈ pts      → LEAN_VERIFIED
  theorem k_closest_optimal : ∀ pts k p q, p ∈ result → q ∉ result → ...   → LLM_JUDGED (sorry-free proof attempted)

TRUST: min(Z3_PROVEN, LLM_JUDGED, LEAN_VERIFIED) = LLM_JUDGED
H¹(ProductSite, HybridTy) = 0  ← no intent-implementation gap
```

---

## V. IMPLEMENTATION: 10 PILLARS (~90K LOC)

### Pillar 1: Core Type System (`src/deppy/hybrid/core/`) — ~14K lines

| File | Lines | Status | Purpose |
|------|-------|--------|---------|
| `types.py` | 2500 | 🔄 | Product presheaf HybridTy, Π/Σ/refinement/identity types, oracle monad |
| `trust.py` | 1500 | ✅ | Trust topos Sh(TrustSite, J_trust) |
| `provenance.py` | 1300 | ✅ | Derivation category, hallucination tracing |
| `checker.py` | 2500 | ✅ | Bidirectional type checking, SemanticCheckCache |
| `contracts.py` | 2300 | ✅ | Dependent contracts Π-type, CEGAR, quality lattice |
| `intent_bridge.py` | 1500 | 🔄 | H¹(Layer) computation, cocycle checking, drift |
| `algebraic_geometry.py` | 2000 | 📋 | Pure AG: CechComplex, CechCohomology, MayerVietoris, DescentDatum, FiberedCategory |
| `oracle_theory.py` | 1500 | 📋 | ControlledOracle, OracleMonad laws, DecidabilityClassifier, HallucinationTheory |

### Pillar 1.5: Mixed-Mode Surface Language (`src/deppy/hybrid/mixed_mode/`) — ~7K lines

| File | Lines | Status | Purpose |
|------|-------|--------|---------|
| `syntax.py` | 1500 | ✅ | hole/spec/guarantee/assume/check surface forms |
| `parser.py` | 2000 | ✅ | AST + NL fragment extraction + type context |
| `compiler.py` | 2000 | 🔄 | 7-phase compilation pipeline |
| `hole_synthesizer.py` | 800 | 📋 | Pattern library + LLM synthesis + CEGAR |
| `incremental.py` | 500 | 📋 | Incremental compilation with caching |

### Pillar 2: Python → Lean Translation (`src/deppy/hybrid/lean_translation/`) — ~10K lines

| File | Lines | Purpose |
|------|-------|---------|
| `python_model.py` | 2000 | PyValue/PyExpr/PyStmt AST, operational semantics |
| `lean_emitter.py` | 2500 | Full Lean 4 code generation, pretty-printing |
| `type_translation.py` | 1500 | HybridType → Lean proposition |
| `semantics_bridge.py` | 1500 | deppy sheaf semantics → Lean model |
| `roundtrip_checker.py` | 1000 | Property-based translation fidelity |
| `lean_project_manager.py` | 1000 | lakefile management, build, error mapping |
| `incremental_translator.py` | 500 | Cache + delta translation |

### Pillar 3: NL → Hybrid Spec (`src/deppy/hybrid/nl_spec/`) — ~6K lines

| File | Lines | Purpose |
|------|-------|---------|
| `nl_parser.py` | 1500 | Parse NL → HybridSpec (docstrings, claims, issues) |
| `decidability_classifier.py` | 1000 | Classify φ into Dec vs Oracle |
| `z3_compiler.py` | 1200 | Structural NL → Z3 constraints |
| `llm_compiler.py` | 1000 | Semantic NL → oracle judge prompts |
| `lean_compiler.py` | 800 | HybridSpec → Lean propositions |
| `drift_detector.py` | 500 | Theory/docs/code drift as H¹ ≠ 0 |

### Pillar 4: Anti-Hallucination Type Checker (`src/deppy/hybrid/anti_hallucination/`) — ~7K lines

| File | Lines | Purpose |
|------|-------|---------|
| `artifact_types.py` | 1200 | Hybrid types for Code/Text/Data/Proof artifacts |
| `checker.py` | 2000 | 4-phase: Structural → Consistency → Semantic → Lean |
| `detectors.py` | 2000 | API/Citation/Numeric/Logic hallucination detectors |
| `report.py` | 1000 | HallucinationReport + SARIF export |
| `registry.py` | 800 | Known API + fact registries |

### Pillar 5: Z3 + LLM → Lean Discharge (`src/deppy/hybrid/discharge/`) — ~6K lines

| File | Lines | Purpose |
|------|-------|---------|
| `cascade.py` | 1500 | 5-stage: Trivial → Z3 → LLM → Lean → Residual |
| `z3_to_lean.py` | 1500 | Z3 proof trees → Lean tactics (omega/decide/simp) |
| `llm_prover.py` | 1200 | LLM-as-theorem-prover + CEGAR repair |
| `lean_interface.py` | 1000 | Lean 4 REPL, proof checking, lemma search |
| `proof_certificate.py` | 800 | Portable certificates, persistent storage |

### Pillar 6: Pipeline (`src/deppy/hybrid/pipeline/`) — ~5K lines

| File | Lines | Purpose |
|------|-------|---------|
| `stages.py` | 1500 | 8 pipeline stages with dependent contracts |
| `orchestrator.py` | 1200 | Contract-enforced orchestration |
| `gates.py` | 800 | Verification gates |
| `manifest.py` | 500 | Audit trail |
| `cli.py` | 500 | `deppy hybrid {verify,translate,spec,check,pipeline}` |
| `config.py` | 500 | Configuration |

### Pillar 7: Theory Library (`src/deppy/hybrid/theory_library/`) — ~6K lines

| File | Lines | Purpose |
|------|-------|---------|
| `base.py` | 800 | HybridTheoryPack base + registry |
| `stdlib.py` | 1200 | Python stdlib types + axioms |
| `numpy_theory.py` | 1000 | NumPy shape tracking |
| `torch_theory.py` | 1000 | PyTorch tensor types |
| `pandas_theory.py` | 800 | DataFrame types |
| `testing_theory.py` | 600 | pytest semantics |
| `llm_theory.py` | 600 | OpenAI/Anthropic API types |

### Pillar 8: Lean Formalizations (`lean_proofs/DeppyProofs/Hybrid/`) — ~15K lines

| File | Lines | Purpose |
|------|-------|---------|
| `PythonModel.lean` | 2000 | Python operational semantics |
| `HybridType.lean` | 2000 | Product presheaf formalization |
| `OracleMonad.lean` | 1500 | T_O monad laws, trust propagation |
| `TrustTopos.lean` | 1500 | Trust topos, promotion/demotion |
| `TypeTranslation.lean` | 1500 | Soundness of type translation |
| `RefinementSoundness.lean` | 1500 | Soundness of refinement checking |
| `HybridSpec.lean` | 1000 | NL spec formalization |
| `AntiHallucination.lean` | 1000 | Hallucination-free predicate |
| `DischargeVerification.lean` | 1000 | Certificate checking |
| `MixedMode.lean` | 1000 | Mixed-mode compilation soundness |

### Pillar 9: Benchmarks (`src/deppy/hybrid/benchmark/`) — ~3K lines

| File | Lines | Purpose |
|------|-------|---------|
| `hallucination_suite.py` | 800 | 100 LLM artifacts + ground truth |
| `lean_translation_suite.py` | 800 | 50 Python→Lean pairs |
| `nl_spec_suite.py` | 600 | 100 NL specs + ground truth |
| `run_benchmarks.py` | 500 | Runner |
| `integration_tests.py` | 300 | End-to-end smoke tests |

### Total: ~90K LOC (61K Python + 29K Lean)

---

## VI. WHAT MAKES THIS THE HOLY GRAIL

| Property | How It's Achieved | Mathematical Basis |
|----------|------------------|--------------------|
| Every LLM output is typed | HybridType with 5-layer sections | Product presheaf over Site(P) × Layer |
| Hallucination = type error | Value fails to inhabit HybridType | Inhabitation failure in dependent type |
| Intent-code gap is measurable | H¹(ProductSite, HybridTy) ≠ 0 | Čech cohomology of product presheaf |
| Gap is localizable | Each H¹ generator identifies the obstruction | Independent generators of cohomology group |
| Gap is fixable | Resolve obstructions → H¹ = 0 | Obstruction resolution = coboundary correction |
| Proofs are machine-checked | All obligations compile to Lean | Curry-Howard: proofs as terms |
| LLM is controlled | Oracle monad T_O with trust tracking | Controlled oracle in trust topos |
| Verification is incremental | Mayer-Vietoris long exact sequence | Connecting homomorphism δ |
| Caching saves tokens | Content-hash keyed oracle cache | Oracle monad is functional on content |
| JSON is typed | JSON refinement types with Z3 + oracle | Semi-structured refinement lattice |
| Programs = Σ-types | Code paired with proof certificate | Dependent pair type |
| Equivalence is checkable | H¹(Iso-sheaf) = 0 | Descent theorem |

**The system doesn't make software "more likely" to be correct. It makes correctness MEASURABLE (H¹), LOCALIZABLE (generators), PROVABLE (Lean), and AUDITABLE (certificates). That's the holy grail.**

---

## VII. IMPLEMENTATION STATUS (as of 46K LOC)

✅ = complete & verified, 🔄 = agent building, ❌ = failed (relaunched)

### Core (Pillar 1): trust, provenance, contracts, checker ✅ | types 🔄 | intent_bridge 🔄 | oracle_theory 🔄 | algebraic_geometry 🔄
### Mixed-Mode (1.5): syntax, parser ✅ | compiler 🔄
### Lean Translation (2): python_model ✅ | type_translation, semantics_bridge ✅ | lean_emitter 🔄
### NL→Spec (3): nl_parser, decidability_classifier, z3_compiler ✅
### Anti-Hallucination (4): artifact_types ✅ | checker, detectors 🔄
### Discharge (5): cascade, z3_to_lean, llm_prover ✅
### Pipeline (6): stages, orchestrator, cli ✅
### Theory Library (7): base, stdlib, numpy_theory, torch_theory ✅
### Lean Proofs (8): HybridType, OracleMonad, TrustTopos, AntiHallucination ✅
### Benchmarks (9): hallucination_suite, integration_tests, run_benchmarks ✅
### Type Expansion (10): expander, codegen_plan, large_scale 🔄
### Agent: verification_loop, project_assembler, cli, financial_trading ✅ | orchestrator, intent_oracle, code_generator 🔄
### Integrations: copilot, claude, codex ✅
### Tests: test_core (33 tests) ✅

---

# PILLAR 11: WHAT'S MISSING — THE "PEOPLE WILL ACTUALLY USE THIS" GAP

## The Hard Truth

We have ~46K lines of deep algebraic-geometric dependent type theory. Beautiful math.
But verification systems die in the gap between "theoretically sound" and "I'll add this
to my CI pipeline." Here's what bridges that gap — all grounded in the same sheaf/oracle/DTT
framework, but oriented toward the *pragmatics* of real adoption.

## 11.1  The Zero-Change Entry Point

**Problem**: Nobody will rewrite their codebase to use deppy. The adoption barrier must be ZERO.

**Solution**: `deppy check myfile.py` works on EXISTING Python code with NO annotations.

How this works mathematically:
- Parse the Python AST → extract the **implicit presheaf** Ty_implicit
- Ty_implicit comes from: type hints (if any), docstrings, assert statements,
  variable names, control flow patterns, test files (if found)
- This is a *degenerate* HybridType — mostly at INTENT and STRUCTURAL layers,
  with CODE layer fully populated from the AST
- Compute H¹(implicit cover) — gaps between what the code *appears* to promise
  (via names, docstrings, type hints) and what it *actually does* (via AST analysis)
- Report gaps as human-readable diagnostics, NOT "H¹ generator at cocycle (3,7)"
  but "Function `validate_order` has no check for negative quantities, despite
  the docstring saying 'validates all fields'"

**Files needed:**
- [ ] `src/deppy/hybrid/zero_change/implicit_presheaf.py` (~1500 lines)
  - Extract HybridType from bare Python: AST → implicit intent (names, docstrings),
    implicit structural (type hints, asserts), implicit semantic (patterns, idioms)
  - `ImplicitPresheafExtractor.extract(source: str) -> Dict[str, HybridType]`
  - Uses theory library to recognize stdlib/numpy/torch patterns

- [ ] `src/deppy/hybrid/zero_change/existing_code_checker.py` (~1200 lines)
  - Runs H¹ analysis on implicit presheaf, produces human-readable diagnostics
  - `ExistingCodeChecker.check(file_path: str) -> List[Diagnostic]`
  - SARIF output for CI/CD integration

## 11.2  Human-Readable Error Messages (the "Don't Say Cocycle" Rule)

**Problem**: "Cohomological obstruction in Čech complex" is useless to a developer.

**Solution**: Every H¹ generator maps to a *concrete, actionable* message via a
**localization functor** Loc : H¹ → HumanDiagnostic.

```
Loc : H¹(U, HybridTy) → Diagnostic
     obstruction at (INTENT, CODE)        →  "Intent says X, code does Y"
     obstruction at (STRUCTURAL, CODE)    →  "Type annotation says A, value can be B"
     obstruction at (INTENT, STRUCTURAL)  →  "Docstring promises X, no check enforces it"
     obstruction at (SEMANTIC, PROOF)     →  "Semantic property X has no proof or test"
```

Each diagnostic includes: plain English description, code location (file:line:col),
intent fragment, suggested fix (with confidence and trust level of diagnosis).

**File needed:**
- [ ] `src/deppy/hybrid/diagnostics/localization.py` (~1000 lines)
  - `LocalizationFunctor` — maps H¹ generators to Diagnostic objects
  - `DiagnosticFormatter` — plain text, SARIF, JSON, GitHub annotations
  - `SuggestedFix` — with diff, confidence, and provenance

## 11.3  Gradual Trust Dashboard

**Problem**: Verification is all-or-nothing in most systems. Nobody goes from 0→100%.

**Solution**: A **trust dashboard** showing per-module, per-function trust levels,
with a clear path from UNTRUSTED → LEAN_VERIFIED.

Mathematically: the trust level is a **global section** of the trust presheaf:
```
Trust : Site(P)^op → TrustLattice
```
The dashboard shows: heatmap, progress ("73% PROPERTY_CHECKED"), next steps
("To promote auth.validate_token, add these 3 predicates..."), cost estimates.

**File needed:**
- [ ] `src/deppy/hybrid/diagnostics/trust_dashboard.py` (~800 lines)
  - `TrustDashboard`, `TrustHeatmap`, `PromotionAdvisor`, `CostEstimator`

## 11.4  Diff-Based Incremental Verification

**Problem**: Re-verifying 50K LOC on every commit is too expensive.

**Solution**: Only re-verify the **affected sheaf sections**. A change at site s
only invalidates sections at s and its *Čech neighbors* (sites sharing a cover element).

```
ΔVerify(commit) =
  changed_sites = git_diff → affected AST nodes → sites in Site(P)
  affected_sections = {s ∈ cover | s ∩ changed_sites ≠ ∅}
  recheck H¹ only on affected_sections ∪ neighbors(affected_sections)
```

This is **sheaf locality** in action.

**File needed:**
- [ ] `src/deppy/hybrid/incremental/diff_verifier.py` (~1200 lines)
  - `DiffVerifier`, `SheafLocalityAnalyzer`, `IncrementalCache`

## 11.5  Oracle Budget & Cost Control

**Problem**: LLM oracle calls cost money. Users need to control spending.

**Solution**: Budget-annotated oracle monad T_O^budget(A) = T_O(A) × Cost.

Modes: `--mode=free` (Z3 only), `--mode=cheap` (~$0.01/KLOC),
`--mode=standard` (~$0.05/KLOC), `--mode=thorough` (~$0.20/KLOC).

**File needed:**
- [ ] `src/deppy/hybrid/oracle/budget.py` (~800 lines)
  - `OracleBudget`, `BudgetAllocator`, `CostModel`, `BudgetReport`

## 11.6  The "Aha Moment" Demo — Catching What Others Miss

**Problem**: People need to SEE deppy catch a real bug that mypy/pylint/pytest all miss.

10 curated examples: semantically correct but logically wrong code.
Each with: buggy code, mypy output (nothing), pytest (passes), deppy (BUG + fix).

**File needed:**
- [ ] `src/deppy/hybrid/demos/aha_moment.py` (~1000 lines)

## 11.7  Verified Planning — The Type Expansion Certification

A plan P for spec S is **verified** iff:
1. Coverage: Γ_P ⊢ ΣᵢMᵢ : S (modules cover spec)
2. Coherence: H¹(Cover_P, HybridTy) = 0
3. Feasibility: ∀ leaf. atomic(leaf)
4. Consistency: Z3.check(⋀ constraints) = SAT
5. Budget: estimated_cost(P) ≤ budget

Plan certificate = Σ(coverage). Σ(h1). Σ(feasibility). Σ(consistency). Σ(budget). ⊤

**File needed:**
- [ ] `src/deppy/hybrid/type_expansion/plan_verifier.py` (~1200 lines)

## 11.8  Pre-Commit Hook & CI Plugin

**File needed:**
- [ ] `src/deppy/hybrid/ci/hooks.py` (~600 lines)

## Summary

| # | Feature | Lines | Math Foundation |
|---|---------|-------|-----------------|
| 11.1 | Zero-change entry | ~2700 | Implicit presheaf extraction |
| 11.2 | Human error messages | ~1000 | Localization functor H¹→Diagnostic |
| 11.3 | Trust dashboard | ~800 | Trust presheaf visualization |
| 11.4 | Diff-based incremental | ~1200 | Sheaf locality |
| 11.5 | Oracle budget | ~800 | Budget-annotated oracle monad |
| 11.6 | Aha moment demo | ~1000 | Real H¹ ≠ 0 on LLM-generated code |
| 11.7 | Verified planning | ~1200 | Plan-as-Σ-type certification |
| 11.8 | CI/pre-commit hooks | ~600 | Pipeline integration |
| **Total** | | **~9300** | |

---

# PILLAR 12: IDEATION-AS-TYPING — CREATIVE CROSS-DOMAIN THINKING AS A SHEAF PROBLEM

## The Meta-Observation

Deppy itself was born from a radically interdisciplinary act: someone saw that
*algebraic geometry* (sheaves, cohomology, descent), *type theory* (Π, Σ, refinement),
and *LLM behavior* (hallucination, confidence, grounding) are not three separate things
but three local sections of a single global insight that glue together.

**That act of creative connection is itself a typing problem.**

This is not metaphor. We can formalize it precisely, implement it, and use it to
*systematically generate new interdisciplinary insights* with LLM oracles while
using the same sheaf-theoretic machinery to filter out shallow analogies (hallucinations)
from deep structural connections (functors).

## 12.0  The Core Formalization

### Domains as Sites

Each intellectual domain D is a **site** Site(D):
```
Objects:    concepts in D
            e.g., Site(AlgGeom) has: sheaf, presheaf, cohomology, site, 
            covering_family, section, restriction, gluing, descent, Čech_complex, ...

Morphisms:  logical/definitional relationships
            e.g., sheaf → presheaf (every sheaf is a presheaf)
                  cohomology → obstruction (cohomology detects obstructions)
                  descent → gluing (descent data determines gluing)

Topology:   J_D = the "explanatory" covering families
            A concept c is "covered" by {c₁,...,cₖ} if understanding
            c₁,...,cₖ is sufficient to understand c.
            e.g., {sections, restrictions, gluing_axiom} covers "sheaf"
```

### Knowledge as Presheaves

A body of knowledge in domain D is a **presheaf** K : Site(D)^op → InfoLattice:
```
K(concept) = everything known about that concept
K(c₁ → c₂) = how knowledge of c₂ restricts/specializes to c₁
```

K is a **sheaf** iff local knowledge glues: if you understand all the parts,
you understand the whole. (Most textbook knowledge IS a sheaf — that's why
textbooks are possible.)

### Analogies as Natural Transformations

An **analogy** between domain A and domain B is a pair:
```
(F : Site(A) → Site(B),  η : K_A → F* K_B)
```
where F is a functor mapping concepts and η shows how knowledge transfers.

Examples:
- F("sheaf") = "type assignment", F("section") = "type at a program point",
  F("gluing") = "type inference", F("cohomology") = "type error detection"
  → This is the deppy analogy. η maps AG knowledge to PL knowledge.

- F("covering family") = "test suite", F("sheaf condition") = "test adequacy",
  F("H¹ ≠ 0") = "untested behavior"
  → This is the testing-as-sheaf-theory analogy.

### Deep vs Shallow Analogies

A **deep analogy** is a **morphism of sites**: F preserves the topology.
```
deep(F) ⟺ F preserves covering families
        ⟺ if {cᵢ → c} covers c in Site(A), 
           then {F(cᵢ) → F(c)} covers F(c) in Site(B)
```

A **shallow analogy** maps objects but not structure. It's a function on objects
that doesn't respect morphisms or coverings. These are the hallucinations of
interdisciplinary thinking — "X looks like Y" but the resemblance is surface-level.

**The typing rule:**
```
F : Site(A) → Site(B)
F preserves J (topology)
η : K_A →^nat F* K_B   (knowledge transfers naturally)
──────────────────────────────────────────────────────
(F, η) : DeepAnalogy(A, B)
```

If any premise fails, the analogy is **ill-typed** — it doesn't type-check.

### Creative Insight as Gluing

The moment of creative insight is precisely **sheaf gluing** over a multi-domain cover.

You have domains D₁, ..., Dₙ. Each has local knowledge K_{Dᵢ}. You discover that
on overlaps D_i ∩ D_j (shared concepts), the knowledge sections are compatible:
```
restrict(K_{Dᵢ}, Dᵢ ∩ Dⱼ) ≅ restrict(K_{Dⱼ}, Dᵢ ∩ Dⱼ)
```

When this cocycle condition holds for all pairs, you can **glue** into a global section:
```
K_global = glue({K_{Dᵢ}}) : a unified theory that spans all domains
```

**Deppy's creation was exactly this:**
- K_{AG}: "H¹ detects obstructions to gluing local data into global data"
- K_{TT}: "type errors are obstructions to constructing well-typed programs"
- K_{LLM}: "hallucinations are ungrounded claims that don't cohere with evidence"

On the overlap AG ∩ TT: "obstruction" in AG ≅ "type error" in TT ✓
On the overlap AG ∩ LLM: "failure to glue" in AG ≅ "hallucination" in LLM ✓
On the overlap TT ∩ LLM: "ill-typed" in TT ≅ "ungrounded" in LLM ✓

All cocycle conditions hold → glue → deppy.

### H¹ of the Interdisciplinary Cover

When cocycle conditions FAIL, you get H¹ ≠ 0:
```
H¹({D₁,...,Dₙ}, Knowledge) ≠ 0
⟺ the domains don't fit together (yet)
⟺ there's a gap in the interdisciplinary theory
```

Each H¹ generator = one independent "conceptual gap" that needs bridging.

**This is where LLM oracles shine**: they can *propose* bridge concepts
(new objects in the overlap D_i ∩ D_j) that might make the cocycle condition hold.
But the proposal is in T_O — it needs validation.

### Ideation as Type Inhabitation

The ultimate formalization:
```
"Find a new idea connecting domains D₁,...,Dₙ"

=  inhabit the type:

   IdeationType(D₁,...,Dₙ) = Σ(F : ∏ᵢ Site(Dᵢ) → UnifiedSite).
                               Σ(η : ∏ᵢ K_{Dᵢ} →^nat F* K_unified).
                               Σ(deep : topology_preserving(F)).
                               Σ(novel : ¬previously_known(F)).
                               Σ(useful : value_estimate(F) > threshold).
                               ⊤
```

The **existence** of an inhabitant IS the creative insight.
The **proof** it's topology-preserving IS the validation it's deep, not shallow.
The **novelty** check IS the filter against rediscovery.
The **value** estimate IS the pragmatic filter.

### 12.0.1  Why Algebraic Geometry Is the Right Language for Ideation

The key claim is stronger than "geometry gives a nice metaphor for ideas."
The claim is that **ideation has the exact shape of a local-to-global problem**, and
algebraic geometry is the mature mathematics of local-to-global problems.

When a researcher is thinking across domains, they almost never begin with a fully
formed global theory. They begin with:

1. Local fragments that make sense inside one domain
2. Partial correspondences on overlaps between domains
3. Tensions, gaps, or ambiguities when trying to merge those fragments

That is precisely the data of a sheaf problem:
```
local sections on U_i
compatibility data on U_i ∩ U_j
question: do these glue to a global section on ⋃ U_i?
```

In research terms:
```
local section      = a domain-local insight that is internally coherent
overlap            = a shared explanatory structure between two domains
gluing             = a unified theory or design principle
nonzero H¹         = a genuine conceptual obstruction, not just confusion
```

This matters because it distinguishes two very different situations that are often
collapsed in ordinary brainstorming:

- "I do not yet understand the connection."
- "There is no coherent connection of the required kind."

Sheaf theory separates them. A missing proof of compatibility is not the same thing
as a proved nontrivial cocycle. The former is incomplete work; the latter is evidence
that some bridge concept, refinement, or change of cover is needed.

### 12.0.2  The Dependent Type-Theoretic View of a Partial Idea

Dependent type theory supplies the second half of the picture: it tells us what kind
of object an idea must be in order to count as a real explanation rather than an
association.

A serious cross-domain idea is not a bare pair of labels. It has internal fields:
```
Idea(A, B)
  = Σ(F_obj    : Obj(A) → Obj(B)).
    Σ(F_mor    : preserves_morphisms(F_obj)).
    Σ(F_cov    : preserves_covers(F_obj)).
    Σ(eta      : transfer_of_predicates(F_obj)).
    Σ(witness  : explanatory_payoff(F_obj, eta)).
    ⊤
```

This is proof-relevant. To inhabit `Idea(A, B)` you do not merely assert that an
analogy exists; you provide the data that makes the analogy computationally usable.

The dependent structure is essential:

- `F_mor` depends on `F_obj`
- `F_cov` depends on how objects and morphisms were mapped
- `eta` depends on the chosen functor and the presheaves being related
- `witness` depends on the whole prior construction

This means ideation is not an untyped search over slogans. It is a search over
increasingly constrained inhabitants of a dependent record, where each field rules
out large classes of shallow analogies.

In this framing, a "promising but incomplete idea" is literally a partial term:
```
?f : Σ(F_obj : Obj(A) → Obj(B)). preserves_morphisms(F_obj)
```
or
```
?g : IdeationType(D₁, D₂, D₃)
```
with holes for topology preservation, novelty, or usefulness.

That is why the language of holes, obligations, and refinement is natural here.
Research ideation becomes a typed proof search problem with oracle-assisted hole
filling and explicit residual obligations.

### 12.0.3  Covers Are Viewpoints, Not Just Domain Labels

The most important modeling decision is the choice of cover.
If we model a domain too coarsely, every analogy looks trivial. If we model it too
finely, every analogy looks impossible. The right cover exposes the intermediate
structures where real transfer happens.

For ideation, the cover is usually not just:
```
{algebraic geometry, type theory, machine learning}
```

It is closer to:
```
U_AG = {locality, gluing, descent, obstruction, moduli}
U_TT = {context, substitution, dependent family, identity, normalization}
U_LLM = {prompt, latent representation, confidence, grounding, repair}
```

Now the overlaps become much more informative:
```
U_AG ∩ U_TT   contains: local context, compatibility, witness transport
U_TT ∩ U_LLM  contains: proof obligation, partial term, admissible oracle query
U_AG ∩ U_LLM  contains: failed gluing, inconsistency detection, repair-by-refinement
```

An ideation engine therefore needs **adaptive cover selection**.
Sometimes the correct move is not to propose a new analogy, but to refine the cover
until the relevant overlap becomes visible.

Formally:
```
refine_cover : Cover(D) → Cover(D) 
```

and ideation may need to search over both:
```
Σ(U : Cover(D₁ ⊔ ... ⊔ Dₙ)). section_problem(U)
```

This is one reason LLMs are useful but insufficient: they can suggest candidate
refinements of the cover, but the system still needs structural checks to determine
whether the refined overlap actually supports gluing.

### 12.0.4  Conceptual Overlap as a Fiber Product

The phrase "overlap between domains" should be made mathematically precise.
It is not mere lexical intersection. The right notion is a pullback or fiber product
over shared explanatory roles.

Suppose both domain A and domain B admit maps into a smaller site of abstract
research patterns R:
```
role_A : Site(A) → R
role_B : Site(B) → R
```

Then the meaningful overlap is:
```
Site(A) ×_R Site(B)
```

whose objects are pairs `(a, b)` that play the same role in R.

Example:
```
a = "Čech 1-cocycle" in algebraic geometry
b = "incompatible local typing judgments" in program semantics
role(a) = role(b) = "obstruction to global coherence"
```

This is much stronger than matching words. It says the two concepts occupy the same
position in a structural pattern category. A deep analogy is therefore not just an
object map `A → B`; it is a map that is stable under passage through the role site.

This also yields a measurable notion of analogy quality:
```
depth(F) = size of the largest role-pattern subsite preserved by F
```

The more commutative squares, pullbacks, and covering structures preserved, the
deeper the analogy.

### 12.0.5  Gluing Data Is a Research Program

An important shift happens once we stop treating a creative insight as a single flash
of genius and instead view it as descent data.

In algebraic geometry, to glue local sections you need:

1. Local sections on each open set
2. Isomorphisms on overlaps
3. A cocycle condition on triple overlaps

For ideation, the analogous structure is:

1. A local explanation inside each domain
2. Translation rules on pairwise overlaps
3. Coherence of those translations when moving across three or more domains

So a research program is not just "find an analogy." It is:
```
DescentData(D₁,...,Dₙ)
  = Σ(local_models   : ∏ᵢ Model(Dᵢ)).
    Σ(pairwise_maps  : ∏ᵢⱼ Translate(Dᵢ, Dⱼ)).
    Σ(cocycle_proofs : coherent_on_triples(local_models, pairwise_maps)).
    ⊤
```

The output of ideation should therefore often be a structured object like:

- what each domain contributes locally
- what the bridge concepts are
- what obligations remain unresolved
- what experiment, proof, or implementation would discharge each obligation

That is much closer to how real breakthroughs are made. The insight is not a slogan;
it is a package of gluing data plus a roadmap for completing the glue.

### 12.0.6  H¹ Measures the Shape of "Almost an Idea"

The phrase "almost an idea" can be made precise.

Suppose we have candidate correspondences on pairwise overlaps. They may satisfy many
local checks, but fail to extend globally. Then we have a 1-cocycle that is not a
1-coboundary:
```
[c] ∈ H¹(U, Knowledge) ,  [c] ≠ 0
```

Interpretation:

- The idea is not nonsense; local pieces really do line up.
- But the local compatibilities do not come from a single coherent global viewpoint.

This is exactly the state of many strong but unfinished research intuitions.
One can see that multiple areas are "trying to say the same thing," but some bridge
definition is missing.

Each nonzero generator suggests a different repair action:

1. Refine the domain sites.
2. Add an intermediate bridge concept.
3. Weaken the claimed equivalence to an adjunction, lens, or approximation.
4. Split one supposed global idea into two genuinely different ones.

That gives a principled ideation loop:
```
propose local correspondences
compute overlap inconsistencies
extract H¹ generators
for each generator:
    propose bridge or refinement
recompute until H¹ = 0 or declare obstruction fundamental
```

This is a better story than naive brainstorming because failure becomes informative.
The system can say not just "bad idea" but "the problem is specifically that your
mapping preserves objects and some morphisms, but not the cover needed for descent."

### 12.0.7  Identity Types Explain When Two Concepts Are "The Same"

Dependent type theory contributes a second kind of precision: what counts as sameness.

In interdisciplinary work, two concepts are rarely definitionally equal. At best they
are propositionally equal, equivalent, or connected by transport along a structure map.

So the right question is not:
```
sheaf = type_assignment ?
```

but rather:
```
Id_{RoleSite}( role("sheaf"), role("type_assignment") ) ?
```

or more operationally:
```
Equiv(Behavior("sheaf"), Behavior("type_assignment")) ?
```

This prevents category errors. Many bad analogies implicitly claim definitional
equality where only a weaker correspondence is available.

The hierarchy is useful:

- definitional equality: literally the same structure
- propositional equality: equal up to proof
- equivalence: interchangeable for relevant purposes
- adjunction/lens: partially matching but directional
- mere association: not enough to support transfer

An ideation checker should classify mappings at the strongest valid level.
That classification directly affects what can be transported across the analogy.

### 12.0.8  Universes and Abstraction Boundaries

Many cross-domain ideas fail because they are posed at the wrong universe level.
They mix:

- object-level claims about particular algorithms
- meta-level claims about classes of constructions
- methodological claims about how to search for explanations

Type theory forces these apart.

We may have:
```
Type_0  = concrete artifacts and examples
Type_1  = patterns over artifacts
Type_2  = strategies for finding or validating patterns
```

Then an ideation claim can be rejected as ill-formed if it jumps levels without an
explicit lifting operation.

Example:
"Because one neural network learned an internal parser, category theory explains all
language models" confuses a local empirical phenomenon with a universe-level theory.

By contrast, a disciplined statement would be:
```
Π(M : ModelClass). P(M) → Σ(S : StructuralPattern). explains(S, M)
```

This explicitly states the quantification level and the evidence required.

### 12.0.9  Ideation About deppy, Formally

Now the motivating example can be restated with much more precision.

The deppy insight was not just:
"bugs are like cohomology classes."

It was closer to the following composite inhabitant:
```
Σ(F₁ : Site(AlgGeom) → Site(ProgramSemantics)).
Σ(F₂ : Site(TypeTheory) → Site(ProgramSemantics)).
Σ(F₃ : Site(LLMBehavior) → Site(ProgramSemantics)).
Σ(eta₁ : Knowledge_AG → F₁* Knowledge_PS).
Σ(eta₂ : Knowledge_TT → F₂* Knowledge_PS).
Σ(eta₃ : Knowledge_LLM → F₃* Knowledge_PS).
Σ(cohere : pairwise_and_triple_overlap_compatibility).
Σ(value  : yields_new_verification_pipeline).
⊤
```

The crucial bridge concepts were not the names of objects but the preservation of
roles:

- local section ↔ local typing judgment / local evidence
- gluing failure ↔ inconsistency across program regions or trust layers
- obstruction class ↔ minimal nonlocal explanation of failure
- descent data ↔ verified assembly from local checked components

Once seen this way, the insight had executable consequences. It told us what data
structures to build, what invariants to check, what failures to compute, and what a
certificate should contain. That is the standard for a real interdisciplinary idea:
it should not merely redescribe the problem; it should induce a new typed interface
for solving it.

### 12.0.10  The Practical Output: Ideas as Certified Interfaces

The end state of ideation should therefore be a certified object that downstream
components can consume:
```
CertifiedIdea
  = Σ(mapping        : AnalogyType).
    Σ(obligations    : List[OpenProofGoal]).
    Σ(experiments    : List[ValidationTask]).
    Σ(codegen_hooks  : Optional[TypeExpansionPlan]).
    Σ(trust_report   : ProvenanceBundle).
    ⊤
```

This makes ideation operational.

- If obligations are empty and trust is high, compile the idea into code or proofs.
- If obligations remain, route them to experiment design or theorem proving.
- If H¹ stays nonzero, keep the idea as a partial bridge rather than overselling it.

The payoff is that creative thinking becomes part of the same pipeline as typing,
verification, and synthesis. Instead of brainstorming first and formalizing later,
the brainstorming process itself emits proof-relevant artifacts.

### 12.0.11  Lean-Level Basis: What Is a "Good Idea for Software Development"?

If this pillar is going to become executable mathematics, we need a Lean object that
captures what software teams informally mean by a "good idea":

- it solves some real problem in the current context
- it respects architectural and interface constraints
- it composes with surrounding modules and workflows
- it generates verifiable obligations rather than vague aspirations
- it survives descent from local plausibility to global implementability

That suggests a new proof object, not just a score.

At the Lean level, the right approach is to define a site of software-development
facets and then define good ideas as gluable local sections over that site.

The cover should not be "frontend/backend/database" only. For ideation, a better
initial facet cover is:

```lean
inductive SoftwareFacet where
  | intent
  | domainModel
  | apiSurface
  | invariants
  | failureModes
  | tests
  | rollout
  deriving DecidableEq, Repr
```

This lets us distinguish an idea that is attractive only at the intent level from an
idea that also survives contact with invariants, failure modes, and rollout.

Then a local section is "what this idea says when viewed from one facet":

```lean
structure LocalIdeaSection where
  facet : SoftwareFacet
  claim : String
  structuralObligations : List Prop
  semanticObligations : List Prop
  artifacts : List String
```

This is intentionally proof-oriented. A local idea section is not prose alone; it is
paired with obligations and expected artifacts.

### 12.0.12  Proposed Lean Module: `DeppyProofs/Hybrid/Ideation.lean`

The first pass should probably introduce the following core objects.

```lean
namespace DeppyProofs

structure IdeaContext where
  problem : String
  existingConstraints : List Prop
  existingArtifacts : List String

structure IdeaSite where
  Facet : Type
  overlap : Facet → Facet → Type
  tripleOverlap : Facet → Facet → Facet → Type

structure IdeaPresheaf (α : Type) (S : IdeaSite) where
  section : S.Facet → Type
  restrict : {a b : S.Facet} → S.overlap a b → section a → section b

structure LocalSoftwareIdea (S : IdeaSite) where
  sectionAt : (f : S.Facet) → Type

structure OverlapAgreement (S : IdeaSite) (I : LocalSoftwareIdea S) where
  agrees : ∀ {a b : S.Facet}, S.overlap a b → Prop

structure GoodSoftwareIdea (S : IdeaSite) where
  localSections : (f : S.Facet) → Type
  compatibility : Prop
  implementable : Prop
  nontrivial : Prop
  valuePositive : Prop

end DeppyProofs
```

That sketch is deliberately minimal. In the real Lean file, `Type` placeholders would
be replaced by structures carrying explicit local claims, obligations, and transport
maps. But even this minimal version tells us the shape of the theorem we want:
goodness is a gluing theorem with extra witnesses for implementability and value.

### 12.0.13  The Fundamental Theorem Schema

The central theorem should say:

1. if each facet-local section is valid
2. if the pairwise translations agree on overlaps
3. if the induced cocycle is trivial
4. if the resulting global object has an implementation witness

then the candidate is a good software idea.

In Lean style:

```lean
theorem local_good_ideas_glue
    (S : IdeaSite)
    (local : (f : S.Facet) → LocalIdeaSection)
    (hCompat : ∀ {a b}, S.overlap a b → Prop)
    (hCocycle : ∀ {a b c}, S.tripleOverlap a b c → Prop)
    (hImpl : Prop)
    (hValue : Prop) :
    ∃ global : GoodSoftwareIdea S,
      global.compatibility ∧ global.implementable ∧ global.valuePositive := by
  sorry
```

That theorem is too weak as written, but it has the correct direction: local adequacy
plus descent data plus implementation witness yields a global certified idea.

What makes it useful is that each premise corresponds to something operational:

- `hCompat` comes from interface and invariant checks
- `hCocycle` comes from multi-facet coherence checks
- `hImpl` comes from a codegen or plan witness
- `hValue` comes from either oracle judgment or downstream measured payoff

### 12.0.14  Reusing the Existing Descent Theorem

A major advantage of this formulation is that much of the proof theory already exists
in the repo.

The theorem in [lean_proofs/DeppyProofs/Descent.lean](/Users/halleyyoung/Documents/div/mathdivergence/deppy/lean_proofs/DeppyProofs/Descent.lean) says, in effect:

```lean
H¹(U, Iso) = 0  ↔  local equivalences glue to a global equivalence
```

For ideation, we want to instantiate the same pattern with an "idea semantics"
presheaf rather than a program semantics presheaf.

So one target theorem is:

```lean
theorem idea_descent_theorem
    (Sem_local Sem_global : IdeaSemanticPresheaf α)
    (s : IdeaFacetSite)
    (cf : CoveringFamily s)
    (base : IdeaFacet) (hbase : base ∈ cf.members) :
    (∀ ge : GlobalEquiv Sem_local Sem_global,
      ∀ ov : Overlap s cf, ∀ σ,
        transitionFunction Sem_local Sem_global
          (globalToLocal Sem_local Sem_global s cf ge) ov σ = σ) ∧
    (∀ equivs : LocalEquivFamily Sem_local Sem_global s cf,
      (∀ ov : Overlap s cf, ∀ σ,
        transitionFunction Sem_local Sem_global equivs ov σ = σ) →
      ∃ forward backward,
        (∀ σ, forward (backward σ) = σ) ∧
        (∀ σ, backward (forward σ) = σ)) := by
  exact descent_theorem Sem_local Sem_global s cf base hbase
```

The proof is not deep because the depth is pushed into the instance: once we model
idea semantics as a presheaf with overlaps and restrictions, the generic descent
machinery should apply nearly unchanged.

That is exactly the right architecture. We should prove theorems once at the sheaf
level and reuse them for code, plans, and ideas.

### 12.0.15  Formalizing Goodness as a Hybrid Type

A software idea is not good merely because it glues. It also has to avoid the
ideational analogue of hallucination: a globally coherent story that has no grounded
implementation path.

So the better target is a hybrid type for ideas:

```lean
structure IdeaHybridType where
  intentLayer : Prop
  structuralLayer : Prop
  semanticLayer : Prop
  proofLayer : Prop
  implementationLayer : Prop
```

And a candidate idea inhabits this type only if all layers are satisfied.

```lean
def ideaInhabits (candidate : GoodSoftwareIdea S) (T : IdeaHybridType) : Prop :=
  T.intentLayer ∧
  T.structuralLayer ∧
  T.semanticLayer ∧
  T.proofLayer ∧
  T.implementationLayer
```

This gives us the exact analogue of the anti-hallucination theorem in
[lean_proofs/DeppyProofs/Hybrid/AntiHallucination.lean](/Users/halleyyoung/Documents/div/mathdivergence/deppy/lean_proofs/DeppyProofs/Hybrid/AntiHallucination.lean):

```lean
def is_idea_hallucination (candidate : GoodSoftwareIdea S) (T : IdeaHybridType) : Prop :=
  ¬ ideaInhabits candidate T

theorem anti_hallucination_for_ideas
    (candidate : GoodSoftwareIdea S)
    (T : IdeaHybridType)
    (h_intent : T.intentLayer)
    (h_struct : T.structuralLayer)
    (h_sem : T.semanticLayer)
    (h_proof : T.proofLayer)
    (h_impl : T.implementationLayer) :
    ¬ is_idea_hallucination candidate T := by
  unfold is_idea_hallucination ideaInhabits
  simp [h_intent, h_struct, h_sem, h_proof, h_impl]
```

This theorem is intentionally simple, but conceptually important. It says the system
should treat a bad product idea, architecture idea, or workflow idea exactly the way
it treats a hallucinated code artifact: as failure to inhabit a tracked hybrid type.

### 12.0.16  What the Structural Layer Should Prove

To be useful for software development, the structural layer needs to state more than
"the idea sounds organized." It should prove concrete transport properties.

At minimum:

```lean
structure StructuralIdeaWitness (ctx : IdeaContext) where
  preservesInterfaces : Prop
  preservesInvariants : Prop
  preservesDependencyAcyclicity : Prop
  hasTestObligations : Prop
  hasRollbackStory : Prop
```

Then define:

```lean
def StructurallyGood (ctx : IdeaContext) : Prop :=
  ∃ w : StructuralIdeaWitness ctx,
    w.preservesInterfaces ∧
    w.preservesInvariants ∧
    w.preservesDependencyAcyclicity ∧
    w.hasTestObligations ∧
    w.hasRollbackStory
```

Now theorems become meaningful for engineering:

```lean
theorem structural_good_has_safe_refinement_path
    (ctx : IdeaContext)
    (h : StructurallyGood ctx) :
    ∃ obligations : List Prop, obligations.length > 0 := by
  sorry
```

Interpretation: every structurally good idea should induce explicit proof or test
obligations. If an idea yields no obligations at all, that is usually a sign that it
is too vague to matter.

### 12.0.17  What the Semantic Layer Should Say Honestly

The semantic layer will often depend on oracle judgment, so the Lean theorems must be
honest in the same way the oracle monad already is in
[lean_proofs/DeppyProofs/Hybrid/OracleMonad.lean](/Users/halleyyoung/Documents/div/mathdivergence/deppy/lean_proofs/DeppyProofs/Hybrid/OracleMonad.lean).

We should not try to prove:
"this idea will definitely improve the product."

We should prove something weaker and honest:

```lean
structure IdeaOracleResult (α : Type) where
  value : α
  trust : TrustLevel
  confidence : Confidence
  rationale : String

def SemanticallyPromising (ctx : IdeaContext) : Prop :=
  ∃ r : IdeaOracleResult Bool,
    r.value = true ∧
    r.trust ≥ TrustLevel.llm_judged
```
```

Then the theorem is a trust-bounding theorem, not a truth theorem:

```lean
theorem idea_semantic_judgment_is_bounded
    (r : IdeaOracleResult α) :
    r.trust ≤ TrustLevel.lean_verified := by
  sorry
```

This is the correct attitude for software ideation. The semantic oracle can tell us
that a proposal is plausible, high-value, or elegant, but the system must never erase
the fact that these are oracle-level claims.

### 12.0.18  From Good Ideas to Code Generation Plans

Ultimately, the point of a software idea is not just to be admired; it is to induce a
safer development trajectory.

So we want a theorem relating good ideas to plan generation:

```lean
structure ImplementationPlan where
  phases : List String
  obligations : List Prop
  touchedArtifacts : List String

def ExtractablePlan (idea : GoodSoftwareIdea S) : Prop :=
  ∃ p : ImplementationPlan,
    p.phases.length > 0 ∧ p.obligations.length > 0

theorem good_idea_yields_plan
    (idea : GoodSoftwareIdea S)
    (hStruct : StructurallyGood ctx)
    (hCompat : idea.compatibility)
    (hImpl : idea.implementable) :
    ExtractablePlan idea := by
  sorry
```

This theorem is the hinge between ideation and type expansion.
It says a good idea should compile into a plan with explicit phases and obligations.
If it cannot, then it may still be philosophically interesting, but it is not yet a
good software-development idea in the sense deppy cares about.

### 12.0.19  The Strongest Version: Good Ideas Preserve or Improve Global Coherence

The most ambitious theorem should express that adopting a good idea does not increase
the obstruction burden of the system, except in controlled ways.

In ideal form:

```lean
theorem good_idea_does_not_increase_unexplained_obstruction
    (before after : SemanticPresheaf α)
    (idea : GoodSoftwareIdea S)
    (hApply : applyIdea before idea = after)
    (hGood : ideaInhabits idea T) :
    obstructionRank after ≤ obstructionRank before + idea.introducedObligations := by
  sorry
```

This is the mathematically serious notion of a good engineering idea. A good idea may
introduce new obligations, but it should do so in a way that is explicit, bounded,
and paired with a path to discharge them.

### 12.0.20  Proof Strategy Roadmap

The proof development should proceed in this order:

1. Define an idea-facet site and presheaf.
2. Reuse generic descent results to get gluing theorems for local idea sections.
3. Define `IdeaHybridType` and the analogue of hallucination-freedom.
4. Prove structural lemmas that a certified idea induces obligations and interfaces.
5. Connect certified ideas to implementation plans.
6. Finally, prove monotonicity or boundedness results about obstructions under idea application.

The important design principle is that "good idea" should not be a primitive scalar.
It should be a theorem-backed structure whose fields expose exactly why the idea is
good, what it preserves, what it assumes, and what new obligations it creates.

## 12.1  The LLM Oracle's Role in Ideation

LLMs are uniquely positioned for interdisciplinary ideation because they've ingested
text from ALL domains. They can pattern-match across domains at a scale no human can.

But: most cross-domain pattern matches are shallow. "Quantum computing is like cooking"
might share words ("state," "transformation," "measurement") without sharing structure.

**The oracle protocol for ideation:**
```
1. oracle_propose(D₁, D₂) → T_O(List[ConceptMapping])
   "What concepts in D₁ correspond to concepts in D₂?"
   Trust: LLM_RAW. May be shallow.

2. validate_functor(mapping) → T_O(bool)
   "Does this mapping preserve morphisms? If c₁ → c₂ in D₁,
    does F(c₁) → F(c₂) in D₂?"
   Trust: promoted to LLM_JUDGED if cross-validated.

3. validate_topology(mapping) → bool ∨ T_O(bool)
   "Does the mapping preserve covering families?"
   PARTIALLY DECIDABLE: some covers have structural signatures (Z3-checkable),
   others need oracle judgment.

4. check_novelty(mapping, known_analogies_db) → bool
   DECIDABLE: lookup in database of known cross-domain mappings.

5. estimate_value(mapping, context) → T_O(float)
   "How useful would this connection be for the current problem?"
   Trust: LLM_JUDGED.
```

The pipeline: propose → validate → filter → rank.
Most proposals fail at step 2 (not functorial). That's correct — most "ideas" are bad.
The ones that survive are the deep insights.

## 12.2  Decidability Stratification for Ideation

Not all aspects of analogy-checking are equally hard:

```
DECIDABLE (Z3/structural):
  - Arity matching: does the mapping preserve the number of arguments?
  - Type signature matching: do mapped functions have compatible signatures?
  - Acyclicity: is the mapped dependency graph still a DAG?
  - Known equivalences: is this mapping in the database of known isomorphisms?

SEMI-DECIDABLE (bounded search):
  - Commutativity: do mapped diagrams commute (up to finite depth)?
  - Covering preservation: do mapped covering families still cover (finite check)?

ORACLE-REQUIRED (semantic):
  - "Is this analogy deep?" (requires understanding both domains)
  - "Is this novel?" (requires knowledge of the field)
  - "Is this useful?" (requires context about the current problem)

UNDECIDABLE (in general):
  - "Is this the BEST analogy?" (no finite procedure can guarantee optimality)
  - "Will this lead to a breakthrough?" (halting-problem-hard in general)
```

The system is honest about which judgments are certain and which are oracle-dependent.

## 12.3  Recursive Self-Application

The deepest payoff: **deppy can ideate about deppy**.

Since ideation is now a typing problem within deppy's own framework:
```
deppy "find a new connection between X and Y that could improve deppy itself"
```

This is a type expansion where the spec is "improve this tool" and the domains include
the tool's own mathematical foundations. The system can:

1. Propose new analogies (oracle): "What if we also used derived categories?"
2. Validate them (type-check): does derived-category theory have a topology-preserving
   map to something useful in program analysis?
3. Generate the code (type expansion): if the analogy type-checks, expand it into
   new modules, complete with verification conditions

This is **self-improving verified software** — not in the AGI sense, but in the
precise mathematical sense of a system that can propose, validate, and implement
extensions to itself, all within its own type theory.

## 12.4  Implementation

### File 1: `src/deppy/hybrid/ideation/domain_site.py` (~1200 lines)
- [ ] `DomainSite` — a site representing an intellectual domain
  - `concepts: Dict[str, Concept]` — objects of the category
  - `morphisms: Dict[Tuple, Morphism]` — relationships between concepts
  - `covering_families: Dict[str, List[List[str]]]` — explanatory covers
  - Pre-built sites: ALGEBRAIC_GEOMETRY, TYPE_THEORY, MACHINE_LEARNING,
    SOFTWARE_ENGINEERING, CATEGORY_THEORY, FORMAL_VERIFICATION, LINGUISTICS
  - `from_corpus(texts: List[str], oracle_fn) -> DomainSite` — extract site from text

### File 2: `src/deppy/hybrid/ideation/analogy_types.py` (~1500 lines)
- [ ] `ConceptMapping` — a proposed correspondence F : Site(A) → Site(B)
- [ ] `AnalogyType` — the full Σ-type for a validated analogy
  - `functor_check(mapping) -> bool` — does it preserve morphisms?
  - `topology_check(mapping) -> bool` — does it preserve covers?
  - `novelty_check(mapping, known_db) -> bool` — is it new?
  - `depth_score(mapping) -> float` — how many structural layers are preserved?
- [ ] `AnalogyChecker` — type-checks analogies using the decidability stratification
- [ ] `IdeationOracle` — LLM oracle protocol for proposing and validating analogies
- [ ] `CrossDomainGluing` — attempts to glue local domain knowledge into unified theory
  - `compute_h1(domains, mappings) -> int` — are there conceptual gaps?
  - `propose_bridges(h1_generators, oracle_fn) -> List[ConceptMapping]` — fill the gaps

### File 3: `src/deppy/hybrid/ideation/self_improve.py` (~800 lines)
- [ ] `SelfImprovementLoop` — deppy ideates about its own extensions
  - `propose_extension(current_system, problem) -> List[ExtensionProposal]`
  - `validate_extension(proposal) -> AnalogyType` — type-check the proposal
  - `generate_extension(validated) -> CodeGenPlan` — plan the implementation
- [ ] `ExtensionProposal` — a proposed new module/feature with its analogy provenance

## 12.5  What This Means

This pillar turns deppy from a *tool* into a *methodology*:

1. **For software**: verify code against specs (Pillars 1-9)
2. **For planning**: verify plans before execution (Pillars 10-11)
3. **For thinking**: verify ideas before committing to them (Pillar 12)

All three are the same mathematical operation: check that local sections glue
(H¹ = 0) in a dependent type theory where oracles are controlled and trusted
only to the degree warranted by evidence.

The progression is:
```
code           ∈ Type_CODE        (well-typed program)
plan           ∈ Type_PLAN        (well-typed plan = Σ-type covering spec)
interdisciplinary idea ∈ Type_IDEA (well-typed analogy = topology-preserving functor)
```

And the trust hierarchy applies at every level:
- An untrusted code change is like an unvalidated idea
- A Z3-proven invariant is like a structurally verified analogy
- A Lean-verified theorem is like a mathematically proven connection
- An LLM-judged semantic property is like an expert's intuition

**The holy grail is not just trustworthy software. It's trustworthy thinking.**
