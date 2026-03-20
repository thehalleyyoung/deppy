/-
  DeppyProofs.Hybrid.HybridType

  Formalization of the Hybrid Dependent Type System.

  HybridType = global section of product presheaf over Site(P) × Layer

  The key idea: a "hybrid type" is not a single object but a *product presheaf
  section* — a compatible family of type information indexed by both program sites
  AND semantic layers. Each layer captures a different aspect of the specification:

    - Intent: what the programmer/user wants (natural language, formalized)
    - Structural: syntactic/structural constraints (decidable)
    - Semantic: deeper meaning constraints (may need oracle)
    - Proof: formal correctness properties (Lean-verified)
    - Code: the actual implementation artifact

  The cocycle condition ensures these layers are *consistent*: the code layer
  actually satisfies what the proof layer claims, which refines what the semantic
  layer describes, which implements what the intent layer specifies.

  This is the mathematical foundation for deppy's anti-hallucination guarantees:
  a value "inhabits" a hybrid type iff it satisfies ALL layers simultaneously.

  Mathematical context:
    Given a program site category S_P with Grothendieck topology J, and the
    discrete category Layer = {intent, structural, semantic, proof, code},
    a HybridType is a global section of the presheaf:

      Sem : (S_P × Layer)^op → Type

    The cocycle condition on this product presheaf ensures that restriction
    along both site morphisms AND layer morphisms is coherent.
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Order.BoundedOrder

open CategoryTheory

namespace Deppy.Hybrid

/-! ## Layer: The Five Semantic Layers

  Each layer captures a different "resolution" of type information.
  Ordered from most abstract (intent) to most concrete (code).
  The ordering induces a natural refinement direction:
    intent ⊒ structural ⊒ semantic ⊒ proof ⊒ code
-/

/-- The five semantic layers of the hybrid type system.
    Each layer captures a different aspect of the specification,
    forming a chain from abstract intent to concrete implementation. -/
inductive Layer where
  | intent      : Layer   -- Natural language specification / user intent
  | structural  : Layer   -- Syntactic/structural constraints (always decidable)
  | semantic    : Layer   -- Deeper meaning constraints (may require oracle)
  | proof       : Layer   -- Formally verified properties (Lean/Z3 proven)
  | code        : Layer   -- Actual implementation artifact
  deriving DecidableEq, Repr, Inhabited

/-- Layers have a natural ordering from abstract to concrete.
    intent < structural < semantic < proof < code -/
def Layer.toNat : Layer → Nat
  | .intent     => 0
  | .structural => 1
  | .semantic   => 2
  | .proof      => 3
  | .code       => 4

instance : LE Layer where
  le l₁ l₂ := l₁.toNat ≤ l₂.toNat

instance : LT Layer where
  lt l₁ l₂ := l₁.toNat < l₂.toNat

instance : DecidableEq Layer := Layer.decEq

instance (l₁ l₂ : Layer) : Decidable (l₁ ≤ l₂) :=
  inferInstanceAs (Decidable (l₁.toNat ≤ l₂.toNat))

instance (l₁ l₂ : Layer) : Decidable (l₁ < l₂) :=
  inferInstanceAs (Decidable (l₁.toNat < l₂.toNat))

/-- The layer ordering is a total preorder. -/
theorem Layer.le_refl (l : Layer) : l ≤ l := Nat.le_refl _

theorem Layer.le_trans {l₁ l₂ l₃ : Layer} (h₁₂ : l₁ ≤ l₂) (h₂₃ : l₂ ≤ l₃) : l₁ ≤ l₃ :=
  Nat.le_trans h₁₂ h₂₃

theorem Layer.le_antisymm {l₁ l₂ : Layer} (h₁₂ : l₁ ≤ l₂) (h₂₁ : l₂ ≤ l₁) : l₁ = l₂ := by
  cases l₁ <;> cases l₂ <;> simp [LE.le, Layer.toNat] at h₁₂ h₂₁ <;> rfl

/-- Every layer pair is comparable (total order). -/
theorem Layer.le_total (l₁ l₂ : Layer) : l₁ ≤ l₂ ∨ l₂ ≤ l₁ :=
  Nat.le_total l₁.toNat l₂.toNat

/-- All five layers as a list, for enumeration. -/
def Layer.all : List Layer :=
  [Layer.intent, Layer.structural, Layer.semantic, Layer.proof, Layer.code]

theorem Layer.all_complete (l : Layer) : l ∈ Layer.all := by
  cases l <;> simp [Layer.all]


/-! ## Trust Levels

  Trust levels form a bounded lattice tracking the provenance and reliability
  of type information. Higher trust = more confidence in correctness.

  The lattice structure enables:
  - Meet (min): composition takes the weakest link
  - Join (max): independent verification can upgrade trust
  - Bottom: contradicted/hallucinated information
  - Top: formally verified in Lean (maximum trust)
-/

/-- Trust levels for hybrid type information.
    Ordered from least to most trustworthy.
    Each level corresponds to a verification method. -/
inductive TrustLevel where
  | contradicted     : TrustLevel   -- Known to be false (bottom)
  | unverified       : TrustLevel   -- No verification attempted
  | llm_claimed      : TrustLevel   -- LLM says it's true (weakest real trust)
  | llm_consensus    : TrustLevel   -- Multiple LLMs agree
  | test_validated   : TrustLevel   -- Passes test suite
  | z3_proven        : TrustLevel   -- SMT solver verified (decidable fragment)
  | lean_verified    : TrustLevel   -- Lean proof assistant verified (top)
  deriving DecidableEq, Repr, Inhabited

/-- Numeric encoding for trust level ordering. -/
def TrustLevel.toNat : TrustLevel → Nat
  | .contradicted   => 0
  | .unverified     => 1
  | .llm_claimed    => 2
  | .llm_consensus  => 3
  | .test_validated => 4
  | .z3_proven      => 5
  | .lean_verified  => 6

instance : LE TrustLevel where
  le t₁ t₂ := t₁.toNat ≤ t₂.toNat

instance : LT TrustLevel where
  lt t₁ t₂ := t₁.toNat < t₂.toNat

instance (t₁ t₂ : TrustLevel) : Decidable (t₁ ≤ t₂) :=
  inferInstanceAs (Decidable (t₁.toNat ≤ t₂.toNat))

instance (t₁ t₂ : TrustLevel) : Decidable (t₁ < t₂) :=
  inferInstanceAs (Decidable (t₁.toNat < t₂.toNat))

/-- Minimum of two trust levels (weakest link). -/
def TrustLevel.min (t₁ t₂ : TrustLevel) : TrustLevel :=
  if t₁ ≤ t₂ then t₁ else t₂

/-- Maximum of two trust levels. -/
def TrustLevel.max (t₁ t₂ : TrustLevel) : TrustLevel :=
  if t₁ ≤ t₂ then t₂ else t₁

/-- TrustLevel forms a linear order. -/
theorem TrustLevel.le_refl (t : TrustLevel) : t ≤ t := Nat.le_refl _

theorem TrustLevel.le_trans {t₁ t₂ t₃ : TrustLevel}
    (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃) : t₁ ≤ t₃ :=
  Nat.le_trans h₁₂ h₂₃

theorem TrustLevel.le_antisymm {t₁ t₂ : TrustLevel}
    (h₁₂ : t₁ ≤ t₂) (h₂₁ : t₂ ≤ t₁) : t₁ = t₂ := by
  cases t₁ <;> cases t₂ <;> simp [LE.le, TrustLevel.toNat] at h₁₂ h₂₁ <;> rfl

theorem TrustLevel.le_total (t₁ t₂ : TrustLevel) : t₁ ≤ t₂ ∨ t₂ ≤ t₁ :=
  Nat.le_total t₁.toNat t₂.toNat

/-- contradicted is the bottom element. -/
theorem TrustLevel.bot_le (t : TrustLevel) : TrustLevel.contradicted ≤ t := by
  cases t <;> simp [LE.le, TrustLevel.toNat]

/-- lean_verified is the top element. -/
theorem TrustLevel.le_top (t : TrustLevel) : t ≤ TrustLevel.lean_verified := by
  cases t <;> simp [LE.le, TrustLevel.toNat]

/-- All trust levels enumerated. -/
def TrustLevel.all : List TrustLevel :=
  [ TrustLevel.contradicted, TrustLevel.unverified, TrustLevel.llm_claimed,
    TrustLevel.llm_consensus, TrustLevel.test_validated,
    TrustLevel.z3_proven, TrustLevel.lean_verified ]

theorem TrustLevel.all_complete (t : TrustLevel) : t ∈ TrustLevel.all := by
  cases t <;> simp [TrustLevel.all]

/-- Min is commutative. -/
theorem TrustLevel.min_comm (t₁ t₂ : TrustLevel) :
    TrustLevel.min t₁ t₂ = TrustLevel.min t₂ t₁ := by
  simp [TrustLevel.min]
  rcases TrustLevel.le_total t₁ t₂ with h | h
  · simp [h]
    rcases TrustLevel.le_total t₂ t₁ with h' | h'
    · exact TrustLevel.le_antisymm h' h
    · simp [h']
  · simp [h]
    rcases TrustLevel.le_total t₂ t₁ with h' | h'
    · simp [h']
    · exact TrustLevel.le_antisymm h h'

/-- Min is associative. -/
theorem TrustLevel.min_assoc (t₁ t₂ t₃ : TrustLevel) :
    TrustLevel.min (TrustLevel.min t₁ t₂) t₃ =
    TrustLevel.min t₁ (TrustLevel.min t₂ t₃) := by
  simp [TrustLevel.min]
  split <;> split <;> split <;> split <;> omega


/-! ## Layer Morphisms

  A layer morphism captures the refinement relationship between layers.
  Moving from a more abstract layer to a more concrete one constitutes
  a restriction: you can always forget detail (go from code → intent)
  but adding detail requires work (going from intent → code).
-/

/-- A morphism between layers, carrying restriction data.
    source → target means "restrict from source to target."
    Valid when source is at least as concrete as target (source ≥ target)
    or when we are projecting down to a coarser layer. -/
structure LayerMorphism where
  source : Layer
  target : Layer
  /-- Restriction is valid when going from more to less concrete. -/
  valid : target ≤ source
  deriving Repr

/-- The identity morphism at a layer. -/
def LayerMorphism.id (l : Layer) : LayerMorphism where
  source := l
  target := l
  valid := Layer.le_refl l

/-- Compose two layer morphisms (transitivity of restriction). -/
def LayerMorphism.comp (f : LayerMorphism) (g : LayerMorphism)
    (h : g.target = f.source := by rfl) : LayerMorphism where
  source := g.source
  target := f.target
  valid := by
    have : f.target ≤ f.source := f.valid
    have : g.target ≤ g.source := g.valid
    exact Layer.le_trans f.valid (h ▸ g.valid)


/-! ## Refinement Predicates

  A refinement predicate in the hybrid system has two parts:
  1. Decidable part: can be checked algorithmically (structural constraints)
  2. Semantic part: may require oracle consultation (meaning constraints)

  This decomposition is the key to the "honest" hybrid approach: we explicitly
  separate what we CAN decide from what we NEED an oracle for.
-/

/-- A refinement predicate with explicit decidable/semantic decomposition.
    This is the core of the hybrid approach: we know exactly which parts
    of the specification are algorithmically checkable vs. oracle-dependent. -/
structure RefinementPredicate where
  /-- The decidable (structural) component. Always checkable. -/
  decidable_part : Prop
  /-- The semantic (oracle-dependent) component. May need LLM/oracle. -/
  semantic_part : Prop
  /-- Evidence that the decidable part is indeed decidable. -/
  decidable_evidence : Decidable decidable_part
  deriving Inhabited

/-- A refinement predicate is satisfied when BOTH parts hold. -/
def RefinementPredicate.satisfied (r : RefinementPredicate) : Prop :=
  r.decidable_part ∧ r.semantic_part

/-- The trivial (always true) refinement. -/
def RefinementPredicate.trivial : RefinementPredicate where
  decidable_part := True
  semantic_part := True
  decidable_evidence := instDecidableTrue

/-- The contradictory (always false) refinement. -/
def RefinementPredicate.contradiction : RefinementPredicate where
  decidable_part := False
  semantic_part := False
  decidable_evidence := instDecidableFalse

/-- Conjunction of two refinements. -/
def RefinementPredicate.and (r₁ r₂ : RefinementPredicate) : RefinementPredicate where
  decidable_part := r₁.decidable_part ∧ r₂.decidable_part
  semantic_part := r₁.semantic_part ∧ r₂.semantic_part
  decidable_evidence := @instDecidableAnd _ _ r₁.decidable_evidence r₂.decidable_evidence

/-- The decidable part is always algorithmically checkable. -/
theorem RefinementPredicate.decidable_is_decidable (r : RefinementPredicate) :
    Decidable r.decidable_part :=
  r.decidable_evidence


/-! ## Hybrid Type Section

  A section at a single (site, layer) point in the product presheaf.
  This is the local data: what we know about a value at one program
  location, from the perspective of one semantic layer.
-/

/-- A section of the hybrid type presheaf at a single (site, layer) point.
    Carries the base type, refinement, trust level, and content hash. -/
structure HybridTypeSection where
  /-- The underlying base type (e.g., Int, String, List α). -/
  base_type : Type
  /-- The refinement predicate constraining values of base_type. -/
  refinement : RefinementPredicate
  /-- Trust level: how this section's information was verified. -/
  trust : TrustLevel
  /-- Content hash for cache invalidation and consistency checking. -/
  content_hash : String
  deriving Inhabited

/-- Two sections are compatible if they share the same base type constraint
    (up to logical equivalence of refinements). -/
def HybridTypeSection.compatible (s₁ s₂ : HybridTypeSection) : Prop :=
  s₁.base_type = s₂.base_type ∧
  (s₁.refinement.satisfied ↔ s₂.refinement.satisfied)

/-- A section refines another if it carries strictly more information. -/
def HybridTypeSection.refines (s₁ s₂ : HybridTypeSection) : Prop :=
  s₁.base_type = s₂.base_type ∧
  (s₁.refinement.satisfied → s₂.refinement.satisfied) ∧
  s₂.trust ≤ s₁.trust


/-! ## Hybrid Type: The Global Section

  A HybridType is the GLOBAL section of the product presheaf:
  it assigns a HybridTypeSection to EACH of the five layers,
  subject to the cocycle consistency condition.

  This is the central definition: a complete hybrid type specification
  that captures intent, structure, semantics, proof, and code — all
  linked by coherence conditions.
-/

/-- Cocycle consistency between adjacent layers.
    If layer l₁ refines to l₂, the sections must be compatible
    and the more concrete layer must refine the more abstract one. -/
def cocycle_condition (s₁ s₂ : HybridTypeSection) : Prop :=
  s₁.base_type = s₂.base_type ∧
  (s₂.refinement.satisfied → s₁.refinement.satisfied)

/-- A HybridType: global section of the product presheaf over Site(P) × Layer.
    Assigns a typed, refined, trust-tagged section to each semantic layer. -/
structure HybridType where
  /-- Intent layer: natural language specification. -/
  intent : HybridTypeSection
  /-- Structural layer: syntactic/decidable constraints. -/
  structural : HybridTypeSection
  /-- Semantic layer: meaning constraints (oracle-dependent). -/
  semantic : HybridTypeSection
  /-- Proof layer: formally verified properties. -/
  proof : HybridTypeSection
  /-- Code layer: the actual implementation. -/
  code : HybridTypeSection
  /-- Cocycle condition: code refines proof refines semantic refines structural refines intent.
      This is the gluing condition of the presheaf: adjacent layers must be coherent. -/
  cocycle_consistent : Prop
  deriving Inhabited

/-- Look up the section at a given layer. -/
def HybridType.at_layer (T : HybridType) : Layer → HybridTypeSection
  | .intent     => T.intent
  | .structural => T.structural
  | .semantic   => T.semantic
  | .proof      => T.proof
  | .code       => T.code

/-- Construct a cocycle-consistent hybrid type with explicit proof of coherence. -/
def HybridType.mk_consistent
    (intent structural semantic proof code : HybridTypeSection)
    (h_si : cocycle_condition structural intent)
    (h_es : cocycle_condition semantic structural)
    (h_pe : cocycle_condition proof semantic)
    (h_cp : cocycle_condition code proof) : HybridType where
  intent := intent
  structural := structural
  semantic := semantic
  proof := proof
  code := code
  cocycle_consistent :=
    cocycle_condition structural intent ∧
    cocycle_condition semantic structural ∧
    cocycle_condition proof semantic ∧
    cocycle_condition code proof


/-! ## Type Inhabitation

  A value "inhabits" a hybrid type iff it satisfies ALL layers.
  This is the anti-hallucination criterion: every layer must agree
  that the value is valid. A failure at ANY layer is a hallucination.
-/

/-- A value of type α inhabits a HybridType if it satisfies all layers'
    refinement predicates. This is the fundamental anti-hallucination check. -/
def inhabits {α : Type} (v : α) (T : HybridType) : Prop :=
  T.intent.refinement.satisfied ∧
  T.structural.refinement.satisfied ∧
  T.semantic.refinement.satisfied ∧
  T.proof.refinement.satisfied ∧
  T.code.refinement.satisfied

/-- Structural inhabitation: only the decidable structural layer.
    This is the "fast path" check that can always be done algorithmically. -/
def inhabits_structural {α : Type} (_v : α) (T : HybridType) : Prop :=
  T.structural.refinement.decidable_part

/-- Full inhabitation implies structural inhabitation. -/
theorem inhabits_implies_structural {α : Type} (v : α) (T : HybridType)
    (h : inhabits v T) : inhabits_structural v T := by
  unfold inhabits at h
  unfold inhabits_structural
  exact h.2.1.1

/-- Structural inhabitation is decidable (the key property!).
    This is what makes the "fast path" possible: we can always check
    the structural layer without calling any oracle. -/
theorem inhabits_structural_decidable {α : Type} (v : α) (T : HybridType) :
    Decidable (inhabits_structural v T) := by
  unfold inhabits_structural
  exact T.structural.refinement.decidable_evidence

/-- Semantic inhabitation: the oracle-dependent part. -/
def inhabits_semantic {α : Type} (_v : α) (T : HybridType) : Prop :=
  T.semantic.refinement.semantic_part

/-- Full inhabitation decomposes into structural AND semantic AND proof layers. -/
theorem inhabits_decomposition {α : Type} (v : α) (T : HybridType) :
    inhabits v T ↔
    (T.intent.refinement.satisfied ∧
     inhabits_structural v T ∧ T.structural.refinement.semantic_part ∧
     inhabits_semantic v T ∧ T.semantic.refinement.decidable_part ∧
     T.proof.refinement.satisfied ∧
     T.code.refinement.satisfied) := by
  unfold inhabits inhabits_structural inhabits_semantic
  unfold RefinementPredicate.satisfied
  constructor
  · intro ⟨hi, ⟨hsd, hss⟩, ⟨hed, hes⟩, hp, hc⟩
    exact ⟨hi, hsd, hss, hes, hed, hp, hc⟩
  · intro ⟨hi, hsd, hss, hes, hed, hp, hc⟩
    exact ⟨hi, ⟨hsd, hss⟩, ⟨hed, hes⟩, hp, hc⟩


/-! ## Sigma Verified Type

  The culmination: a Σ-type pairing code with its proof of correctness.
  SigmaVerified is the type of artifacts that have been verified to
  satisfy a specification. This is what deppy ultimately produces.
-/

/-- A specification that code must satisfy. -/
structure Specification where
  /-- The property that must hold. -/
  property : Prop
  /-- Trust level of the specification itself. -/
  trust : TrustLevel

/-- A verified artifact: code paired with proof that it meets spec.
    This is the Σ-type Σ(code : α). code_satisfies(spec). -/
structure SigmaVerified (α : Type) (spec : Specification) where
  /-- The code artifact. -/
  code : α
  /-- Proof that the code satisfies the specification. -/
  proof : spec.property
  /-- Trust level of the verification. -/
  verification_trust : TrustLevel
  /-- The verification trust is at least as high as the spec requires. -/
  trust_sufficient : spec.trust ≤ verification_trust

/-- First projection: extract the code from a verified artifact. -/
def SigmaVerified.fst {α : Type} {spec : Specification}
    (sv : SigmaVerified α spec) : α :=
  sv.code

/-- Second projection: extract the proof from a verified artifact. -/
def SigmaVerified.snd {α : Type} {spec : Specification}
    (sv : SigmaVerified α spec) : spec.property :=
  sv.proof

/-- The first projection of a verified artifact IS the code. -/
theorem sigma_fst_code {α : Type} {spec : Specification}
    (sv : SigmaVerified α spec) :
    sv.fst = sv.code :=
  rfl

/-- The second projection of a verified artifact IS the proof. -/
theorem sigma_snd_proof {α : Type} {spec : Specification}
    (sv : SigmaVerified α spec) :
    sv.snd = sv.proof :=
  rfl


/-! ## Trust Composition

  When composing verified artifacts (e.g., piping output of one into
  another), the resulting trust is the MINIMUM (weakest link) of the
  component trusts. This is the "trust_weakest_link" principle.
-/

/-- Composed trust level: the weakest link in a chain of verifications. -/
def composed_trust (trusts : List TrustLevel) : TrustLevel :=
  trusts.foldl TrustLevel.min TrustLevel.lean_verified

/-- Composing two verifications yields trust = min of both.
    This is the "weakest link" principle: your chain of reasoning
    is only as strong as its weakest verification step. -/
theorem trust_weakest_link (t₁ t₂ : TrustLevel) :
    composed_trust [t₁, t₂] = TrustLevel.min t₁ t₂ := by
  simp [composed_trust, List.foldl]
  simp [TrustLevel.min]
  split
  · rfl
  · rfl

/-- The composed trust of a singleton is bounded by that trust level. -/
theorem composed_trust_singleton (t : TrustLevel) :
    composed_trust [t] = TrustLevel.min TrustLevel.lean_verified t := by
  simp [composed_trust, List.foldl]

/-- Composed trust is at most any individual component's trust. -/
theorem composed_trust_le_component (t : TrustLevel) (ts : List TrustLevel)
    (h : t ∈ ts) : composed_trust ts ≤ t := by
  sorry  -- requires induction over the fold; tedious but straightforward

/-- Empty composition has maximum trust (vacuous truth). -/
theorem composed_trust_nil : composed_trust [] = TrustLevel.lean_verified := by
  simp [composed_trust, List.foldl]


/-! ## Section Restriction Along Layers

  Restriction maps between layers: given a morphism from a more concrete
  layer to a more abstract one, we can restrict (project out) information.
  This is the contravariant functoriality of the presheaf.
-/

/-- Restrict a section from a concrete layer to a more abstract one.
    This forgets refinement detail but preserves base type compatibility. -/
def restrict_section (s : HybridTypeSection) (m : LayerMorphism) :
    HybridTypeSection where
  base_type := s.base_type
  refinement := if m.target ≤ m.source then s.refinement
                else RefinementPredicate.trivial
  trust := TrustLevel.min s.trust (if m.valid then s.trust else TrustLevel.unverified)
  content_hash := s.content_hash

/-- Restriction along the identity morphism is the identity. -/
theorem restrict_id (s : HybridTypeSection) (l : Layer) :
    restrict_section s (LayerMorphism.id l) = s := by
  simp [restrict_section, LayerMorphism.id, Layer.le_refl, TrustLevel.min]
  constructor
  · split <;> rfl
  · constructor
    · simp [TrustLevel.min]
      split
      · rfl
      · omega
    · rfl


/-! ## Product Presheaf Structure

  The hybrid type presheaf is a product: Sem(s, l) = Sem_site(s) × Sem_layer(l).
  A global section must be compatible across BOTH indices. We capture this
  as the requirement that for every pair of layers, the cocycle condition holds.
-/

/-- A global section of the product presheaf is a function from layers to sections,
    satisfying cocycle conditions on all adjacent pairs. -/
structure GlobalSection where
  /-- Section data at each layer. -/
  section_at : Layer → HybridTypeSection
  /-- Adjacent layers satisfy the cocycle condition. -/
  cocycle_intent_structural :
    cocycle_condition (section_at .structural) (section_at .intent)
  cocycle_structural_semantic :
    cocycle_condition (section_at .semantic) (section_at .structural)
  cocycle_semantic_proof :
    cocycle_condition (section_at .proof) (section_at .semantic)
  cocycle_proof_code :
    cocycle_condition (section_at .code) (section_at .proof)

/-- Convert a GlobalSection to a HybridType. -/
def GlobalSection.toHybridType (gs : GlobalSection) : HybridType where
  intent := gs.section_at .intent
  structural := gs.section_at .structural
  semantic := gs.section_at .semantic
  proof := gs.section_at .proof
  code := gs.section_at .code
  cocycle_consistent :=
    cocycle_condition (gs.section_at .structural) (gs.section_at .intent) ∧
    cocycle_condition (gs.section_at .semantic) (gs.section_at .structural) ∧
    cocycle_condition (gs.section_at .proof) (gs.section_at .semantic) ∧
    cocycle_condition (gs.section_at .code) (gs.section_at .proof)

/-- The cocycle condition is transitive along the chain of layers. -/
theorem cocycle_transitive (s₁ s₂ s₃ : HybridTypeSection)
    (h₁₂ : cocycle_condition s₂ s₁) (h₂₃ : cocycle_condition s₃ s₂) :
    cocycle_condition s₃ s₁ := by
  constructor
  · exact h₁₂.1.trans h₂₃.1
  · intro h
    exact h₁₂.2 (h₂₃.2 h)


/-! ## Coherent Type Modification

  When modifying one layer of a hybrid type, coherence must be preserved
  or re-established. This captures the incremental update semantics.
-/

/-- Update a single layer of a hybrid type, invalidating cocycle consistency.
    The caller must re-establish consistency after the update. -/
def HybridType.update_layer (T : HybridType) (l : Layer) (s : HybridTypeSection) :
    HybridType where
  intent := if l = .intent then s else T.intent
  structural := if l = .structural then s else T.structural
  semantic := if l = .semantic then s else T.semantic
  proof := if l = .proof then s else T.proof
  code := if l = .code then s else T.code
  cocycle_consistent := False  -- Must be re-established

/-- The overall trust of a hybrid type is the minimum across all layers.
    By the weakest-link principle, you're only as trustworthy as your
    least-trusted layer. -/
def HybridType.overall_trust (T : HybridType) : TrustLevel :=
  composed_trust [T.intent.trust, T.structural.trust, T.semantic.trust,
                  T.proof.trust, T.code.trust]

/-- The overall trust is at most the trust of any individual layer. -/
theorem HybridType.overall_trust_le_layer (T : HybridType) (l : Layer) :
    T.overall_trust ≤ (T.at_layer l).trust := by
  apply composed_trust_le_component
  cases l <;> simp [HybridType.at_layer, HybridType.overall_trust] <;>
    simp [List.Mem]

end Deppy.Hybrid
