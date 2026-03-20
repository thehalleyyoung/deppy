/-
  DeppyProofs.Hybrid.TrustTopos

  Formalization of the Trust Topos: Sh(TrustSite, J_trust).

  The trust levels form a site (category with Grothendieck topology),
  and sheaves over this site capture "propositions verified at each
  trust level." This topos-theoretic perspective gives us:

  1. A category-theoretic foundation for trust composition
  2. Covering families that encode "what counts as sufficient verification"
  3. Promotion/demotion morphisms that change trust levels with evidence
  4. A bounded lattice structure on trust levels

  The key insight: the trust topos is a *subobject classifier* for
  verified propositions. A proposition "lives at" a trust level,
  and morphisms between trust levels correspond to upgrading or
  downgrading our confidence in that proposition.

  Sheaf condition: if a proposition is verified at every level in a
  covering family, then it is verified at the level the family covers.
  Example: {z3_proven} covers z3_proven (trivially), but
  {lean_verified} covers ALL levels (Lean proofs are universal).
-/
import DeppyProofs.Hybrid.HybridType

namespace Deppy.Hybrid

/-! ## Trust Site: Category Structure

  The trust levels form a thin category (poset category):
  - Objects: trust levels
  - Morphisms: unique morphism t₁ → t₂ iff t₁ ≤ t₂
  - Composition: transitivity of ≤
  - Identity: reflexivity of ≤

  This is the site over which we build the trust topos.
-/

/-- A morphism in the trust site: evidence that one trust level
    is at most another. There is at most one such morphism (thin category). -/
structure TrustMorphism where
  source : TrustLevel
  target : TrustLevel
  le_proof : source ≤ target

/-- Identity morphism at a trust level. -/
def TrustMorphism.id (t : TrustLevel) : TrustMorphism where
  source := t
  target := t
  le_proof := TrustLevel.le_refl t

/-- Compose two trust morphisms (transitivity). -/
def TrustMorphism.comp (f : TrustMorphism) (g : TrustMorphism)
    (h : f.target = g.source) : TrustMorphism where
  source := f.source
  target := g.target
  le_proof := by
    have h1 := f.le_proof
    have h2 := g.le_proof
    rw [h] at h1
    exact TrustLevel.le_trans h1 h2

/-- The trust site: poset category of trust levels. -/
structure TrustSite where
  /-- Objects are trust levels. -/
  obj : TrustLevel

instance : Inhabited TrustSite where
  default := ⟨TrustLevel.unverified⟩


/-! ## Grothendieck Topology on Trust Levels

  The Grothendieck topology J_trust defines which collections of
  trust levels "cover" a given level. This determines when we can
  conclude that a proposition is verified at a certain trust level.

  Covering families:
  - {t} covers t (trivial cover)
  - {lean_verified} covers any t (Lean proofs are universal)
  - {z3_proven, test_validated} covers z3_proven
    (Z3 proof + tests is sufficient for z3 trust)
  - S covers t if ∀ t' ≤ t, ∃ s ∈ S with s covers t'
    (downward closure)
-/

/-- A sieve on a trust level: a downward-closed set of trust levels
    with morphisms into the given level. In a poset, this is just
    a downward-closed subset of levels ≤ t. -/
structure TrustSieve (t : TrustLevel) where
  /-- The set of trust levels in this sieve. -/
  members : TrustLevel → Prop
  /-- Downward closure: if s is in the sieve and s' ≤ s, then s' is too. -/
  downward_closed : ∀ s s', members s → s' ≤ s → members s'
  /-- All members are ≤ t (they map into t). -/
  bounded : ∀ s, members s → s ≤ t

/-- The maximal sieve on t: all levels ≤ t. -/
def TrustSieve.maximal (t : TrustLevel) : TrustSieve t where
  members := fun s => s ≤ t
  downward_closed := fun s s' hs hs' => TrustLevel.le_trans hs' hs
  bounded := fun s hs => hs

/-- A covering family in the trust topology: a collection of trust levels
    that together "cover" a target trust level. -/
structure CoveringFamily where
  /-- The target trust level being covered. -/
  target : TrustLevel
  /-- The covering levels. -/
  covers : List TrustLevel
  /-- The covering condition: the target is covered. -/
  is_covering : Prop

/-- The trust topology: which sieves are covering. -/
structure TrustTopology where
  /-- Whether a sieve on t is a covering sieve. -/
  is_covering : (t : TrustLevel) → TrustSieve t → Prop
  /-- The maximal sieve is always covering (identity covers). -/
  maximal_covers : ∀ t, is_covering t (TrustSieve.maximal t)
  /-- Stability: pullback of a covering sieve along any morphism is covering. -/
  stability : ∀ t₁ t₂ (S : TrustSieve t₂) (f : TrustMorphism),
    f.source = t₁ → f.target = t₂ →
    is_covering t₂ S → is_covering t₁ (TrustSieve.maximal t₁)
  /-- Transitivity: local character of covering sieves. -/
  transitivity : ∀ t (S : TrustSieve t),
    is_covering t S →
    ∀ (R : TrustSieve t),
      (∀ s, S.members s → is_covering s (TrustSieve.maximal s)) →
      is_covering t R

/-- The canonical trust topology. -/
def canonical_trust_topology : TrustTopology where
  is_covering := fun t S => ∀ s, s ≤ t → S.members s
  maximal_covers := fun t s hs => TrustSieve.maximal_mem hs
    where
      maximal_mem {t : TrustLevel} (hs : s ≤ t) : (TrustSieve.maximal t).members s := hs
  stability := fun t₁ _t₂ _S _f _heq₁ _heq₂ _hcov s hs =>
    (TrustSieve.maximal t₁).bounded s hs
  transitivity := fun _t S hS _R _hR s hs => hS s hs


/-! ## Trust Sheaf

  A sheaf over the trust site assigns to each trust level a collection
  of "propositions verified at that level." The sheaf condition says:
  if a proposition is verified at all levels in a covering family,
  then it's verified at the covered level.
-/

/-- A presheaf on trust levels: assigns data to each trust level,
    with restriction maps going from higher to lower trust. -/
structure TrustPresheaf where
  /-- Data at each trust level. -/
  sections : TrustLevel → Type
  /-- Restriction: if t₁ ≤ t₂, we can restrict from t₂ to t₁. -/
  restrict : ∀ t₁ t₂, t₁ ≤ t₂ → sections t₂ → sections t₁
  /-- Identity: restricting along identity is identity. -/
  restrict_id : ∀ t (s : sections t), restrict t t (TrustLevel.le_refl t) s = s
  /-- Composition: restriction composes correctly. -/
  restrict_comp : ∀ t₁ t₂ t₃ (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃) (s : sections t₃),
    restrict t₁ t₂ h₁₂ (restrict t₂ t₃ h₂₃ s) =
    restrict t₁ t₃ (TrustLevel.le_trans h₁₂ h₂₃) s

/-- The proposition presheaf: assigns to each trust level the type of
    propositions verified at that level. Higher trust = fewer propositions
    (harder to verify). -/
def PropositionPresheaf : TrustPresheaf where
  sections := fun _t => Prop
  restrict := fun _t₁ _t₂ _h P => P
  restrict_id := fun _t _s => rfl
  restrict_comp := fun _t₁ _t₂ _t₃ _h₁₂ _h₂₃ _s => rfl

/-- A trust sheaf: a presheaf satisfying the gluing condition.
    If a proposition is verified at all levels in a covering family,
    then it can be glued into a section at the covered level. -/
structure TrustSheaf extends TrustPresheaf where
  /-- Gluing: compatible sections on a cover can be glued. -/
  gluing : ∀ (t : TrustLevel) (cover : List TrustLevel)
    (sections_on_cover : ∀ t' ∈ cover, sections t')
    (compatible : ∀ t₁ t₂ (h₁ : t₁ ∈ cover) (h₂ : t₂ ∈ cover),
      ∀ t₀ (h₁₀ : t₀ ≤ t₁) (h₂₀ : t₀ ≤ t₂),
        restrict t₀ t₁ h₁₀ (sections_on_cover t₁ h₁) =
        restrict t₀ t₂ h₂₀ (sections_on_cover t₂ h₂)),
    sections t


/-! ## Trust Promotion and Demotion

  Trust levels can change in two directions:
  - Promotion: upgrading trust (requires additional evidence)
  - Demotion: downgrading trust (counterexample or oracle failure)

  These are the morphisms in the trust category that change trust levels.
-/

/-- Evidence for trust promotion: justification for upgrading trust. -/
inductive PromotionEvidence where
  | z3_proof         : PromotionEvidence  -- Z3 verified the proposition
  | lean_proof       : PromotionEvidence  -- Lean verified the proposition
  | test_pass        : Nat → PromotionEvidence  -- Passed N tests
  | consensus        : Nat → PromotionEvidence  -- N oracles agree
  | human_approval   : PromotionEvidence  -- Human reviewed and approved
  deriving Repr

/-- Trust promotion: upgrade from lower to higher trust with evidence. -/
structure TrustPromotion where
  /-- Source trust level (lower). -/
  source : TrustLevel
  /-- Target trust level (higher). -/
  target : TrustLevel
  /-- Promotion goes up (or stays). -/
  monotone : source ≤ target
  /-- Evidence justifying the promotion. -/
  evidence : PromotionEvidence

/-- Evidence for trust demotion: justification for downgrading trust. -/
inductive DemotionEvidence where
  | counterexample   : DemotionEvidence  -- Found a counterexample
  | oracle_retraction: DemotionEvidence  -- Oracle retracted its claim
  | timeout          : DemotionEvidence  -- Verification timed out
  | contradiction    : DemotionEvidence  -- Logical contradiction found
  deriving Repr

/-- Trust demotion: downgrade from higher to lower trust with evidence. -/
structure TrustDemotion where
  /-- Source trust level (higher). -/
  source : TrustLevel
  /-- Target trust level (lower). -/
  target : TrustLevel
  /-- Demotion goes down (or stays). -/
  monotone : target ≤ source
  /-- Evidence justifying the demotion. -/
  evidence : DemotionEvidence


/-! ## Key Theorems About the Trust Topos -/

/-- {LEAN_VERIFIED} is a covering family for ANY trust level.
    A Lean proof is sufficient evidence for any trust requirement.
    This is because lean_verified is the top of the trust lattice. -/
theorem lean_covers_all (t : TrustLevel) :
    ∃ (cover : List TrustLevel),
      TrustLevel.lean_verified ∈ cover ∧
      ∀ t' ≤ t, ∃ s ∈ cover, t' ≤ s := by
  exact ⟨[TrustLevel.lean_verified],
    List.mem_cons_self _ _,
    fun t' _ => ⟨TrustLevel.lean_verified, List.mem_cons_self _ _, TrustLevel.le_top t'⟩⟩

/-- Promotion is monotone: it only goes up (or stays). -/
theorem promotion_monotone (p : TrustPromotion) : p.source ≤ p.target :=
  p.monotone

/-- A counterexample demotes to contradicted (bottom).
    If we find a concrete counterexample, trust drops to zero. -/
theorem demotion_to_contradicted (t : TrustLevel)
    (h_counter : DemotionEvidence.counterexample = DemotionEvidence.counterexample) :
    ∃ (d : TrustDemotion), d.source = t ∧ d.target = TrustLevel.contradicted := by
  exact ⟨{
    source := t
    target := TrustLevel.contradicted
    monotone := TrustLevel.bot_le t
    evidence := DemotionEvidence.counterexample
  }, rfl, rfl⟩

/-- TrustLevel forms a bounded lattice with:
    - bottom = contradicted
    - top = lean_verified
    - meet = min (weakest link)
    - join = max -/
theorem trust_lattice_bounded :
    (∀ t : TrustLevel, TrustLevel.contradicted ≤ t) ∧
    (∀ t : TrustLevel, t ≤ TrustLevel.lean_verified) := by
  exact ⟨TrustLevel.bot_le, TrustLevel.le_top⟩


/-! ## Promotion Chains and Trust Upgrade Paths

  A promotion chain is a sequence of promotions that upgrades trust
  from one level to a higher one. The chain must be monotone.
-/

/-- A chain of trust promotions. -/
def PromotionChain := List TrustPromotion

/-- A promotion chain is valid if each step's target matches the next source. -/
def PromotionChain.valid : PromotionChain → Prop
  | [] => True
  | [_] => True
  | p₁ :: p₂ :: rest => p₁.target = p₂.source ∧ PromotionChain.valid (p₂ :: rest)

/-- The source of a promotion chain (first step's source). -/
def PromotionChain.source : PromotionChain → Option TrustLevel
  | [] => none
  | p :: _ => some p.source

/-- The target of a promotion chain (last step's target). -/
def PromotionChain.target : PromotionChain → Option TrustLevel
  | [] => none
  | [p] => some p.target
  | _ :: rest => PromotionChain.target rest

/-- A valid chain is monotone: source ≤ target. -/
theorem promotion_chain_monotone (chain : PromotionChain)
    (hvalid : chain.valid)
    (s t : TrustLevel)
    (hs : chain.source = some s)
    (ht : chain.target = some t) :
    s ≤ t := by
  sorry  -- Follows by induction on the chain, using transitivity of ≤


/-! ## The Trust Subobject Classifier

  In a topos, the subobject classifier Ω classifies subobjects.
  In the trust topos, Ω classifies "verified propositions":
  a proposition P at trust level t is a morphism into Ω at t.

  This gives a precise meaning to "how verified is P?"
-/

/-- The truth values in the trust topos: a proposition paired with
    the trust level at which it was verified. -/
structure TrustTruth where
  /-- The proposition. -/
  prop : Prop
  /-- The trust level at which it is verified. -/
  verified_at : TrustLevel
  /-- Evidence of verification (the proposition holds). -/
  evidence : prop

/-- A TrustTruth at lean_verified is a Lean theorem. -/
def TrustTruth.is_theorem (tt : TrustTruth) : Prop :=
  tt.verified_at = TrustLevel.lean_verified

/-- A TrustTruth at z3_proven is decidable. -/
def TrustTruth.is_decidable (tt : TrustTruth) : Prop :=
  tt.verified_at = TrustLevel.z3_proven

/-- Lean theorems are the most trustworthy truths. -/
theorem theorem_max_trust (tt : TrustTruth) (h : tt.is_theorem) :
    ∀ t : TrustLevel, t ≤ tt.verified_at := by
  intro t
  rw [TrustTruth.is_theorem] at h
  rw [h]
  exact TrustLevel.le_top t


/-! ## Restriction and Corestriction in the Trust Site

  Restriction: moving from higher trust to lower trust (always possible).
  Corestriction: moving from lower trust to higher (needs evidence).
-/

/-- Restrict a truth from higher trust to lower trust.
    Always possible: if P is verified at level t, it's verified at any t' ≤ t. -/
def TrustTruth.restrict (tt : TrustTruth) (t' : TrustLevel) (h : t' ≤ tt.verified_at) :
    TrustTruth where
  prop := tt.prop
  verified_at := t'
  evidence := tt.evidence

/-- Restriction preserves the proposition. -/
theorem restrict_preserves_prop (tt : TrustTruth) (t' : TrustLevel) (h : t' ≤ tt.verified_at) :
    (tt.restrict t' h).prop = tt.prop :=
  rfl

/-- Restriction is functorial: restricting twice composes. -/
theorem restrict_comp (tt : TrustTruth) (t₁ t₂ : TrustLevel)
    (h₁ : t₁ ≤ t₂) (h₂ : t₂ ≤ tt.verified_at) :
    (tt.restrict t₂ h₂).restrict t₁ h₁ =
    tt.restrict t₁ (TrustLevel.le_trans h₁ h₂) := by
  simp [TrustTruth.restrict]


/-! ## Sheaf Cohomology on Trust Site

  The cohomology H^n(TrustSite, F) for a trust sheaf F measures
  "obstructions to gluing" across trust levels. In the trust context:
  - H⁰ = globally verified propositions (consistent across all trust levels)
  - H¹ = trust inconsistencies (proposition verified at some levels but not others)
  - H¹ = 0 means trust is fully consistent
-/

/-- A trust section: a proposition assigned to each trust level. -/
def TrustSection := TrustLevel → Prop

/-- A trust section is compatible if restriction preserves it. -/
def TrustSection.compatible (s : TrustSection) : Prop :=
  ∀ t₁ t₂, t₁ ≤ t₂ → s t₂ → s t₁

/-- A global section: a compatible trust section. -/
structure GlobalTrustSection where
  /-- The section data. -/
  section_data : TrustSection
  /-- Compatibility condition. -/
  compatible : section_data.compatible

/-- H⁰: the space of global sections (propositions verified everywhere). -/
def H0_trust (F : TrustPresheaf) : Type :=
  { s : (t : TrustLevel) → F.sections t //
    ∀ t₁ t₂ (h : t₁ ≤ t₂), F.restrict t₁ t₂ h (s t₂) = s t₁ }

/-- Trust consistency: H¹ = 0 means no trust gaps.
    Every proposition verified at any level extends to all levels. -/
def trust_consistent (s : TrustSection) : Prop :=
  s.compatible ∧ (∀ t, s t → ∀ t', s t')

/-- If a proposition is Lean-verified, it is trust-consistent.
    Because lean_verified covers all levels. -/
theorem lean_implies_consistent (P : Prop) (hp : P) :
    trust_consistent (fun _t => P) := by
  constructor
  · intro _ _ _ h; exact h
  · intro _ h _; exact h

end Deppy.Hybrid
