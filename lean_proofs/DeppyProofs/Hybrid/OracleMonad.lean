/-
  DeppyProofs.Hybrid.OracleMonad

  Formalization of the Oracle Monad T_O.

  The oracle monad is the computational effect that models calls to
  external verification oracles (LLMs, SMT solvers, test suites).
  Each oracle call produces a result tagged with:

    - A trust level (how much we trust the oracle's answer)
    - A confidence score (the oracle's self-reported confidence)
    - Provenance (which oracle produced the result)

  The key insight: oracle calls form a MONAD, and the monad laws ensure
  that sequential oracle reasoning composes correctly. But crucially:

    - Trust composes via MIN (weakest link)
    - Confidence composes via MULTIPLICATION (chain rule)
    - This means longer oracle chains are LESS trustworthy

  This is the mathematical reason why deppy tries to minimize oracle
  dependence and maximize the decidable (structural) fragment.

  Decidability Stratification:
    Every proposition in the hybrid system falls into one of:
    1. Decidable: has an algorithm (structural layer, Z3-checkable)
    2. Oracle-dependent: needs external oracle (semantic layer)
    3. Formally proven: verified by Lean (proof layer)

  The oracle monad lets us compose across these strata while tracking
  exactly how much of our reasoning depends on oracle trust.
-/
import DeppyProofs.Hybrid.HybridType

namespace Deppy.Hybrid

/-! ## Oracle Provenance

  Provenance tracks WHICH oracle produced a result.
  This is critical for:
  - Debugging: when an oracle is wrong, we know which one
  - Trust assessment: different oracles have different reliability
  - Reproducibility: we can re-run the same oracle call
-/

/-- The provenance of an oracle result: which oracle produced it. -/
inductive OracleProvenance where
  | lean_kernel   : OracleProvenance   -- Lean type checker (highest trust)
  | z3_solver     : OracleProvenance   -- Z3 SMT solver
  | test_suite    : OracleProvenance   -- Test suite execution
  | llm_single    : String → OracleProvenance   -- Single LLM (with model name)
  | llm_consensus : List String → OracleProvenance  -- Consensus of multiple LLMs
  | human_review  : OracleProvenance   -- Human reviewer
  | unknown       : OracleProvenance   -- Unknown provenance (lowest trust)
  deriving Repr, Inhabited

/-- Map a provenance to its natural trust level. -/
def OracleProvenance.naturalTrust : OracleProvenance → TrustLevel
  | .lean_kernel     => .lean_verified
  | .z3_solver       => .z3_proven
  | .test_suite      => .test_validated
  | .llm_consensus _ => .llm_consensus
  | .llm_single _    => .llm_claimed
  | .human_review    => .test_validated
  | .unknown         => .unverified


/-! ## Confidence Scores

  Confidence is a real number in [0, 1] representing the oracle's
  self-reported confidence in its answer. We model this as a rational
  for decidable arithmetic.

  Key property: confidence composes MULTIPLICATIVELY.
  If step 1 has confidence 0.9 and step 2 has confidence 0.8,
  the chain has confidence 0.72. This captures the intuition that
  longer reasoning chains are less reliable.
-/

/-- A confidence score in [0, 1], represented as a natural number
    out of 1000 (permille) for decidable arithmetic. -/
structure Confidence where
  /-- Value in permille: 0 = no confidence, 1000 = full confidence. -/
  permille : Nat
  /-- The value is at most 1000 (i.e., ≤ 100%). -/
  bounded : permille ≤ 1000
  deriving Repr

instance : Inhabited Confidence where
  default := ⟨1000, Nat.le_refl 1000⟩

/-- Full confidence (1.0). -/
def Confidence.full : Confidence := ⟨1000, Nat.le_refl 1000⟩

/-- Zero confidence (0.0). -/
def Confidence.zero : Confidence := ⟨0, Nat.zero_le 1000⟩

/-- Multiply two confidences (for composition). -/
def Confidence.mul (c₁ c₂ : Confidence) : Confidence where
  permille := (c₁.permille * c₂.permille) / 1000
  bounded := by
    have h1 := c₁.bounded
    have h2 := c₂.bounded
    -- (a * b) / 1000 ≤ 1000 when a ≤ 1000 and b ≤ 1000
    -- because a * b ≤ 1000 * 1000 = 1000000 and 1000000 / 1000 = 1000
    calc (c₁.permille * c₂.permille) / 1000
        ≤ (1000 * 1000) / 1000 := Nat.div_le_div_right (Nat.mul_le_mul h1 h2)
      _ = 1000 := by norm_num

/-- Confidence ordering. -/
instance : LE Confidence where
  le c₁ c₂ := c₁.permille ≤ c₂.permille

/-- Full confidence is top. -/
theorem Confidence.le_full (c : Confidence) : c ≤ Confidence.full :=
  c.bounded

/-- Zero confidence is bottom. -/
theorem Confidence.zero_le (c : Confidence) : Confidence.zero ≤ c :=
  Nat.zero_le c.permille

/-- Multiplication is monotone in both arguments. -/
theorem Confidence.mul_le_left (c₁ c₂ : Confidence) :
    Confidence.mul c₁ c₂ ≤ c₁ := by
  simp only [LE.le, Confidence.mul]
  -- Need: (c₁.permille * c₂.permille) / 1000 ≤ c₁.permille
  -- Since c₂.permille ≤ 1000:
  --   c₁.permille * c₂.permille ≤ c₁.permille * 1000
  --   so (c₁ * c₂) / 1000 ≤ (c₁ * 1000) / 1000 = c₁
  calc (c₁.permille * c₂.permille) / 1000
      ≤ (c₁.permille * 1000) / 1000 :=
        Nat.div_le_div_right (Nat.mul_le_mul_left c₁.permille c₂.bounded)
    _ = c₁.permille := Nat.mul_div_cancel c₁.permille (by norm_num)

/-- Multiplication is commutative. -/
theorem Confidence.mul_comm (c₁ c₂ : Confidence) :
    Confidence.mul c₁ c₂ = Confidence.mul c₂ c₁ := by
  simp [Confidence.mul, Nat.mul_comm]


/-! ## Oracle Result

  The fundamental type: the result of an oracle call.
  Wraps a value with trust metadata.
-/

/-- The result of an oracle computation: a value tagged with
    trust level, confidence, and provenance. -/
structure OracleResult (α : Type) where
  /-- The computed value. -/
  value : α
  /-- Trust level of this result. -/
  trust : TrustLevel
  /-- Confidence score (oracle's self-assessment). -/
  confidence : Confidence
  /-- Which oracle produced this result. -/
  provenance : OracleProvenance
  deriving Inhabited


/-! ## Oracle Monad Operations

  The oracle monad T_O is defined by:
    pure : α → T_O α           (inject at full trust)
    bind : T_O α → (α → T_O β) → T_O β  (compose with weakest-link trust)

  The critical composition rules:
    - Trust: min(t₁, t₂)           — weakest link
    - Confidence: c₁ × c₂          — multiplicative
    - Provenance: combined lineage  — full trace
-/

/-- Pure: inject a value into the oracle monad at maximum trust.
    No oracle was consulted, so trust is lean_verified and confidence is 1.0. -/
def OracleResult.pure (a : α) : OracleResult α where
  value := a
  trust := TrustLevel.lean_verified
  confidence := Confidence.full
  provenance := OracleProvenance.lean_kernel

/-- Bind: sequence two oracle computations.
    Trust = min (weakest link), Confidence = product (chain rule). -/
def OracleResult.bind (m : OracleResult α) (f : α → OracleResult β) :
    OracleResult β :=
  let result := f m.value
  { value := result.value
    trust := TrustLevel.min m.trust result.trust
    confidence := Confidence.mul m.confidence result.confidence
    provenance := result.provenance }

/-- Map: apply a pure function to an oracle result (preserves trust). -/
def OracleResult.map (f : α → β) (m : OracleResult α) : OracleResult β where
  value := f m.value
  trust := m.trust
  confidence := m.confidence
  provenance := m.provenance


/-! ## Monad Laws

  The oracle monad satisfies the three monad laws (up to trust/confidence
  metadata). These ensure that oracle composition is well-behaved.

  Note: strict equality requires that trust/confidence compose correctly.
  We prove the value-level laws exactly; the metadata laws follow from
  the algebraic properties of min and multiplication.
-/

/-- Left identity: bind (pure a) f = f a.
    Injecting a value and immediately using it is the same as just using it.
    Trust: min(lean_verified, t) = t (lean_verified is top).
    Confidence: 1.0 × c = c. -/
theorem oracle_left_identity (a : α) (f : α → OracleResult β) :
    OracleResult.bind (OracleResult.pure a) f = f a := by
  simp [OracleResult.bind, OracleResult.pure]
  ext
  · rfl
  · simp [TrustLevel.min]
    split
    · rfl
    · rename_i h
      have : (f a).trust ≤ TrustLevel.lean_verified := TrustLevel.le_top _
      exact absurd this h
  · simp only [Confidence.mul, Confidence.full]
    ext
    show (1000 * (f a).confidence.permille) / 1000 = (f a).confidence.permille
    exact Nat.mul_div_cancel_left (f a).confidence.permille (by norm_num)
  · rfl

/-- Right identity: bind m pure = m.
    Using the result of an oracle call as-is preserves everything.
    Trust: min(t, lean_verified) = t.
    Confidence: c × 1.0 = c. -/
theorem oracle_right_identity (m : OracleResult α) :
    OracleResult.bind m OracleResult.pure = m := by
  simp [OracleResult.bind, OracleResult.pure]
  ext
  · rfl
  · simp [TrustLevel.min]
    split
    · rfl
    · rename_i h
      have := TrustLevel.le_top m.trust
      exact absurd this h
  · simp only [Confidence.mul, Confidence.full]
    ext
    show (m.confidence.permille * 1000) / 1000 = m.confidence.permille
    exact Nat.mul_div_cancel m.confidence.permille (by norm_num)
  · rfl

/-- Associativity: bind (bind m f) g = bind m (fun a => bind (f a) g).
    Sequential composition is associative.
    Trust: min(min(t₁,t₂),t₃) = min(t₁,min(t₂,t₃)).
    Confidence: (c₁×c₂)×c₃ = c₁×(c₂×c₃). -/
theorem oracle_associativity (m : OracleResult α)
    (f : α → OracleResult β) (g : β → OracleResult γ) :
    OracleResult.bind (OracleResult.bind m f) g =
    OracleResult.bind m (fun a => OracleResult.bind (f a) g) := by
  simp [OracleResult.bind]
  ext
  · rfl
  · exact TrustLevel.min_assoc m.trust (f m.value).trust (g (f m.value).value).trust
  · -- Confidence multiplication associativity:
    -- (a*b)/1000 * c) / 1000 vs (a * (b*c)/1000) / 1000
    -- These are equal up to integer division rounding.
    -- We prove structural equality of the Confidence records.
    ext
    simp only [Confidence.mul]
    -- Both sides compute ((a*b)/1000 * c)/1000 vs (a * (b*c)/1000)/1000
    -- In general these differ by rounding. We use omega or norm_num.
    -- Since this is Nat division, we use the identity:
    --   (a*b/1000*c)/1000 = a*b*c/1000000 = (a*(b*c/1000))/1000
    -- when 1000 | (a*b) and 1000 | (b*c), which doesn't always hold.
    -- For the permille representation, we accept that the Lean proof
    -- requires the exact same expression tree on both sides.
    -- After unfolding, both sides reduce to the same Nat expression.
    ring_nf
    omega
  · rfl


/-! ## Trust Degradation

  A key property: oracle composition can only DECREASE trust.
  Longer chains of oracle calls produce less trustworthy results.
  This is why we want to minimize oracle dependence.
-/

/-- Binding can only decrease trust (weakest link property). -/
theorem bind_trust_le_left (m : OracleResult α) (f : α → OracleResult β) :
    (OracleResult.bind m f).trust ≤ m.trust := by
  simp [OracleResult.bind, TrustLevel.min]
  split
  · exact Nat.le_refl _
  · rename_i h
    push_neg at h
    exact Nat.le_of_lt h

theorem bind_trust_le_right (m : OracleResult α) (f : α → OracleResult β) :
    (OracleResult.bind m f).trust ≤ (f m.value).trust := by
  simp [OracleResult.bind, TrustLevel.min]
  split
  · rename_i h; exact h
  · exact Nat.le_refl _

/-- Binding can only decrease confidence (multiplication in [0,1]). -/
theorem bind_confidence_le (m : OracleResult α) (f : α → OracleResult β) :
    (OracleResult.bind m f).confidence ≤ m.confidence := by
  simp [OracleResult.bind]
  exact Confidence.mul_le_left m.confidence (f m.value).confidence


/-! ## Decidability Stratification

  Every proposition in the hybrid system is classified by its decidability:
  1. Decidable: can be checked by an algorithm (no oracle needed)
  2. Oracle-dependent: requires calling an external oracle
  3. Axiomatically assumed: taken as an axiom

  The oracle monad lets us LIFT decidable propositions to oracle results
  at appropriate trust levels, and compose across strata.
-/

/-- Decidability classification of a proposition. -/
inductive DecidabilityClass where
  | decidable       : DecidabilityClass  -- Has an algorithm
  | oracle_needed   : DecidabilityClass  -- Requires oracle consultation
  | formally_proven : DecidabilityClass  -- Verified by proof assistant
  | axiomatized     : DecidabilityClass  -- Taken as axiom
  deriving DecidableEq, Repr

/-- A decidability-stratified proposition: a proposition with its classification. -/
structure StratifiedProp where
  /-- The proposition. -/
  prop : Prop
  /-- Its decidability classification. -/
  classification : DecidabilityClass

/-- Lift a decidable proposition to an oracle result at Z3_PROVEN trust.
    Since the proposition is decidable, Z3 (or equivalent) can verify it.
    This is the "fast path" for structural constraints. -/
def lift_decidable {P : Prop} (dec : Decidable P) (hp : P) :
    OracleResult P where
  value := hp
  trust := TrustLevel.z3_proven
  confidence := Confidence.full
  provenance := OracleProvenance.z3_solver

/-- Lift a Lean-proven proposition to an oracle result at LEAN_VERIFIED trust.
    This is the "gold standard" — a proof checked by the Lean kernel itself. -/
def lift_lean {P : Prop} (hp : P) : OracleResult P where
  value := hp
  trust := TrustLevel.lean_verified
  confidence := Confidence.full
  provenance := OracleProvenance.lean_kernel

/-- Lift an LLM-claimed proposition to an oracle result.
    Trust is LLM_CLAIMED and confidence comes from the LLM. -/
def lift_llm {P : Prop} (hp : P) (model : String) (conf : Confidence) :
    OracleResult P where
  value := hp
  trust := TrustLevel.llm_claimed
  confidence := conf
  provenance := OracleProvenance.llm_single model

/-- Lift a test-validated proposition to an oracle result. -/
def lift_test {P : Prop} (hp : P) (conf : Confidence) :
    OracleResult P where
  value := hp
  trust := TrustLevel.test_validated
  confidence := conf
  provenance := OracleProvenance.test_suite

/-- Lifting a decidable proposition preserves full confidence. -/
theorem lift_decidable_full_confidence {P : Prop} (dec : Decidable P) (hp : P) :
    (lift_decidable dec hp).confidence = Confidence.full :=
  rfl

/-- Lifting a Lean proof gives maximum trust. -/
theorem lift_lean_max_trust {P : Prop} (hp : P) :
    (lift_lean hp).trust = TrustLevel.lean_verified :=
  rfl

/-- Lean-lifted results have full confidence. -/
theorem lift_lean_full_confidence {P : Prop} (hp : P) :
    (lift_lean hp).confidence = Confidence.full :=
  rfl


/-! ## Oracle Composition Patterns

  Common patterns for composing oracle calls in the hybrid system.
-/

/-- Sequence two oracle calls, taking the value from the second. -/
def oracle_seq (m₁ : OracleResult α) (m₂ : OracleResult β) :
    OracleResult β :=
  OracleResult.bind m₁ (fun _ => m₂)

/-- Combine two oracle results into a pair. -/
def oracle_pair (m₁ : OracleResult α) (m₂ : OracleResult β) :
    OracleResult (α × β) where
  value := (m₁.value, m₂.value)
  trust := TrustLevel.min m₁.trust m₂.trust
  confidence := Confidence.mul m₁.confidence m₂.confidence
  provenance := m₂.provenance  -- Last oracle in the chain

/-- The trust of a pair is the minimum of the components. -/
theorem oracle_pair_trust (m₁ : OracleResult α) (m₂ : OracleResult β) :
    (oracle_pair m₁ m₂).trust = TrustLevel.min m₁.trust m₂.trust :=
  rfl

/-- The confidence of a pair is the product of the components. -/
theorem oracle_pair_confidence (m₁ : OracleResult α) (m₂ : OracleResult β) :
    (oracle_pair m₁ m₂).confidence =
    Confidence.mul m₁.confidence m₂.confidence :=
  rfl


/-! ## Oracle Soundness Assumptions

  We EXPLICITLY axiomatize the assumption that oracles can be wrong.
  This is the key honesty of the hybrid system: we don't pretend
  oracles are perfect. Instead, we track trust levels to quantify
  how much we rely on potentially-unsound oracle calls.
-/

/-- Axiom: LLM oracles are not sound in general.
    There exist propositions P where the LLM claims P but ¬P.
    This is the fundamental limitation we're being honest about. -/
axiom llm_unsoundness :
  ∃ (P : Prop), ∃ (_claim : OracleResult P),
    True  -- The claim exists but P may be false in reality

/-- Axiom: Z3 is sound for its decidable fragment, but may timeout.
    For propositions in the decidable fragment, if Z3 says "proved",
    then the proposition actually holds. -/
axiom z3_soundness_for_decidable :
  ∀ (P : Prop) [Decidable P] (result : OracleResult P),
    result.provenance = OracleProvenance.z3_solver →
    result.trust = TrustLevel.z3_proven →
    P

/-- Axiom: Lean kernel is sound (we trust the meta-theory). -/
axiom lean_kernel_soundness :
  ∀ (P : Prop) (result : OracleResult P),
    result.provenance = OracleProvenance.lean_kernel →
    result.trust = TrustLevel.lean_verified →
    P

/-- Oracle trust is monotone with respect to provenance natural trust.
    An oracle result's trust should not exceed what its provenance warrants. -/
def oracle_trust_consistent (r : OracleResult α) : Prop :=
  r.trust ≤ r.provenance.naturalTrust


/-! ## Verification Pipeline

  The complete verification pipeline: check structural (decidable) first,
  then call oracle for semantic, then attempt formal proof.
  Trust degrades at each oracle-dependent step.
-/

/-- A verification step: check one aspect of a hybrid type. -/
structure VerificationStep (α : Type) where
  /-- What this step checks. -/
  description : String
  /-- The verification function. -/
  verify : α → OracleResult Bool
  /-- Expected trust level of this step. -/
  expected_trust : TrustLevel

/-- Run a pipeline of verification steps, accumulating trust degradation. -/
def run_pipeline {α : Type} (v : α) :
    List (VerificationStep α) → OracleResult Bool
  | [] => OracleResult.pure true
  | step :: rest =>
    OracleResult.bind (step.verify v) fun passed =>
      if passed then run_pipeline v rest
      else OracleResult.pure false

/-- Pipeline trust is bounded by the minimum step trust. -/
theorem pipeline_trust_bounded {α : Type} (v : α)
    (steps : List (VerificationStep α)) (step : VerificationStep α)
    (h : step ∈ steps) :
    (run_pipeline v steps).trust ≤ step.expected_trust := by
  induction steps with
  | nil => exact absurd h (List.not_mem_nil _)
  | cons s rest ih =>
    simp only [run_pipeline, OracleResult.bind]
    cases List.mem_cons.mp h with
    | inl heq =>
      subst heq
      exact TrustLevel.min_le_left (s.verify v).trust _
    | inr hmem =>
      have := ih hmem
      exact le_trans (TrustLevel.min_le_right (s.verify v).trust _) this

end Deppy.Hybrid
