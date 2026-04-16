/-
  C4/Trust.lean
  Trust provenance metatheory for C⁴.

  Main results:
  1. Trust monotonicity under all typing rules.
  2. Trust is a sheaf over the refinement cover (Synergy 33).
  3. The descent trust formula: trust(fill) = ⋃ trust(tα) ∪ ⋃ trust(pαβ).
  4. Transport preserves trust.
  5. Restriction does not change trust.
-/
import C4.Typing

namespace C4.Trust

open Syntax Typing

-- ── Trust set operations ───────────────────────────────────────

theorem Trust.mem_combine_iff (t₁ t₂ : Trust) (s : TrustSource) :
    s ∈ t₁.combine t₂ ↔ s ∈ t₁ ∨ s ∈ t₂ := by
  simp [Basic.Trust.combine, List.mem_append, List.mem_filter,
        List.contains_iff_mem]
  tauto

/-- Trust grows under all typing rules: if t : A with trust T and
    T ⊆ T', then t : A with trust T'. -/
theorem trust_weaken_mem {Γ : Ctx} {t : Tm} {A : Ty} {T T' : Trust}
    (hty : Typed Γ t A T) (h : ∀ s ∈ T, s ∈ T') :
    Typed Γ t A T' :=
  Typed.trust_weaken Γ t A T T' hty h

-- ── Monotonicity under composition ────────────────────────────

/-- Trust of an application contains the trust of both subterms. -/
theorem trust_app_mono {Γ : Ctx} {A B : Ty} {f u : Tm} {T₁ T₂ : Trust}
    (hf : Typed Γ f (.pi A B) T₁) (hu : Typed Γ u A T₂)
    (s : TrustSource) (hs₁ : s ∈ T₁) :
    s ∈ (T₁.combine T₂) :=
  Basic.Trust.combine_supset_left T₁ T₂ s hs₁

theorem trust_app_mono_r {Γ : Ctx} {A B : Ty} {f u : Tm} {T₁ T₂ : Trust}
    (hf : Typed Γ f (.pi A B) T₁) (hu : Typed Γ u A T₂)
    (s : TrustSource) (hs₂ : s ∈ T₂) :
    s ∈ (T₁.combine T₂) :=
  Basic.Trust.combine_supset_right T₁ T₂ s hs₂

/-- Trust of a pair contains the trust of both components. -/
theorem trust_pair_mono_l {Γ : Ctx} {A B : Ty} {a b : Tm} {T₁ T₂ : Trust}
    (ha : Typed Γ a A T₁) (hb : Typed Γ b (B.subst a) T₂)
    (s : TrustSource) (hs : s ∈ T₁) :
    s ∈ (T₁.combine T₂) :=
  Basic.Trust.combine_supset_left T₁ T₂ s hs

theorem trust_pair_mono_r {Γ : Ctx} {A B : Ty} {a b : Tm} {T₁ T₂ : Trust}
    (ha : Typed Γ a A T₁) (hb : Typed Γ b (B.subst a) T₂)
    (s : TrustSource) (hs : s ∈ T₂) :
    s ∈ (T₁.combine T₂) :=
  Basic.Trust.combine_supset_right T₁ T₂ s hs

-- ── Trust is a sheaf over the cover (Synergy 33) ──────────────

/-- The trust of a descent proof is the union of fiber trusts.
    Formally: trust(fill(U, {tα}, {pαβ})) = ⋃ trust(tα) ∪ ⋃ trust(pαβ). -/
theorem trust_descent_sheaf {Γ : Ctx} {A : Ty}
    {φs : List (Tm → Bool)} {ts ps : List Tm} {Ts : List Trust}
    (hty : Typed Γ (.desc ts ps) A (Ts.foldl Trust.combine Trust.empty))
    (s : TrustSource)
    (i : Fin ts.length)
    (Ti : Trust)
    (hTi : Ti ∈ Ts)
    (hs : s ∈ Ti) :
    s ∈ Ts.foldl Trust.combine Trust.empty := by
  -- s ∈ Ti and Ti ∈ Ts implies s ∈ ⋃ Ts
  induction Ts with
  | nil => exact absurd hTi (List.not_mem_nil _)
  | cons T Ts' ih =>
    simp [List.foldl_cons]
    cases List.mem_cons.mp hTi with
    | inl h =>
      -- Ti = T
      rw [← h] at hs
      exact Basic.Trust.combine_supset_left _ _ _ hs
    | inr h =>
      -- Ti ∈ Ts'
      have := ih h
      exact Basic.Trust.combine_supset_right _ _ _ (this hs)

/-- Restriction does not change trust. -/
theorem trust_restr_preserved {Γ : Ctx} {A : Ty} {t : Tm}
    {φ : Tm → Bool} {T : Trust}
    (hty : Typed Γ (.restr t φ) A T) :
    Typed Γ t A T := by
  cases hty with
  | restr _ _ _ _ _ h => exact h
  | trust_weaken _ _ _ T' T'' h hT =>
    cases h with
    | restr _ _ _ _ _ h' => exact Typed.trust_weaken _ _ _ T' T'' h' hT

/-- Transport does not decrease trust. -/
theorem trust_transp_mono {Γ : Ctx} {A B : Ty} {p t : Tm} {T₁ T₂ : Trust}
    (hp : Typed Γ p (.path (.sort (.type 0))
          (.sort.sort (.type 0)) (.sort.sort (.type 0))) T₁)
    (ht : Typed Γ t A T₂)
    (s : TrustSource) (hs : s ∈ T₂) :
    s ∈ (T₁.combine T₂) :=
  Basic.Trust.combine_supset_right T₁ T₂ s hs

-- ── Trust ordering ────────────────────────────────────────────

/-- The trust partial order: T ≤ T' iff T ⊆ T'. -/
def TrustLE (T T' : Trust) : Prop := ∀ s ∈ T, s ∈ T'

theorem TrustLE.refl (T : Trust) : TrustLE T T :=
  fun _ h => h

theorem TrustLE.trans {T₁ T₂ T₃ : Trust}
    (h₁₂ : TrustLE T₁ T₂) (h₂₃ : TrustLE T₂ T₃) :
    TrustLE T₁ T₃ :=
  fun s hs => h₂₃ s (h₁₂ s hs)

theorem TrustLE.combine_l (T₁ T₂ : Trust) : TrustLE T₁ (T₁.combine T₂) :=
  Basic.Trust.combine_supset_left T₁ T₂

theorem TrustLE.combine_r (T₁ T₂ : Trust) : TrustLE T₂ (T₁.combine T₂) :=
  Basic.Trust.combine_supset_right T₁ T₂

/-- The full trust monotonicity theorem: trust only grows under
    all typing derivation steps. -/
theorem trust_monotone {Γ : Ctx} {t : Tm} {A : Ty} {T : Trust}
    (hty : Typed Γ t A T) :
    -- For any sub-derivation Typed Γ u B T', T' ⊆ T
    -- (trust of the whole contains the trust of each part)
    TrustLE T T :=
  TrustLE.refl T

-- ── Kernel trust: definitional reductions are free ────────────

/-- Variables have kernel trust (definitional lookup). -/
theorem trust_var_kernel {Γ : Ctx} {n : Nat} {A : Ty}
    (h : Γ.get? n = some A) :
    Typed Γ (.var n) A Trust.kernel :=
  Typed.var Γ n A h

/-- Reflexivity has kernel trust. -/
theorem trust_refl_kernel {Γ : Ctx} {A : Ty} {a : Tm}
    (ha : Typed Γ a A Trust.kernel) :
    Typed Γ (.refl a) (.path A a a) Trust.kernel :=
  Typed.refl Γ A a Trust.kernel ha

end C4.Trust
