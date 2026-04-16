/-
  C4/SubjectReduction.lean
  Subject reduction for the C⁴ novel fragment.

  Main theorem: if Γ ⊢ t : A and t ↝ t', then Γ ⊢ t' : A.

  We prove subject reduction for all novel C⁴ rules:
  - Fill-β (descent-β): restr(fill({tα},{pαβ}), φ_k) ↝ t_k
  - Restriction distribution: restr(λx.t, φ) ↝ λx.restr(t, φ)  etc.
  - Refinement-β: refinE(refinI(A, a, h)) ↝ a
  - Standard β-reduction

  CIC and cubical subject reduction are axiomatized with references.
-/
import C4.Typing
import C4.Reduction

namespace C4.SubjectReduction

open Syntax Typing Reduction

-- ── Axioms for the established fragments ──────────────────────
-- These are proved in the literature; we take them as axioms.

/-- Subject reduction for CIC β-reduction.
    Reference: Barras (1997), "Coq en Coq." -/
axiom sr_cic_beta (Γ : Ctx) (A B : Ty) (body u : Tm) (T : Trust) :
    Typed Γ (.app (.lam A body) u) B T →
    Typed Γ (body.subst u) B T

/-- Subject reduction for cubical β-reduction.
    Reference: Huber (2018), "Canonicity for Cubical Type Theory." -/
axiom sr_cubical_transp (Γ : Ctx) (A : Ty) (t : Tm) (T : Trust) :
    Typed Γ (.transp (.refl (.sort (.type 0))) t) A T →
    Typed Γ t A T

-- ── Inversion lemmas ──────────────────────────────────────────

/-- Inversion for lam: if λx.t : Π(A).B then t : B in A::Γ. -/
theorem inversion_lam {Γ : Ctx} {A B : Ty} {t : Tm} {T : Trust}
    (h : Typed Γ (.lam A t) (.pi A B) T) :
    Typed (A :: Γ) t B T := by
  cases h with
  | lam _ _ _ _ _ h => exact h
  | trust_weaken _ _ _ T T' h hT =>
    cases h with
    | lam _ _ _ _ _ h' =>
      exact Typed.trust_weaken _ _ _ _ T' h' hT

/-- Inversion for pair: if (a,b) : Σ(A).B then a : A and b : B[a]. -/
theorem inversion_pair_fst {Γ : Ctx} {A B : Ty} {a b : Tm} {T : Trust}
    (h : Typed Γ (.pair a b) (.sigma A B) T) :
    ∃ T₁ T₂, Typed Γ a A T₁ ∧ Typed Γ b (B.subst a) T₂ ∧
              ∀ s, s ∈ T₁.combine T₂ → s ∈ T := by
  cases h with
  | pair _ _ _ _ _ T₁ T₂ ha hb =>
    exact ⟨T₁, T₂, ha, hb, fun s hs => hs⟩
  | trust_weaken _ _ _ T' T'' h hT =>
    cases h with
    | pair _ _ _ _ _ T₁ T₂ ha hb =>
      exact ⟨T₁, T₂, ha, hb, fun s hs => hT s (Trust.combine_supset_left _ _ _ hs)⟩

/-- Inversion for refinI: if ⟨a,h⟩_φ : {x:A|φ} then a : A. -/
theorem inversion_refinI {Γ : Ctx} {A : Ty} {φ : Tm → Bool} {a h : Tm}
    {T : Trust}
    (hty : Typed Γ (.refinI A a h) (.refin A φ) T) :
    ∃ T₁ T₂, Typed Γ a A T₁ ∧ Typed Γ h (.sort .prop) T₂ ∧ φ a = true := by
  cases hty with
  | refinI _ _ _ _ _ T₁ T₂ ha hh hφ =>
    exact ⟨T₁, T₂, ha, hh, hφ⟩
  | trust_weaken _ _ _ T' T'' h hT =>
    cases h with
    | refinI _ _ _ _ _ T₁ T₂ ha hh hφ =>
      exact ⟨T₁, T₂, ha, hh, hφ⟩

/-- Inversion for desc: if fill({tα},{pαβ}) : A then each tα : A. -/
theorem inversion_desc {Γ : Ctx} {A : Ty} {φs : List (Tm → Bool)}
    {ts ps : List Tm} {T : Trust}
    (hty : Typed Γ (.desc ts ps) A T) :
    ∀ i : Fin ts.length,
    ∃ Ti ∈ T, Typed Γ (ts[i.val]'(by omega)) A Ti := by
  cases hty with
  | desc _ _ _ _ _ Ts hts _ =>
    intro i
    obtain ⟨Ti, hTi, hty⟩ := hts i
    exact ⟨Ti, List.foldl_mem_of_mem _ _ _ hTi, hty⟩
  | trust_weaken _ _ _ T' T'' h hT =>
    cases h with
    | desc _ _ _ _ _ Ts hts _ =>
      intro i
      obtain ⟨Ti, hTi, hty⟩ := hts i
      exact ⟨Ti, hT Ti (List.foldl_mem_of_mem _ _ _ hTi), hty⟩

-- ── Subject reduction: novel rules ────────────────────────────

/-- SR for standard β-reduction: (λx.t) u ↝ t[u/x] -/
theorem sr_beta {Γ : Ctx} {A B : Ty} {body u : Tm} {T : Trust}
    (hf : Typed Γ (.lam A body) (.pi A B) T)
    (hu : Typed Γ u A T) :
    Typed Γ (body.subst u) B T :=
  sr_cic_beta Γ A B body u T (.app (.pi A B) (.sigma A (.sort .prop))
    body u T T hf hu |>.elim (fun h => h) (fun h => absurd h (by simp)))

/-- SR for Refinement-β: refinE(refinI(A, a, h)) ↝ a -/
theorem sr_refin_beta {Γ : Ctx} {A : Ty} {φ : Tm → Bool} {a h : Tm}
    {T : Trust}
    (hty : Typed Γ (.refinE (.refinI A a h)) A T) :
    Typed Γ a A T := by
  -- The type of refinE(r) is A when r : {x:A|φ}
  cases hty with
  | refinE _ _ _ r T hr =>
    cases hr with
    | refinI _ _ _ _ _ T₁ T₂ ha _ _ =>
      exact Typed.trust_weaken _ _ _ T₁ T ha
        (Trust.combine_supset_left T₁ T₂)
    | trust_weaken _ _ _ T' T'' h hT =>
      cases h with
      | refinI _ _ _ _ _ T₁ T₂ ha _ _ =>
        exact Typed.trust_weaken _ _ _ T₁ T ha
          (fun s hs => hT s (Trust.combine_supset_left T₁ T₂ s hs))
  | trust_weaken _ _ _ T' T'' h hT =>
    exact Typed.trust_weaken _ a A T' T (sr_refin_beta h) hT

/-- SR for restriction-lam: restr(λx.t, φ) ↝ λx.restr(t, φ) -/
theorem sr_restr_lam {Γ : Ctx} {A B : Ty} {body : Tm} {φ : Tm → Bool}
    {T : Trust}
    (hty : Typed Γ (.restr (.lam A body) φ) (.pi A B) T) :
    Typed Γ (.lam A (.restr body φ)) (.pi A B) T := by
  cases hty with
  | restr _ _ _ t T hinner =>
    cases hinner with
    | lam _ _ _ _ _ hbody =>
      exact .lam _ _ _ _ _ (.restr _ _ _ _ _ hbody)
    | trust_weaken _ _ _ T' T'' h hT =>
      cases h with
      | lam _ _ _ _ _ hbody =>
        exact Typed.trust_weaken _ _ _ _ T''
          (.lam _ _ _ _ _ (.restr _ _ _ _ _ hbody)) hT
  | trust_weaken _ _ _ T' T'' h hT =>
    exact Typed.trust_weaken _ _ _ _ T'' (sr_restr_lam h) hT

/-- SR for restriction-pair: restr((a,b), φ) ↝ (restr(a,φ), restr(b,φ)) -/
theorem sr_restr_pair {Γ : Ctx} {A B : Ty} {a b : Tm} {φ : Tm → Bool}
    {T : Trust}
    (hty : Typed Γ (.restr (.pair a b) φ) (.sigma A B) T) :
    Typed Γ (.pair (.restr a φ) (.restr b φ)) (.sigma A B) T := by
  cases hty with
  | restr _ _ _ t T hinner =>
    cases hinner with
    | pair _ _ _ _ _ T₁ T₂ ha hb =>
      exact .pair _ _ _ _ _ T₁ T₂
        (.restr _ _ _ _ _ ha) (.restr _ _ _ _ _ hb)
    | trust_weaken _ _ _ T' T'' h hT =>
      cases h with
      | pair _ _ _ _ _ T₁ T₂ ha hb =>
        exact Typed.trust_weaken _ _ _ _ T''
          (.pair _ _ _ _ _ T₁ T₂
            (.restr _ _ _ _ _ ha) (.restr _ _ _ _ _ hb)) hT
  | trust_weaken _ _ _ T' T'' h hT =>
    exact Typed.trust_weaken _ _ _ _ T'' (sr_restr_pair h) hT

/-- SR for Fill-β (descent-β): the KEY C⁴ subject reduction rule.

    restr(fill({tα}, {pαβ}), φ_k) ↝ t_k

    Subject reduction: if this restricted descent term has type A,
    then t_k has type A.  This is the core soundness of descent:
    restricting a global proof to a fiber gives the local section,
    which has the same type. -/
theorem sr_fill_beta {Γ : Ctx} {A : Ty} {φs : List (Tm → Bool)}
    {ts ps : List Tm} {φ : Tm → Bool} {k : Nat} {hk : k < ts.length}
    {T : Trust}
    (hty : Typed Γ (.restr (.desc ts ps) φ) A T) :
    Typed Γ (ts[k]'hk) A T := by
  -- The restriction of a descent term has the same type A as the descent term.
  -- The k-th fiber proof t_k has type A on the k-th fiber.
  cases hty with
  | restr _ _ _ t T hdesc =>
    -- hdesc : Typed Γ (desc ts ps) A T
    -- By inversion of desc, each ts[i] has type A (for some Ti ⊆ T)
    cases hdesc with
    | desc _ _ _ _ _ Ts hts _ =>
      obtain ⟨Tk, hTk, htk⟩ := hts ⟨k, hk⟩
      exact Typed.trust_weaken _ _ _ Tk T htk
        (fun s hs => List.foldl_mem_of_mem _ _ _ hTk |>.elim id id |>.elim
          (fun h => by exact List.mem_of_mem_of_subset hs (by simp))
          id)
    | trust_weaken _ _ _ T' T'' h hT =>
      cases h with
      | desc _ _ _ _ _ Ts hts _ =>
        obtain ⟨Tk, _hTk, htk⟩ := hts ⟨k, hk⟩
        exact Typed.trust_weaken _ _ _ Tk T'' htk
          (fun s hs => hT s (by exact List.mem_of_mem_of_subset hs (by simp)))
  | trust_weaken _ _ _ T' T'' h hT =>
    exact Typed.trust_weaken _ _ _ T' T'' (sr_fill_beta h) hT

-- ── Master subject reduction theorem ──────────────────────────

/-- Master subject reduction theorem for the C⁴ core fragment.

    If Γ ⊢ t : A and t ↝ t', then Γ ⊢ t' : A.

    Proved for all novel C⁴ rules.  CIC and cubical rules
    are handled by the axioms sr_cic_beta and sr_cubical_transp. -/
theorem subject_reduction {Γ : Ctx} {t t' : Tm} {A : Ty} {T : Trust}
    (hty : Typed Γ t A T)
    (hred : Reduces t t') :
    Typed Γ t' A T := by
  induction hred generalizing A T with

  | beta A' body u =>
    exact sr_cic_beta Γ A' A body u T hty

  | fst_beta a b =>
    cases hty with
    | fst _ _ _ _ _ h => cases h with
      | pair _ _ _ _ _ T₁ T₂ ha _ =>
        exact Typed.trust_weaken _ _ _ T₁ T ha (Trust.combine_supset_left _ _)
      | trust_weaken _ _ _ T' T'' h hT =>
        cases h with
        | pair _ _ _ _ _ T₁ T₂ ha _ =>
          exact Typed.trust_weaken _ _ _ T₁ T'' ha
            (fun s hs => hT s (Trust.combine_supset_left _ _ s hs))
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.fst_beta a b)) hT

  | snd_beta a b =>
    cases hty with
    | snd _ _ _ _ _ h => cases h with
      | pair _ _ _ _ _ T₁ T₂ _ hb =>
        exact Typed.trust_weaken _ _ _ T₂ T hb (Trust.combine_supset_right _ _)
      | trust_weaken _ _ _ T' T'' h hT =>
        cases h with
        | pair _ _ _ _ _ T₁ T₂ _ hb =>
          exact Typed.trust_weaken _ _ _ T₂ T'' hb
            (fun s hs => hT s (Trust.combine_supset_right _ _ s hs))
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.snd_beta a b)) hT

  | refin_beta A' φ a h =>
    exact sr_refin_beta hty

  | fill_beta ts ps φ k hk =>
    exact sr_fill_beta hty

  | restr_lam A' body φ =>
    cases A with
    | pi A'' B => exact sr_restr_lam hty
    | _ =>
      -- Other types: restriction still preserves typing
      cases hty with
      | restr _ _ _ _ _ h => exact .restr _ _ _ _ _ h
      | trust_weaken _ _ _ T' T'' h hT =>
        exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.restr_lam A' body φ)) hT

  | restr_pair a b φ =>
    cases A with
    | sigma A' B => exact sr_restr_pair hty
    | _ =>
      cases hty with
      | restr _ _ _ _ _ h => exact .restr _ _ _ _ _ h
      | trust_weaken _ _ _ T' T'' h hT =>
        exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.restr_pair a b φ)) hT

  | restr_refl a φ =>
    cases hty with
    | restr _ _ _ _ _ h =>
      cases h with
      | refl _ _ _ T ha => exact .refl _ _ _ _ (.restr _ _ _ _ _ ha)
      | trust_weaken _ _ _ T' T'' h hT =>
        cases h with
        | refl _ _ _ T ha =>
          exact Typed.trust_weaken _ _ _ T' T''
            (.refl _ _ _ _ (.restr _ _ _ _ _ ha)) hT
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.restr_refl a φ)) hT

  | restr_comp t φ ψ =>
    cases hty with
    | restr _ _ _ _ _ h =>
      cases h with
      | restr _ _ _ _ _ hinner =>
        -- restr(restr(t, φ), ψ) : A → restr(t, φ∧ψ) : A
        exact .restr _ _ _ _ _ hinner
      | trust_weaken _ _ _ T' T'' h hT =>
        cases h with
        | restr _ _ _ _ _ hinner =>
          exact Typed.trust_weaken _ _ _ T' T'' (.restr _ _ _ _ _ hinner) hT
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.restr_comp t φ ψ)) hT

  | cong_app_l f f' u hff' ih =>
    cases hty with
    | app _ _ _ _ _ T₁ T₂ hf hu =>
      exact .app _ _ _ _ _ T₁ T₂ (ih hf) hu
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.cong_app_l f f' u hff')) hT

  | cong_app_r f u u' huu' ih =>
    cases hty with
    | app _ _ _ _ _ T₁ T₂ hf hu =>
      exact .app _ _ _ _ _ T₁ T₂ hf (ih hu)
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.cong_app_r f u u' huu')) hT

  | cong_lam A' t t' htt' ih =>
    cases hty with
    | lam _ _ _ _ _ hbody =>
      exact .lam _ _ _ _ _ (ih hbody)
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.cong_lam A' t t' htt')) hT

  | cong_fst p p' hpp' ih =>
    cases hty with
    | fst _ _ _ _ _ h => exact .fst _ _ _ _ _ (ih h)
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.cong_fst p p' hpp')) hT

  | cong_snd p p' hpp' ih =>
    cases hty with
    | snd _ _ _ _ _ h => exact .snd _ _ _ _ _ (ih h)
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.cong_snd p p' hpp')) hT

  | cong_restr t t' φ htt' ih =>
    cases hty with
    | restr _ _ _ _ _ h => exact .restr _ _ _ _ _ (ih h)
    | trust_weaken _ _ _ T' T'' h hT =>
      exact Typed.trust_weaken _ _ _ T' T'' (subject_reduction h (.cong_restr t t' φ htt')) hT

/-- Multi-step subject reduction: typing is preserved under
    arbitrary reduction sequences. -/
theorem subject_reduction_star {Γ : Ctx} {t t' : Tm} {A : Ty} {T : Trust}
    (hty : Typed Γ t A T)
    (hred : ReducesStar t t') :
    Typed Γ t' A T := by
  induction hred with
  | refl _ => exact hty
  | step _ u _ h _ ih => exact ih (subject_reduction hty h)

end C4.SubjectReduction
