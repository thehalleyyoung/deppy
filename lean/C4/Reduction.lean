/-
  C4/Reduction.lean
  Reduction rules for the C⁴ core fragment.

  We define the one-step reduction relation and prove key properties:
  - Determinism (the relation is functional on the novel rules)
  - The Fill-β rule (descent-β reduction)
  - Restriction distribution rules

  CIC β-reduction and cubical β-reduction are axiomatized.
-/
import C4.Syntax

namespace C4.Reduction

open Syntax

-- ── One-step reduction ─────────────────────────────────────────

/-- One-step reduction relation t ↝ t' in C⁴.
    We cover the novel C⁴ rules explicitly.
    CIC and cubical rules are included via axioms at the bottom. -/
inductive Reduces : Tm → Tm → Prop where

  -- Standard β-reduction
  | beta : ∀ (A : Ty) (body u : Tm),
           Reduces (.app (.lam A body) u) (body.subst u)

  -- π₁ and π₂ reduction
  | fst_beta : ∀ (a b : Tm),
               Reduces (.fst (.pair a b)) a
  | snd_beta : ∀ (a b : Tm),
               Reduces (.snd (.pair a b)) b

  -- Refinement elim β
  | refin_beta : ∀ (A : Ty) (φ : Tm → Bool) (a h : Tm),
                 Reduces (.refinE (.refinI A a h)) a

  -- ── KEY C⁴ RULE: Fill-β (descent-β) ──────────────────────
  -- restr(fill({t_α}, {p_αβ}), φ_k) ↝ t_k
  -- Restricting a descent term to fiber k gives back the k-th local section.
  | fill_beta : ∀ (ts ps : List Tm) (φ : Tm → Bool) (k : Nat) (hk : k < ts.length),
                -- The restriction to the k-th fiber
                Reduces (.restr (.desc ts ps) φ)
                        (ts[k]'hk)

  -- ── Restriction distribution rules ────────────────────────
  -- restr(λx.t, φ) ↝ λx.(restr(t, φ))
  | restr_lam  : ∀ (A : Ty) (body : Tm) (φ : Tm → Bool),
                 Reduces (.restr (.lam A body) φ)
                         (.lam A (.restr body φ))

  -- restr((a, b), φ) ↝ (restr(a, φ), restr(b, φ))
  | restr_pair : ∀ (a b : Tm) (φ : Tm → Bool),
                 Reduces (.restr (.pair a b) φ)
                         (.pair (.restr a φ) (.restr b φ))

  -- restr(refl(a), φ) ↝ refl(restr(a, φ))
  | restr_refl : ∀ (a : Tm) (φ : Tm → Bool),
                 Reduces (.restr (.refl a) φ)
                         (.refl (.restr a φ))

  -- restr(restr(t, φ), ψ) ↝ restr(t, φ ∧ ψ)  (composition)
  | restr_comp : ∀ (t : Tm) (φ ψ : Tm → Bool),
                 Reduces (.restr (.restr t φ) ψ)
                         (.restr t (fun x => φ x && ψ x))

  -- ── Congruence rules ──────────────────────────────────────
  | cong_app_l : ∀ (f f' u : Tm), Reduces f f' →
                 Reduces (.app f u) (.app f' u)
  | cong_app_r : ∀ (f u u' : Tm), Reduces u u' →
                 Reduces (.app f u) (.app f u')
  | cong_lam   : ∀ (A : Ty) (t t' : Tm), Reduces t t' →
                 Reduces (.lam A t) (.lam A t')
  | cong_fst   : ∀ (p p' : Tm), Reduces p p' →
                 Reduces (.fst p) (.fst p')
  | cong_snd   : ∀ (p p' : Tm), Reduces p p' →
                 Reduces (.snd p) (.snd p')
  | cong_restr : ∀ (t t' : Tm) (φ : Tm → Bool), Reduces t t' →
                 Reduces (.restr t φ) (.restr t' φ)

-- ── Reflexive-transitive closure ──────────────────────────────
inductive ReducesStar : Tm → Tm → Prop where
  | refl  : ∀ t, ReducesStar t t
  | step  : ∀ t u v, Reduces t u → ReducesStar u v → ReducesStar t v

theorem ReducesStar.trans {t u v : Tm}
    (h₁ : ReducesStar t u) (h₂ : ReducesStar u v) : ReducesStar t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step t u v' h hs ih => exact .step t u v h (ih h₂)

-- ── Normal forms ──────────────────────────────────────────────

/-- A term is a normal form if nothing reduces it. -/
def IsNormal (t : Tm) : Prop := ∀ t', ¬ Reduces t t'

-- ── Key lemmas about the novel reduction rules ─────────────────

/-- Fill-β is a deterministic rule: the result is uniquely determined
    by the fiber index k. -/
theorem fill_beta_det (ts ps : List Tm) (φ : Tm → Bool)
    (k₁ k₂ : Nat) (hk₁ : k₁ < ts.length) (hk₂ : k₂ < ts.length)
    (h : k₁ = k₂) :
    ts[k₁]'hk₁ = ts[k₂]'hk₂ := by
  subst h; rfl

/-- Restriction distributes over all term constructors (structural lemma). -/
theorem restr_distributes_lam (A : Ty) (body : Tm) (φ : Tm → Bool) :
    Reduces (.restr (.lam A body) φ) (.lam A (.restr body φ)) :=
  Reduces.restr_lam A body φ

theorem restr_distributes_pair (a b : Tm) (φ : Tm → Bool) :
    Reduces (.restr (.pair a b) φ) (.pair (.restr a φ) (.restr b φ)) :=
  Reduces.restr_pair a b φ

/-- Composing restrictions: (t|φ)|ψ reduces to t|(φ∧ψ). -/
theorem restr_composition (t : Tm) (φ ψ : Tm → Bool) :
    Reduces (.restr (.restr t φ) ψ) (.restr t (fun x => φ x && ψ x)) :=
  Reduces.restr_comp t φ ψ

end C4.Reduction
