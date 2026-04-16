/-
  C4/Typing.lean
  Typing judgments for the C⁴ deep embedding.

  We define the typing relation for the novel C⁴ fragment.
  CIC and cubical rules are axiomatized (referenced to the literature).
  The novel rules (refinement types, fiber restriction, descent) are
  given explicit inference rules.
-/
import C4.Syntax

namespace C4.Typing

open Syntax

-- ── Typing relation ────────────────────────────────────────────

/-- The typing judgment Γ ⊢ t : A, with trust provenance T. -/
inductive Typed : Ctx → Tm → Ty → Trust → Prop where

  -- ── Variable rule ──────────────────────────────────────────
  | var : ∀ (Γ : Ctx) (n : Nat) (A : Ty),
          Γ.get? n = some A →
          Typed Γ (.var n) A Trust.kernel

  -- ── Sort rule ──────────────────────────────────────────────
  | sort : ∀ (Γ : Ctx) (s : Sort'),
           Typed Γ (.sort s) (.sort (.type 0)) Trust.kernel

  -- ── Lambda / Pi ────────────────────────────────────────────
  | lam : ∀ (Γ : Ctx) (A B : Ty) (t : Tm) (T : Trust),
          Typed (A :: Γ) t B T →
          Typed Γ (.lam A t) (.pi A B) T

  | app : ∀ (Γ : Ctx) (A B : Ty) (f u : Tm) (T₁ T₂ : Trust),
          Typed Γ f (.pi A B) T₁ →
          Typed Γ u A T₂ →
          Typed Γ (.app f u) (B.subst u) (T₁.combine T₂)

  -- ── Pair / Sigma ────────────────────────────────────────────
  | pair : ∀ (Γ : Ctx) (A B : Ty) (a b : Tm) (T₁ T₂ : Trust),
           Typed Γ a A T₁ →
           Typed Γ b (B.subst a) T₂ →
           Typed Γ (.pair a b) (.sigma A B) (T₁.combine T₂)

  | fst : ∀ (Γ : Ctx) (A B : Ty) (p : Tm) (T : Trust),
          Typed Γ p (.sigma A B) T →
          Typed Γ (.fst p) A T

  | snd : ∀ (Γ : Ctx) (A B : Ty) (p : Tm) (T : Trust),
          Typed Γ p (.sigma A B) T →
          Typed Γ (.snd p) (B.subst (.fst p)) T

  -- ── Base type literals ────────────────────────────────────────
  | nat_zero : ∀ (Γ : Ctx),
               Typed Γ .zero .nat Trust.kernel
  | nat_succ : ∀ (Γ : Ctx) (n : Tm) (T : Trust),
               Typed Γ n .nat T →
               Typed Γ (.succ n) .nat T
  | bool_true  : ∀ (Γ : Ctx),
                 Typed Γ .btrue .bool Trust.kernel
  | bool_false : ∀ (Γ : Ctx),
                 Typed Γ .bfalse .bool Trust.kernel

  -- ── Refinement type intro ────────────────────────────────────
  | refinI : ∀ (Γ : Ctx) (A : Ty) (φ : Tm → Bool) (a h : Tm)
               (T₁ T₂ : Trust),
             Typed Γ a A T₁ →
             -- h is a proof that φ(a) holds
             Typed Γ h (.sort .prop) T₂ →
             -- Z3 decides φ (represented as Bool → Prop)
             (φ a = true) →
             Typed Γ (.refinI A a h) (.refin A φ) (T₁.combine T₂)

  -- ── Refinement type elim ────────────────────────────────────
  | refinE : ∀ (Γ : Ctx) (A : Ty) (φ : Tm → Bool) (r : Tm) (T : Trust),
             Typed Γ r (.refin A φ) T →
             Typed Γ (.refinE r) A T

  -- ── Fiber restriction ──────────────────────────────────────
  -- (Res rule: global term restricted to fiber φ)
  | restr : ∀ (Γ : Ctx) (A : Ty) (φ : Tm → Bool) (t : Tm) (T : Trust),
            Typed Γ t A T →
            -- Restriction preserves type (on the restricted domain)
            Typed Γ (.restr t φ) A T

  -- ── Descent / Fill rule ────────────────────────────────────
  -- This is the key C⁴ rule: local sections + exhaustive cover
  -- → global section.  For Prop-valued A, compatibility is automatic.
  | desc : ∀ (Γ : Ctx) (A : Ty) (φs : List (Tm → Bool))
             (ts ps : List Tm) (Ts : List Trust),
           -- Each local section ts[i] has type A on fiber φs[i]
           (∀ i : Fin ts.length,
             ∃ T ∈ Ts, Typed Γ (ts[i.val]'(by omega)) A T) →
           -- Compatibility proofs ps[i,j] (simplified: listed as ps)
           (∀ i : Fin ps.length,
             ∃ T ∈ Ts, Typed Γ (ps[i.val]'(by omega)) (.sort .prop) T) →
           Typed Γ (.desc ts ps) A (Ts.foldl Trust.combine Trust.empty)

  -- ── Reflexivity ───────────────────────────────────────────
  | refl : ∀ (Γ : Ctx) (A : Ty) (a : Tm) (T : Trust),
           Typed Γ a A T →
           Typed Γ (.refl a) (.path A a a) T

  -- ── Transport ─────────────────────────────────────────────
  -- p is a path between types A and B in Type₀
  | transp : ∀ (Γ : Ctx) (A B : Ty) (p t : Tm) (T₁ T₂ : Trust),
             Typed Γ p (.path (.sort (.type 1))
                              (.sort (.type 0)) (.sort (.type 0))) T₁ →
             Typed Γ t A T₂ →
             Typed Γ (.transp p t) B (T₁.combine T₂)

  -- ── Trust weakening ────────────────────────────────────────
  -- If t : A with trust T ⊆ T', then also t : A with trust T'
  | trust_weaken : ∀ (Γ : Ctx) (t : Tm) (A : Ty) (T T' : Trust),
                   Typed Γ t A T →
                   (∀ s ∈ T, s ∈ T') →
                   Typed Γ t A T'

-- ── Ty.subst placeholder ──────────────────────────────────────
/-- Type-level substitution (simplified for the deep embedding). -/
def Ty.subst (A : Ty) (t : Tm) : Ty :=
  match A with
  | .sort s       => .sort s
  | .pi A' B      => .pi A' (B.subst t)
  | .sigma A' B   => .sigma A' (B.subst t)
  | .path A' a b  => .path A' (a.subst t) (b.subst t)
  | .refin A' φ   => .refin A' φ
  | .descent As B => .descent As B
  | .nat          => .nat
  | .bool         => .bool

end C4.Typing
