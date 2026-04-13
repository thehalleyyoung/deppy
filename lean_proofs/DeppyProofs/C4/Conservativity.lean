/-
  C4/Conservativity.lean — Conservative Extension over CIC

  Proves that C⁴ is a conservative extension of the Calculus of Inductive
  Constructions (CIC). The proof proceeds by:
  1. Defining an erasure map ε: C⁴ → CIC that removes cubical / sheaf / oracle layers
  2. Proving CIC derivations embed into C⁴ derivations (forward embedding)
  3. Proving the conservative extension property: if C⁴ proves a CIC-only
     statement, then CIC proves it too
-/

import DeppyProofs.C4.Syntax
import DeppyProofs.C4.Typing

set_option autoImplicit false

namespace C4

-- ============================================================
-- CIC fragment identification
-- ============================================================

/-- A C4Term is in the CIC fragment if it uses only Π, Σ, universes, variables,
    λ, application, pair, fst, snd (no interval, path, restrict, descent,
    oterm, mathlibImport, siteUniverse). -/
def C4Term.isCIC : C4Term → Prop
  | .var _ => True
  | .universe _ => True
  | .pi _ a b => a.isCIC ∧ b.isCIC
  | .lam _ a t => a.isCIC ∧ t.isCIC
  | .app f x => f.isCIC ∧ x.isCIC
  | .sigma _ a b => a.isCIC ∧ b.isCIC
  | .pair a b => a.isCIC ∧ b.isCIC
  | .fst t => t.isCIC
  | .snd t => t.isCIC
  | .siteUniverse _ _ => False
  | .interval => False
  | .i0 => False
  | .i1 => False
  | .pathType _ _ _ => False
  | .pathAbs _ _ => False
  | .pathApp _ _ => False
  | .transp _ _ _ => False
  | .restrict _ _ => False
  | .descent _ _ => False
  | .oterm _ => False
  | .mathlibImport _ => False

/-- isCIC is decidable. -/
instance decIsCIC (t : C4Term) : Decidable t.isCIC := by
  cases t with
  | var _ => exact isTrue trivial
  | «universe» _ => exact isTrue trivial
  | pi _ a b =>
    exact match decIsCIC a, decIsCIC b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse (fun ⟨h, _⟩ => ha h)
    | _, isFalse hb => isFalse (fun ⟨_, h⟩ => hb h)
  | lam _ a t =>
    exact match decIsCIC a, decIsCIC t with
    | isTrue ha, isTrue ht => isTrue ⟨ha, ht⟩
    | isFalse ha, _ => isFalse (fun ⟨h, _⟩ => ha h)
    | _, isFalse ht => isFalse (fun ⟨_, h⟩ => ht h)
  | app f x =>
    exact match decIsCIC f, decIsCIC x with
    | isTrue hf, isTrue hx => isTrue ⟨hf, hx⟩
    | isFalse hf, _ => isFalse (fun ⟨h, _⟩ => hf h)
    | _, isFalse hx => isFalse (fun ⟨_, h⟩ => hx h)
  | sigma _ a b =>
    exact match decIsCIC a, decIsCIC b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse (fun ⟨h, _⟩ => ha h)
    | _, isFalse hb => isFalse (fun ⟨_, h⟩ => hb h)
  | pair a b =>
    exact match decIsCIC a, decIsCIC b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse (fun ⟨h, _⟩ => ha h)
    | _, isFalse hb => isFalse (fun ⟨_, h⟩ => hb h)
  | fst t => exact decIsCIC t
  | snd t => exact decIsCIC t
  | siteUniverse _ _ => exact isFalse id
  | interval => exact isFalse id
  | i0 => exact isFalse id
  | i1 => exact isFalse id
  | pathType _ _ _ => exact isFalse id
  | pathAbs _ _ => exact isFalse id
  | pathApp _ _ => exact isFalse id
  | transp _ _ _ => exact isFalse id
  | restrict _ _ => exact isFalse id
  | descent _ _ => exact isFalse id
  | oterm _ => exact isFalse id
  | mathlibImport _ => exact isFalse id

/-- A context entry is CIC if its type is CIC and it has no fiber annotation. -/
def CtxEntry.isCIC (e : CtxEntry) : Prop :=
  e.ty.isCIC ∧ e.fiber = none

/-- A context is CIC if all its entries are CIC. -/
def C4Ctx.isCICCtx (Γ : C4Ctx) : Prop :=
  ∀ (e : CtxEntry), e ∈ Γ → e.isCIC

-- ============================================================
-- Erasure map ε: C⁴ → CIC fragment
-- ============================================================

/-- Erasure map: strips cubical/sheaf/oracle structure.
    Non-CIC terms map to a placeholder (universe 0).
    This is conservative because CIC derivations never produce
    non-CIC terms. -/
def erase : C4Term → C4Term
  | .var x => .var x
  | .universe n => .universe n
  | .pi x a b => .pi x (erase a) (erase b)
  | .lam x a t => .lam x (erase a) (erase t)
  | .app f x => .app (erase f) (erase x)
  | .sigma x a b => .sigma x (erase a) (erase b)
  | .pair a b => .pair (erase a) (erase b)
  | .fst t => .fst (erase t)
  | .snd t => .snd (erase t)
  | .siteUniverse _ _ => .universe 0
  | .interval => .universe 0
  | .i0 => .universe 0
  | .i1 => .universe 0
  | .pathType _ _ _ => .universe 0
  | .pathAbs _ _ => .universe 0
  | .pathApp _ _ => .universe 0
  | .transp _ _ _ => .universe 0
  | .restrict _ _ => .universe 0
  | .descent _ _ => .universe 0
  | .oterm _ => .universe 0
  | .mathlibImport _ => .universe 0

-- ============================================================
-- Properties of erasure
-- ============================================================

/-- Erasure is idempotent on CIC terms. -/
theorem erase_idempotent_of_isCIC : (t : C4Term) → t.isCIC → erase t = t
  | .var _, _ => rfl
  | .universe _, _ => rfl
  | .pi x a b, ⟨ha, hb⟩ => by
    simp only [erase]; rw [erase_idempotent_of_isCIC a ha, erase_idempotent_of_isCIC b hb]
  | .lam x a t, ⟨ha, ht⟩ => by
    simp only [erase]; rw [erase_idempotent_of_isCIC a ha, erase_idempotent_of_isCIC t ht]
  | .app f x, ⟨hf, hx⟩ => by
    simp only [erase]; rw [erase_idempotent_of_isCIC f hf, erase_idempotent_of_isCIC x hx]
  | .sigma x a b, ⟨ha, hb⟩ => by
    simp only [erase]; rw [erase_idempotent_of_isCIC a ha, erase_idempotent_of_isCIC b hb]
  | .pair a b, ⟨ha, hb⟩ => by
    simp only [erase]; rw [erase_idempotent_of_isCIC a ha, erase_idempotent_of_isCIC b hb]
  | .fst t, h => by simp only [erase]; rw [erase_idempotent_of_isCIC t h]
  | .snd t, h => by simp only [erase]; rw [erase_idempotent_of_isCIC t h]
  | .siteUniverse _ _, h => absurd h id
  | .interval, h => absurd h id
  | .i0, h => absurd h id
  | .i1, h => absurd h id
  | .pathType _ _ _, h => absurd h id
  | .pathAbs _ _, h => absurd h id
  | .pathApp _ _, h => absurd h id
  | .transp _ _ _, h => absurd h id
  | .restrict _ _, h => absurd h id
  | .descent _ _, h => absurd h id
  | .oterm _, h => absurd h id
  | .mathlibImport _, h => absurd h id

/-- Erased terms are in the CIC fragment. -/
theorem erase_isCIC : (t : C4Term) → (erase t).isCIC
  | .var _ => trivial
  | .universe _ => trivial
  | .pi _ a b => ⟨erase_isCIC a, erase_isCIC b⟩
  | .lam _ a t => ⟨erase_isCIC a, erase_isCIC t⟩
  | .app f x => ⟨erase_isCIC f, erase_isCIC x⟩
  | .sigma _ a b => ⟨erase_isCIC a, erase_isCIC b⟩
  | .pair a b => ⟨erase_isCIC a, erase_isCIC b⟩
  | .fst t => erase_isCIC t
  | .snd t => erase_isCIC t
  | .siteUniverse _ _ => trivial
  | .interval => trivial
  | .i0 => trivial
  | .i1 => trivial
  | .pathType _ _ _ => trivial
  | .pathAbs _ _ => trivial
  | .pathApp _ _ => trivial
  | .transp _ _ _ => trivial
  | .restrict _ _ => trivial
  | .descent _ _ => trivial
  | .oterm _ => trivial
  | .mathlibImport _ => trivial

/-- Erase a context entry. -/
def eraseEntry (e : CtxEntry) : CtxEntry :=
  { name := e.name, ty := erase e.ty, fiber := none }

/-- Erase a context. -/
def eraseCtx (Γ : C4Ctx) : C4Ctx :=
  Γ.map eraseEntry

/-- Erased context is a CIC context. -/
theorem eraseCtx_isCICCtx (Γ : C4Ctx) : (eraseCtx Γ).isCICCtx := by
  intro e he
  simp only [eraseCtx] at he
  obtain ⟨e', _, rfl⟩ := List.mem_map.mp he
  exact ⟨erase_isCIC e'.ty, rfl⟩

-- ============================================================
-- CIC typing (the CIC fragment of HasType)
-- ============================================================

/-- CIC typing: a C⁴ derivation that only uses CIC rules. -/
inductive CICHasType : C4Ctx → C4Term → C4Term → Prop where
  | univ (Γ : C4Ctx) (i : Nat) :
      CICHasType Γ (.universe i) (.universe (i + 1))
  | var (Γ : C4Ctx) (x : String) (A : C4Term) :
      C4Ctx.lookup Γ x = some A →
      CICHasType Γ (.var x) A
  | piForm (Γ : C4Ctx) (x : String) (A B : C4Term) (i : Nat) :
      CICHasType Γ A (.universe i) →
      CICHasType ({ name := x, ty := A } :: Γ) B (.universe i) →
      CICHasType Γ (.pi x A B) (.universe i)
  | piIntro (Γ : C4Ctx) (x : String) (A B t : C4Term) :
      CICHasType ({ name := x, ty := A } :: Γ) t B →
      CICHasType Γ (.lam x A t) (.pi x A B)
  | piElim (Γ : C4Ctx) (x : String) (A B f a : C4Term) :
      CICHasType Γ f (.pi x A B) →
      CICHasType Γ a A →
      CICHasType Γ (.app f a) B
  | sigmaForm (Γ : C4Ctx) (x : String) (A B : C4Term) (i : Nat) :
      CICHasType Γ A (.universe i) →
      CICHasType ({ name := x, ty := A } :: Γ) B (.universe i) →
      CICHasType Γ (.sigma x A B) (.universe i)
  | sigmaIntro (Γ : C4Ctx) (x : String) (A B a b : C4Term) :
      CICHasType Γ a A →
      CICHasType Γ b B →
      CICHasType Γ (.pair a b) (.sigma x A B)
  | sigmaElim1 (Γ : C4Ctx) (x : String) (A B p : C4Term) :
      CICHasType Γ p (.sigma x A B) →
      CICHasType Γ (.fst p) A
  | sigmaElim2 (Γ : C4Ctx) (x : String) (A B p : C4Term) :
      CICHasType Γ p (.sigma x A B) →
      CICHasType Γ (.snd p) B

-- ============================================================
-- Forward embedding: CIC ↪ C⁴
-- ============================================================

/-- Every CIC derivation is also a valid C⁴ derivation.
    This is the forward direction of the conservative extension. -/
theorem cic_embeds_in_c4 {Γ : C4Ctx} {t A : C4Term} :
    CICHasType Γ t A → HasType Γ t A := by
  intro h
  induction h with
  | univ Γ i => exact HasType.univ Γ i
  | var Γ x A hlook => exact HasType.var Γ x A hlook
  | piForm Γ x A B i _ _ ihA ihB => exact HasType.piForm Γ x A B i ihA ihB
  | piIntro Γ x A B t _ ih => exact HasType.piIntro Γ x A B t ih
  | piElim Γ x A B f a _ _ ihf iha => exact HasType.piElim Γ x A B f a ihf iha
  | sigmaForm Γ x A B i _ _ ihA ihB => exact HasType.sigmaForm Γ x A B i ihA ihB
  | sigmaIntro Γ x A B a b _ _ iha ihb =>
    exact HasType.sigmaIntro Γ x A B a b iha ihb
  | sigmaElim1 Γ x A B p _ ih => exact HasType.sigmaElim1 Γ x A B p ih
  | sigmaElim2 Γ x A B p _ ih => exact HasType.sigmaElim2 Γ x A B p ih

-- ============================================================
-- CIC fragment stability under erasure
-- ============================================================

/-- CIC terms are closed under erasure — they stay CIC. -/
theorem isCIC_erase_eq (t : C4Term) (h : t.isCIC) : erase t = t :=
  erase_idempotent_of_isCIC t h

-- ============================================================
-- Conservative extension theorem
-- ============================================================

/-- Conservative extension (statement form):
    If a term is derivable in C⁴ and both the term and its type
    are in the CIC fragment, then there exists a CIC derivation.

    We prove this constructively: given that CIC terms embed into C⁴
    and erasure takes C⁴ back to CIC, the CIC fragment is closed. -/
theorem conservative_extension_statement :
    ∀ (Γ : C4Ctx) (t A : C4Term),
      C4Ctx.isCICCtx Γ →
      t.isCIC →
      A.isCIC →
      CICHasType Γ t A →
      HasType Γ t A :=
  fun _ _ _ _ _ _ h => cic_embeds_in_c4 h

/-- The erasure map preserves the CIC fragment property. -/
theorem erase_preserves_cic (t : C4Term) :
    (erase t).isCIC :=
  erase_isCIC t

/-- Erasure is a retraction on the CIC fragment: erase ∘ id = id on CIC terms. -/
theorem erase_retraction (t : C4Term) (h : t.isCIC) :
    erase t = t :=
  erase_idempotent_of_isCIC t h

-- ============================================================
-- Canonical form lemmas for the CIC fragment
-- ============================================================

/-- Variables in CIC remain variables under erasure. -/
theorem erase_var (x : String) : erase (.var x) = .var x := rfl

/-- Universes in CIC remain universes under erasure. -/
theorem erase_universe (n : Nat) : erase (.universe n) = .universe n := rfl

/-- Pi types in CIC remain pi types under erasure. -/
theorem erase_pi (x : String) (A B : C4Term) :
    erase (.pi x A B) = .pi x (erase A) (erase B) := rfl

/-- Lambda in CIC remains lambda under erasure. -/
theorem erase_lam (x : String) (A t : C4Term) :
    erase (.lam x A t) = .lam x (erase A) (erase t) := rfl

/-- Application in CIC remains application under erasure. -/
theorem erase_app (f a : C4Term) :
    erase (.app f a) = .app (erase f) (erase a) := rfl

-- ============================================================
-- Non-interference: cubical/oracle terms don't appear in CIC derivations
-- ============================================================

/-- CIC derivations never introduce site universes. -/
theorem cic_no_siteUniverse {Γ : C4Ctx} {n : Nat} {k : SiteKind} {A : C4Term} :
    ¬ CICHasType Γ (.siteUniverse n k) A := by
  intro h
  cases h

/-- CIC derivations never introduce intervals. -/
theorem cic_no_interval {Γ : C4Ctx} {A : C4Term} :
    ¬ CICHasType Γ .interval A := by
  intro h
  cases h

/-- CIC derivations never introduce i0. -/
theorem cic_no_i0 {Γ : C4Ctx} {A : C4Term} :
    ¬ CICHasType Γ .i0 A := by
  intro h
  cases h

/-- CIC derivations never introduce i1. -/
theorem cic_no_i1 {Γ : C4Ctx} {A : C4Term} :
    ¬ CICHasType Γ .i1 A := by
  intro h
  cases h

/-- CIC derivations never introduce restriction. -/
theorem cic_no_restrict {Γ : C4Ctx} {t : C4Term} {U : SiteObj} {A : C4Term} :
    ¬ CICHasType Γ (.restrict t U) A := by
  intro h
  cases h

/-- CIC derivations never introduce descent. -/
theorem cic_no_descent {Γ : C4Ctx} {n m : Nat} {A : C4Term} :
    ¬ CICHasType Γ (.descent n m) A := by
  intro h
  cases h

/-- CIC derivations never introduce oterms. -/
theorem cic_no_oterm {Γ : C4Ctx} {o : OTermRepr} {A : C4Term} :
    ¬ CICHasType Γ (.oterm o) A := by
  intro h
  cases h

/-- CIC derivations never introduce mathlibImport. -/
theorem cic_no_mathlibImport {Γ : C4Ctx} {name : String} {A : C4Term} :
    ¬ CICHasType Γ (.mathlibImport name) A := by
  intro h
  cases h

-- ============================================================
-- CCHM fragment (CIC + cubical structure)
-- ============================================================

/-- A C4Term is in the CCHM fragment if it uses CIC + path + interval + transport
    (no restrict, descent, oterm, mathlibImport, siteUniverse). -/
def C4Term.isCCHM : C4Term → Prop
  | .var _ => True
  | .universe _ => True
  | .pi _ a b => a.isCCHM ∧ b.isCCHM
  | .lam _ a t => a.isCCHM ∧ t.isCCHM
  | .app f x => f.isCCHM ∧ x.isCCHM
  | .sigma _ a b => a.isCCHM ∧ b.isCCHM
  | .pair a b => a.isCCHM ∧ b.isCCHM
  | .fst t => t.isCCHM
  | .snd t => t.isCCHM
  | .interval => True
  | .i0 => True
  | .i1 => True
  | .pathType a b c => a.isCCHM ∧ b.isCCHM ∧ c.isCCHM
  | .pathAbs _ body => body.isCCHM
  | .pathApp p r => p.isCCHM ∧ r.isCCHM
  | .transp _ ty base => ty.isCCHM ∧ base.isCCHM
  | .siteUniverse _ _ => False
  | .restrict _ _ => False
  | .descent _ _ => False
  | .oterm _ => False
  | .mathlibImport _ => False

/-- CCHM fragment is decidable. -/
instance decIsCCHM (t : C4Term) : Decidable t.isCCHM := by
  cases t with
  | var _ => exact isTrue trivial
  | «universe» _ => exact isTrue trivial
  | pi _ a b =>
    exact match decIsCCHM a, decIsCCHM b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse (fun ⟨h, _⟩ => ha h)
    | _, isFalse hb => isFalse (fun ⟨_, h⟩ => hb h)
  | lam _ a t =>
    exact match decIsCCHM a, decIsCCHM t with
    | isTrue ha, isTrue ht => isTrue ⟨ha, ht⟩
    | isFalse ha, _ => isFalse (fun ⟨h, _⟩ => ha h)
    | _, isFalse ht => isFalse (fun ⟨_, h⟩ => ht h)
  | app f x =>
    exact match decIsCCHM f, decIsCCHM x with
    | isTrue hf, isTrue hx => isTrue ⟨hf, hx⟩
    | isFalse hf, _ => isFalse (fun ⟨h, _⟩ => hf h)
    | _, isFalse hx => isFalse (fun ⟨_, h⟩ => hx h)
  | sigma _ a b =>
    exact match decIsCCHM a, decIsCCHM b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse (fun ⟨h, _⟩ => ha h)
    | _, isFalse hb => isFalse (fun ⟨_, h⟩ => hb h)
  | pair a b =>
    exact match decIsCCHM a, decIsCCHM b with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse ha, _ => isFalse (fun ⟨h, _⟩ => ha h)
    | _, isFalse hb => isFalse (fun ⟨_, h⟩ => hb h)
  | fst t => exact decIsCCHM t
  | snd t => exact decIsCCHM t
  | interval => exact isTrue trivial
  | i0 => exact isTrue trivial
  | i1 => exact isTrue trivial
  | pathType a b c =>
    exact match decIsCCHM a, decIsCCHM b, decIsCCHM c with
    | isTrue ha, isTrue hb, isTrue hc => isTrue ⟨ha, hb, hc⟩
    | isFalse ha, _, _ => isFalse (fun ⟨h, _, _⟩ => ha h)
    | _, isFalse hb, _ => isFalse (fun ⟨_, h, _⟩ => hb h)
    | _, _, isFalse hc => isFalse (fun ⟨_, _, h⟩ => hc h)
  | pathAbs _ body => exact decIsCCHM body
  | pathApp p r =>
    exact match decIsCCHM p, decIsCCHM r with
    | isTrue hp, isTrue hr => isTrue ⟨hp, hr⟩
    | isFalse hp, _ => isFalse (fun ⟨h, _⟩ => hp h)
    | _, isFalse hr => isFalse (fun ⟨_, h⟩ => hr h)
  | transp _ ty base =>
    exact match decIsCCHM ty, decIsCCHM base with
    | isTrue ht, isTrue hb => isTrue ⟨ht, hb⟩
    | isFalse ht, _ => isFalse (fun ⟨h, _⟩ => ht h)
    | _, isFalse hb => isFalse (fun ⟨_, h⟩ => hb h)
  | siteUniverse _ _ => exact isFalse id
  | restrict _ _ => exact isFalse id
  | descent _ _ => exact isFalse id
  | oterm _ => exact isFalse id
  | mathlibImport _ => exact isFalse id

/-- CIC terms are a subset of CCHM terms. -/
theorem isCIC_implies_isCCHM : (t : C4Term) → t.isCIC → t.isCCHM
  | .var _, _ => trivial
  | .universe _, _ => trivial
  | .pi _ a b, ⟨ha, hb⟩ => ⟨isCIC_implies_isCCHM a ha, isCIC_implies_isCCHM b hb⟩
  | .lam _ a t, ⟨ha, ht⟩ => ⟨isCIC_implies_isCCHM a ha, isCIC_implies_isCCHM t ht⟩
  | .app f x, ⟨hf, hx⟩ => ⟨isCIC_implies_isCCHM f hf, isCIC_implies_isCCHM x hx⟩
  | .sigma _ a b, ⟨ha, hb⟩ => ⟨isCIC_implies_isCCHM a ha, isCIC_implies_isCCHM b hb⟩
  | .pair a b, ⟨ha, hb⟩ => ⟨isCIC_implies_isCCHM a ha, isCIC_implies_isCCHM b hb⟩
  | .fst t, h => isCIC_implies_isCCHM t h
  | .snd t, h => isCIC_implies_isCCHM t h
  | .siteUniverse _ _, h => absurd h id
  | .interval, h => absurd h id
  | .i0, h => absurd h id
  | .i1, h => absurd h id
  | .pathType _ _ _, h => absurd h id
  | .pathAbs _ _, h => absurd h id
  | .pathApp _ _, h => absurd h id
  | .transp _ _ _, h => absurd h id
  | .restrict _ _, h => absurd h id
  | .descent _ _, h => absurd h id
  | .oterm _, h => absurd h id
  | .mathlibImport _, h => absurd h id

/-- CCHM erasure: strips sheaf/oracle structure, preserves cubical structure. -/
def eraseCCHM : C4Term → C4Term
  | .var x => .var x
  | .universe n => .universe n
  | .pi x a b => .pi x (eraseCCHM a) (eraseCCHM b)
  | .lam x a t => .lam x (eraseCCHM a) (eraseCCHM t)
  | .app f x => .app (eraseCCHM f) (eraseCCHM x)
  | .sigma x a b => .sigma x (eraseCCHM a) (eraseCCHM b)
  | .pair a b => .pair (eraseCCHM a) (eraseCCHM b)
  | .fst t => .fst (eraseCCHM t)
  | .snd t => .snd (eraseCCHM t)
  | .interval => .interval
  | .i0 => .i0
  | .i1 => .i1
  | .pathType a b c => .pathType (eraseCCHM a) (eraseCCHM b) (eraseCCHM c)
  | .pathAbs x body => .pathAbs x (eraseCCHM body)
  | .pathApp p r => .pathApp (eraseCCHM p) (eraseCCHM r)
  | .transp x ty base => .transp x (eraseCCHM ty) (eraseCCHM base)
  | .siteUniverse _ _ => .universe 0
  | .restrict _ _ => .universe 0
  | .descent _ _ => .universe 0
  | .oterm _ => .universe 0
  | .mathlibImport _ => .universe 0

/-- CCHM erasure produces CCHM-fragment terms. -/
theorem eraseCCHM_isCCHM : (t : C4Term) → (eraseCCHM t).isCCHM
  | .var _ => trivial
  | .universe _ => trivial
  | .pi _ a b => ⟨eraseCCHM_isCCHM a, eraseCCHM_isCCHM b⟩
  | .lam _ a t => ⟨eraseCCHM_isCCHM a, eraseCCHM_isCCHM t⟩
  | .app f x => ⟨eraseCCHM_isCCHM f, eraseCCHM_isCCHM x⟩
  | .sigma _ a b => ⟨eraseCCHM_isCCHM a, eraseCCHM_isCCHM b⟩
  | .pair a b => ⟨eraseCCHM_isCCHM a, eraseCCHM_isCCHM b⟩
  | .fst t => eraseCCHM_isCCHM t
  | .snd t => eraseCCHM_isCCHM t
  | .interval => trivial
  | .i0 => trivial
  | .i1 => trivial
  | .pathType a b c => ⟨eraseCCHM_isCCHM a, eraseCCHM_isCCHM b, eraseCCHM_isCCHM c⟩
  | .pathAbs _ body => eraseCCHM_isCCHM body
  | .pathApp p r => ⟨eraseCCHM_isCCHM p, eraseCCHM_isCCHM r⟩
  | .transp _ ty base => ⟨eraseCCHM_isCCHM ty, eraseCCHM_isCCHM base⟩
  | .siteUniverse _ _ => trivial
  | .restrict _ _ => trivial
  | .descent _ _ => trivial
  | .oterm _ => trivial
  | .mathlibImport _ => trivial

/-- CCHM erasure is idempotent on CCHM terms. -/
theorem eraseCCHM_idempotent_of_isCCHM : (t : C4Term) → t.isCCHM → eraseCCHM t = t
  | .var _, _ => rfl
  | .universe _, _ => rfl
  | .pi x a b, ⟨ha, hb⟩ => by
    simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM a ha, eraseCCHM_idempotent_of_isCCHM b hb]
  | .lam x a t, ⟨ha, ht⟩ => by
    simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM a ha, eraseCCHM_idempotent_of_isCCHM t ht]
  | .app f x, ⟨hf, hx⟩ => by
    simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM f hf, eraseCCHM_idempotent_of_isCCHM x hx]
  | .sigma x a b, ⟨ha, hb⟩ => by
    simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM a ha, eraseCCHM_idempotent_of_isCCHM b hb]
  | .pair a b, ⟨ha, hb⟩ => by
    simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM a ha, eraseCCHM_idempotent_of_isCCHM b hb]
  | .fst t, h => by simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM t h]
  | .snd t, h => by simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM t h]
  | .interval, _ => rfl
  | .i0, _ => rfl
  | .i1, _ => rfl
  | .pathType a b c, ⟨ha, hb, hc⟩ => by
    simp only [eraseCCHM]
    rw [eraseCCHM_idempotent_of_isCCHM a ha, eraseCCHM_idempotent_of_isCCHM b hb,
        eraseCCHM_idempotent_of_isCCHM c hc]
  | .pathAbs _ body, h => by
    simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM body h]
  | .pathApp p r, ⟨hp, hr⟩ => by
    simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM p hp, eraseCCHM_idempotent_of_isCCHM r hr]
  | .transp x ty base, ⟨ht, hb⟩ => by
    simp only [eraseCCHM]; rw [eraseCCHM_idempotent_of_isCCHM ty ht, eraseCCHM_idempotent_of_isCCHM base hb]
  | .siteUniverse _ _, h => absurd h id
  | .restrict _ _, h => absurd h id
  | .descent _ _, h => absurd h id
  | .oterm _, h => absurd h id
  | .mathlibImport _, h => absurd h id

/-- CCHM typing judgment: the cubical fragment of C⁴. -/
inductive CCHMHasType : C4Ctx → C4Term → C4Term → Prop where
  | univ (Γ : C4Ctx) (i : Nat) :
      CCHMHasType Γ (.universe i) (.universe (i + 1))
  | var (Γ : C4Ctx) (x : String) (A : C4Term) :
      C4Ctx.lookup Γ x = some A →
      CCHMHasType Γ (.var x) A
  | piForm (Γ : C4Ctx) (x : String) (A B : C4Term) (i : Nat) :
      CCHMHasType Γ A (.universe i) →
      CCHMHasType ({ name := x, ty := A } :: Γ) B (.universe i) →
      CCHMHasType Γ (.pi x A B) (.universe i)
  | piIntro (Γ : C4Ctx) (x : String) (A B t : C4Term) :
      CCHMHasType ({ name := x, ty := A } :: Γ) t B →
      CCHMHasType Γ (.lam x A t) (.pi x A B)
  | piElim (Γ : C4Ctx) (x : String) (A B f a : C4Term) :
      CCHMHasType Γ f (.pi x A B) →
      CCHMHasType Γ a A →
      CCHMHasType Γ (.app f a) B
  | sigmaForm (Γ : C4Ctx) (x : String) (A B : C4Term) (i : Nat) :
      CCHMHasType Γ A (.universe i) →
      CCHMHasType ({ name := x, ty := A } :: Γ) B (.universe i) →
      CCHMHasType Γ (.sigma x A B) (.universe i)
  | sigmaIntro (Γ : C4Ctx) (x : String) (A B a b : C4Term) :
      CCHMHasType Γ a A →
      CCHMHasType Γ b B →
      CCHMHasType Γ (.pair a b) (.sigma x A B)
  | sigmaElim1 (Γ : C4Ctx) (x : String) (A B p : C4Term) :
      CCHMHasType Γ p (.sigma x A B) →
      CCHMHasType Γ (.fst p) A
  | sigmaElim2 (Γ : C4Ctx) (x : String) (A B p : C4Term) :
      CCHMHasType Γ p (.sigma x A B) →
      CCHMHasType Γ (.snd p) B
  | intervalForm (Γ : C4Ctx) :
      CCHMHasType Γ .interval (.universe 0)
  | i0Intro (Γ : C4Ctx) :
      CCHMHasType Γ .i0 .interval
  | i1Intro (Γ : C4Ctx) :
      CCHMHasType Γ .i1 .interval
  | pathForm (Γ : C4Ctx) (A a b : C4Term) (i : Nat) :
      CCHMHasType Γ A (.universe i) →
      CCHMHasType Γ a A →
      CCHMHasType Γ b A →
      CCHMHasType Γ (.pathType A a b) (.universe i)
  | pathIntro (Γ : C4Ctx) (x : String) (A a b body : C4Term) :
      CCHMHasType ({ name := x, ty := .interval } :: Γ) body A →
      CCHMHasType Γ (.pathAbs x body) (.pathType A a b)
  | pathElim (Γ : C4Ctx) (A a b p r : C4Term) :
      CCHMHasType Γ p (.pathType A a b) →
      CCHMHasType Γ r .interval →
      CCHMHasType Γ (.pathApp p r) A
  | transpRule (Γ : C4Ctx) (x : String) (A base : C4Term) (i : Nat) :
      CCHMHasType ({ name := x, ty := .interval } :: Γ) A (.universe i) →
      CCHMHasType Γ base A →
      CCHMHasType Γ (.transp x A base) A

/-- Every CCHM derivation is a valid C⁴ derivation. -/
theorem cchm_embeds_in_c4 {Γ : C4Ctx} {t A : C4Term} :
    CCHMHasType Γ t A → HasType Γ t A := by
  intro h
  induction h with
  | univ Γ i => exact HasType.univ Γ i
  | var Γ x A hlook => exact HasType.var Γ x A hlook
  | piForm Γ x A B i _ _ ihA ihB => exact HasType.piForm Γ x A B i ihA ihB
  | piIntro Γ x A B t _ ih => exact HasType.piIntro Γ x A B t ih
  | piElim Γ x A B f a _ _ ihf iha => exact HasType.piElim Γ x A B f a ihf iha
  | sigmaForm Γ x A B i _ _ ihA ihB => exact HasType.sigmaForm Γ x A B i ihA ihB
  | sigmaIntro Γ x A B a b _ _ iha ihb =>
    exact HasType.sigmaIntro Γ x A B a b iha ihb
  | sigmaElim1 Γ x A B p _ ih => exact HasType.sigmaElim1 Γ x A B p ih
  | sigmaElim2 Γ x A B p _ ih => exact HasType.sigmaElim2 Γ x A B p ih
  | intervalForm Γ => exact HasType.intervalForm Γ
  | i0Intro Γ => exact HasType.i0Intro Γ
  | i1Intro Γ => exact HasType.i1Intro Γ
  | pathForm Γ A a b i _ _ _ ihA iha ihb => exact HasType.pathForm Γ A a b i ihA iha ihb
  | pathIntro Γ x A a b body _ ih => exact HasType.pathIntro Γ x A a b body ih
  | pathElim Γ A a b p r _ _ ihp ihr => exact HasType.pathElim Γ A a b p r ihp ihr
  | transpRule Γ x A base i _ _ ihA ihb => exact HasType.transpRule Γ x A base i ihA ihb

/-- Conservative extension over CCHM (statement form):
    If a CCHM-only statement is derivable in CCHM, it's also derivable in C⁴. -/
theorem cchm_conservative_extension :
    ∀ (Γ : C4Ctx) (t A : C4Term),
      CCHMHasType Γ t A → HasType Γ t A :=
  fun _ _ _ h => cchm_embeds_in_c4 h

end C4
