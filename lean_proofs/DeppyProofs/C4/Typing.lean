/-
  C4/Typing.lean — Typing Rules for C⁴

  Defines:
  - C4Ctx: typing contexts with optional fiber annotations
  - HasType: the main typing judgment Γ ⊢ t : A
  - HasTypeFiber: fiber-local typing Γ ⊢_U t : A
  - DefEq: definitional equality Γ ⊢ t ≡ u : A
  - All formation/intro/elim rules for Π, Σ, Path, Restriction, Descent
-/

import DeppyProofs.C4.Syntax

set_option autoImplicit false

namespace C4

/-- A context entry: variable name, its type, and optional fiber annotation. -/
structure CtxEntry where
  name : String
  ty : C4Term
  fiber : Option SiteObj := none
  deriving DecidableEq, Repr

/-- Typing context — ordered list of bindings. -/
abbrev C4Ctx := List CtxEntry

/-- Context lookup. -/
def C4Ctx.lookup (Γ : C4Ctx) (x : String) : Option C4Term :=
  match Γ.find? (fun e => e.name == x) with
  | some e => some e.ty
  | none => none

/-- Well-formed context (all types well-typed at some universe level). -/
inductive WfCtx : C4Ctx → Prop where
  | empty : WfCtx []
  | extend {Γ : C4Ctx} {x : String} {A : C4Term} {f : Option SiteObj} :
      WfCtx Γ → WfCtx ({ name := x, ty := A, fiber := f } :: Γ)

/-- The main typing judgment: Γ ⊢ t : A -/
inductive HasType : C4Ctx → C4Term → C4Term → Prop where
  -- Universe hierarchy
  | univ (Γ : C4Ctx) (i : Nat) :
      HasType Γ (.universe i) (.universe (i + 1))
  | siteUniv (Γ : C4Ctx) (i : Nat) (k : SiteKind) :
      HasType Γ (.siteUniverse i k) (.universe (i + 1))

  -- Variables
  | var (Γ : C4Ctx) (x : String) (A : C4Term) :
      C4Ctx.lookup Γ x = some A →
      HasType Γ (.var x) A

  -- Π formation, introduction, elimination
  | piForm (Γ : C4Ctx) (x : String) (A B : C4Term) (i : Nat) :
      HasType Γ A (.universe i) →
      HasType ({ name := x, ty := A } :: Γ) B (.universe i) →
      HasType Γ (.pi x A B) (.universe i)
  | piIntro (Γ : C4Ctx) (x : String) (A B t : C4Term) :
      HasType ({ name := x, ty := A } :: Γ) t B →
      HasType Γ (.lam x A t) (.pi x A B)
  | piElim (Γ : C4Ctx) (x : String) (A B f a : C4Term) :
      HasType Γ f (.pi x A B) →
      HasType Γ a A →
      HasType Γ (.app f a) B

  -- Σ formation, introduction, elimination
  | sigmaForm (Γ : C4Ctx) (x : String) (A B : C4Term) (i : Nat) :
      HasType Γ A (.universe i) →
      HasType ({ name := x, ty := A } :: Γ) B (.universe i) →
      HasType Γ (.sigma x A B) (.universe i)
  | sigmaIntro (Γ : C4Ctx) (x : String) (A B a b : C4Term) :
      HasType Γ a A →
      HasType Γ b B →
      HasType Γ (.pair a b) (.sigma x A B)
  | sigmaElim1 (Γ : C4Ctx) (x : String) (A B p : C4Term) :
      HasType Γ p (.sigma x A B) →
      HasType Γ (.fst p) A
  | sigmaElim2 (Γ : C4Ctx) (x : String) (A B p : C4Term) :
      HasType Γ p (.sigma x A B) →
      HasType Γ (.snd p) B

  -- Interval type
  | intervalForm (Γ : C4Ctx) :
      HasType Γ .interval (.universe 0)
  | i0Intro (Γ : C4Ctx) :
      HasType Γ .i0 .interval
  | i1Intro (Γ : C4Ctx) :
      HasType Γ .i1 .interval

  -- Path types (cubical)
  | pathForm (Γ : C4Ctx) (A a b : C4Term) (i : Nat) :
      HasType Γ A (.universe i) →
      HasType Γ a A →
      HasType Γ b A →
      HasType Γ (.pathType A a b) (.universe i)
  | pathIntro (Γ : C4Ctx) (x : String) (A a b body : C4Term) :
      HasType ({ name := x, ty := .interval } :: Γ) body A →
      HasType Γ (.pathAbs x body) (.pathType A a b)
  | pathElim (Γ : C4Ctx) (A a b p r : C4Term) :
      HasType Γ p (.pathType A a b) →
      HasType Γ r .interval →
      HasType Γ (.pathApp p r) A

  -- Transport
  | transpRule (Γ : C4Ctx) (x : String) (A base : C4Term) (i : Nat) :
      HasType ({ name := x, ty := .interval } :: Γ) A (.universe i) →
      HasType Γ base A →
      HasType Γ (.transp x A base) A

  -- Restriction to fibers
  | restrictRule (Γ : C4Ctx) (t A : C4Term) (U : SiteObj) :
      HasType Γ t A →
      HasType Γ (.restrict t U) A

  -- Descent
  | descentRule (Γ : C4Ctx) (n m : Nat) (A : C4Term) (i : Nat) :
      HasType Γ A (.universe i) →
      HasType Γ (.descent n m) A

  -- OTerm embedding
  | otermRule (Γ : C4Ctx) (o : OTermRepr) :
      HasType Γ (.oterm o) (.oterm .onil)

  -- Mathlib import
  | mathlibRule (Γ : C4Ctx) (name : String) (A : C4Term) :
      HasType Γ (.mathlibImport name) A

/-- Definitional equality: Γ ⊢ t ≡ u : A -/
inductive DefEq : C4Ctx → C4Term → C4Term → C4Term → Prop where
  -- Reflexivity, symmetry, transitivity
  | refl (Γ : C4Ctx) (t A : C4Term) :
      HasType Γ t A → DefEq Γ t t A
  | symm (Γ : C4Ctx) (t u A : C4Term) :
      DefEq Γ t u A → DefEq Γ u t A
  | trans (Γ : C4Ctx) (t u v A : C4Term) :
      DefEq Γ t u A → DefEq Γ u v A → DefEq Γ t v A

  -- β-reduction
  | beta (Γ : C4Ctx) (x : String) (A B t a : C4Term) :
      HasType ({ name := x, ty := A } :: Γ) t B →
      HasType Γ a A →
      DefEq Γ (.app (.lam x A t) a) t (.pi x A B)

  -- Σ-β
  | fstBeta (Γ : C4Ctx) (x : String) (A B a b : C4Term) :
      HasType Γ a A → HasType Γ b B →
      DefEq Γ (.fst (.pair a b)) a A
  | sndBeta (Γ : C4Ctx) (x : String) (A B a b : C4Term) :
      HasType Γ a A → HasType Γ b B →
      DefEq Γ (.snd (.pair a b)) b B

  -- Path-β: (⟨i⟩ t) r ≡ t[r/i]
  | pathBeta (Γ : C4Ctx) (x : String) (A body r : C4Term) :
      HasType ({ name := x, ty := .interval } :: Γ) body A →
      HasType Γ r .interval →
      DefEq Γ (.pathApp (.pathAbs x body) r) body A

  -- Path endpoint rules
  | pathZero (Γ : C4Ctx) (A a b p : C4Term) :
      HasType Γ p (.pathType A a b) →
      DefEq Γ (.pathApp p .i0) a A
  | pathOne (Γ : C4Ctx) (A a b p : C4Term) :
      HasType Γ p (.pathType A a b) →
      DefEq Γ (.pathApp p .i1) b A

  -- Restriction distributes over λ
  | restrictLam (Γ : C4Ctx) (x : String) (A body : C4Term) (U : SiteObj) :
      DefEq Γ (.restrict (.lam x A body) U)
              (.lam x (.restrict A U) (.restrict body U))
              (.pi x (.restrict A U) (.restrict body U))

  -- Restriction distributes over pairs
  | restrictPair (Γ : C4Ctx) (x : String) (A B a b : C4Term) (U : SiteObj) :
      DefEq Γ (.restrict (.pair a b) U)
              (.pair (.restrict a U) (.restrict b U))
              (.sigma x (.restrict A U) (.restrict B U))

  -- Restriction distributes over path abstraction
  | restrictPathAbs (Γ : C4Ctx) (x : String) (body : C4Term) (U : SiteObj) :
      DefEq Γ (.restrict (.pathAbs x body) U)
              (.pathAbs x (.restrict body U))
              (.restrict (.pathAbs x body) U)

/-- Fiber-local typing: Γ ⊢_U t : A (typing at a specific fiber). -/
inductive HasTypeFiber : C4Ctx → SiteObj → C4Term → C4Term → Prop where
  | fromGlobal (Γ : C4Ctx) (U : SiteObj) (t A : C4Term) :
      HasType Γ t A → HasTypeFiber Γ U (.restrict t U) (.restrict A U)
  | localTerm (Γ : C4Ctx) (U : SiteObj) (t A : C4Term) :
      HasType ({ name := "fiber", ty := .oterm (.ovar (toString (repr U))), fiber := some U } :: Γ) t A →
      HasTypeFiber Γ U t A

/-- Variables are well-typed when present in context. -/
theorem var_well_typed (Γ : C4Ctx) (x : String) (A : C4Term)
    (h : C4Ctx.lookup Γ x = some A) : HasType Γ (.var x) A :=
  HasType.var Γ x A h

/-- Every universe is well-typed in any context. -/
theorem univ_well_typed (Γ : C4Ctx) (i : Nat) :
    HasType Γ (.universe i) (.universe (i + 1)) :=
  HasType.univ Γ i

/-- Restriction preserves typing. -/
theorem restrict_preserves_typing (Γ : C4Ctx) (t A : C4Term) (U : SiteObj)
    (h : HasType Γ t A) : HasType Γ (.restrict t U) A :=
  HasType.restrictRule Γ t A U h

/-- Fiber-local typing follows from global typing. -/
theorem global_implies_fiber (Γ : C4Ctx) (U : SiteObj) (t A : C4Term)
    (h : HasType Γ t A) : HasTypeFiber Γ U (.restrict t U) (.restrict A U) :=
  HasTypeFiber.fromGlobal Γ U t A h

/-- β-reduction respects typing. -/
theorem beta_type_preservation (Γ : C4Ctx) (x : String) (A B t a : C4Term)
    (ht : HasType ({ name := x, ty := A } :: Γ) t B)
    (ha : HasType Γ a A) :
    DefEq Γ (.app (.lam x A t) a) t (.pi x A B) :=
  DefEq.beta Γ x A B t a ht ha

/-- Definitional equality is reflexive. -/
theorem defeq_refl (Γ : C4Ctx) (t A : C4Term) (h : HasType Γ t A) :
    DefEq Γ t t A :=
  DefEq.refl Γ t A h

/-- Definitional equality is symmetric. -/
theorem defeq_symm (Γ : C4Ctx) (t u A : C4Term)
    (h : DefEq Γ t u A) : DefEq Γ u t A :=
  DefEq.symm Γ t u A h

/-- Definitional equality is transitive. -/
theorem defeq_trans (Γ : C4Ctx) (t u v A : C4Term)
    (h1 : DefEq Γ t u A) (h2 : DefEq Γ u v A) : DefEq Γ t v A :=
  DefEq.trans Γ t u v A h1 h2

end C4
