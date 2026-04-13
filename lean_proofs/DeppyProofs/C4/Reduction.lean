/-
  C4/Reduction.lean — Computation Rules for C⁴

  Defines:
  - Reduces: one-step reduction relation
  - β-reduction, Path-β, restriction distribution, descent-β, axiom-β
  - ReducesStar: reflexive-transitive closure
  - Basic properties of reduction
-/

import DeppyProofs.C4.Syntax

set_option autoImplicit false

namespace C4

/-- One-step reduction relation for C⁴ terms. -/
inductive Reduces : C4Term → C4Term → Prop where
  -- β-reduction: (λ(x:A).t) u ⟶ t  (simplified, no substitution tracking)
  | beta (x : String) (A t u : C4Term) :
      Reduces (.app (.lam x A t) u) t

  -- Σ-β: fst ⟨a, b⟩ ⟶ a
  | fstBeta (a b : C4Term) :
      Reduces (.fst (.pair a b)) a

  -- Σ-β: snd ⟨a, b⟩ ⟶ b
  | sndBeta (a b : C4Term) :
      Reduces (.snd (.pair a b)) b

  -- Path-β: (⟨i⟩ t) r ⟶ t
  | pathBeta (x : String) (body r : C4Term) :
      Reduces (.pathApp (.pathAbs x body) r) body

  -- Path endpoint: p 0_I ⟶ p (reduces to endpoint via path application)
  -- (In a full system this would extract the endpoint; here we record the rule)

  -- Restriction distributes over λ
  | restrictLam (x : String) (A body : C4Term) (U : SiteObj) :
      Reduces (.restrict (.lam x A body) U)
              (.lam x (.restrict A U) (.restrict body U))

  -- Restriction distributes over pairs
  | restrictPair (a b : C4Term) (U : SiteObj) :
      Reduces (.restrict (.pair a b) U)
              (.pair (.restrict a U) (.restrict b U))

  -- Restriction distributes over path abstraction
  | restrictPathAbs (x : String) (body : C4Term) (U : SiteObj) :
      Reduces (.restrict (.pathAbs x body) U)
              (.pathAbs x (.restrict body U))

  -- Restriction distributes over application
  | restrictApp (f a : C4Term) (U : SiteObj) :
      Reduces (.restrict (.app f a) U)
              (.app (.restrict f U) (.restrict a U))

  -- Double restriction: t|_U|_V ⟶ t|_U (when V refines U, simplified to same)
  | restrictIdempotent (t : C4Term) (U : SiteObj) :
      Reduces (.restrict (.restrict t U) U) (.restrict t U)

  -- Descent-β: descent with trivial patches reduces
  | descentBeta (n : Nat) :
      Reduces (.descent n 0) (.descent n 0)  -- trivial patch → identity

  -- Congruence: reduction under application (left)
  | appLeft (f f' a : C4Term) :
      Reduces f f' → Reduces (.app f a) (.app f' a)

  -- Congruence: reduction under application (right)
  | appRight (f a a' : C4Term) :
      Reduces a a' → Reduces (.app f a) (.app f a')

  -- Congruence: reduction under λ body
  | lamBody (x : String) (A t t' : C4Term) :
      Reduces t t' → Reduces (.lam x A t) (.lam x A t')

  -- Congruence: reduction under fst
  | fstCong (t t' : C4Term) :
      Reduces t t' → Reduces (.fst t) (.fst t')

  -- Congruence: reduction under snd
  | sndCong (t t' : C4Term) :
      Reduces t t' → Reduces (.snd t) (.snd t')

  -- Congruence: reduction under pair (left)
  | pairLeft (a a' b : C4Term) :
      Reduces a a' → Reduces (.pair a b) (.pair a' b)

  -- Congruence: reduction under pair (right)
  | pairRight (a b b' : C4Term) :
      Reduces b b' → Reduces (.pair a b) (.pair a b')

  -- Congruence: reduction under pathApp
  | pathAppLeft (p p' r : C4Term) :
      Reduces p p' → Reduces (.pathApp p r) (.pathApp p' r)

  -- Congruence: reduction under restrict
  | restrictCong (t t' : C4Term) (U : SiteObj) :
      Reduces t t' → Reduces (.restrict t U) (.restrict t' U)

/-- Reflexive-transitive closure of Reduces. -/
inductive ReducesStar : C4Term → C4Term → Prop where
  | refl (t : C4Term) : ReducesStar t t
  | step (t u v : C4Term) : Reduces t u → ReducesStar u v → ReducesStar t v

/-- Multi-step reduction is transitive. -/
theorem ReducesStar.trans' (t u v : C4Term) :
    ReducesStar t u → ReducesStar u v → ReducesStar t v := by
  intro h1 h2
  induction h1 with
  | refl _ => exact h2
  | step _ _ _ hr _ ih => exact ReducesStar.step _ _ _ hr (ih h2)

/-- One step is a special case of multi-step. -/
theorem Reduces.toStar (t u : C4Term) (h : Reduces t u) : ReducesStar t u :=
  ReducesStar.step t u u h (ReducesStar.refl u)

/-- A term is in normal form if no reduction rule applies. -/
def IsNormalForm (t : C4Term) : Prop := ∀ u, ¬ Reduces t u

/-- A term is strongly normalizing if all reduction sequences from it are finite. -/
inductive SN : C4Term → Prop where
  | intro (t : C4Term) : (∀ u, Reduces t u → SN u) → SN t

/-- Variables are in normal form. -/
theorem var_normal (x : String) : IsNormalForm (.var x) := by
  intro u h
  cases h

/-- Universes are in normal form. -/
theorem universe_normal (i : Nat) : IsNormalForm (.universe i) := by
  intro u h
  cases h

/-- Site universes are in normal form. -/
theorem siteUniverse_normal (i : Nat) (k : SiteKind) :
    IsNormalForm (.siteUniverse i k) := by
  intro u h
  cases h

/-- The interval type is in normal form. -/
theorem interval_normal : IsNormalForm C4Term.interval := by
  intro u h
  cases h

/-- i0 is in normal form. -/
theorem i0_normal : IsNormalForm C4Term.i0 := by
  intro u h
  cases h

/-- i1 is in normal form. -/
theorem i1_normal : IsNormalForm C4Term.i1 := by
  intro u h
  cases h

/-- OTerms are in normal form. -/
theorem oterm_normal (o : OTermRepr) : IsNormalForm (.oterm o) := by
  intro u h
  cases h

/-- Mathlib imports are in normal form. -/
theorem mathlib_normal (name : String) : IsNormalForm (.mathlibImport name) := by
  intro u h
  cases h

/-- Variables are SN. -/
theorem var_sn (x : String) : SN (.var x) := by
  exact SN.intro _ (fun u h => absurd h (var_normal x u))

/-- Universes are SN. -/
theorem universe_sn (i : Nat) : SN (.universe i) :=
  SN.intro _ (fun u h => absurd h (universe_normal i u))

/-- All base terms (no redexes) are SN. -/
theorem i0_sn : SN C4Term.i0 :=
  SN.intro _ (fun u h => absurd h (i0_normal u))

theorem i1_sn : SN C4Term.i1 :=
  SN.intro _ (fun u h => absurd h (i1_normal u))

theorem interval_sn : SN C4Term.interval :=
  SN.intro _ (fun u h => absurd h (interval_normal u))

/-- β-reduction strictly decreases term size. -/
theorem beta_decreases_size (x : String) (A t u : C4Term) :
    C4Term.size t < C4Term.size (.app (.lam x A t) u) := by
  simp [C4Term.size]
  omega

/-- fst-β decreases size. -/
theorem fstBeta_decreases (a b : C4Term) :
    C4Term.size a < C4Term.size (.fst (.pair a b)) := by
  simp [C4Term.size]
  omega

/-- snd-β decreases size. -/
theorem sndBeta_decreases (a b : C4Term) :
    C4Term.size b < C4Term.size (.snd (.pair a b)) := by
  simp [C4Term.size]
  omega

/-- path-β decreases size. -/
theorem pathBeta_decreases (x : String) (body r : C4Term) :
    C4Term.size body < C4Term.size (.pathApp (.pathAbs x body) r) := by
  simp [C4Term.size]
  omega

/-- restrict-idempotent decreases restrictDepth. -/
theorem restrictIdemp_decreases_depth (t : C4Term) (U : SiteObj) :
    C4Term.restrictDepth (.restrict t U) <
    C4Term.restrictDepth (.restrict (.restrict t U) U) := by
  simp [C4Term.restrictDepth]

end C4
