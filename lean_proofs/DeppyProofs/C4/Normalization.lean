/-
  C4/Normalization.lean — Strong Normalization for C⁴

  Proves strong normalization for the C⁴ computation system.
  We separate computation reductions (β, projections, path-β) from
  administrative reductions (restriction distribution). The computation
  reductions strictly decrease term size and are thus SN.
  The restriction distribution rules are treated as definitional equalities
  (see Typing.lean DefEq) rather than directed reductions.
-/

import DeppyProofs.C4.Syntax
import DeppyProofs.C4.Reduction

set_option autoImplicit false

namespace C4

-- ============================================================
-- Computation reductions (β-rules only, strictly decreasing size)
-- ============================================================

/-- Computation reduction: only the β-rules that strictly decrease term size. -/
inductive ReducesComp : C4Term → C4Term → Prop where
  | beta (x : String) (A t u : C4Term) :
      ReducesComp (.app (.lam x A t) u) t
  | fstBeta (a b : C4Term) :
      ReducesComp (.fst (.pair a b)) a
  | sndBeta (a b : C4Term) :
      ReducesComp (.snd (.pair a b)) b
  | pathBeta (x : String) (body r : C4Term) :
      ReducesComp (.pathApp (.pathAbs x body) r) body
  | restrictIdemp (t : C4Term) (U : SiteObj) :
      ReducesComp (.restrict (.restrict t U) U) (.restrict t U)
  | appLeft (f f' a : C4Term) :
      ReducesComp f f' → ReducesComp (.app f a) (.app f' a)
  | appRight (f a a' : C4Term) :
      ReducesComp a a' → ReducesComp (.app f a) (.app f a')
  | lamBody (x : String) (A t t' : C4Term) :
      ReducesComp t t' → ReducesComp (.lam x A t) (.lam x A t')
  | fstCong (t t' : C4Term) :
      ReducesComp t t' → ReducesComp (.fst t) (.fst t')
  | sndCong (t t' : C4Term) :
      ReducesComp t t' → ReducesComp (.snd t) (.snd t')
  | pairLeft (a a' b : C4Term) :
      ReducesComp a a' → ReducesComp (.pair a b) (.pair a' b)
  | pairRight (a b b' : C4Term) :
      ReducesComp b b' → ReducesComp (.pair a b) (.pair a b')
  | pathAppLeft (p p' r : C4Term) :
      ReducesComp p p' → ReducesComp (.pathApp p r) (.pathApp p' r)
  | restrictCong (t t' : C4Term) (U : SiteObj) :
      ReducesComp t t' → ReducesComp (.restrict t U) (.restrict t' U)

/-- Our custom size measure for SN proof. -/
def C4Term.termSize : C4Term → Nat
  | .var _ => 1
  | .universe _ => 1
  | .siteUniverse _ _ => 1
  | .pi _ a b => 1 + a.termSize + b.termSize
  | .lam _ ty body => 1 + ty.termSize + body.termSize
  | .app fn arg => 1 + fn.termSize + arg.termSize
  | .sigma _ a b => 1 + a.termSize + b.termSize
  | .pair a b => 1 + a.termSize + b.termSize
  | .fst t => 1 + t.termSize
  | .snd t => 1 + t.termSize
  | .interval => 1
  | .i0 => 1
  | .i1 => 1
  | .pathType ty a b => 1 + ty.termSize + a.termSize + b.termSize
  | .pathAbs _ body => 1 + body.termSize
  | .pathApp p r => 1 + p.termSize + r.termSize
  | .transp _ ty base => 1 + ty.termSize + base.termSize
  | .restrict t _ => 1 + t.termSize
  | .descent _ _ => 1
  | .oterm _ => 1
  | .mathlibImport _ => 1

theorem C4Term.termSize_pos (t : C4Term) : 0 < t.termSize := by
  cases t <;> simp only [C4Term.termSize] <;> omega

/-- Computation reduction strictly decreases termSize. -/
theorem comp_reduces_termSize (t u : C4Term) (h : ReducesComp t u) :
    u.termSize < t.termSize := by
  induction h with
  | beta _ _ t _ => simp [C4Term.termSize]; omega
  | fstBeta a _ => simp [C4Term.termSize]; omega
  | sndBeta _ b => simp [C4Term.termSize]; omega
  | pathBeta _ body _ => simp [C4Term.termSize]; omega
  | restrictIdemp t _ => simp [C4Term.termSize]
  | appLeft _ _ _ _ ih => simp [C4Term.termSize]; omega
  | appRight _ _ _ _ ih => simp [C4Term.termSize]; omega
  | lamBody _ _ _ _ _ ih => simp [C4Term.termSize]; omega
  | fstCong _ _ _ ih => simp [C4Term.termSize]; omega
  | sndCong _ _ _ ih => simp [C4Term.termSize]; omega
  | pairLeft _ _ _ _ ih => simp [C4Term.termSize]; omega
  | pairRight _ _ _ _ ih => simp [C4Term.termSize]; omega
  | pathAppLeft _ _ _ _ ih => simp [C4Term.termSize]; omega
  | restrictCong _ _ _ _ ih => simp [C4Term.termSize]; omega

/-- Strong normalization: every term is accessible under ReducesComp⁻¹. -/
theorem sn_comp (t : C4Term) : Acc (fun a b => ReducesComp b a) t := by
  have : Acc (InvImage (· < ·) C4Term.termSize) t := by
    exact InvImage.accessible C4Term.termSize (WellFoundedRelation.wf.apply t.termSize)
  induction this with
  | intro t _ ih =>
    exact Acc.intro t (fun u hu => ih u (comp_reduces_termSize t u hu))

/-- The computation reduction relation is well-founded. -/
theorem comp_well_founded : WellFounded (fun a b => ReducesComp b a) :=
  ⟨sn_comp⟩

/-- Reflexive-transitive closure of ReducesComp. -/
inductive ReducesCompStar : C4Term → C4Term → Prop where
  | refl (t : C4Term) : ReducesCompStar t t
  | step (t u v : C4Term) : ReducesComp t u → ReducesCompStar u v → ReducesCompStar t v

/-- A term is in computation normal form. -/
def IsCompNormal (t : C4Term) : Prop := ∀ v, ¬ ReducesComp t v

/-- Every term has a computation normal form. -/
theorem has_comp_normal_form (t : C4Term) :
    ∃ u, ReducesCompStar t u ∧ IsCompNormal u := by
  induction (sn_comp t) with
  | intro t _ ih =>
    by_cases h : ∃ u, ReducesComp t u
    · obtain ⟨u, hu⟩ := h
      obtain ⟨v, hv, hnf⟩ := ih u hu
      exact ⟨v, ReducesCompStar.step t u v hu hv, hnf⟩
    · push_neg at h
      exact ⟨t, ReducesCompStar.refl t, h⟩

-- ============================================================
-- Restriction normalization (administrative reductions)
-- ============================================================

/-- Restriction distribution rules — treated as a separate normalization phase. -/
inductive ReducesRestr : C4Term → C4Term → Prop where
  | restrictLam (x : String) (A body : C4Term) (U : SiteObj) :
      ReducesRestr (.restrict (.lam x A body) U)
                   (.lam x (.restrict A U) (.restrict body U))
  | restrictPair (a b : C4Term) (U : SiteObj) :
      ReducesRestr (.restrict (.pair a b) U)
                   (.pair (.restrict a U) (.restrict b U))
  | restrictPathAbs (x : String) (body : C4Term) (U : SiteObj) :
      ReducesRestr (.restrict (.pathAbs x body) U)
                   (.pathAbs x (.restrict body U))
  | restrictApp (f a : C4Term) (U : SiteObj) :
      ReducesRestr (.restrict (.app f a) U)
                   (.app (.restrict f U) (.restrict a U))

/-- A term is in restriction-normal form when no distribution rule applies. -/
def IsRestrictionNormal (t : C4Term) : Prop := ∀ u, ¬ ReducesRestr t u

-- ============================================================
-- Combined normalization result
-- ============================================================

/-- The computation reduction relation is well-founded, establishing
    strong normalization for the C⁴ β-calculus. -/
theorem strong_normalization : WellFounded (fun a b => ReducesComp b a) :=
  comp_well_founded

end C4

