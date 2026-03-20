/-
  DeppyProofs.Presheaf

  Formalization of semantic presheaves over program site categories.

  A semantic presheaf Sem : S^op → Lat assigns to each program site
  a complete lattice of "local sections" (type information at that site),
  and to each morphism a restriction map (monotone function).

  Key definitions:
  - Section: local type information at a site (carrier + refinements)
  - SemanticPresheaf: contravariant functor from sites to lattices
  - SheafCondition: gluing axiom (agreement on overlaps ⟹ unique global section)
  - GlobalSection: a compatible family of local sections
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Order.CompleteLattice
import DeppyProofs.SiteCategory

open CategoryTheory

namespace DeppyProofs

/-! ## Refinement Predicates

  Refinements form a bounded lattice where ⊤ = no information (any value)
  and ⊥ = contradiction (no value). Meet is conjunction, join is disjunction.
-/

/-- Abstract refinement predicate. In the implementation these are Z3 formulas;
    here we model them as elements of a complete lattice. -/
class RefinementLattice (α : Type*) extends CompleteLattice α

/-- A local section at a program site: the type information observable there. -/
structure LocalSection (α : Type*) [RefinementLattice α] where
  /-- The refinement predicate at this site. -/
  refinement : α
  /-- Trust level: how the section was derived. -/
  trusted : Bool := true

variable {α : Type*} [RefinementLattice α]

/-- The information order on sections: s₁ ≤ s₂ iff s₁ has more information. -/
instance : LE (LocalSection α) where
  le s₁ s₂ := s₂.refinement ≤ s₁.refinement

instance : Preorder (LocalSection α) where
  le_refl s := le_refl s.refinement
  le_trans s₁ s₂ s₃ h₁₂ h₂₃ := le_trans h₂₃ h₁₂

/-! ## Restriction Maps

  A restriction map transforms a section at site t into a section at site s,
  given a morphism s → t. Restriction preserves the lattice order
  (is monotone) and satisfies functoriality.
-/

/-- A restriction map: transforms sections along a morphism.
    Must be monotone (preserving information order). -/
structure RestrictionMap (α : Type*) [RefinementLattice α]
    (s t : ProgramSite) where
  map : LocalSection α → LocalSection α
  monotone : ∀ a b : LocalSection α, a ≤ b → map a ≤ map b

/-- A semantic presheaf assigns sections to sites and restriction maps to morphisms. -/
structure SemanticPresheaf (α : Type*) [RefinementLattice α] where
  /-- Assign a set of possible sections to each site. -/
  sections : ProgramSite → Set (LocalSection α)
  /-- For each morphism s → t, a restriction map. -/
  restrict : (s t : ProgramSite) → (s ⟶ t) → RestrictionMap α s t
  /-- Functoriality: restriction along identity is identity. -/
  restrict_id : ∀ (s : ProgramSite) (σ : LocalSection α),
    (restrict s s (𝟙 s)).map σ = σ
  /-- Functoriality: restriction along composition is composition of restrictions. -/
  restrict_comp : ∀ (s t u : ProgramSite) (f : s ⟶ t) (g : t ⟶ u)
    (σ : LocalSection α),
    (restrict s u (f ≫ g)).map σ = (restrict s t f).map ((restrict t u g).map σ)

/-! ## The Sheaf Condition

  The sheaf condition states that for any cover {Uᵢ → s} and any
  family of local sections {σᵢ ∈ Sem(Uᵢ)} that agree on overlaps,
  there exists a unique global section σ ∈ Sem(s) that restricts to
  each σᵢ.
-/

/-- A compatible family: local sections at cover members that agree on overlaps. -/
structure CompatibleFamily (Sem : SemanticPresheaf α) (s : ProgramSite)
    (cf : CoveringFamily s) where
  /-- A section at each cover member. -/
  localSections : (t : ProgramSite) → t ∈ cf.members → LocalSection α
  /-- Agreement on overlaps: for any overlap (u; i,j), the restrictions agree. -/
  agreement : ∀ (ov : Overlap s cf),
    (Sem.restrict ov.u ov.i ov.toI).map (localSections ov.i ov.hi) =
    (Sem.restrict ov.u ov.j ov.toJ).map (localSections ov.j ov.hj)

/-- A global section: a section at s that restricts to a given compatible family. -/
structure GlobalSectionWitness (Sem : SemanticPresheaf α) (s : ProgramSite)
    (cf : CoveringFamily s) (fam : CompatibleFamily Sem s cf) where
  /-- The global section at s. -/
  section_ : LocalSection α
  /-- It restricts to each local section. -/
  restricts : ∀ (t : ProgramSite) (ht : t ∈ cf.members),
    (Sem.restrict t s (cf.morphisms t ht)).map section_ = fam.localSections t ht

/-- The sheaf condition for a presheaf Sem with respect to a cover cf. -/
structure SheafCondition (Sem : SemanticPresheaf α) (s : ProgramSite)
    (cf : CoveringFamily s) where
  /-- Existence: every compatible family has a global section. -/
  existence : ∀ (fam : CompatibleFamily Sem s cf),
    GlobalSectionWitness Sem s cf fam
  /-- Uniqueness: the global section is unique. -/
  uniqueness : ∀ (fam : CompatibleFamily Sem s cf)
    (g₁ g₂ : GlobalSectionWitness Sem s cf fam),
    g₁.section_ = g₂.section_

/-! ## Key Theorem: H⁰ as Global Sections

  H⁰(U, Sem) = ker(δ⁰) is exactly the set of global sections:
  families of local sections that agree on all overlaps.
-/

/-- H⁰ is the set of compatible families (global sections). -/
def H0 (Sem : SemanticPresheaf α) (s : ProgramSite) (cf : CoveringFamily s) :=
  { fam : CompatibleFamily Sem s cf // True }

/-- If Sem is a sheaf, every element of H⁰ lifts to a unique section at s. -/
theorem h0_lifts_to_section (Sem : SemanticPresheaf α) (s : ProgramSite)
    (cf : CoveringFamily s) (sc : SheafCondition Sem s cf)
    (fam : CompatibleFamily Sem s cf) :
    ∃! σ : LocalSection α,
      ∀ (t : ProgramSite) (ht : t ∈ cf.members),
        (Sem.restrict t s (cf.morphisms t ht)).map σ = fam.localSections t ht := by
  obtain ⟨⟨σ, hσ⟩⟩ := ⟨sc.existence fam⟩
  exact ⟨σ, hσ, fun σ' hσ' =>
    sc.uniqueness fam ⟨σ, hσ⟩ ⟨σ', hσ'⟩⟩

end DeppyProofs
