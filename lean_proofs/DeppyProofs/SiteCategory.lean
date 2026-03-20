/-
  DeppyProofs.SiteCategory

  Formalization of program site categories and their covers.
  The key mathematical content:
  - ProgramSite forms a category with SiteMorphism as hom
  - Composition is contravariant composition of projection functions
  - CoveringFamily / Overlap model the Grothendieck topology data
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompleteLattice

open CategoryTheory

namespace DeppyProofs

/-- The five site families used in the formal development. -/
inductive SiteKind where
  | argumentBoundary
  | branchGuard
  | callResult
  | outputBoundary
  | errorSite
  deriving DecidableEq, Repr

/-- A program site: an observation point in a program's control/data flow. -/
structure ProgramSite where
  kind : SiteKind
  name : String
  deriving DecidableEq, Repr

/-- A morphism between program sites: a data-flow edge carrying a
    projection on refinement keys (contravariant: keys at target map
    back to keys at source). -/
structure SiteMorphism (s t : ProgramSite) where
  projection : String → Option String

@[ext]
theorem SiteMorphism.ext' {s t : ProgramSite} {f g : SiteMorphism s t}
    (h : f.projection = g.projection) : f = g := by
  cases f; cases g; congr

/-- ProgramSite forms a category. Composition is Option.bind
    (contravariant on projections). -/
instance : Category ProgramSite where
  Hom s t := SiteMorphism s t
  id _ := ⟨some⟩
  comp f g := ⟨fun k => (g.projection k).bind f.projection⟩
  id_comp f := by
    apply SiteMorphism.ext'
    funext k; simp [Option.bind]
  comp_id f := by
    apply SiteMorphism.ext'
    funext k; simp [Option.bind]
    cases h : f.projection k <;> rfl
  assoc f g h := by
    apply SiteMorphism.ext'
    funext k; simp [Option.bind]
    cases h' : h.projection k <;> simp [Option.bind]

/-! ## Covers -/

/-- A covering family for site `s`. -/
structure CoveringFamily (s : ProgramSite) where
  members : List ProgramSite
  morphisms : (t : ProgramSite) → t ∈ members → (t ⟶ s)

/-- An overlap: a site u with morphisms into two cover members. -/
structure Overlap (s : ProgramSite) (cf : CoveringFamily s) where
  u : ProgramSite
  i : ProgramSite
  j : ProgramSite
  hi : i ∈ cf.members
  hj : j ∈ cf.members
  toI : u ⟶ i
  toJ : u ⟶ j

/-- The trivial cover: {id : s → s}. -/
def trivialCover (s : ProgramSite) : CoveringFamily s where
  members := [s]
  morphisms := fun t ht => by
    have : t = s := List.mem_singleton.mp ht
    subst this; exact 𝟙 s

theorem identity_cover (s : ProgramSite) :
    (trivialCover s).members.length = 1 := rfl

end DeppyProofs
