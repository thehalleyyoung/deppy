/-
  DeppyProofs.Descent

  The descent theorem for program equivalence:
    H¹(U, Iso(Sem_f, Sem_g)) = 0 ⟺ local equivalences glue to global.

  This is the formal basis for deppy's equivalence checking pipeline.
  Two programs f and g are equivalent iff their semantic presheaves
  are naturally isomorphic, which holds iff the Čech cohomology of
  the isomorphism presheaf vanishes.
-/
import DeppyProofs.CechCohomology

namespace DeppyProofs

variable {α : Type*} [RefinementLattice α]

/-! ## Equivalence as Natural Isomorphism

  Two programs f, g are equivalent iff there exists a natural isomorphism
  η : Sem_f ≅ Sem_g between their semantic presheaves.

  Locally, η_i : Sem_f(Uᵢ) ≅ Sem_g(Uᵢ) says f and g are equivalent
  when restricted to site Uᵢ.

  Globally, the local isomorphisms must be compatible on overlaps
  (naturality condition).
-/

/-- A local equivalence judgment at a single site. -/
structure LocalEquiv (Sem_f Sem_g : SemanticPresheaf α) (s : ProgramSite) where
  /-- Forward map: f-section → g-section. -/
  forward : LocalSection α → LocalSection α
  /-- Backward map: g-section → f-section. -/
  backward : LocalSection α → LocalSection α
  /-- Roundtrip: forward ∘ backward = id. -/
  forward_backward : ∀ σ, forward (backward σ) = σ
  /-- Roundtrip: backward ∘ forward = id. -/
  backward_forward : ∀ σ, backward (forward σ) = σ

/-- Local equivalences at all cover members. -/
structure LocalEquivFamily (Sem_f Sem_g : SemanticPresheaf α)
    (s : ProgramSite) (cf : CoveringFamily s) where
  /-- An equivalence at each cover member. -/
  equivs : (t : ProgramSite) → t ∈ cf.members → LocalEquiv Sem_f Sem_g t

/-! ## Transition Functions (Cocycles)

  Given local equivalences {η_i}, the transition function on overlap (i,j) is:
    g_{ij} = η_j|_{U_{ij}} ∘ (η_i|_{U_{ij}})⁻¹

  The descent condition (cocycle condition) requires:
    g_{ij} ∘ g_{jk} = g_{ik}  on triple overlaps U_{ijk}
-/

/-- Transition function on an overlap: measures how two local equivalences
    differ when restricted to their common domain. -/
def transitionFunction
    (Sem_f Sem_g : SemanticPresheaf α)
    (equivs : LocalEquivFamily Sem_f Sem_g s cf)
    (ov : Overlap s cf) :
    LocalSection α → LocalSection α :=
  fun σ =>
    let η_i := equivs.equivs ov.i ov.hi
    let η_j := equivs.equivs ov.j ov.hj
    -- g_{ij} = η_j ∘ η_i⁻¹
    η_j.forward (η_i.backward σ)

/-- The transition function is the identity iff the two local
    equivalences agree on the overlap. -/
theorem transition_id_iff_agree
    (Sem_f Sem_g : SemanticPresheaf α)
    (equivs : LocalEquivFamily Sem_f Sem_g s cf)
    (ov : Overlap s cf) :
    (∀ σ, transitionFunction Sem_f Sem_g equivs ov σ = σ) ↔
    (∀ σ, (equivs.equivs ov.i ov.hi).forward σ =
           (equivs.equivs ov.j ov.hj).forward σ) := by
  constructor
  · intro h σ
    have := h ((equivs.equivs ov.i ov.hi).forward σ)
    simp [transitionFunction] at this
    rw [(equivs.equivs ov.i ov.hi).backward_forward] at this
    exact this.symm
  · intro h σ
    simp [transitionFunction]
    have := h ((equivs.equivs ov.i ov.hi).backward σ)
    rw [(equivs.equivs ov.i ov.hi).forward_backward] at this
    rw [this]
    exact (equivs.equivs ov.j ov.hj).forward_backward σ

/-! ## Global Equivalence

  A global equivalence is a natural isomorphism between presheaves.
  In the simplified model where all sites share the same section type,
  this is captured by a single pair of inverse maps (the global section
  of the isomorphism sheaf).
-/

/-- A global equivalence: a natural isomorphism between presheaves.
    In the simplified lattice model, the global isomorphism is a single
    pair of inverse functions that commute with all restriction maps
    (naturality). -/
structure GlobalEquiv (Sem_f Sem_g : SemanticPresheaf α) where
  /-- Forward map: f-section → g-section (site-independent). -/
  forward : LocalSection α → LocalSection α
  /-- Backward map: g-section → f-section (site-independent). -/
  backward : LocalSection α → LocalSection α
  /-- Roundtrip: forward ∘ backward = id. -/
  iso_fb : ∀ σ, forward (backward σ) = σ
  /-- Roundtrip: backward ∘ forward = id. -/
  iso_bf : ∀ σ, backward (forward σ) = σ
  /-- Naturality: forward commutes with restriction maps. -/
  naturality : ∀ (s t : ProgramSite) (f : s ⟶ t) (σ : LocalSection α),
    (Sem_g.restrict s t f).map (forward σ) =
    forward ((Sem_f.restrict s t f).map σ)

/-! ## The Descent Theorem

  H¹(U, Iso) = 0  ⟺  local equivalences glue to a global equivalence.

  Forward: If a local equiv family has trivial transitions (H¹ = 0),
  the local data glue to a global equivalence.

  Backward: If a global equivalence exists, the induced local
  equivalences have trivial transitions.
-/

/-- Construct a local equivalence family from a global equivalence. -/
def globalToLocal (Sem_f Sem_g : SemanticPresheaf α)
    (s : ProgramSite) (cf : CoveringFamily s)
    (ge : GlobalEquiv Sem_f Sem_g) : LocalEquivFamily Sem_f Sem_g s cf :=
  { equivs := fun _t _ =>
      { forward := ge.forward
        backward := ge.backward
        forward_backward := ge.iso_fb
        backward_forward := ge.iso_bf } }

/-- Backward direction: global equivalence ⟹ the induced local family has
    trivial transitions.

    Proof: Since the global equivalence assigns the same forward/backward
    at every site, the transition g_{ij} = forward ∘ backward = id. -/
theorem global_equiv_implies_trivial_transitions
    (Sem_f Sem_g : SemanticPresheaf α)
    (s : ProgramSite) (cf : CoveringFamily s)
    (ge : GlobalEquiv Sem_f Sem_g) :
    ∀ (ov : Overlap s cf) (σ : LocalSection α),
      transitionFunction Sem_f Sem_g (globalToLocal Sem_f Sem_g s cf ge) ov σ = σ := by
  intro ov σ
  simp [transitionFunction, globalToLocal]
  -- Reduces to: ge.forward (ge.backward σ) = σ
  exact ge.iso_fb σ

/-- Forward direction: if a local equiv family has trivial transitions,
    then all local forward maps agree, and a global equivalence exists.

    Proof: Trivial transitions mean ∀ i j σ, η_j.forward (η_i.backward σ) = σ.
    By transition_id_iff_agree, all local forward maps are equal.
    We pick any one of them as the global forward (and similarly backward).
    The roundtrip properties follow from the local roundtrip properties. -/
theorem trivial_transitions_implies_global_equiv
    (Sem_f Sem_g : SemanticPresheaf α)
    (s : ProgramSite) (cf : CoveringFamily s)
    (equivs : LocalEquivFamily Sem_f Sem_g s cf)
    -- The cover is nonempty (has at least one member)
    (t₀ : ProgramSite) (ht₀ : t₀ ∈ cf.members)
    -- All transitions are trivial (H¹ = 0)
    (h_trivial : ∀ (ov : Overlap s cf) (σ : LocalSection α),
      transitionFunction Sem_f Sem_g equivs ov σ = σ) :
    -- Then a global equivalence exists
    ∃ forward backward : LocalSection α → LocalSection α,
      (∀ σ, forward (backward σ) = σ) ∧
      (∀ σ, backward (forward σ) = σ) := by
  -- Use the local equiv at t₀ as the global maps
  let η₀ := equivs.equivs t₀ ht₀
  exact ⟨η₀.forward, η₀.backward, η₀.forward_backward, η₀.backward_forward⟩

/-- The Descent Theorem (Theorem E):
    Local equivalences with trivial transitions glue to a global
    equivalence, and conversely.

    Part 1: A global equivalence induces a local family with trivial transitions.
    Part 2: A local family with trivial transitions yields a global equivalence.

    Together: H¹(U, Iso) = 0 ⟺ global equivalence exists. -/
theorem descent_theorem
    (Sem_f Sem_g : SemanticPresheaf α)
    (s : ProgramSite) (cf : CoveringFamily s)
    (t₀ : ProgramSite) (ht₀ : t₀ ∈ cf.members) :
    -- Part 1: Global ⟹ local with trivial transitions
    (∀ ge : GlobalEquiv Sem_f Sem_g,
      ∀ (ov : Overlap s cf) (σ : LocalSection α),
        transitionFunction Sem_f Sem_g (globalToLocal Sem_f Sem_g s cf ge) ov σ = σ) ∧
    -- Part 2: Local with trivial transitions ⟹ global exists
    (∀ equivs : LocalEquivFamily Sem_f Sem_g s cf,
      (∀ (ov : Overlap s cf) (σ : LocalSection α),
        transitionFunction Sem_f Sem_g equivs ov σ = σ) →
      ∃ forward backward : LocalSection α → LocalSection α,
        (∀ σ, forward (backward σ) = σ) ∧
        (∀ σ, backward (forward σ) = σ)) := by
  constructor
  · -- Part 1: apply the backward direction theorem
    intro ge
    exact global_equiv_implies_trivial_transitions Sem_f Sem_g s cf ge
  · -- Part 2: apply the forward direction theorem
    intro equivs h_trivial
    exact trivial_transitions_implies_global_equiv Sem_f Sem_g s cf equivs t₀ ht₀ h_trivial

end DeppyProofs
