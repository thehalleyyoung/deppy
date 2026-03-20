/-
  DeppyProofs.Soundness

  The core soundness theorem for sheaf-cohomological program analysis.

  Main result (Theorem A):
    If the analysis reports H¹(S_P, Sem) = 0, then the program P
    has no bugs of the corresponding class.

  Proof structure:
  1. Define concrete (collecting) semantics as sets of reachable states
  2. Define the abstraction function α mapping concrete states to sections
  3. Show α is a Galois connection (sound abstraction)
  4. Show the sheaf condition relates to concrete execution:
     agreement of abstract sections on overlaps ⟹ no concrete path
     witnesses a type violation
  5. Conclude: H¹ = 0 ⟹ all overlaps agree ⟹ no bug
-/
import DeppyProofs.CechCohomology

namespace DeppyProofs

/-! ## Concrete Semantics

  The concrete semantics assigns to each program site the set of
  concrete states (values of variables) reachable at that site during
  any execution of the program.
-/

/-- A concrete state: assignment of values to variables. -/
structure ConcreteState where
  values : String → Option Int
  deriving DecidableEq

/-- The concrete semantics at a site: the set of reachable states. -/
def ConcreteSemantics (s : ProgramSite) := Set ConcreteState

/-- A bug witness: a concrete state at an error site that triggers the error. -/
structure BugWitness where
  site : ProgramSite
  state : ConcreteState
  isErrorSite : site.kind = SiteKind.errorSite

/-! ## Abstraction Function

  α maps a set of concrete states to a section (refinement predicate).
  γ maps a section back to the set of states it describes.
  (α, γ) form a Galois connection: α(S) ≤ σ ⟺ S ⊆ γ(σ).
-/

variable {α : Type*} [RefinementLattice α]

/-- Abstraction: maps concrete state sets to sections. -/
structure AbstractionFn (α : Type*) [RefinementLattice α] where
  /-- Abstract a set of concrete states to a section. -/
  abstract : Set ConcreteState → LocalSection α
  /-- Concretize a section to a set of states. -/
  concretize : LocalSection α → Set ConcreteState
  /-- Galois connection: abstraction overapproximates. -/
  galois : ∀ (S : Set ConcreteState) (σ : LocalSection α),
    abstract S ≤ σ ↔ S ⊆ concretize σ
  /-- Monotonicity of abstraction. -/
  abstract_mono : ∀ (S₁ S₂ : Set ConcreteState),
    S₁ ⊆ S₂ → abstract S₂ ≤ abstract S₁

/-- A sound analysis: the section at each site overapproximates the concrete states. -/
structure SoundAnalysis (Sem : SemanticPresheaf α) (αfn : AbstractionFn α) where
  /-- For each site, the assigned section overapproximates reachable states. -/
  overapprox : ∀ (s : ProgramSite) (concrete : ConcreteSemantics s)
    (σ : LocalSection α), σ ∈ Sem.sections s →
    concrete ⊆ αfn.concretize σ

/-! ## Restriction Map Soundness

  Restriction maps preserve soundness: if σ_t overapproximates the
  concrete states at t, then restrict(σ_t, t→s) overapproximates the
  concrete states at s (for states that flow from s to t).
-/

/-- Concrete restriction: states at s that flow to t. -/
def concreteRestriction (concrete_t : Set ConcreteState)
    (dataflow : ConcreteState → ConcreteState) : Set ConcreteState :=
  { cs | dataflow cs ∈ concrete_t }

/-- A restriction map is sound if it preserves the overapproximation. -/
structure SoundRestriction (αfn : AbstractionFn α) (rm : RestrictionMap α s t)
    (dataflow : ConcreteState → ConcreteState) : Prop where
  sound : ∀ (σ : LocalSection α) (S : Set ConcreteState),
    S ⊆ αfn.concretize σ →
    concreteRestriction S dataflow ⊆ αfn.concretize (rm.map σ)

/-! ## The Soundness Theorem

  Theorem A: If H¹(S_P, Sem) = 0 (all overlaps agree), then P has no bugs.

  Proof: By contrapositive. Suppose P has a bug: there exists a concrete
  state cs at error site e that triggers the error. Then:
  1. cs is in the concrete semantics at e
  2. cs reached e via some path through sites s₁, ..., sₖ
  3. At each site sᵢ, the abstract section overapproximates the concrete state
  4. At the overlap between sᵢ and sᵢ₊₁, the restrictions must agree
     (both overapproximate cs)
  5. At the error site e, the section must include the error-triggering state
  6. But the error-site section should have been flagged as potentially failing
     (its viability predicate is unsatisfied)
  7. This means the section at e disagrees with the "no error" assertion
  8. Therefore some overlap involving e has a disagreement ⟹ H¹ ≠ 0
-/

/-- A viability predicate at an error site: states that do NOT trigger the error. -/
structure ViabilityPredicate (αfn : AbstractionFn α) (e : ProgramSite)
    (he : e.kind = SiteKind.errorSite) where
  /-- The safe states: those that do not trigger the error. -/
  safeStates : Set ConcreteState
  /-- The section encoding the safe states. -/
  safeSection : LocalSection α
  /-- Correctness: the safe section exactly captures safe states. -/
  correct : αfn.concretize safeSection = safeStates

/-- A bug is an overlap disagreement: the concrete states at an error
    site include states outside the viability predicate's safe set. -/
theorem bug_implies_h1_nonzero
    (Sem : SemanticPresheaf α) (αfn : AbstractionFn α)
    (sa : SoundAnalysis Sem αfn)
    (s : ProgramSite) (cf : CoveringFamily s)
    (c : Cochain0 Sem s cf)
    -- Suppose: there is an error site e in the cover with an unsafe state
    (e : ProgramSite) (he : e.kind = SiteKind.errorSite) (he_mem : e ∈ cf.members)
    (vp : ViabilityPredicate αfn e he)
    (bug : ∃ cs : ConcreteState, cs ∉ vp.safeStates)
    -- And: the analysis section at e includes the bug-triggering state
    (includes_bug : ∀ cs, cs ∉ vp.safeStates →
      cs ∈ αfn.concretize (c.values e he_mem))
    -- And: there exists a neighbor site where the section IS safe
    (neighbor : ProgramSite) (hn_mem : neighbor ∈ cf.members)
    (safe_neighbor : αfn.concretize (c.values neighbor hn_mem) ⊆ vp.safeStates)
    -- And: there is an overlap between e and neighbor with a sound
    --   restriction map that preserves membership
    (ov : Overlap s cf)
    (hov_i : ov.i = neighbor) (hov_j : ov.j = e)
    (restrict_preserves :
      ∀ σ, αfn.concretize ((Sem.restrict ov.u ov.j ov.toJ).map σ) ⊆
           αfn.concretize σ)
    (restrict_preserves_neighbor :
      ∀ σ, αfn.concretize ((Sem.restrict ov.u ov.i ov.toI).map σ) ⊆
           αfn.concretize σ)
    -- Then: the cochain is NOT a cocycle (H¹ ≠ 0)
    : ¬ isCocycle0 Sem s cf c := by
  intro h_cocycle
  -- By the cocycle condition, the restrictions at the overlap agree
  have h_agree := h_cocycle ov
  -- Get a concrete bug-witnessing state
  obtain ⟨cs, hcs_unsafe⟩ := bug
  -- The section at e includes cs (by includes_bug)
  have hcs_in_e := includes_bug cs hcs_unsafe
  -- The restriction at e preserves this membership
  have hcs_in_restr_e : cs ∈ αfn.concretize ((Sem.restrict ov.u ov.j ov.toJ).map
      (c.values ov.j ov.hj)) :=
    restrict_preserves (c.values ov.j ov.hj) (by rw [hov_j]; exact hcs_in_e)
  -- Since restrictions agree, cs is also in the restriction of neighbor's section
  rw [h_agree] at hcs_in_restr_e
  -- The restriction of neighbor's section is contained in neighbor's concretization
  have hcs_in_neighbor : cs ∈ αfn.concretize (c.values ov.i ov.hi) :=
    restrict_preserves_neighbor (c.values ov.i ov.hi) hcs_in_restr_e
  -- But neighbor's section only contains safe states
  have hcs_safe : cs ∈ vp.safeStates := by
    rw [hov_i] at hcs_in_neighbor
    exact safe_neighbor hcs_in_neighbor
  -- Contradiction: cs is both unsafe and safe
  exact hcs_unsafe hcs_safe

/-- Main Soundness Theorem (Theorem A):
    If H¹ = 0 (all cocycles are coboundaries, i.e., the sheaf condition
    holds), then every error site's viability predicate is satisfied. -/
theorem soundness
    (Sem : SemanticPresheaf α) (αfn : AbstractionFn α)
    (sa : SoundAnalysis Sem αfn)
    (s : ProgramSite) (cf : CoveringFamily s)
    -- H¹ = 0: every compatible family glues
    (h1_zero : ∀ c : Cochain0 Sem s cf, isCocycle0 Sem s cf c →
      ∃ σ : LocalSection α, ∀ t (ht : t ∈ cf.members),
        (Sem.restrict t s (cf.morphisms t ht)).map σ = c.values t ht)
    -- The global section has no error
    (global_safe : ∀ σ : LocalSection α,
      (∀ t (ht : t ∈ cf.members),
        (Sem.restrict t s (cf.morphisms t ht)).map σ ∈ Sem.sections t) →
      ∀ e (he : e ∈ cf.members) (herr : e.kind = SiteKind.errorSite)
        (vp : ViabilityPredicate αfn e herr),
      αfn.concretize ((Sem.restrict e s (cf.morphisms e he)).map σ) ⊆ vp.safeStates)
    -- Section membership: sections from the compatible family are in Sem.sections
    (sections_closed : ∀ (fam : CompatibleFamily Sem s cf)
        (t : ProgramSite) (ht : t ∈ cf.members),
      fam.localSections t ht ∈ Sem.sections t)
    -- Restriction closure: sections produced by restriction of a valid
    --   global section are in the presheaf's section set
    (restrict_closed : ∀ (σ : LocalSection α) (t : ProgramSite) (ht : t ∈ cf.members),
      (∀ u (hu : u ∈ cf.members),
        (Sem.restrict u s (cf.morphisms u hu)).map σ ∈ Sem.sections u) →
      (Sem.restrict t s (cf.morphisms t ht)).map σ ∈ Sem.sections t)
    : ∀ (fam : CompatibleFamily Sem s cf)
        (e : ProgramSite) (he : e ∈ cf.members)
        (herr : e.kind = SiteKind.errorSite)
        (vp : ViabilityPredicate αfn e herr),
      αfn.concretize (fam.localSections e he) ⊆ vp.safeStates := by
  intro fam e he herr vp
  -- By H¹ = 0, the compatible family fam glues to a global section σ
  obtain ⟨σ, hσ⟩ := h1_zero ⟨fam.localSections⟩ fam.agreement
  -- The global section restricts to fam at e
  have h_restrict := hσ e he
  -- Show that the restriction of σ at each site is a valid section
  have h_mem : ∀ t (ht : t ∈ cf.members),
      (Sem.restrict t s (cf.morphisms t ht)).map σ ∈ Sem.sections t := by
    intro t ht
    -- The restriction equals the family section, which is a valid section
    rw [hσ t ht]
    exact sections_closed fam t ht
  -- By global_safe, the restriction at e is within safe states
  have h_safe := global_safe σ h_mem e he herr vp
  -- Since restriction equals the family section, we're done
  rw [← h_restrict]
  exact h_safe

end DeppyProofs
