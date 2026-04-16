/-
  C4/Basic.lean
  Basic definitions: universe levels, sorts, trust provenance.

  This file provides the foundation for the C⁴ formalization.
  No external dependencies.
-/
import Lean

namespace C4

-- ── Universe levels ────────────────────────────────────────
abbrev Level := Nat

-- ── Sorts ──────────────────────────────────────────────────
inductive Sort' : Type where
  | prop  : Sort'
  | type  : Level → Sort'
  deriving DecidableEq, Repr

-- ── Trust provenance ───────────────────────────────────────

/-- The five trust sources recognised by C⁴. -/
inductive TrustSource : Type where
  | kernel   : TrustSource  -- definitional reduction in the type kernel
  | z3       : TrustSource  -- discharged by Z3
  | lean     : TrustSource  -- imported from the Lean / Mathlib kernel
  | library  : TrustSource  -- library axiom (assumed but documented)
  | assumed  : TrustSource  -- explicit user assumption
  deriving DecidableEq, Repr

/-- Trust provenance is a finite set of sources. -/
abbrev Trust := List TrustSource

/-- The kernel trust level: only definitional reduction. -/
def Trust.kernel : Trust := [TrustSource.kernel]

/-- The bottom trust: no sources (only meaningful for vacuous proofs). -/
def Trust.empty : Trust := []

/-- Combine two trust sets — their union under decidable equality. -/
def Trust.combine (t₁ t₂ : Trust) : Trust :=
  t₁ ++ t₂.filter (fun s => !t₁.contains s)

/-- Trust is monotone: combining only adds sources. -/
theorem Trust.combine_supset_left (t₁ t₂ : Trust) :
    ∀ s ∈ t₁, s ∈ Trust.combine t₁ t₂ := by
  intro s hs
  simp [Trust.combine, List.mem_append]
  exact Or.inl hs

theorem Trust.combine_supset_right (t₁ t₂ : Trust) :
    ∀ s ∈ t₂, s ∈ Trust.combine t₁ t₂ := by
  intro s hs
  simp [Trust.combine, List.mem_append]
  by_cases h : s ∈ t₁
  · exact Or.inl h
  · right
    simp [List.mem_filter]
    exact ⟨hs, by simp [List.contains_iff_mem]; exact h⟩

/-- Combining trust is commutative (up to set equality). -/
theorem Trust.combine_comm_mem (t₁ t₂ : Trust) (s : TrustSource) :
    s ∈ Trust.combine t₁ t₂ ↔ s ∈ Trust.combine t₂ t₁ := by
  simp [Trust.combine, List.mem_append, List.mem_filter,
        List.contains_iff_mem]
  tauto

end C4
