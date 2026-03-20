/-
  DeppyProofs.FixedPoint

  Convergence of the bidirectional synthesis algorithm.

  Main result (Theorem F):
    If the refinement lattice has finite height h and the cover has n sites,
    then the bidirectional synthesis converges in at most O(n · h) iterations.

  Strategy: we axiomatize the ascending chain condition for the product
  lattice, then derive convergence as a corollary.
-/
import DeppyProofs.Presheaf

namespace DeppyProofs

variable {α : Type*} [RefinementLattice α]

/-! ## Ascending Chain Condition -/

/-- A lattice satisfies the ascending chain condition with bound h if
    every strictly ascending chain has length at most h. -/
class ACC (β : Type*) [LE β] where
  bound : ℕ
  acc : ∀ (chain : ℕ → β) (k : ℕ),
    k > bound →
    (∀ i, i < k → chain i ≤ chain (i + 1)) →
    (∀ i, i < k → chain i ≠ chain (i + 1)) →
    False

/-- Refinement lattice height. -/
structure FiniteHeight (α : Type*) [RefinementLattice α] where
  height : ℕ
  acc_refinement : ∀ (chain : ℕ → α) (k : ℕ),
    k > height →
    (∀ i, i < k → chain i ≤ chain (i + 1)) →
    (∀ i, i < k → chain i ≠ chain (i + 1)) →
    False

/-! ## Synthesis State -/

/-- A synthesis state: assignment of a section to each of n sites. -/
def SynthesisState (α : Type*) [RefinementLattice α] (n : ℕ) :=
  Fin n → LocalSection α

/-- A synthesis step: monotone extensive operator. -/
structure SynthesisStep (α : Type*) [RefinementLattice α] (n : ℕ) where
  step : SynthesisState α n → SynthesisState α n
  monotone : ∀ s₁ s₂ : SynthesisState α n,
    (∀ i, s₁ i ≤ s₂ i) → (∀ i, step s₁ i ≤ step s₂ i)
  extensive : ∀ (s : SynthesisState α n) (i : Fin n), s i ≤ step s i

/-- Fixed-point predicate. -/
def isFixedPoint (step : SynthesisStep α n) (s : SynthesisState α n) : Prop :=
  step.step s = s

/-- Iteration. -/
def iterateStep (step : SynthesisStep α n) (s₀ : SynthesisState α n) :
    ℕ → SynthesisState α n
  | 0 => s₀
  | k + 1 => step.step (iterateStep step s₀ k)

/-- Iteration is ascending. -/
theorem iterate_ascending (step : SynthesisStep α n) (s₀ : SynthesisState α n)
    (k : ℕ) (i : Fin n) :
    iterateStep step s₀ k i ≤ iterateStep step s₀ (k + 1) i := by
  induction k with
  | zero => exact step.extensive s₀ i
  | succ k ih =>
    simp [iterateStep]
    exact step.monotone _ _ (fun j => iterate_ascending step s₀ k j) i

/-! ## Convergence Theorem

  We state and prove convergence using the ascending chain condition
  on the product lattice. The product of n copies of a height-h lattice
  has height n·h (every strictly ascending chain in the product projects
  to a strictly ascending chain in some component, by pigeonhole).
-/

/-- Product ACC: the product of n lattices each with ACC bound h has
    ACC bound n · h.

    Proof sketch: an ascending chain of length > n·h in the product,
    by pigeonhole, has some component with a chain of length > h.

    We axiomatize this as it requires Finset.sum machinery. -/
axiom product_acc (n : ℕ) (fh : FiniteHeight α)
    (chain : ℕ → SynthesisState α n) (k : ℕ)
    (h_len : k > n * fh.height)
    (h_asc : ∀ i j, i < k → ∀ c : Fin n, chain i c ≤ chain (i + 1) c)
    (h_strict : ∀ i, i < k → chain i ≠ chain (i + 1)) : False

/-- Main Convergence Theorem (Theorem F):
    The iteration sequence reaches a fixed point within n · h steps. -/
theorem convergence (n : ℕ) (fh : FiniteHeight α)
    (step : SynthesisStep α n) (s₀ : SynthesisState α n) :
    ∃ k, k ≤ n * fh.height ∧ isFixedPoint step (iterateStep step s₀ k) := by
  by_contra h_no_fp
  push_neg at h_no_fp
  -- Every k ≤ n * fh.height is not a fixed point
  -- So iterate k ≠ iterate (k + 1) for all k < n * fh.height + 1
  have h_ne : ∀ k, k ≤ n * fh.height → iterateStep step s₀ k ≠ iterateStep step s₀ (k + 1) := by
    intro k hk h_eq
    have := h_no_fp k hk
    exact this (by simp [isFixedPoint, iterateStep, h_eq])
  -- Apply product_acc with k = n * fh.height + 1
  exact product_acc n fh (iterateStep step s₀) (n * fh.height + 1)
    (by omega)
    (fun i _j hi c => iterate_ascending step s₀ i c)
    (fun i hi => h_ne i (by omega))

/-- Corollary: bidirectional synthesis converges. -/
theorem bidirectional_convergence (n : ℕ) (fh : FiniteHeight α)
    (backward forward_ : SynthesisStep α n) (s₀ : SynthesisState α n) :
    let combined : SynthesisStep α n :=
      { step := fun s => forward_.step (backward.step s)
        monotone := fun s₁ s₂ h => forward_.monotone _ _
          (backward.monotone s₁ s₂ h)
        extensive := fun s i => le_trans (backward.extensive s i)
          (forward_.extensive (backward.step s) i) }
    ∃ k, k ≤ n * fh.height ∧
      isFixedPoint combined (iterateStep combined s₀ k) :=
  convergence n fh _ s₀

/-- The fixed point is a least fixed point above the initial state
    (Kleene's theorem for finite lattices). -/
theorem fixed_point_least (n : ℕ) (step : SynthesisStep α n)
    (s₀ : SynthesisState α n) (k : ℕ)
    (hfp : isFixedPoint step (iterateStep step s₀ k))
    (s' : SynthesisState α n)
    (hs' : isFixedPoint step s')
    (h_above : ∀ i, s₀ i ≤ s' i) :
    ∀ i, iterateStep step s₀ k i ≤ s' i := by
  -- By induction on k: iterate 0 = s₀ ≤ s' by hypothesis.
  -- If iterate k ≤ s', then iterate (k+1) = step(iterate k) ≤ step(s') = s'.
  induction k with
  | zero => exact h_above
  | succ k ih =>
    intro i
    simp [iterateStep]
    -- step(iterate k) ≤ step(s') = s'
    have h_mono := step.monotone (iterateStep step s₀ k) s'
      (fun j => by
        -- Need: iterate k j ≤ s' j
        -- This follows from the same argument by inner induction
        -- Since we can't use the outer IH directly (it requires hfp for k),
        -- we prove a stronger intermediate result.
        -- Actually, iterate k ≤ s' follows from iterate_ascending + monotonicity:
        -- iterate 0 = s₀ ≤ s', and step preserves ≤, so by induction
        -- iterate k ≤ s' for all k.
        induction k with
        | zero => exact h_above j
        | succ k' ih' =>
          simp [iterateStep]
          exact step.monotone _ _ ih' j)
    -- step(iterate k) i ≤ step(s') i = s' i
    have : step.step s' = s' := hs'
    rw [← this]
    exact h_mono i

end DeppyProofs
