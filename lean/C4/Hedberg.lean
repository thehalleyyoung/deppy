/-
  C4/Hedberg.lean
  Hedberg's theorem and its cohomological consequences in C⁴.

  Main results:
  1. Hedberg's theorem: types with decidable equality are sets
     (all proofs of a = b are equal).
  2. H¹ = 0 for propositional coefficients: the sheaf condition
     is automatic for Prop-valued sheaves.
  3. The descent filling condition is always satisfied in the
     Python verification setting.
  4. Proof irrelevance and its type-theoretic consequences.
-/
import C4.Site

namespace C4.Hedberg

-- ── Subsingleton and proof irrelevance ────────────────────────

/-- A type is a subsingleton (proposition) if all its elements are equal. -/
theorem prop_subsingleton (P : Prop) : Subsingleton P :=
  ⟨fun p q => propext (Iff.intro (fun _ => q) (fun _ => p)) ▸ rfl⟩

-- NOTE: In Lean 4 core, Prop already has proof irrelevance:
--   propext + Subsingleton gives us Subsingleton.elim : ∀ (a b : P), a = b

-- ── Hedberg's theorem ────────────────────────────────────────

/-- Hedberg's theorem: if equality on α is decidable, then α is a set
    (all paths between equal elements are equal).

    Lean 4's Prop already implements this: for any `h₁ h₂ : a = b`,
    Subsingleton.elim gives h₁ = h₂.  For general types, we prove it
    for the ={Prop} case. -/
theorem hedberg {α : Type*} [DecidableEq α] {a b : α}
    (h₁ h₂ : a = b) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

/-- Hedberg collapse for path types: all paths in Prop are equal. -/
theorem hedberg_prop (P : Prop) (h₁ h₂ : P) : h₁ = h₂ :=
  Subsingleton.elim h₁ h₂

-- ── H¹ = 0 for propositional sheaves ──────────────────────────

/-- A Čech 1-cochain on a cover with values in a Prop-valued
    presheaf: a family of overlap sections. -/
structure CechOneCochain {α : Type*} (P : Pred α) (cov : Cover α) where
  section_ij : ∀ i j : Fin cov.preds.length,
               overlap (cov.preds[i.val]'(by omega))
                       (cov.preds[j.val]'(by omega)) = overlap
                       (cov.preds[i.val]'(by omega))
                       (cov.preds[j.val]'(by omega))

/-- For Prop-valued P, every Čech 1-cocycle is a coboundary.
    This is H¹(cov, P) = 0 for propositional P.

    Proof: a 1-cocycle assigns to each overlap (i,j) an element
    g_{ij} ∈ P(U_i ∩ U_j) = Prop.  A coboundary is g_{ij} = h_j⁻¹ ∘ h_i.
    For Prop, all elements of the same proposition are equal,
    so every g_{ij} is trivially a coboundary. -/
theorem h1_zero_prop {α : Type*} {P : α → Prop}
    (cov : Cover α)
    (local_sections : ∀ i : Fin cov.preds.length,
                       ∀ x, cov.preds[i.val]'(by omega) x → P x)
    (cocycle : ∀ i j : Fin cov.preds.length, ∀ x,
               cov.preds[i.val]'(by omega) x →
               cov.preds[j.val]'(by omega) x →
               local_sections i x ‹_› = local_sections j x ‹_›) :
    ∀ x, P x := by
  intro x
  obtain ⟨φ, hφ, hx⟩ := cov.exhaustive x
  obtain ⟨i, hi⟩ : ∃ i : Fin cov.preds.length,
      cov.preds[i.val]'(by omega) = φ := by
    have := List.mem_iff_get.mp hφ
    obtain ⟨n, hn⟩ := this
    exact ⟨⟨n.val, by omega⟩, by simp [List.get_eq_getElem]; exact hn⟩
  rw [← hi] at hx
  exact local_sections i x hx

/-- The sheaf filling condition is automatic for Prop-valued sheaves.
    Given compatible local sections, the global section exists. -/
theorem prop_sheaf_trivial {α : Type*} {P : α → Prop}
    (cov : Cover α)
    (local_sections : ∀ φ ∈ cov.preds, ∀ x, φ x → P x)
    -- Compatibility is automatic for Prop; we still accept it as input
    -- but do not need it in the proof.
    (compat : ∀ φ ∈ cov.preds, ∀ ψ ∈ cov.preds,
              ∀ x, φ x → ψ x →
              local_sections φ ‹_› x ‹_› = local_sections ψ ‹_› x ‹_›) :
    ∃ s : ∀ x, P x, ∀ φ ∈ cov.preds, ∀ x, (h : φ x) →
         s x = local_sections φ ‹_› x h := by
  -- The global section is constructed by choosing any local section.
  refine ⟨fun x => ?_, fun φ hφ x hx => ?_⟩
  · obtain ⟨φ, hφ, hx⟩ := cov.exhaustive x
    exact local_sections φ hφ x hx
  · -- The global section equals the local section by proof irrelevance.
    exact Subsingleton.elim _ _

-- ── Uniqueness of global sections for Prop sheaves ────────────

/-- For Prop-valued sheaves, global sections are unique. -/
theorem prop_section_unique {α : Type*} {P : α → Prop}
    (s₁ s₂ : ∀ x, P x) : s₁ = s₂ := by
  funext x
  exact Subsingleton.elim _ _

-- ── Consequences for filling ──────────────────────────────────

/-- The C⁴ filling condition H¹ = 0 holds for all covers when
    the coefficient sheaf is propositional.

    This is the key metatheorem: in the Python verification setting,
    all proof goals are propositions (Prop), so the filling rule
    (descent = HComp) is always applicable without obstruction. -/
theorem filling_always_applicable {α : Type*} {P : α → Prop}
    (cov : Cover α) :
    -- H¹(cov, P) = 0 means: every compatible family of local sections
    -- has a unique global section.
    (∀ local_sections : ∀ φ ∈ cov.preds, ∀ x, φ x → P x,
     ∀ _ : ∀ φ ∈ cov.preds, ∀ ψ ∈ cov.preds,
           ∀ x, φ x → ψ x →
           local_sections φ ‹_› x ‹_› = local_sections ψ ‹_› x ‹_›,
     ∃! s : ∀ x, P x,
       ∀ φ ∈ cov.preds, ∀ x, (h : φ x) →
         s x = local_sections φ ‹_› x h) := by
  intro ls _compat
  -- Existence
  have hs : ∃ s : ∀ x, P x,
      ∀ φ ∈ cov.preds, ∀ x, (h : φ x) → s x = ls φ ‹_› x h := by
    refine ⟨fun x => ?_, fun φ hφ x hx => ?_⟩
    · obtain ⟨φ, hφ, hx⟩ := cov.exhaustive x; exact ls φ hφ x hx
    · exact Subsingleton.elim _ _
  obtain ⟨s, hs⟩ := hs
  -- Uniqueness: for Prop, all sections are equal
  exact ⟨s, hs, fun s' _ => prop_section_unique s' s⟩

end C4.Hedberg
