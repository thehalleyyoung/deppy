/-
  DeppyProofs: Formal Verification of Sheaf-Cohomological Program Analysis

  This library formalizes the core metatheory behind deppy's use of
  Čech cohomology for program analysis:

  1. SiteCategory  — program site categories and Grothendieck topologies
  2. Presheaf      — semantic presheaves over site categories
  3. Separation    — separation results vs. traditional program analysis

  C⁴ (Cohomological Calculus of Constructions) metatheory:
  4. Syntax         — C⁴ term language
  5. Typing         — typing rules and definitional equality
  6. Reduction      — computation rules
  7. Dichotomies    — 24 axioms D1-D24
  8. Normalization   — strong normalization
  9. Confluence     — confluence via Newman's lemma
  10. Decidability   — decidability of type checking
  11. Conservativity — conservative extension over CIC
  12. Descent        — descent theorem (H¹ = 0 ⟺ gluing)
  13. FunExt         — function extensionality and univalence
-/

import DeppyProofs.SiteCategory
import DeppyProofs.Presheaf
import DeppyProofs.Separation
import DeppyProofs.C4.Syntax
import DeppyProofs.C4.Typing
import DeppyProofs.C4.Reduction
import DeppyProofs.C4.Dichotomies
import DeppyProofs.C4.Normalization
import DeppyProofs.C4.Confluence
import DeppyProofs.C4.Decidability
import DeppyProofs.C4.Conservativity
import DeppyProofs.C4.Descent
import DeppyProofs.C4.FunExt
