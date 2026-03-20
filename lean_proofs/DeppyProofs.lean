/-
  DeppyProofs: Formal Verification of Sheaf-Cohomological Program Analysis

  This library formalizes the core metatheory behind deppy's use of
  Čech cohomology for program analysis:

  1. SiteCategory    — program site categories and Grothendieck topologies
  2. Presheaf        — semantic presheaves over site categories
  3. CechCohomology  — Čech complex, coboundary maps, H⁰ and H¹
  4. Soundness       — soundness of the analysis (H¹=0 ⟹ no bugs)
  5. Descent         — descent theorem (H¹=0 ⟺ local equivalences glue)
  6. MayerVietoris   — compositional obstruction counting, incremental analysis
  7. FixedPoint      — convergence of bidirectional synthesis in O(n·h)
-/

import DeppyProofs.SiteCategory
import DeppyProofs.Presheaf
import DeppyProofs.CechCohomology
import DeppyProofs.Soundness
import DeppyProofs.Descent
import DeppyProofs.MayerVietoris
import DeppyProofs.FixedPoint
import DeppyProofs.Hybrid.HybridType
import DeppyProofs.Hybrid.OracleMonad
import DeppyProofs.Hybrid.TrustTopos
import DeppyProofs.Hybrid.AntiHallucination
