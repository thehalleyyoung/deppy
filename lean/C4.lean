/-
  C4.lean — Root module for the C⁴ formalization.

  C⁴ = Cubical Cohomological Calculus of Constructions
  A proof system for Python programs using:
    - Refinement types (site objects = decidable predicates)
    - Čech descent = cubical hcomp (the fundamental identification)
    - Trust provenance as a sheaf
    - F*-style binding
-/

import C4.Basic
import C4.Site
import C4.Syntax
import C4.Typing
import C4.Reduction
import C4.Descent
import C4.Hedberg
import C4.SubjectReduction
import C4.Trust
import C4.Canonicity
import C4.Soundness
