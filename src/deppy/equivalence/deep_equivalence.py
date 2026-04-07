"""Deep sheaf-cohomological equivalence engine.

This module re-exports the radical cohomological engine from
cohomological_engine.py, which implements the full framework from
programcohomology.tex (POPL 2027) plus six beyond-paper extensions:

  1. Spectral Sequences — hierarchical module decomposition
  2. Derived Categories — quasi-isomorphism equivalence
  3. Persistent Cohomology — obstruction birth/death tracking
  4. Étale Cohomology — polymorphic function verification
  5. Galois Cohomology — implementation symmetries
  6. Betti Numbers — topological complexity measures
"""

from __future__ import annotations

# Re-export everything from the radical engine
from deppy.equivalence.cohomological_engine import (  # noqa: F401
    # §3.1 Site Category
    SiteKind,
    Site,
    SiteMorphism,
    SiteCategory,
    # §3.2 Semantic Presheaf
    RefinementPredicate,
    LocalSection,
    SemanticPresheaf,
    # §3.3 Grothendieck Topology
    CoveringFamily,
    GrothendieckTopology,
    # §3.4 Čech Complex
    ProofMethod,
    CechCochain,
    CechComplex,
    LocalIsoSection,
    # §5.2 Descent
    DescentCertificate,
    DescentVerifier,
    # §6.3 Mayer-Vietoris
    MayerVietorisResult,
    MayerVietorisAnalyzer,
    # Beyond Paper
    SpectralSequenceResult,
    SpectralSequenceEngine,
    DerivedCategoryResult,
    DerivedCategoryEngine,
    PersistentCohomologyResult,
    PersistentCohomologyEngine,
    EtaleCohomologyResult,
    EtaleCohomologyEngine,
    GaloisCohomologyResult,
    GaloisCohomologyEngine,
    # GF(2) Linear Algebra
    _gf2_rank,
    _gf2_kernel_basis,
    # Čech Builder
    CechComplexBuilder,
    # Z3 Encoder
    Z3SectionEncoder,
    # Top-level engine
    DeepEquivalenceEngine,
)

# Keep the old PathSite name for backward compatibility
PathSite = Site

__all__ = [
    "DeepEquivalenceEngine",
    "DescentCertificate",
    "CechComplex",
    "ProofMethod",
    "PathSite",
]
