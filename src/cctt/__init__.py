"""CCTT: Cubical Cohomological Type Theory for Program Semantics.

A complete implementation of algorithm equivalence checking,
specification checking, and bug finding via:
  - PyObj Z3 algebraic data type (Python's value universe)
  - TypeTag fibration (type-fiber decomposition)
  - Shared function symbols (univalence principle)
  - 52 equational axioms (cubical path constructors)
  - Čech cohomology (H¹ = 0 ↔ equivalence)
  - Automated path search with 5-phase normalization
  - Galois connections for abstract type-level pre-filtering (§12)
  - Stalk computations, spectral sequences, Mayer-Vietoris (stalks module)
  - Duck-type lattice enrichment, decidability classification, strategy oracle (§15–17)
  - Cubical foundations: interval types, face formulas, typed paths (§1-2)
"""

from .cubical import (  # noqa: F401
    # Interval & De Morgan algebra
    IVal, I0, I1, IVar, INeg, IMeet, IJoin,
    i_neg, i_meet, i_join, ival_normalize,
    # Face formulas
    FaceFormula, FaceAtom, FaceAnd, FaceOr, FaceTop, FaceBot,
    face_restrict, face_eval, face_negate, face_implies,
    # Typed cubical paths
    CubicalPath,
    # Funext witness
    FunextWitness,
    # Groupoid law certification
    GroupoidLaw, GroupoidVerdict, GroupoidCertificate, verify_groupoid_laws,
    # De Morgan verification
    DeMorganVerifier, DMLawResult,
    # Cubical set
    CubicalSet, Cube0, Cube1, Cube2,
    # Path optimization
    PathCompositionOptimizer,
    # Interval substitution
    IntervalSubstitutionEngine,
    # Dependent path types
    TypeTag, TypeFamily, DependentPath, make_dependent_path,
    # Connection operations
    ConnectionOps,
    # Integration helpers
    path_result_to_cubical, build_funext_from_fibers,
    build_cubical_set_from_path,
)
