"""deppy.surface -- proof-surface lowering from decorators to sheaf cover.

This package converts user-facing contract and proof decorators into
boundary seeds and proof sites for the sheaf cover.  It is the bridge
between the ``deppy.contracts`` user-annotation layer and the
``deppy.core`` sheaf-descent engine.

Submodules
----------

- ``contract_lowering`` -- @requires/@ensures to boundary seeds.
- ``theorem_lowering`` -- @theorem/@lemma to proof sites + transport maps.
- ``witness_lowering`` -- witness declarations to witness carriers.
- ``invariant_lowering`` -- @loop_invariant/@class_invariant to site constraints.
- ``decreases_lowering`` -- @decreases to ranking-function sites.
- ``proof_surface`` -- full proof-surface elaboration pipeline.
"""

from __future__ import annotations

# -- contract_lowering -------------------------------------------------------
from deppy.surface.contract_lowering import (
    ContractSeed,
    EnsuresSeed,
    RequiresSeed,
    SeedOrigin,
    apply_seeds_to_cover,
    deduplicate_ensures,
    deduplicate_requires,
    lower_and_apply,
    lower_contract_set,
    lower_ensures,
    lower_ensures_contract,
    lower_exceptional_ensures,
    lower_requires,
    lower_requires_contract,
    seeds_to_collection,
)

# -- theorem_lowering --------------------------------------------------------
from deppy.surface.theorem_lowering import (
    LemmaSeed,
    ProofTransportSeed,
    TheoremSeed,
    build_dependency_graph,
    create_proof_sites,
    lower_and_install_theorems,
    lower_assumption,
    lower_lemma,
    lower_theorem,
    lower_theorem_contracts,
    lower_transport_contract,
    resolve_dependencies,
    topological_order,
)

# -- witness_lowering --------------------------------------------------------
from deppy.surface.witness_lowering import (
    DecreasesWitnessSeed,
    ExistentialWitnessSeed,
    TransportWitnessSeed,
    WitnessKind,
    WitnessSeed,
    inject_all_witnesses,
    inject_witness_into_cover,
    lower_decreases_witness,
    lower_existential_witness,
    lower_transport_witness,
    lower_witness_contracts,
    lower_witness_declaration,
)

# -- invariant_lowering ------------------------------------------------------
from deppy.surface.invariant_lowering import (
    ClassInvariantSeed,
    InvariantScope,
    InvariantSeed,
    LoopInvariantSeed,
    ModuleInvariantSeed,
    apply_all_invariants,
    apply_invariant_to_cover,
    deduplicate_invariant_seeds,
    lower_and_apply_invariants,
    lower_class_invariant,
    lower_invariant_contracts,
    lower_loop_invariant,
    lower_module_invariant,
)

# -- decreases_lowering ------------------------------------------------------
from deppy.surface.decreases_lowering import (
    BoundType,
    DecreasesSeed,
    create_all_ranking_sites,
    create_ranking_sites,
    extract_decreases_seeds,
    lower_and_install_decreases,
    lower_decreases,
    lower_decreases_from_loop,
    lower_decreases_from_string,
    lower_lexicographic_decreases,
)

# -- proof_surface -----------------------------------------------------------
from deppy.surface.proof_surface import (
    ElaborationConfig,
    ElaborationResult,
    ElaborationStage,
    ProofSurface,
    count_proof_obligations,
    elaborate,
    elaborate_contracts_only,
    elaborate_full,
    elaborate_invariants_only,
    elaborate_proofs_only,
    summarize_elaboration,
)

# -- sugar ------------------------------------------------------------------
from deppy.surface.sugar import (
    And,
    Bool,
    BoundedInt,
    Bytes,
    ContractViolation,
    Dep,
    Eq,
    Float,
    Fn,
    FunctionSpec,
    Geq,
    Gt,
    Idx,
    Int,
    Leq,
    Len,
    Lt,
    Nat,
    Neq,
    NonEmptyOf,
    NoneType,
    Not,
    Opt,
    Or,
    Pair,
    Pos,
    Rank,
    Ref,
    Return,
    Shape,
    Sized,
    Str,
    Tensor,
    Var,
    Vec,
    checked,
    extract_spec,
    fn,
    pretty,
    to_predicate,
    v,
    x,
    y,
    n,
)

__all__ = [
    # contract_lowering
    "ContractSeed",
    "RequiresSeed",
    "EnsuresSeed",
    "SeedOrigin",
    "lower_requires",
    "lower_ensures",
    "lower_requires_contract",
    "lower_ensures_contract",
    "lower_exceptional_ensures",
    "lower_contract_set",
    "deduplicate_requires",
    "deduplicate_ensures",
    "seeds_to_collection",
    "apply_seeds_to_cover",
    "lower_and_apply",
    # theorem_lowering
    "TheoremSeed",
    "LemmaSeed",
    "ProofTransportSeed",
    "lower_theorem",
    "lower_lemma",
    "lower_transport_contract",
    "lower_assumption",
    "lower_theorem_contracts",
    "build_dependency_graph",
    "topological_order",
    "resolve_dependencies",
    "create_proof_sites",
    "lower_and_install_theorems",
    # witness_lowering
    "WitnessKind",
    "WitnessSeed",
    "ExistentialWitnessSeed",
    "TransportWitnessSeed",
    "DecreasesWitnessSeed",
    "lower_witness_declaration",
    "lower_existential_witness",
    "lower_transport_witness",
    "lower_decreases_witness",
    "lower_witness_contracts",
    "inject_witness_into_cover",
    "inject_all_witnesses",
    # invariant_lowering
    "InvariantScope",
    "InvariantSeed",
    "LoopInvariantSeed",
    "ClassInvariantSeed",
    "ModuleInvariantSeed",
    "lower_loop_invariant",
    "lower_class_invariant",
    "lower_module_invariant",
    "lower_invariant_contracts",
    "deduplicate_invariant_seeds",
    "apply_invariant_to_cover",
    "apply_all_invariants",
    "lower_and_apply_invariants",
    # decreases_lowering
    "BoundType",
    "DecreasesSeed",
    "lower_decreases",
    "lower_decreases_from_loop",
    "lower_decreases_from_string",
    "lower_lexicographic_decreases",
    "create_ranking_sites",
    "create_all_ranking_sites",
    "extract_decreases_seeds",
    "lower_and_install_decreases",
    # proof_surface
    "ElaborationStage",
    "ElaborationResult",
    "ElaborationConfig",
    "ProofSurface",
    "elaborate",
    "elaborate_full",
    "elaborate_contracts_only",
    "elaborate_proofs_only",
    "elaborate_invariants_only",
    "summarize_elaboration",
    "count_proof_obligations",
    # sugar
    "Int", "Float", "Str", "Bool", "NoneType", "Bytes",
    "Var", "v", "x", "y", "n", "Return",
    "Ref", "Fn", "Pair", "Dep",
    "Eq", "Neq", "Lt", "Gt", "Leq", "Geq", "And", "Or", "Not",
    "Len", "Shape", "Rank", "Idx",
    "Nat", "Pos", "BoundedInt", "Sized", "NonEmptyOf", "Vec", "Tensor", "Opt",
    "to_predicate", "pretty", "extract_spec", "fn", "checked",
    "FunctionSpec", "ContractViolation",
]
