"""deppy.contracts — annotation surface for sheaf-descent semantic typing.

Contracts define preconditions (requires), postconditions (ensures),
invariants, witnesses, and theorems.  Under the sheaf-descent framework
contracts are *boundary seeds* — they seed the input/output boundaries
of the site cover.
"""

from __future__ import annotations

# -- foundational types -----------------------------------------------------
from deppy.contracts.base import (
    Contract,
    ContractSet,
    Predicate,
    PredicateKind,
    SourceLocation,
    Term,
    TermKind,
    TypeBase,
)

# -- requires ---------------------------------------------------------------
from deppy.contracts.requires import (
    CompositeRequires,
    ParameterRequirement,
    RequiresContract,
    requires,
)

# -- ensures ----------------------------------------------------------------
from deppy.contracts.ensures import (
    CompositeEnsures,
    EnsuresContract,
    ExceptionalEnsures,
    ensures,
    ensures_raises,
)

# -- invariants -------------------------------------------------------------
from deppy.contracts.invariant import (
    ClassInvariant,
    InvariantContract,
    InvariantKind,
    LoopInvariant,
    ModuleInvariant,
    class_invariant,
    loop_invariant,
    module_invariant,
)

# -- witnesses --------------------------------------------------------------
from deppy.contracts.witness import (
    WitnessContract,
    WitnessExport,
    WitnessImport,
    WitnessRegistry,
    witness,
)

# -- theorems / lemmas / transport / assumptions ----------------------------
from deppy.contracts.theorem import (
    AssumptionContract,
    LemmaContract,
    TheoremContract,
    TransportContract,
    assume,
    lemma,
    theorem,
    transport,
)

# -- boundary seeds ---------------------------------------------------------
from deppy.contracts.seed import (
    BoundarySeed,
    InputBoundarySeed,
    OutputBoundarySeed,
    SeedCollection,
    SeedProvenance,
)

# -- transport seeds --------------------------------------------------------
from deppy.contracts.transport_seed import (
    TransportJustification,
    TransportSeed,
    TransportSeedBuilder,
    TransportSeedCollection,
)

# -- parser / extractor -----------------------------------------------------
from deppy.contracts.parser import (
    ContractExtractor,
    ContractParser,
)

__all__ = [
    # base
    "Contract",
    "ContractSet",
    "Predicate",
    "PredicateKind",
    "SourceLocation",
    "Term",
    "TermKind",
    "TypeBase",
    # requires
    "RequiresContract",
    "ParameterRequirement",
    "CompositeRequires",
    "requires",
    # ensures
    "EnsuresContract",
    "ExceptionalEnsures",
    "CompositeEnsures",
    "ensures",
    "ensures_raises",
    # invariant
    "InvariantKind",
    "InvariantContract",
    "LoopInvariant",
    "ClassInvariant",
    "ModuleInvariant",
    "loop_invariant",
    "class_invariant",
    "module_invariant",
    # witness
    "WitnessContract",
    "WitnessExport",
    "WitnessImport",
    "WitnessRegistry",
    "witness",
    # theorem
    "TheoremContract",
    "LemmaContract",
    "TransportContract",
    "AssumptionContract",
    "theorem",
    "lemma",
    "assume",
    "transport",
    # seed
    "BoundarySeed",
    "InputBoundarySeed",
    "OutputBoundarySeed",
    "SeedCollection",
    "SeedProvenance",
    # transport seed
    "TransportJustification",
    "TransportSeed",
    "TransportSeedBuilder",
    "TransportSeedCollection",
    # parser
    "ContractParser",
    "ContractExtractor",
]
