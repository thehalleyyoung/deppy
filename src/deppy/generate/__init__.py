"""deppy.generate -- Code generation from solved sections.

Phase 10 (generate) of the sheaf-descent semantic typing pipeline.  This
package provides:

- **ContractGenerator**: Generate @requires/@ensures/@raises contracts.
- **StubGenerator**: Generate .pyi type stub files.
- **InvariantCandidateGenerator**: Generate loop invariant candidates.
- **AnnotationSynthesizer**: Synthesize Python type annotations.

Typical usage::

    from deppy.generate import (
        ContractGenerator,
        StubGenerator,
        InvariantCandidateGenerator,
        AnnotationSynthesizer,
    )

    # Contract generation
    gen = ContractGenerator()
    contracts = gen.generate(cover, sections)

    # Stub generation
    stub_gen = StubGenerator()
    stub_text = stub_gen.generate_stub("my_module", covers, sections)

    # Invariant candidates
    inv_gen = InvariantCandidateGenerator()
    candidates = inv_gen.generate(loop_site, sections)

    # Annotation synthesis
    synth = AnnotationSynthesizer()
    annotations = synth.synthesize(sections)
"""

from deppy.generate.contract_generator import (
    ContractClause,
    ContractGenerator,
    GeneratedContract,
)
from deppy.generate.stub_generator import StubGenerator
from deppy.generate.invariant_candidate import (
    InvariantCandidate,
    InvariantCandidateGenerator,
)
from deppy.generate.annotation_synthesizer import (
    AnnotationSynthesizer,
    SynthesizedAnnotation,
)

__all__ = [
    "AnnotationSynthesizer",
    "ContractClause",
    "ContractGenerator",
    "GeneratedContract",
    "InvariantCandidate",
    "InvariantCandidateGenerator",
    "StubGenerator",
    "SynthesizedAnnotation",
]
