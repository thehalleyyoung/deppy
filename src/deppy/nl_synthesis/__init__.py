from __future__ import annotations

import inspect
from typing import Optional, Sequence

from deppy.nl_synthesis.annotator import apply_synthesized_annotations, bundle_to_contract_annotations
from deppy.nl_synthesis.docstring_parser import DocstringParser, parse_docstring_fragments
from deppy.nl_synthesis.models import (
    DocstringFragment,
    DocstringSynthesisConfig,
    NLSynthesisConfigurationError,
    SynthesizedAnnotationBundle,
    SynthesizedConstraint,
    SynthesisEvidence,
)
from deppy.nl_synthesis.template_registry import ConstraintTemplate, TemplateRegistry, default_template_registry
from deppy.nl_synthesis.verifier import DocstringConstraintVerifier, verify_synthesized_constraints


def synthesize_types_from_docstring(
    source: object,
    *,
    function_name: Optional[str] = None,
    params: Optional[Sequence[str]] = None,
    config: Optional[DocstringSynthesisConfig] = None,
    registry: Optional[TemplateRegistry] = None,
) -> SynthesizedAnnotationBundle:
    parser = DocstringParser()
    fragments = parser.parse(source)
    if callable(source):
        fn_name = function_name or source.__name__
        signature = inspect.signature(source)
        param_names = list(params or signature.parameters)
    elif isinstance(source, str):
        fn_name = function_name or "<docstring>"
        param_names = list(params or ())
    else:
        raise NLSynthesisConfigurationError("source must be a callable or raw docstring")
    constraints = verify_synthesized_constraints(
        fragments,
        param_names,
        config=config,
        registry=registry,
    )
    warnings = tuple(
        warning
        for constraint in constraints
        for warning in constraint.warnings
    )
    return SynthesizedAnnotationBundle(
        fragments=tuple(fragments),
        constraints=tuple(constraints),
        warnings=warnings,
        source_name=fn_name,
    )


__all__ = [
    "ConstraintTemplate",
    "DocstringConstraintVerifier",
    "DocstringFragment",
    "DocstringParser",
    "DocstringSynthesisConfig",
    "NLSynthesisConfigurationError",
    "SynthesizedAnnotationBundle",
    "SynthesizedConstraint",
    "SynthesisEvidence",
    "TemplateRegistry",
    "apply_synthesized_annotations",
    "bundle_to_contract_annotations",
    "default_template_registry",
    "parse_docstring_fragments",
    "synthesize_types_from_docstring",
    "verify_synthesized_constraints",
]
