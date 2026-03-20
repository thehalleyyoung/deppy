
from __future__ import annotations

from typing import Any

from .constraint_templates import constraint_from_fragment
from .docstring_parser import parse_docstring
from .models import SynthesisResult
from .synthesis_verifier import verify_synthesized_constraints


def synthesize_types_from_docstring(fn: Any) -> SynthesisResult:
    annotations = getattr(fn, '__annotations__', {})
    return_type = annotations.get('return', object)
    fragments = parse_docstring(fn)
    constraints = tuple(
        constraint
        for fragment in fragments
        for constraint in [constraint_from_fragment(fragment, return_type)]
        if constraint is not None
    )
    verification = verify_synthesized_constraints(constraints)
    applied_annotation = None
    for constraint, verdict in zip(constraints, verification):
        if verdict.verified:
            applied_annotation = constraint.annotation
            break
    return SynthesisResult(
        function_name=getattr(fn, '__name__', '<anonymous>'),
        fragments=fragments,
        constraints=constraints,
        verification=verification,
        applied_annotation=applied_annotation,
    )


def annotate_function_from_docstring(fn: Any) -> SynthesisResult:
    result = synthesize_types_from_docstring(fn)
    if result.applied_annotation is not None:
        fn.__annotations__ = dict(getattr(fn, '__annotations__', {}))
        fn.__annotations__['return'] = result.applied_annotation
    return result
