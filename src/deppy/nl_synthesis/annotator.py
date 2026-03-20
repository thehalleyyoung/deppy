from __future__ import annotations

from typing import Callable, List, Tuple

from deppy.pipeline.stages.render_stage import ContractAnnotation

from deppy.nl_synthesis.models import SynthesizedAnnotationBundle


def bundle_to_contract_annotations(bundle: SynthesizedAnnotationBundle) -> Tuple[ContractAnnotation, ...]:
    annotations: List[ContractAnnotation] = []
    scope_name = bundle.source_name or "<docstring>"
    for constraint in bundle.accepted_constraints:
        variable = None
        if constraint.target and (
            not constraint.dependencies or set(constraint.dependencies) <= {constraint.target}
        ):
            variable = constraint.target
        annotations.append(
            ContractAnnotation(
                _scope_name=scope_name,
                _kind=constraint.kind,
                _predicate_text=constraint.predicate_text,
                _variable=variable,
                _trust=constraint.trust,
                _source_sites=(),
            )
        )
    return tuple(annotations)


def apply_synthesized_annotations(
    fn: Callable[..., object],
    bundle: SynthesizedAnnotationBundle,
) -> Callable[..., object]:
    annotations = dict(getattr(fn, "__annotations__", {}) or {})
    annotations["__docstring_constraints__"] = bundle.to_dict()
    annotations["__contracts__"] = [
        contract.to_decorator_string()
        for contract in bundle_to_contract_annotations(bundle)
    ]
    fn.__annotations__ = annotations
    return fn
