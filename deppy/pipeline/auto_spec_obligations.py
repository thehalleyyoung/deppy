"""
Deppy Pipeline — Auto-Spec → Sidecar Annotation Bridge (Gap 8)

Adapts inferred specifications from ``auto_spec.py`` (which mines type
annotations, docstrings, tests, and AST patterns) into *draft* sidecar
``ExternalSpec`` entries the LLM/user can refine.

This explicitly preserves the trust hierarchy:
    * inferred specs are tagged ``trust_level=UNTRUSTED`` and
      ``verified=False`` until a human or LLM endorses them;
    * the obligation system can still consume them — just at the
      lowest trust level.

Public API::

    from deppy.pipeline.auto_spec_obligations import (
        infer_module_specs, draft_specs_to_sidecar,
    )
    inferred = infer_module_specs(source)
    drafts = draft_specs_to_sidecar(inferred)
    # drafts: dict[str, ExternalSpec]
"""
from __future__ import annotations

import ast
from typing import Optional

from deppy.core.kernel import TrustLevel
from deppy.pipeline.auto_spec import (
    AutoSpecGenerator,
    FunctionAutoSpec,
    InferredSpec,
)
from deppy.proofs.sidecar import ExternalSpec


def infer_module_specs(source: str) -> dict[str, FunctionAutoSpec]:
    """Run the auto-spec generator over a module source string."""
    return AutoSpecGenerator().generate_specs(source)


def _spec_for_function(fn_name: str, auto: FunctionAutoSpec) -> ExternalSpec:
    """Project a FunctionAutoSpec into a draft ExternalSpec."""
    pre: list[str] = []
    post: list[str] = []
    safe_when: list[str] = []
    raises: list[tuple[str, str]] = []
    exception_free_when: list[str] = []

    for s in auto.inferred:
        formal = (s.formal or s.description or "").strip()
        if not formal:
            continue
        if s.kind == "precondition":
            pre.append(formal)
            # High-confidence preconditions are also reasonable
            # safe_when candidates.
            if s.confidence >= 0.75:
                safe_when.append(formal)
        elif s.kind == "postcondition":
            post.append(formal)
        elif s.kind == "type_constraint":
            # Type constraints add to safe_when: they restrict input shape.
            safe_when.append(formal)
        elif s.kind == "invariant":
            safe_when.append(formal)
        elif s.kind == "exception":
            # Try to split "RaisesX when COND" into class + condition.
            cls, _, cond = formal.partition(" when ")
            cls = cls.strip().rstrip(":")
            cond = cond.strip().strip("\"'")
            if cls:
                raises.append((cls, cond or "True"))

    # If no exception specs were inferred and there are preconditions,
    # offer them as exception_free_when candidates.
    if not raises and pre:
        exception_free_when.extend(pre)

    spec = ExternalSpec(
        target_name=fn_name,
        preconditions=list(pre),
        postconditions=list(post),
        safe_when=safe_when,
        raises_declarations=raises,
        exception_free_when=exception_free_when,
        verified=False,
        trust_level=TrustLevel.UNTRUSTED,
    )
    return spec


def draft_specs_to_sidecar(
    inferred: dict[str, FunctionAutoSpec],
) -> dict[str, ExternalSpec]:
    """Convert a mapping of FunctionAutoSpec → draft ExternalSpec.

    All resulting specs are tagged UNTRUSTED — they are *suggestions*
    for the LLM/user to refine and re-emit at higher trust.
    """
    return {name: _spec_for_function(name, auto)
            for name, auto in inferred.items()}


def merge_drafts_with_sidecar(
    drafts: dict[str, ExternalSpec],
    user_specs: Optional[dict[str, ExternalSpec]] = None,
) -> dict[str, ExternalSpec]:
    """Overlay user-supplied sidecar specs onto inferred drafts.

    Where the user has provided a spec, that spec wins outright (the
    user/LLM has higher authority than the auto-spec heuristics).
    Where they have not, the draft is retained.
    """
    user_specs = user_specs or {}
    out = dict(drafts)
    for name, spec in user_specs.items():
        out[name] = spec
    return out


__all__ = [
    "infer_module_specs",
    "draft_specs_to_sidecar",
    "merge_drafts_with_sidecar",
]
