from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Callable, List, Optional, Sequence, Tuple

from deppy.nl_synthesis.models import DocstringFragment, NLSynthesisConfigurationError
from deppy.render.verify import _parse_refinement


@dataclass(frozen=True)
class ConstraintTemplate:
    """A deterministic lowering rule from fragment text to refinement clauses."""

    name: str
    priority: int
    pattern: str
    builder: Callable[[DocstringFragment], Sequence[str]] = field(compare=False, repr=False)

    def matches(self, fragment: DocstringFragment) -> bool:
        return re.search(self.pattern, fragment.normalized_text, re.IGNORECASE) is not None

    def lower(self, fragment: DocstringFragment, params: Sequence[str]) -> List[Tuple[str, object]]:
        clauses: List[Tuple[str, object]] = []
        for clause in self.builder(fragment):
            for spec in _parse_refinement(clause, list(params)):
                clauses.append((clause, spec))
        return clauses


class TemplateRegistry:
    """Deterministic registry ordered by priority then template name."""

    def __init__(self, templates: Optional[Sequence[ConstraintTemplate]] = None) -> None:
        self._templates = tuple(
            sorted(templates or (), key=lambda item: (-item.priority, item.name))
        )

    @property
    def templates(self) -> Tuple[ConstraintTemplate, ...]:
        return self._templates

    def register(self, template: ConstraintTemplate) -> "TemplateRegistry":
        if not template.name:
            raise NLSynthesisConfigurationError("Constraint templates must have a name")
        return TemplateRegistry(self._templates + (template,))

    def select(self, fragment: DocstringFragment) -> ConstraintTemplate:
        for template in self._templates:
            if template.matches(fragment):
                return template
        return _GENERIC_TEMPLATE


def _contextualize(fragment: DocstringFragment) -> str:
    text = fragment.normalized_text.strip()
    target = fragment.target or ("result" if fragment.kind == "ensures" else None)
    if not text:
        return text
    lowered = text.lower()
    if target and re.match(r"^(>=|<=|==|!=|>|<)\s*", text):
        return f"{target} {text}"
    if target and lowered in {"sorted", "non-empty", "nonempty", "unique"}:
        return f"{target} is {text}"
    if target and lowered in {"not none", "not null"}:
        return f"{target} is not None"
    if target and lowered.startswith("permutation of"):
        return f"result is a {text}" if target == "result" else f"{target} is a {text}"
    if target and lowered.startswith("length "):
        return text.replace("length", f"len({target})", 1)
    if (
        target
        and not re.search(rf"\b{re.escape(target)}\b", text)
        and not re.search(r"\bresult\b", text)
    ):
        if lowered.startswith("is "):
            return f"{target} {text}"
        return f"{target} is {text}"
    return text


_GENERIC_TEMPLATE = ConstraintTemplate(
    name="generic-refinement",
    priority=0,
    pattern=r".*",
    builder=lambda fragment: (_contextualize(fragment),),
)


def default_template_registry() -> TemplateRegistry:
    templates = [
        ConstraintTemplate(
            "comparison",
            90,
            r"(>=|<=|==|!=|>|<)",
            lambda fragment: (_contextualize(fragment),),
        ),
        ConstraintTemplate(
            "nullability",
            80,
            r"not\s+(none|null)|is\s+not\s+none",
            lambda fragment: (_contextualize(fragment),),
        ),
        ConstraintTemplate(
            "collection-shape",
            70,
            r"non-empty|sorted|unique|permutation|len\(",
            lambda fragment: (_contextualize(fragment),),
        ),
        _GENERIC_TEMPLATE,
    ]
    return TemplateRegistry(templates)
