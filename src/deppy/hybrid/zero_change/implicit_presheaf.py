"""Zero-change presheaf extraction from ordinary Python code.

The goal is to extract local sections and verification hints without requiring
users to rewrite code with hybrid-specific annotations.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

from deppy.hybrid.core.intent_bridge import IntentBridge


@dataclass(frozen=True)
class ImplicitLocalSection:
    """A local section inferred from an existing scope."""

    site_id: str
    symbol: str
    line_span: Tuple[int, int]
    intent_text: str
    structural_hints: List[str] = field(default_factory=list)
    semantic_hints: List[str] = field(default_factory=list)
    proof_obligations: List[str] = field(default_factory=list)


@dataclass
class ImplicitPresheafModel:
    """Inferred presheaf-like view of a Python file."""

    file_path: str
    module_intent: str = ""
    sections: List[ImplicitLocalSection] = field(default_factory=list)
    overlaps: Dict[str, List[str]] = field(default_factory=dict)

    def section_for_symbol(self, symbol: str) -> Optional[ImplicitLocalSection]:
        for section in self.sections:
            if section.symbol == symbol:
                return section
        return None

    def to_spec_hints(self) -> Dict[str, List[str]]:
        return {
            sec.symbol: [
                *sec.structural_hints,
                *sec.semantic_hints,
                *sec.proof_obligations,
            ]
            for sec in self.sections
        }


class ImplicitPresheafExtractor:
    """Extract a usable implicit presheaf from unmodified Python source."""

    def __init__(self) -> None:
        self._intent_bridge = IntentBridge()

    def extract_source(self, source: str, *, file_path: str = "<string>") -> ImplicitPresheafModel:
        module = ast.parse(source)
        model = ImplicitPresheafModel(file_path=file_path)
        model.module_intent = ast.get_docstring(module) or ""
        self._collect_sections(module, model)
        self._compute_overlaps(model)
        return model

    def extract_file(self, file_path: str) -> ImplicitPresheafModel:
        content = Path(file_path).read_text(encoding="utf-8")
        return self.extract_source(content, file_path=file_path)

    def extract_many(self, file_paths: Iterable[str]) -> List[ImplicitPresheafModel]:
        return [self.extract_file(path) for path in file_paths]

    def _collect_sections(self, module: ast.Module, model: ImplicitPresheafModel) -> None:
        for node in module.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                model.sections.append(self._function_section(node, model.file_path))
            elif isinstance(node, ast.ClassDef):
                for child in node.body:
                    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        model.sections.append(self._function_section(child, model.file_path, parent=node.name))

    def _function_section(
        self,
        fn: ast.FunctionDef | ast.AsyncFunctionDef,
        file_path: str,
        *,
        parent: Optional[str] = None,
    ) -> ImplicitLocalSection:
        symbol = f"{parent}.{fn.name}" if parent else fn.name
        start = getattr(fn, "lineno", 0)
        end = getattr(fn, "end_lineno", start)
        site_id = f"{file_path}:{symbol}:{start}"
        doc = ast.get_docstring(fn) or f"Function {symbol}"
        bridged = self._intent_bridge.from_text(doc, type_name=f"{symbol}_implicit")

        structural_hints: List[str] = []
        semantic_hints: List[str] = []
        proof_obligations: List[str] = []

        for arg in fn.args.args:
            ann = ast.unparse(arg.annotation) if arg.annotation is not None else None
            if ann:
                structural_hints.append(f"{arg.arg}: {ann}")
        for inner in ast.walk(fn):
            if isinstance(inner, ast.Assert):
                structural_hints.append(ast.unparse(inner.test))
            elif isinstance(inner, ast.Return) and inner.value is not None and fn.returns is not None:
                proof_obligations.append(f"return satisfies {ast.unparse(fn.returns)}")
            elif isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name) and inner.func.id in {"sorted", "sum", "len"}:
                semantic_hints.append(f"uses {inner.func.id} in core logic")

        for pred in bridged.structural.predicates:
            structural_hints.append(pred.formula)
        for pred in bridged.semantic.predicates:
            semantic_hints.append(pred.description)
        if not proof_obligations:
            proof_obligations.append(f"termination/{symbol}_totality")

        return ImplicitLocalSection(
            site_id=site_id,
            symbol=symbol,
            line_span=(start, end),
            intent_text=doc,
            structural_hints=sorted(set(structural_hints)),
            semantic_hints=sorted(set(semantic_hints)),
            proof_obligations=sorted(set(proof_obligations)),
        )

    def _compute_overlaps(self, model: ImplicitPresheafModel) -> None:
        for section in model.sections:
            model.overlaps.setdefault(section.site_id, [])
        for i, left in enumerate(model.sections):
            for right in model.sections[i + 1 :]:
                if self._overlap(left.line_span, right.line_span):
                    model.overlaps[left.site_id].append(right.site_id)
                    model.overlaps[right.site_id].append(left.site_id)

    @staticmethod
    def _overlap(a: Tuple[int, int], b: Tuple[int, int]) -> bool:
        return max(a[0], b[0]) <= min(a[1], b[1])


def extract_implicit_presheaf(file_path: str) -> ImplicitPresheafModel:
    """Convenience API for one-shot extraction."""
    return ImplicitPresheafExtractor().extract_file(file_path)


__all__ = [
    "ImplicitLocalSection",
    "ImplicitPresheafModel",
    "ImplicitPresheafExtractor",
    "extract_implicit_presheaf",
]

