from __future__ import annotations

import inspect
import textwrap
from dataclasses import dataclass
from typing import List, Optional, Tuple

from deppy.nl_synthesis.models import DocstringFragment


@dataclass(frozen=True)
class _SectionState:
    kind: str = ""
    section: str = ""
    style: str = "plain"


class DocstringParser:
    """Deterministic parser for constraint-bearing docstring fragments."""

    def parse(self, obj: object) -> Tuple[DocstringFragment, ...]:
        if callable(obj):
            doc = inspect.getdoc(obj) or ""
        elif isinstance(obj, str):
            doc = obj
        else:
            raise TypeError("DocstringParser.parse expects a callable or string")
        return tuple(self.parse_text(doc))

    def parse_text(self, docstring: str) -> List[DocstringFragment]:
        doc = textwrap.dedent(docstring or "").strip("\n")
        if not doc:
            return []

        lines = doc.splitlines()
        fragments: List[DocstringFragment] = []
        state = _SectionState()
        i = 0
        while i < len(lines):
            raw = lines[i]
            line = raw.strip()
            lower = line.lower()

            if not line:
                i += 1
                continue

            if i + 1 < len(lines) and set(lines[i + 1].strip()) == {"-"}:
                mapping = {
                    "parameters": ("requires", "Parameters", "numpy"),
                    "returns": ("ensures", "Returns", "numpy"),
                    "yields": ("ensures", "Yields", "numpy"),
                    "notes": ("invariant", "Notes", "numpy"),
                }
                if lower in mapping:
                    kind, section, style = mapping[lower]
                    state = _SectionState(kind=kind, section=section, style=style)
                    i += 2
                    continue

            google_headings = {
                "args:": ("requires", "Args", "google"),
                "arguments:": ("requires", "Arguments", "google"),
                "parameters:": ("requires", "Parameters", "google"),
                "returns:": ("ensures", "Returns", "google"),
                "yields:": ("ensures", "Yields", "google"),
                "requires:": ("requires", "Requires", "google"),
                "ensures:": ("ensures", "Ensures", "google"),
                "invariants:": ("invariant", "Invariants", "google"),
                "invariant:": ("invariant", "Invariant", "google"),
            }
            if lower in google_headings:
                kind, section, style = google_headings[lower]
                state = _SectionState(kind=kind, section=section, style=style)
                i += 1
                continue

            if lower.startswith(":param "):
                name, text = _split_rest_field(line, ":param ")
                fragments.append(_fragment(text, "requires", name, "param", "rest", i + 1))
                i += 1
                continue
            if lower.startswith(":return:") or lower.startswith(":returns:"):
                prefix = ":returns:" if lower.startswith(":returns:") else ":return:"
                _, text = _split_rest_field(line, prefix)
                fragments.append(_fragment(text, "ensures", "result", "return", "rest", i + 1))
                i += 1
                continue

            if line.startswith(("Requires:", "Ensures:", "Invariant:")):
                head, _, rest = line.partition(":")
                kind = head.lower()
                target = "result" if kind == "ensures" else None
                fragments.append(_fragment(rest.strip(), kind, target, head, "inline", i + 1))
                i += 1
                continue

            parsed = self._parse_section_line(lines, i, state)
            if parsed is not None:
                fragment, next_index = parsed
                if fragment is not None:
                    fragments.append(fragment)
                i = next_index
                continue

            i += 1
        return fragments

    def _parse_section_line(
        self,
        lines: List[str],
        index: int,
        state: _SectionState,
    ) -> Optional[Tuple[Optional[DocstringFragment], int]]:
        if not state.kind:
            return None

        raw = lines[index]
        stripped = raw.strip()
        if not stripped:
            return (None, index + 1)

        if state.kind in {"requires", "ensures"} and ":" in stripped:
            left, _, right = stripped.partition(":")
            if state.style == "numpy" and " : " in stripped:
                left, _, _ = stripped.partition(" : ")
                desc, next_index = _collect_indented_block(lines, index + 1)
                if desc:
                    return (
                        _fragment(
                            desc,
                            state.kind,
                            left.strip(),
                            state.section,
                            state.style,
                            index + 1,
                        ),
                        next_index,
                    )
                return (None, next_index)
            target = left.strip()
            text = right.strip()
            if text:
                if state.kind == "ensures" and target.lower() in {
                    "bool",
                    "int",
                    "float",
                    "list",
                    "tuple",
                    "dict",
                    "set",
                    "str",
                }:
                    target = "result"
                return (
                    _fragment(text, state.kind, target, state.section, state.style, index + 1),
                    index + 1,
                )

        if state.kind in {"requires", "ensures"}:
            text = stripped.lstrip("-* ").strip()
            if text:
                return (
                    _fragment(
                        text,
                        state.kind,
                        "result" if state.kind == "ensures" else None,
                        state.section,
                        state.style,
                        index + 1,
                    ),
                    index + 1,
                )

        if state.kind == "invariant":
            return (
                _fragment(stripped.lstrip("- "), "invariant", None, state.section, state.style, index + 1),
                index + 1,
            )

        return None


def _split_rest_field(line: str, prefix: str) -> Tuple[str, str]:
    rest = line[len(prefix):]
    name, _, text = rest.partition(":")
    return name.strip(), text.strip()


def _collect_indented_block(lines: List[str], start: int) -> Tuple[str, int]:
    collected: List[str] = []
    i = start
    while i < len(lines):
        raw = lines[i]
        if not raw.strip():
            if collected:
                break
            i += 1
            continue
        if raw.startswith(" ") or raw.startswith("\t"):
            collected.append(raw.strip())
            i += 1
            continue
        break
    return " ".join(collected).strip(), i


def _fragment(
    text: str,
    kind: str,
    target: Optional[str],
    section: str,
    style: str,
    line_number: int,
) -> DocstringFragment:
    normalized = " ".join(text.split())
    return DocstringFragment(
        text=text.strip(),
        normalized_text=normalized,
        kind=kind,
        target=target,
        section=section,
        style=style,
        line_number=line_number,
    )


def parse_docstring_fragments(obj: object) -> Tuple[DocstringFragment, ...]:
    return DocstringParser().parse(obj)
