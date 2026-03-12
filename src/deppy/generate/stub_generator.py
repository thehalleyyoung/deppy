"""Generate .pyi type stub files from output sections.

StubGenerator creates Python type stub files with refined type annotations
derived from the solved sections.  The stubs are compatible with standard
type checkers (mypy, pyright) and encode the additional refinement
information as comments.
"""

from __future__ import annotations

import textwrap
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import (
    BoundarySection,
    Cover,
    GlobalSection,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.types.base import (
    ANY_TYPE,
    NEVER_TYPE,
    AnyType,
    CallableType,
    ClassType,
    DictType,
    FrozenSetType,
    ListType,
    NeverType,
    OptionalType,
    PrimitiveKind,
    PrimitiveType,
    SetType,
    TupleType,
    TypeBase,
    UnionType,
)
from deppy.types.refinement import (
    QualifiedType,
    RefinementType,
)


# ---------------------------------------------------------------------------
# Type-to-stub-string conversion
# ---------------------------------------------------------------------------

def _type_to_stub(t: Any) -> str:
    """Convert a TypeBase to a .pyi-compatible annotation string."""
    if t is None:
        return "Any"
    if isinstance(t, AnyType):
        return "Any"
    if isinstance(t, NeverType):
        return "Never"
    if isinstance(t, PrimitiveType):
        return t.kind.value
    if isinstance(t, ListType):
        elem = _type_to_stub(t.element)
        return f"list[{elem}]"
    if isinstance(t, DictType):
        k = _type_to_stub(t.key)
        v = _type_to_stub(t.value)
        return f"dict[{k}, {v}]"
    if isinstance(t, TupleType):
        if t.variadic and len(t.elements) == 1:
            elem = _type_to_stub(t.elements[0])
            return f"tuple[{elem}, ...]"
        elems = ", ".join(_type_to_stub(e) for e in t.elements)
        return f"tuple[{elems}]"
    if isinstance(t, SetType):
        elem = _type_to_stub(t.element)
        return f"set[{elem}]"
    if isinstance(t, FrozenSetType):
        elem = _type_to_stub(t.element)
        return f"frozenset[{elem}]"
    if isinstance(t, OptionalType):
        inner = _type_to_stub(t.inner)
        return f"{inner} | None"
    if isinstance(t, UnionType):
        members = " | ".join(_type_to_stub(m) for m in t.members)
        return members
    if isinstance(t, CallableType):
        params = ", ".join(_type_to_stub(p) for p in t.param_types)
        ret = _type_to_stub(t.return_type)
        return f"Callable[[{params}], {ret}]"
    if isinstance(t, ClassType):
        if t.type_args:
            args = ", ".join(_type_to_stub(a) for a in t.type_args)
            return f"{t.name}[{args}]"
        return t.name
    if isinstance(t, RefinementType):
        return _type_to_stub(t.base)
    if isinstance(t, QualifiedType):
        return _type_to_stub(t.base)
    return str(t)


def _refinements_to_comment(refinements: Dict[str, Any]) -> str:
    """Format refinements as a stub comment."""
    if not refinements:
        return ""
    parts: List[str] = []
    for key, value in sorted(refinements.items()):
        if key.startswith("_"):
            continue
        parts.append(f"{key}={value!r}")
    if not parts:
        return ""
    return f"  # refinements: {', '.join(parts)}"


def _extract_param_name(site_id: SiteId) -> str:
    """Extract parameter name from site ID."""
    name = site_id.name
    for sep in (".", ":", "/"):
        parts = name.rsplit(sep, 1)
        if len(parts) == 2:
            return parts[1]
    return name


def _extract_function_name(site_id: SiteId) -> str:
    """Extract function name from a site ID."""
    name = site_id.name
    for sep in (".", ":", "/"):
        parts = name.split(sep)
        if len(parts) >= 2:
            return parts[-2]
    return name


# ---------------------------------------------------------------------------
# Function stub data
# ---------------------------------------------------------------------------

@dataclass
class _FunctionStubData:
    """Intermediate data for a single function stub."""

    name: str
    params: List[Tuple[str, str, str]]  # (name, type, comment)
    return_type: str = "None"
    return_comment: str = ""
    docstring: str = ""
    is_async: bool = False
    decorators: List[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# StubGenerator
# ---------------------------------------------------------------------------

class StubGenerator:
    """Generate .pyi stub files from output sections.

    Creates type stub files with refined type annotations derived from
    the solved local sections.

    Usage::

        gen = StubGenerator()
        stub_text = gen.generate_stub("my_module", covers, sections)
        # Write stub_text to my_module.pyi
    """

    def __init__(
        self,
        *,
        include_refinement_comments: bool = True,
        include_docstrings: bool = False,
        include_imports: bool = True,
        target_python: str = "3.10",
    ) -> None:
        self._include_comments = include_refinement_comments
        self._include_docstrings = include_docstrings
        self._include_imports = include_imports
        self._target_python = target_python

    def generate_stub(
        self,
        module_name: str,
        covers: List[Cover],
        sections: Dict[SiteId, LocalSection],
    ) -> str:
        """Generate a complete .pyi stub for a module.

        Processes all covers (one per function in the module) and
        produces a unified stub file.
        """
        lines: List[str] = []

        if self._include_imports:
            lines.extend(self._generate_imports(sections))
            lines.append("")

        for cover in covers:
            func_stubs = self._generate_function_stubs(cover, sections)
            for stub in func_stubs:
                lines.extend(self._format_function_stub_lines(stub))
                lines.append("")

        variable_stubs = self._generate_variable_stubs(sections, covers)
        for var_line in variable_stubs:
            lines.append(var_line)

        return "\n".join(lines)

    def _generate_imports(
        self,
        sections: Dict[SiteId, LocalSection],
    ) -> List[str]:
        """Generate import statements needed for the stub."""
        imports: Set[str] = set()
        imports.add("from __future__ import annotations")

        needs_typing: Set[str] = set()

        for sec in sections.values():
            carrier = sec.carrier_type
            if carrier is None:
                needs_typing.add("Any")
                continue
            self._collect_imports(carrier, needs_typing)

        if needs_typing:
            typing_items = sorted(needs_typing)
            imports.add(f"from typing import {', '.join(typing_items)}")

        return sorted(imports)

    def _collect_imports(
        self,
        t: Any,
        needs_typing: Set[str],
    ) -> None:
        """Collect typing imports needed for a type."""
        if isinstance(t, AnyType):
            needs_typing.add("Any")
        elif isinstance(t, NeverType):
            needs_typing.add("Never")
        elif isinstance(t, CallableType):
            needs_typing.add("Callable")
            for p in t.param_types:
                self._collect_imports(p, needs_typing)
            self._collect_imports(t.return_type, needs_typing)
        elif isinstance(t, UnionType):
            for m in t.members:
                self._collect_imports(m, needs_typing)
        elif isinstance(t, OptionalType):
            needs_typing.add("Optional")
            self._collect_imports(t.inner, needs_typing)
        elif isinstance(t, ListType):
            self._collect_imports(t.element, needs_typing)
        elif isinstance(t, DictType):
            self._collect_imports(t.key, needs_typing)
            self._collect_imports(t.value, needs_typing)
        elif isinstance(t, TupleType):
            for e in t.elements:
                self._collect_imports(e, needs_typing)
        elif isinstance(t, SetType):
            self._collect_imports(t.element, needs_typing)
        elif isinstance(t, RefinementType):
            self._collect_imports(t.base, needs_typing)
        elif isinstance(t, QualifiedType):
            self._collect_imports(t.base, needs_typing)

    def _generate_function_stubs(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> List[_FunctionStubData]:
        """Generate function stub data for a single cover."""
        func_groups: Dict[str, _FunctionStubData] = {}

        for sid in sorted(cover.input_boundary, key=str):
            sec = sections.get(sid)
            if sec is None:
                continue
            func_name = _extract_function_name(sid)
            param_name = _extract_param_name(sid)

            if func_name not in func_groups:
                func_groups[func_name] = _FunctionStubData(
                    name=func_name,
                    params=[],
                )

            stub = func_groups[func_name]
            type_str = _type_to_stub(sec.carrier_type)
            comment = ""
            if self._include_comments and sec.refinements:
                comment = _refinements_to_comment(sec.refinements)
            stub.params.append((param_name, type_str, comment))

        for sid in sorted(cover.output_boundary, key=str):
            sec = sections.get(sid)
            if sec is None:
                continue
            func_name = _extract_function_name(sid)

            if func_name not in func_groups:
                func_groups[func_name] = _FunctionStubData(
                    name=func_name,
                    params=[],
                )

            stub = func_groups[func_name]
            stub.return_type = _type_to_stub(sec.carrier_type)
            if self._include_comments and sec.refinements:
                stub.return_comment = _refinements_to_comment(sec.refinements)

        return list(func_groups.values())

    def _format_function_stub_lines(
        self,
        stub: _FunctionStubData,
    ) -> List[str]:
        """Format a function stub as lines of .pyi text."""
        lines: List[str] = []

        for dec in stub.decorators:
            lines.append(f"@{dec}")

        prefix = "async def" if stub.is_async else "def"

        if not stub.params:
            sig = f"{prefix} {stub.name}() -> {stub.return_type}: ..."
            if stub.return_comment:
                sig += stub.return_comment
            lines.append(sig)
        elif len(stub.params) <= 3:
            params_str = ", ".join(
                f"{name}: {typ}" for name, typ, _ in stub.params
            )
            sig = f"{prefix} {stub.name}({params_str}) -> {stub.return_type}: ..."
            lines.append(sig)
            for name, typ, comment in stub.params:
                if comment:
                    lines.append(f"    # {name}{comment}")
            if stub.return_comment:
                lines.append(f"    # return{stub.return_comment}")
        else:
            lines.append(f"{prefix} {stub.name}(")
            for i, (name, typ, comment) in enumerate(stub.params):
                comma = "," if i < len(stub.params) - 1 else ","
                line = f"    {name}: {typ}{comma}"
                if comment:
                    line += comment
                lines.append(line)
            lines.append(f") -> {stub.return_type}: ...")
            if stub.return_comment:
                lines.append(f"    # return{stub.return_comment}")

        if self._include_docstrings and stub.docstring:
            lines.insert(
                len(stub.decorators) + 1,
                f'    """{stub.docstring}"""',
            )

        return lines

    def _generate_variable_stubs(
        self,
        sections: Dict[SiteId, LocalSection],
        covers: List[Cover],
    ) -> List[str]:
        """Generate module-level variable stubs."""
        lines: List[str] = []

        func_sites: Set[SiteId] = set()
        for cover in covers:
            func_sites |= cover.input_boundary
            func_sites |= cover.output_boundary

        for sid, sec in sorted(sections.items(), key=lambda x: str(x[0])):
            if sid in func_sites:
                continue
            if sid.kind == SiteKind.MODULE_SUMMARY:
                var_name = _extract_param_name(sid)
                type_str = _type_to_stub(sec.carrier_type)
                line = f"{var_name}: {type_str}"
                if self._include_comments and sec.refinements:
                    line += _refinements_to_comment(sec.refinements)
                lines.append(line)

        return lines

    def _format_function_stub(
        self,
        func_name: str,
        input_sections: List[LocalSection],
        output_sections: List[LocalSection],
    ) -> str:
        """Format a single function stub from input/output sections."""
        params: List[Tuple[str, str, str]] = []
        for sec in input_sections:
            param_name = _extract_param_name(sec.site_id)
            type_str = _type_to_stub(sec.carrier_type)
            comment = ""
            if self._include_comments and sec.refinements:
                comment = _refinements_to_comment(sec.refinements)
            params.append((param_name, type_str, comment))

        return_type = "None"
        return_comment = ""
        if output_sections:
            return_type = _type_to_stub(output_sections[0].carrier_type)
            if self._include_comments and output_sections[0].refinements:
                return_comment = _refinements_to_comment(
                    output_sections[0].refinements
                )

        stub = _FunctionStubData(
            name=func_name,
            params=params,
            return_type=return_type,
            return_comment=return_comment,
        )
        lines = self._format_function_stub_lines(stub)
        return "\n".join(lines)

    def generate_class_stub(
        self,
        class_name: str,
        method_covers: List[Cover],
        sections: Dict[SiteId, LocalSection],
    ) -> str:
        """Generate a stub for a class with its methods."""
        lines: List[str] = []
        lines.append(f"class {class_name}:")

        for cover in method_covers:
            func_stubs = self._generate_function_stubs(cover, sections)
            for stub in func_stubs:
                stub_lines = self._format_function_stub_lines(stub)
                for sl in stub_lines:
                    lines.append(f"    {sl}")
                lines.append("")

        if len(lines) == 1:
            lines.append("    ...")

        return "\n".join(lines)
