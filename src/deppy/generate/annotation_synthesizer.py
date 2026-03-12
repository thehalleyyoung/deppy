"""Synthesize type annotations from local sections.

AnnotationSynthesizer converts LocalSection refinements into Python type
annotation strings that can be inserted into source code.  It handles
primitive types, container types, refinement types (as comments), and
qualified types.
"""

from __future__ import annotations

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
    Cover,
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
    ComparisonOp,
    ComparisonPred,
    ConjunctionPred,
    LengthPred,
    Predicate,
    QualifiedType,
    RefinementType,
    TruePred,
)


# ---------------------------------------------------------------------------
# Annotation data
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SynthesizedAnnotation:
    """A synthesized type annotation for a code location.

    Attributes:
        site_id: The site this annotation was derived from.
        annotation: The annotation string (e.g. "int", "list[str]").
        refinement_comment: Optional refinement comment for inline use.
        variable_name: The variable or parameter name.
        trust: Trust level of the underlying section.
        is_return: Whether this is a return type annotation.
    """

    _site_id: SiteId
    _annotation: str
    _refinement_comment: str = ""
    _variable_name: str = ""
    _trust: TrustLevel = TrustLevel.TRUSTED_AUTO
    _is_return: bool = False

    @property
    def site_id(self) -> SiteId:
        return self._site_id

    @property
    def annotation(self) -> str:
        return self._annotation

    @property
    def refinement_comment(self) -> str:
        return self._refinement_comment

    @property
    def variable_name(self) -> str:
        return self._variable_name

    @property
    def trust(self) -> TrustLevel:
        return self._trust

    @property
    def is_return(self) -> bool:
        return self._is_return

    def to_inline(self) -> str:
        """Format as an inline annotation: 'var: type'."""
        if self._is_return:
            return f"-> {self._annotation}"
        if self._variable_name:
            return f"{self._variable_name}: {self._annotation}"
        return self._annotation

    def to_inline_with_comment(self) -> str:
        """Format as an inline annotation with refinement comment."""
        base = self.to_inline()
        if self._refinement_comment:
            return f"{base}  # {self._refinement_comment}"
        return base


# ---------------------------------------------------------------------------
# Type-to-annotation conversion
# ---------------------------------------------------------------------------

def _type_to_annotation(t: Any) -> str:
    """Convert a type to a Python annotation string."""
    if t is None:
        return "Any"
    if isinstance(t, AnyType):
        return "Any"
    if isinstance(t, NeverType):
        return "Never"
    if isinstance(t, PrimitiveType):
        return t.kind.value
    if isinstance(t, ListType):
        elem = _type_to_annotation(t.element)
        return f"list[{elem}]"
    if isinstance(t, DictType):
        k = _type_to_annotation(t.key)
        v = _type_to_annotation(t.value)
        return f"dict[{k}, {v}]"
    if isinstance(t, TupleType):
        if t.variadic and len(t.elements) == 1:
            elem = _type_to_annotation(t.elements[0])
            return f"tuple[{elem}, ...]"
        elems = ", ".join(_type_to_annotation(e) for e in t.elements)
        return f"tuple[{elems}]"
    if isinstance(t, SetType):
        elem = _type_to_annotation(t.element)
        return f"set[{elem}]"
    if isinstance(t, FrozenSetType):
        elem = _type_to_annotation(t.element)
        return f"frozenset[{elem}]"
    if isinstance(t, OptionalType):
        inner = _type_to_annotation(t.inner)
        return f"{inner} | None"
    if isinstance(t, UnionType):
        members = " | ".join(_type_to_annotation(m) for m in t.members)
        return members
    if isinstance(t, CallableType):
        params = ", ".join(_type_to_annotation(p) for p in t.param_types)
        ret = _type_to_annotation(t.return_type)
        prefix = ""
        if t.is_async:
            prefix = "Coroutine[Any, Any, "
            return f"{prefix}{ret}]"
        return f"Callable[[{params}], {ret}]"
    if isinstance(t, ClassType):
        if t.type_args:
            args = ", ".join(_type_to_annotation(a) for a in t.type_args)
            return f"{t.name}[{args}]"
        return t.name
    if isinstance(t, RefinementType):
        return _type_to_annotation(t.base)
    if isinstance(t, QualifiedType):
        return _type_to_annotation(t.base)
    return str(t)


def _refinements_to_comment(refinements: Dict[str, Any]) -> str:
    """Convert refinements to a comment string."""
    parts: List[str] = []
    for key, value in sorted(refinements.items()):
        if key.startswith("_"):
            continue
        if isinstance(value, bool):
            if value:
                parts.append(key)
        elif isinstance(value, Predicate):
            parts.append(repr(value))
        else:
            parts.append(f"{key}={value!r}")
    return ", ".join(parts)


def _extract_variable_name(site_id: SiteId) -> str:
    """Extract variable name from a site ID."""
    name = site_id.name
    for sep in (".", ":", "/"):
        parts = name.rsplit(sep, 1)
        if len(parts) == 2:
            return parts[1]
    return name


# ---------------------------------------------------------------------------
# Section-to-annotation conversion
# ---------------------------------------------------------------------------

def _section_to_annotation(section: LocalSection) -> str:
    """Convert a LocalSection to a Python type annotation string.

    Handles carrier types, refinement types, and qualified types.
    The refinement information is encoded in the base type annotation
    since Python's type system cannot express refinements directly.
    """
    carrier = section.carrier_type

    if carrier is None:
        return _infer_from_refinements(section.refinements)

    if isinstance(carrier, RefinementType):
        base_ann = _type_to_annotation(carrier.base)
        return base_ann

    if isinstance(carrier, QualifiedType):
        base_ann = _type_to_annotation(carrier.base)
        return base_ann

    return _type_to_annotation(carrier)


def _infer_from_refinements(refinements: Dict[str, Any]) -> str:
    """Attempt to infer a type from refinement keys alone."""
    if "non_null" in refinements:
        return "Any"  # We know it's not None, but not the base type

    for key in refinements:
        if key in ("positive", "non_negative", "negative", "bounded"):
            return "int"
        if key in ("non_empty", "sorted", "unique", "max_length", "min_length"):
            return "list[Any]"

    return "Any"


def _section_to_refinement_comment(section: LocalSection) -> str:
    """Build a refinement comment from a section."""
    parts: List[str] = []
    carrier = section.carrier_type

    if isinstance(carrier, RefinementType):
        pred_str = repr(carrier.predicate)
        if not isinstance(carrier.predicate, TruePred):
            parts.append(pred_str)

    if isinstance(carrier, QualifiedType):
        quals = [q.name() for q in carrier.qualifiers]
        parts.extend(quals)

    ref_comment = _refinements_to_comment(section.refinements)
    if ref_comment:
        parts.append(ref_comment)

    return ", ".join(parts)


# ---------------------------------------------------------------------------
# AnnotationSynthesizer
# ---------------------------------------------------------------------------

class AnnotationSynthesizer:
    """Synthesize Python type annotations from local sections.

    Converts the LocalSection carrier types and refinements into
    annotation strings suitable for insertion into Python source code.

    Usage::

        synth = AnnotationSynthesizer()
        annotations = synth.synthesize(sections)
        for name, ann in annotations.items():
            print(f"{name}: {ann}")
    """

    def __init__(
        self,
        *,
        include_refinement_comments: bool = True,
        min_trust: TrustLevel = TrustLevel.RESIDUAL,
        prefer_union_syntax: bool = True,
    ) -> None:
        self._include_comments = include_refinement_comments
        self._min_trust = min_trust
        self._prefer_union_syntax = prefer_union_syntax
        self._trust_order = {
            TrustLevel.PROOF_BACKED: 5,
            TrustLevel.TRUSTED_AUTO: 4,
            TrustLevel.TRACE_BACKED: 3,
            TrustLevel.BOUNDED_AUTO: 2,
            TrustLevel.ASSUMED: 1,
            TrustLevel.RESIDUAL: 0,
        }

    def synthesize(
        self,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[str, str]:
        """Synthesize annotations for all sections.

        Returns a dict mapping variable/parameter names to annotation strings.
        """
        result: Dict[str, str] = {}
        for sid, sec in sorted(sections.items(), key=lambda x: str(x[0])):
            if not self._meets_trust(sec.trust):
                continue
            var_name = _extract_variable_name(sid)
            annotation = self._section_to_annotation(sec)
            if annotation and annotation != "Any":
                result[var_name] = annotation
            elif annotation == "Any":
                result.setdefault(var_name, "Any")
        return result

    def synthesize_detailed(
        self,
        sections: Dict[SiteId, LocalSection],
    ) -> List[SynthesizedAnnotation]:
        """Synthesize detailed annotation objects for all sections."""
        results: List[SynthesizedAnnotation] = []

        for sid, sec in sorted(sections.items(), key=lambda x: str(x[0])):
            if not self._meets_trust(sec.trust):
                continue

            var_name = _extract_variable_name(sid)
            annotation = self._section_to_annotation(sec)
            comment = ""
            if self._include_comments:
                comment = _section_to_refinement_comment(sec)

            is_return = sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY

            results.append(SynthesizedAnnotation(
                _site_id=sid,
                _annotation=annotation,
                _refinement_comment=comment,
                _variable_name=var_name,
                _trust=sec.trust,
                _is_return=is_return,
            ))

        return results

    def synthesize_for_function(
        self,
        cover: Cover,
        sections: Dict[SiteId, LocalSection],
    ) -> Dict[str, str]:
        """Synthesize annotations scoped to a function cover."""
        result: Dict[str, str] = {}

        for sid in sorted(cover.input_boundary, key=str):
            sec = sections.get(sid)
            if sec is None:
                continue
            if not self._meets_trust(sec.trust):
                continue
            var_name = _extract_variable_name(sid)
            result[var_name] = self._section_to_annotation(sec)

        for sid in sorted(cover.output_boundary, key=str):
            sec = sections.get(sid)
            if sec is None:
                continue
            if not self._meets_trust(sec.trust):
                continue
            result["return"] = self._section_to_annotation(sec)

        return result

    def _section_to_annotation(self, section: LocalSection) -> str:
        """Convert a section to an annotation string."""
        return _section_to_annotation(section)

    def _meets_trust(self, trust: TrustLevel) -> bool:
        """Check if a trust level meets the minimum threshold."""
        return (
            self._trust_order.get(trust, 0)
            >= self._trust_order.get(self._min_trust, 0)
        )

    def format_signature(
        self,
        func_name: str,
        param_annotations: Dict[str, str],
        return_annotation: Optional[str] = None,
    ) -> str:
        """Format a function signature with synthesized annotations."""
        params: List[str] = []
        for name, ann in param_annotations.items():
            if name == "return":
                continue
            params.append(f"{name}: {ann}")

        params_str = ", ".join(params)
        ret = return_annotation or param_annotations.get("return", "None")
        return f"def {func_name}({params_str}) -> {ret}: ..."

    def summarize(
        self,
        annotations: List[SynthesizedAnnotation],
    ) -> str:
        """Produce a human-readable summary of synthesized annotations."""
        if not annotations:
            return "No annotations synthesized."

        lines: List[str] = []
        lines.append(f"Synthesized Annotations ({len(annotations)} total):")

        for ann in annotations:
            trust_str = f" [{ann.trust.value}]"
            inline = ann.to_inline()
            lines.append(f"  {inline}{trust_str}")
            if ann.refinement_comment:
                lines.append(f"    # {ann.refinement_comment}")

        return "\n".join(lines)
