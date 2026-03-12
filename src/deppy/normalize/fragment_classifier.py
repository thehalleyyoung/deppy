"""Classify predicates by decidability fragment.

The FragmentClassifier examines predicate structure and classifies each
into a decidability fragment:

- **QF_LIA**: Quantifier-free linear integer arithmetic.
- **QF_LRA**: Quantifier-free linear real (rational) arithmetic.
- **PROPOSITIONAL**: Pure boolean combinations of atomic propositions.
- **FINITE_DOMAIN**: Predicates over finite-domain variables (enums, booleans).
- **UNDECIDABLE**: Predicates that fall outside decidable fragments.

This classification drives solver dispatch: decidable fragments can
be handled by decision procedures, while undecidable ones require
heuristics or approximation.
"""

from __future__ import annotations

import enum
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

from deppy.core._protocols import LocalSection, SiteId


# ===================================================================
#  Fragment classification
# ===================================================================


class Fragment(enum.Enum):
    """Decidability fragments for predicate classification."""

    QF_LIA = "qf_lia"  # Quantifier-free linear integer arithmetic
    QF_LRA = "qf_lra"  # Quantifier-free linear real arithmetic
    PROPOSITIONAL = "propositional"  # Pure boolean
    FINITE_DOMAIN = "finite_domain"  # Finite-domain (enum, bool, small int)
    QF_NIA = "qf_nia"  # Quantifier-free nonlinear integer arithmetic
    QF_NRA = "qf_nra"  # Quantifier-free nonlinear real arithmetic
    STRING = "string"  # String constraints
    ARRAY = "array"  # Array/sequence theory
    MIXED = "mixed"  # Multiple fragments
    UNDECIDABLE = "undecidable"  # General (may be undecidable)


@dataclass(frozen=True)
class FragmentInfo:
    """Detailed information about a fragment classification."""

    _fragment: Fragment
    _confidence: float  # 0.0 to 1.0
    _reason: str
    _sub_fragments: Tuple[Fragment, ...] = ()
    _has_quantifiers: bool = False
    _has_nonlinear: bool = False
    _variable_count: int = 0
    _constraint_count: int = 0

    @property
    def fragment(self) -> Fragment:
        return self._fragment

    @property
    def confidence(self) -> float:
        return self._confidence

    @property
    def reason(self) -> str:
        return self._reason

    @property
    def sub_fragments(self) -> Tuple[Fragment, ...]:
        return self._sub_fragments

    @property
    def has_quantifiers(self) -> bool:
        return self._has_quantifiers

    @property
    def has_nonlinear(self) -> bool:
        return self._has_nonlinear

    @property
    def is_decidable(self) -> bool:
        return self._fragment not in (Fragment.UNDECIDABLE, Fragment.QF_NIA)

    @property
    def is_efficiently_decidable(self) -> bool:
        return self._fragment in (
            Fragment.PROPOSITIONAL,
            Fragment.FINITE_DOMAIN,
            Fragment.QF_LIA,
            Fragment.QF_LRA,
        )


# ===================================================================
#  Predicate analysis helpers
# ===================================================================


def _is_linear_term(value: Any) -> bool:
    """Check if a refinement value represents a linear constraint."""
    if isinstance(value, (int, float)):
        return True
    if isinstance(value, str):
        # Heuristic: check for linear arithmetic keywords
        nonlinear_ops = ("**", "pow(", "sqrt(", "exp(", "log(", "*", "/")
        linear_ops = (">", "<", ">=", "<=", "==", "!=", "+", "-")
        text = value
        if any(op in text for op in ("**", "pow(", "sqrt(", "exp(", "log(")):
            return False
        # Check for multiplication of two variables (nonlinear)
        parts = text.split("*")
        if len(parts) > 1:
            non_numeric = sum(1 for p in parts if not p.strip().lstrip("-").isdigit())
            if non_numeric > 1:
                return False
        return True
    return False


def _is_integer_constraint(value: Any) -> bool:
    """Check if a refinement value involves integer arithmetic."""
    if isinstance(value, int):
        return True
    if isinstance(value, float):
        return False
    if isinstance(value, str):
        # Heuristic: integer keywords
        int_keywords = ("int", "len(", "index", "count", "//", "%")
        float_keywords = ("float", ".0", "inf", "nan")
        if any(kw in value for kw in float_keywords):
            return False
        if any(kw in value for kw in int_keywords):
            return True
    return True  # default: assume integer


def _is_boolean_constraint(value: Any) -> bool:
    """Check if a refinement value is purely boolean."""
    if isinstance(value, bool):
        return True
    if isinstance(value, str):
        lower = value.lower().strip()
        if lower in ("true", "false", "none"):
            return True
        # Check for pure boolean operations
        bool_ops = ("and", "or", "not", "is None", "is not None",
                     "isinstance", "is True", "is False")
        if any(op in value for op in bool_ops):
            # But not if there are arithmetic operations
            arith_ops = (">", "<", ">=", "<=", "+", "-", "*", "/", "%")
            if not any(op in value for op in arith_ops):
                return True
    return False


def _is_finite_domain(value: Any) -> bool:
    """Check if a refinement value is over a finite domain."""
    if isinstance(value, bool):
        return True
    if isinstance(value, str):
        # Enum membership or small integer set
        finite_patterns = ("in (", "in [", "in {", "isinstance(", "Literal[")
        return any(p in value for p in finite_patterns)
    if isinstance(value, (list, tuple, set, frozenset)):
        return len(value) <= 256  # arbitrary threshold
    return False


def _has_string_ops(value: Any) -> bool:
    """Check if a refinement involves string operations."""
    if isinstance(value, str):
        string_ops = (
            "str", "startswith", "endswith", "contains",
            "regex", "match", "find", "replace", "split",
            "strip", "lower", "upper", "encode", "decode",
        )
        return any(op in value for op in string_ops)
    return False


def _has_quantifier(value: Any) -> bool:
    """Check if a refinement involves quantifiers."""
    if isinstance(value, str):
        quantifier_words = ("forall", "exists", "all(", "any(", "for all", "there exists")
        return any(q in value.lower() for q in quantifier_words)
    return False


# ===================================================================
#  FragmentClassifier
# ===================================================================


class FragmentClassifier:
    """Classify predicates and refinements by decidability fragment.

    The classifier examines the structure of refinement values in
    local sections and determines which SMT/decision procedure theory
    they belong to.
    """

    def classify(self, predicate: Any) -> FragmentInfo:
        """Classify a single predicate or refinement value.

        Parameters
        ----------
        predicate : Any
            A predicate object, refinement value, or string representation.

        Returns
        -------
        FragmentInfo
            Classification with confidence and reasoning.
        """
        has_quant = _has_quantifier(predicate)

        if has_quant:
            return FragmentInfo(
                _fragment=Fragment.UNDECIDABLE,
                _confidence=0.7,
                _reason="Contains quantifiers",
                _has_quantifiers=True,
            )

        if _is_finite_domain(predicate):
            return FragmentInfo(
                _fragment=Fragment.FINITE_DOMAIN,
                _confidence=0.9,
                _reason="Finite-domain constraint",
            )

        if _is_boolean_constraint(predicate):
            return FragmentInfo(
                _fragment=Fragment.PROPOSITIONAL,
                _confidence=0.9,
                _reason="Pure boolean constraint",
            )

        if _has_string_ops(predicate):
            return FragmentInfo(
                _fragment=Fragment.STRING,
                _confidence=0.8,
                _reason="String theory constraint",
            )

        is_linear = _is_linear_term(predicate)
        is_integer = _is_integer_constraint(predicate)

        if is_linear and is_integer:
            return FragmentInfo(
                _fragment=Fragment.QF_LIA,
                _confidence=0.85,
                _reason="Quantifier-free linear integer arithmetic",
            )

        if is_linear and not is_integer:
            return FragmentInfo(
                _fragment=Fragment.QF_LRA,
                _confidence=0.85,
                _reason="Quantifier-free linear real arithmetic",
            )

        if not is_linear and is_integer:
            return FragmentInfo(
                _fragment=Fragment.QF_NIA,
                _confidence=0.7,
                _reason="Quantifier-free nonlinear integer arithmetic",
                _has_nonlinear=True,
            )

        if not is_linear and not is_integer:
            return FragmentInfo(
                _fragment=Fragment.QF_NRA,
                _confidence=0.7,
                _reason="Quantifier-free nonlinear real arithmetic",
                _has_nonlinear=True,
            )

        return FragmentInfo(
            _fragment=Fragment.UNDECIDABLE,
            _confidence=0.5,
            _reason="Could not classify into a known fragment",
        )

    def classify_section(
        self, section: LocalSection
    ) -> Dict[str, FragmentInfo]:
        """Classify all refinements in a local section.

        Parameters
        ----------
        section : LocalSection
            The local section whose refinements to classify.

        Returns
        -------
        dict
            Mapping from refinement key to its FragmentInfo.
        """
        result: Dict[str, FragmentInfo] = {}
        for key, value in section.refinements.items():
            result[key] = self.classify(value)
        return result

    def classify_sections(
        self, sections: Mapping[SiteId, LocalSection]
    ) -> Dict[SiteId, Dict[str, FragmentInfo]]:
        """Classify refinements across multiple sections.

        Parameters
        ----------
        sections : mapping of SiteId to LocalSection

        Returns
        -------
        dict
            Nested mapping from SiteId to refinement key to FragmentInfo.
        """
        result: Dict[SiteId, Dict[str, FragmentInfo]] = {}
        for site_id, section in sections.items():
            classified = self.classify_section(section)
            if classified:
                result[site_id] = classified
        return result

    def overall_fragment(
        self, sections: Mapping[SiteId, LocalSection]
    ) -> FragmentInfo:
        """Compute the overall fragment for a collection of sections.

        The overall fragment is the least decidable fragment present.
        """
        all_fragments: List[Fragment] = []
        all_infos = self.classify_sections(sections)

        for site_infos in all_infos.values():
            for info in site_infos.values():
                all_fragments.append(info.fragment)

        if not all_fragments:
            return FragmentInfo(
                _fragment=Fragment.PROPOSITIONAL,
                _confidence=1.0,
                _reason="No refinements to classify",
            )

        unique_fragments = set(all_fragments)

        if Fragment.UNDECIDABLE in unique_fragments:
            return FragmentInfo(
                _fragment=Fragment.UNDECIDABLE,
                _confidence=0.8,
                _reason="Contains undecidable constraints",
                _sub_fragments=tuple(sorted(unique_fragments, key=lambda f: f.value)),
            )

        if len(unique_fragments) == 1:
            fragment = unique_fragments.pop()
            return FragmentInfo(
                _fragment=fragment,
                _confidence=0.9,
                _reason=f"Uniform {fragment.value} fragment",
            )

        # Mixed fragments -- determine combined fragment
        decidable_order = [
            Fragment.PROPOSITIONAL,
            Fragment.FINITE_DOMAIN,
            Fragment.QF_LIA,
            Fragment.QF_LRA,
            Fragment.STRING,
            Fragment.QF_NIA,
            Fragment.QF_NRA,
            Fragment.ARRAY,
            Fragment.MIXED,
        ]

        worst = Fragment.PROPOSITIONAL
        for frag in all_fragments:
            if frag in decidable_order:
                idx = decidable_order.index(frag)
                worst_idx = decidable_order.index(worst)
                if idx > worst_idx:
                    worst = frag

        return FragmentInfo(
            _fragment=Fragment.MIXED if len(unique_fragments) > 1 else worst,
            _confidence=0.7,
            _reason=f"Mixed fragments: {', '.join(f.value for f in sorted(unique_fragments, key=lambda f: f.value))}",
            _sub_fragments=tuple(sorted(unique_fragments, key=lambda f: f.value)),
        )

    def summary(self, sections: Mapping[SiteId, LocalSection]) -> str:
        """Produce a human-readable summary of fragment classification."""
        overall = self.overall_fragment(sections)
        all_infos = self.classify_sections(sections)

        lines: List[str] = []
        lines.append(f"Overall fragment: {overall.fragment.value}")
        lines.append(f"  Confidence: {overall.confidence:.0%}")
        lines.append(f"  Decidable: {overall.is_decidable}")
        lines.append(f"  Reason: {overall.reason}")

        if overall.sub_fragments:
            lines.append(f"  Sub-fragments: {', '.join(f.value for f in overall.sub_fragments)}")

        # Per-site breakdown
        fragment_counts: Dict[Fragment, int] = {}
        for site_infos in all_infos.values():
            for info in site_infos.values():
                fragment_counts[info.fragment] = fragment_counts.get(info.fragment, 0) + 1

        if fragment_counts:
            lines.append("\nFragment distribution:")
            for frag, count in sorted(fragment_counts.items(), key=lambda x: -x[1]):
                lines.append(f"  {frag.value}: {count}")

        return "\n".join(lines)
