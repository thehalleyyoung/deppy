"""
Parse natural language specifications into HybridSpec.

Decomposes NL text into structural (decidable, Z3-checkable) and semantic
(oracle/LLM-judged) claims so that downstream compilation can route each
claim to the right verification back-end.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# NLClaimKind
# ---------------------------------------------------------------------------


# --- Integration with existing deppy codebase ---
try:
    from deppy.nl_synthesis import synthesize_types_from_docstring, DocstringParser
    from deppy.nl_synthesis.models import SynthesizedConstraint, SynthesisEvidence
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

class NLClaimKind(Enum):
    """Classification tag for a parsed NL claim."""

    STRUCTURAL_BOUND = auto()
    STRUCTURAL_TYPE = auto()
    STRUCTURAL_RELATION = auto()
    STRUCTURAL_INVARIANT = auto()

    SEMANTIC_CORRECTNESS = auto()
    SEMANTIC_QUALITY = auto()
    SEMANTIC_BEHAVIOR = auto()
    SEMANTIC_SAFETY = auto()

    COMPLEXITY = auto()
    REFERENCE = auto()
    ASSUMPTION = auto()


# ---------------------------------------------------------------------------
# ParsedClaim
# ---------------------------------------------------------------------------

@dataclass
class ParsedClaim:
    """A single claim extracted from a natural-language specification."""

    text: str
    kind: NLClaimKind
    decidable: bool
    structural_formula: Optional[str] = None
    semantic_prompt: Optional[str] = None
    variables: Dict[str, str] = field(default_factory=dict)
    confidence: float = 1.0
    source_location: Optional[str] = None

    # ----- helpers -----

    def is_structural(self) -> bool:
        return self.kind.name.startswith("STRUCTURAL")

    def is_semantic(self) -> bool:
        return self.kind.name.startswith("SEMANTIC")

    def merge_variables(self, other: ParsedClaim) -> Dict[str, str]:
        merged = dict(self.variables)
        merged.update(other.variables)
        return merged

    def weaken(self) -> ParsedClaim:
        """Return a weaker, decidable approximation of a semantic claim."""
        if self.decidable:
            return self
        return ParsedClaim(
            text=self.text,
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            decidable=True,
            structural_formula="True",
            semantic_prompt=None,
            variables=dict(self.variables),
            confidence=self.confidence * 0.5,
            source_location=self.source_location,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "text": self.text,
            "kind": self.kind.name,
            "decidable": self.decidable,
            "structural_formula": self.structural_formula,
            "semantic_prompt": self.semantic_prompt,
            "variables": self.variables,
            "confidence": self.confidence,
            "source_location": self.source_location,
        }


# ===================================================================
# StructuralPatternMatcher  (~400 lines)
# ===================================================================

@dataclass
class _PatternEntry:
    """Internal representation for a single pattern rule."""

    name: str
    regex: re.Pattern[str]
    kind: NLClaimKind
    formula_template: str
    description: str = ""


class StructuralPatternMatcher:
    """
    Library of regex / keyword patterns that recognise decidable claims
    inside natural language text and emit Z3-encodable formulas.
    """

    def __init__(self) -> None:
        self._patterns: List[_PatternEntry] = []
        self._build_patterns()

    # ------------------------------------------------------------------ build
    def _build_patterns(self) -> None:  # noqa: C901 — deliberately long
        _add = self._patterns.append

        # 1. at least N
        _add(_PatternEntry(
            name="at_least",
            regex=re.compile(
                r"(?:at\s+least|>=?|no\s+fewer\s+than)\s+(\d+)",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} >= {n}",
            description="lower bound on a numeric value",
        ))

        # 2. at most N
        _add(_PatternEntry(
            name="at_most",
            regex=re.compile(
                r"(?:at\s+most|<=?|no\s+more\s+than)\s+(\d+)",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} <= {n}",
            description="upper bound on a numeric value",
        ))

        # 3. exactly N
        _add(_PatternEntry(
            name="exactly",
            regex=re.compile(
                r"(?:exactly|==)\s+(\d+)",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} == {n}",
            description="exact equality to a literal",
        ))

        # 4. sorted / ascending
        _add(_PatternEntry(
            name="sorted_ascending",
            regex=re.compile(
                r"\b(?:sorted|ascending|non-decreasing|nondecreasing)\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="ForAll([i], Implies(And(i >= 0, i < Length({var}) - 1), {var}[i] <= {var}[i+1]))",
            description="array is sorted ascending",
        ))

        # 5. descending
        _add(_PatternEntry(
            name="sorted_descending",
            regex=re.compile(
                r"\b(?:descending|non-increasing|nonincreasing)\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="ForAll([i], Implies(And(i >= 0, i < Length({var}) - 1), {var}[i] >= {var}[i+1]))",
            description="array is sorted descending",
        ))

        # 6. non-empty / not empty
        _add(_PatternEntry(
            name="non_empty",
            regex=re.compile(
                r"\b(?:non[- ]?empty|not\s+empty|has\s+elements?)\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="Length({var}) > 0",
            description="collection is non-empty",
        ))

        # 7. unique / no duplicates
        _add(_PatternEntry(
            name="unique",
            regex=re.compile(
                r"\b(?:unique|no\s+duplicates?|distinct\s+elements?|all\s+different)\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="Distinct({var})",
            description="all elements are unique",
        ))

        # 8. in range [a,b]
        _add(_PatternEntry(
            name="in_range",
            regex=re.compile(
                r"\bin\s+(?:the\s+)?range\s*[\[(]\s*(-?\d+)\s*,\s*(-?\d+)\s*[\])]",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="And({var} >= {lo}, {var} <= {hi})",
            description="value lies in a numeric range",
        ))

        # 9. between a and b
        _add(_PatternEntry(
            name="between",
            regex=re.compile(
                r"\bbetween\s+(-?\d+)\s+and\s+(-?\d+)\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="And({var} >= {lo}, {var} <= {hi})",
            description="value between two bounds",
        ))

        # 10. positive
        _add(_PatternEntry(
            name="positive",
            regex=re.compile(r"\b(?:positive|> *0|greater\s+than\s+(?:zero|0))\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} > 0",
            description="value is strictly positive",
        ))

        # 11. negative
        _add(_PatternEntry(
            name="negative",
            regex=re.compile(r"\b(?:negative|< *0|less\s+than\s+(?:zero|0))\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} < 0",
            description="value is strictly negative",
        ))

        # 12. non-negative
        _add(_PatternEntry(
            name="non_negative",
            regex=re.compile(r"\b(?:non[- ]?negative|>= *0)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} >= 0",
            description="value is non-negative",
        ))

        # 13. same length / same size
        _add(_PatternEntry(
            name="same_length",
            regex=re.compile(
                r"\bsame\s+(?:length|size|cardinality)\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_RELATION,
            formula_template="Length({var1}) == Length({var2})",
            description="two collections have equal size",
        ))

        # 14. subset of
        _add(_PatternEntry(
            name="subset_of",
            regex=re.compile(r"\bsubset\s+of\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_RELATION,
            formula_template="IsSubset({var1}, {var2})",
            description="set inclusion (subset)",
        ))

        # 15. superset of
        _add(_PatternEntry(
            name="superset_of",
            regex=re.compile(r"\bsuperset\s+of\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_RELATION,
            formula_template="IsSubset({var2}, {var1})",
            description="set inclusion (superset)",
        ))

        # 16. returns X / output is X
        _add(_PatternEntry(
            name="returns_value",
            regex=re.compile(
                r"\b(?:returns?|output\s+(?:is|equals?|==))\s+(.+)",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} == {value}",
            description="function returns a specific value",
        ))

        # 17. type is X / instance of X
        _add(_PatternEntry(
            name="type_check",
            regex=re.compile(
                r"\b(?:type\s+is|instance\s+of|isinstance)\s+(\w+)\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_TYPE,
            formula_template="isinstance({var}, {type_name})",
            description="runtime type assertion",
        ))

        # 18. not null / not None
        _add(_PatternEntry(
            name="not_none",
            regex=re.compile(
                r"\b(?:not\s+(?:null|None|nil)|non[- ]?null|non[- ]?none)\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} is not None",
            description="value is not None / null",
        ))

        # 19. valid email
        _add(_PatternEntry(
            name="valid_email",
            regex=re.compile(r"\bvalid\s+e-?mail\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="re.match(r'^[^@]+@[^@]+\\.[^@]+$', {var}) is not None",
            description="string matches email pattern",
        ))

        # 20. valid URL
        _add(_PatternEntry(
            name="valid_url",
            regex=re.compile(r"\bvalid\s+(?:URL|uri)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="re.match(r'^https?://.+', {var}) is not None",
            description="string matches URL pattern",
        ))

        # 21. even
        _add(_PatternEntry(
            name="even",
            regex=re.compile(r"\b(?:even|divisible\s+by\s+2)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} % 2 == 0",
            description="value is even",
        ))

        # 22. odd
        _add(_PatternEntry(
            name="odd",
            regex=re.compile(r"\bodd\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} % 2 == 1",
            description="value is odd",
        ))

        # 23. divisible by N
        _add(_PatternEntry(
            name="divisible_by",
            regex=re.compile(r"\bdivisible\s+by\s+(\d+)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} % {n} == 0",
            description="value is divisible by N",
        ))

        # 24. palindrome
        _add(_PatternEntry(
            name="palindrome",
            regex=re.compile(r"\bpalindrome\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="{var} == {var}[::-1]",
            description="sequence is a palindrome",
        ))

        # 25. empty
        _add(_PatternEntry(
            name="empty",
            regex=re.compile(r"\b(?:is\s+)?empty\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="Length({var}) == 0",
            description="collection is empty",
        ))

        # 26. contains / includes
        _add(_PatternEntry(
            name="contains",
            regex=re.compile(r"\b(?:contains?|includes?)\s+(.+)", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_RELATION,
            formula_template="IsMember({element}, {var})",
            description="collection contains an element",
        ))

        # 27. does not contain / excludes
        _add(_PatternEntry(
            name="not_contains",
            regex=re.compile(
                r"\b(?:does\s+not\s+contain|excludes?|not\s+in)\s+(.+)",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_RELATION,
            formula_template="Not(IsMember({element}, {var}))",
            description="collection does not contain an element",
        ))

        # 28. length is / length equals
        _add(_PatternEntry(
            name="length_is",
            regex=re.compile(
                r"\b(?:length|size|count|len)\s+(?:is|equals?|==)\s+(\d+)\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="Length({var}) == {n}",
            description="collection has exact length",
        ))

        # 29. monotonically increasing / strictly increasing
        _add(_PatternEntry(
            name="strictly_increasing",
            regex=re.compile(
                r"\b(?:strictly|monotonically)\s+increasing\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="ForAll([i], Implies(And(i >= 0, i < Length({var}) - 1), {var}[i] < {var}[i+1]))",
            description="array is strictly increasing",
        ))

        # 30. monotonically decreasing / strictly decreasing
        _add(_PatternEntry(
            name="strictly_decreasing",
            regex=re.compile(
                r"\b(?:strictly|monotonically)\s+decreasing\b",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="ForAll([i], Implies(And(i >= 0, i < Length({var}) - 1), {var}[i] > {var}[i+1]))",
            description="array is strictly decreasing",
        ))

        # 31. starts with / prefix
        _add(_PatternEntry(
            name="starts_with",
            regex=re.compile(r"\b(?:starts?\s+with|prefix(?:ed)?\s+(?:by|with)?)\s+(.+)", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="PrefixOf({prefix}, {var})",
            description="string/sequence starts with prefix",
        ))

        # 32. ends with / suffix
        _add(_PatternEntry(
            name="ends_with",
            regex=re.compile(r"\b(?:ends?\s+with|suffix(?:ed)?\s+(?:by|with)?)\s+(.+)", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="SuffixOf({suffix}, {var})",
            description="string/sequence ends with suffix",
        ))

        # 33. greater than (variable comparison)
        _add(_PatternEntry(
            name="greater_than",
            regex=re.compile(r"\bgreater\s+than\s+(\w+)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_RELATION,
            formula_template="{var} > {other}",
            description="one value greater than another",
        ))

        # 34. less than (variable comparison)
        _add(_PatternEntry(
            name="less_than",
            regex=re.compile(r"\bless\s+than\s+(\w+)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_RELATION,
            formula_template="{var} < {other}",
            description="one value less than another",
        ))

        # 35. equals
        _add(_PatternEntry(
            name="equals",
            regex=re.compile(r"\b(?:equals?|equal\s+to|==)\s+(\w+)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_RELATION,
            formula_template="{var} == {other}",
            description="two values are equal",
        ))

        # 36. not equal
        _add(_PatternEntry(
            name="not_equal",
            regex=re.compile(r"\b(?:not\s+equal|!=|<>)\s*(?:to\s+)?(\w+)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_RELATION,
            formula_template="{var} != {other}",
            description="two values are not equal",
        ))

        # 37. boolean true
        _add(_PatternEntry(
            name="is_true",
            regex=re.compile(r"\b(?:is\s+[Tt]rue|holds|satisfied)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} == True",
            description="boolean is true",
        ))

        # 38. boolean false
        _add(_PatternEntry(
            name="is_false",
            regex=re.compile(r"\b(?:is\s+[Ff]alse|does\s+not\s+hold)\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="{var} == False",
            description="boolean is false",
        ))

        # 39. within epsilon / approximately
        _add(_PatternEntry(
            name="approximate",
            regex=re.compile(
                r"\b(?:approximately|within\s+(\S+)\s+of|close\s+to)\s+(\S+)",
                re.IGNORECASE,
            ),
            kind=NLClaimKind.STRUCTURAL_BOUND,
            formula_template="And({var} >= {target} - {eps}, {var} <= {target} + {eps})",
            description="value is within epsilon of a target",
        ))

        # 40. power of 2
        _add(_PatternEntry(
            name="power_of_two",
            regex=re.compile(r"\bpower\s+of\s+2\b", re.IGNORECASE),
            kind=NLClaimKind.STRUCTURAL_INVARIANT,
            formula_template="And({var} > 0, {var} & ({var} - 1) == 0)",
            description="value is a power of two",
        ))

    # ----------------------------------------------------------------- match
    def match(self, text: str) -> Optional[Tuple[str, Dict[str, Any]]]:
        """
        Attempt to match *text* against every known pattern.

        Returns ``(pattern_name, bindings)`` for the first match,
        or ``None`` when no pattern fires.
        """
        text_stripped = text.strip()
        for pat in self._patterns:
            m = pat.regex.search(text_stripped)
            if m is None:
                continue
            bindings = self._extract_bindings(pat, m, text_stripped)
            return pat.name, bindings
        return None

    def match_all(self, text: str) -> List[Tuple[str, Dict[str, Any]]]:
        """Return *all* matching patterns (not just the first)."""
        results: List[Tuple[str, Dict[str, Any]]] = []
        text_stripped = text.strip()
        for pat in self._patterns:
            m = pat.regex.search(text_stripped)
            if m is not None:
                bindings = self._extract_bindings(pat, m, text_stripped)
                results.append((pat.name, bindings))
        return results

    def get_pattern_names(self) -> List[str]:
        return [p.name for p in self._patterns]

    def get_pattern_count(self) -> int:
        return len(self._patterns)

    def get_formula_template(self, name: str) -> Optional[str]:
        for p in self._patterns:
            if p.name == name:
                return p.formula_template
        return None

    def get_kind(self, name: str) -> Optional[NLClaimKind]:
        for p in self._patterns:
            if p.name == name:
                return p.kind
        return None

    # --------------------------------------------------------- private helpers
    @staticmethod
    def _extract_bindings(
        pat: _PatternEntry,
        m: re.Match[str],
        full_text: str,
    ) -> Dict[str, Any]:
        """Build a bindings dict from the regex match groups."""
        groups = m.groups()
        bindings: Dict[str, Any] = {
            "pattern_name": pat.name,
            "kind": pat.kind,
            "formula_template": pat.formula_template,
            "matched_text": m.group(0),
            "full_text": full_text,
        }

        if pat.name in ("at_least", "at_most", "exactly", "divisible_by", "length_is"):
            bindings["n"] = int(groups[0]) if groups else None

        elif pat.name in ("in_range", "between"):
            if len(groups) >= 2:
                bindings["lo"] = int(groups[0])
                bindings["hi"] = int(groups[1])

        elif pat.name in ("returns_value", "contains", "not_contains",
                          "starts_with", "ends_with"):
            bindings["value"] = groups[0].strip() if groups else None

        elif pat.name in ("type_check",):
            bindings["type_name"] = groups[0].strip() if groups else None

        elif pat.name in ("greater_than", "less_than", "equals", "not_equal"):
            bindings["other"] = groups[0].strip() if groups else None

        elif pat.name == "approximate":
            if len(groups) >= 2:
                bindings["eps"] = groups[0]
                bindings["target"] = groups[1]

        return bindings

    def _format_formula(
        self,
        template: str,
        bindings: Dict[str, Any],
        var: str = "x",
    ) -> str:
        replacements: Dict[str, str] = {"{var}": var}
        for key, val in bindings.items():
            replacements["{" + key + "}"] = str(val)
        result = template
        for placeholder, value in replacements.items():
            result = result.replace(placeholder, value)
        return result

    def build_formula(
        self,
        pattern_name: str,
        bindings: Dict[str, Any],
        var: str = "x",
    ) -> Optional[str]:
        template = self.get_formula_template(pattern_name)
        if template is None:
            return None
        return self._format_formula(template, bindings, var)


# ===================================================================
# SemanticPromptBuilder  (~200 lines)
# ===================================================================

class SemanticPromptBuilder:
    """
    Builds prompts for an LLM-based oracle judge that evaluates
    semantic (non-decidable) claims about code outputs.
    """

    # ---- defaults ----
    DEFAULT_SYSTEM_PREAMBLE: str = (
        "You are an expert software-verification oracle.  "
        "Given a specification claim and an observed value, determine "
        "whether the claim is satisfied.  Be precise and cite evidence."
    )

    RUBRIC_SCALE: List[str] = [
        "fully_satisfied",
        "mostly_satisfied",
        "partially_satisfied",
        "not_satisfied",
        "cannot_determine",
    ]

    # ---- build judge prompt ----
    def build_judge_prompt(self, claim: str, context: Dict[str, Any]) -> str:
        """
        Format a prompt that asks the oracle to judge whether *claim*
        holds given the supplied *context* (variable values, function code,
        etc.).
        """
        lines: List[str] = [self.DEFAULT_SYSTEM_PREAMBLE, ""]
        lines.append("## Claim to verify")
        lines.append(f"> {claim}")
        lines.append("")

        if "function_code" in context:
            lines.append("## Function source")
            lines.append("```python")
            lines.append(str(context["function_code"]))
            lines.append("```")
            lines.append("")

        if "variables" in context:
            lines.append("## Variables in scope")
            for vname, vval in context["variables"].items():
                lines.append(f"- `{vname}` = {vval!r}")
            lines.append("")

        if "return_value" in context:
            lines.append("## Return value")
            lines.append(f"`{context['return_value']!r}`")
            lines.append("")

        if "inputs" in context:
            lines.append("## Inputs")
            for iname, ival in context["inputs"].items():
                lines.append(f"- `{iname}` = {ival!r}")
            lines.append("")

        if "constraints" in context:
            lines.append("## Additional constraints")
            for c in context["constraints"]:
                lines.append(f"- {c}")
            lines.append("")

        lines.append("## Instructions")
        lines.append(
            "Respond with one of: "
            + ", ".join(f"`{s}`" for s in self.RUBRIC_SCALE)
            + "."
        )
        lines.append(
            "Then explain your reasoning in ≤3 sentences, citing evidence "
            "from the return value or variables."
        )
        return "\n".join(lines)

    # ---- build rubric ----
    def build_rubric(self, claim: str) -> Dict[str, Any]:
        """
        Return a structured rubric dict an oracle can use to grade
        whether *claim* is satisfied.
        """
        rubric: Dict[str, Any] = {
            "claim": claim,
            "scale": list(self.RUBRIC_SCALE),
            "criteria": [],
        }

        tokens = claim.lower().split()

        if any(w in tokens for w in ("correct", "correctly", "accurate", "accurately")):
            rubric["criteria"].append({
                "name": "correctness",
                "description": "Output matches the expected correct answer",
                "weight": 0.6,
            })
            rubric["criteria"].append({
                "name": "edge_cases",
                "description": "Correct behaviour on boundary/edge inputs",
                "weight": 0.2,
            })
            rubric["criteria"].append({
                "name": "consistency",
                "description": "No internal contradictions",
                "weight": 0.2,
            })

        elif any(w in tokens for w in ("quality", "well-written", "readable", "clean")):
            rubric["criteria"].append({
                "name": "clarity",
                "description": "Output is clear and understandable",
                "weight": 0.4,
            })
            rubric["criteria"].append({
                "name": "completeness",
                "description": "All required parts are present",
                "weight": 0.3,
            })
            rubric["criteria"].append({
                "name": "style",
                "description": "Follows expected conventions",
                "weight": 0.3,
            })

        elif any(w in tokens for w in ("safe", "safety", "harmless", "secure")):
            rubric["criteria"].append({
                "name": "no_harm",
                "description": "Output does not cause harm",
                "weight": 0.5,
            })
            rubric["criteria"].append({
                "name": "no_leakage",
                "description": "No sensitive information exposed",
                "weight": 0.3,
            })
            rubric["criteria"].append({
                "name": "robustness",
                "description": "Handles adversarial input gracefully",
                "weight": 0.2,
            })

        else:
            rubric["criteria"].append({
                "name": "overall_satisfaction",
                "description": "The claim appears to hold given the evidence",
                "weight": 1.0,
            })

        return rubric

    # ---- build comparison prompt ----
    def build_comparison_prompt(self, claim: str, value: Any) -> str:
        """
        Build a prompt asking the oracle to check a *specific* value
        against the claim.
        """
        lines: List[str] = [
            self.DEFAULT_SYSTEM_PREAMBLE,
            "",
            "## Claim",
            f"> {claim}",
            "",
            "## Observed value",
            f"```\n{value!r}\n```",
            "",
            "## Task",
            "Does the observed value satisfy the claim?  "
            "Answer `yes` or `no`, then explain briefly.",
        ]
        return "\n".join(lines)

    # ---- helpers ----
    def build_multi_claim_prompt(
        self,
        claims: List[str],
        context: Dict[str, Any],
    ) -> str:
        """Judge multiple claims at once (saves oracle round-trips)."""
        lines: List[str] = [self.DEFAULT_SYSTEM_PREAMBLE, ""]
        lines.append("## Claims to verify (answer each separately)")
        for idx, c in enumerate(claims, 1):
            lines.append(f"{idx}. {c}")
        lines.append("")

        if "return_value" in context:
            lines.append("## Return value")
            lines.append(f"`{context['return_value']!r}`")
            lines.append("")

        if "variables" in context:
            lines.append("## Variables")
            for vname, vval in context["variables"].items():
                lines.append(f"- `{vname}` = {vval!r}")
            lines.append("")

        lines.append("## Instructions")
        lines.append(
            "For each numbered claim respond with one of: "
            + ", ".join(f"`{s}`" for s in self.RUBRIC_SCALE)
            + " and a one-sentence explanation."
        )
        return "\n".join(lines)


# ===================================================================
# NLSpecParser  (~800 lines)
# ===================================================================

class NLSpecParser:
    """
    Top-level parser that converts free-form natural-language
    specifications into a list of ``ParsedClaim`` objects.
    """

    # Words that indicate semantic (non-decidable) content
    SEMANTIC_KEYWORDS: List[str] = [
        "correct", "correctly", "accurate", "accurately",
        "appropriate", "appropriately", "novel", "creative",
        "well-written", "grounded", "relevant", "helpful",
        "safe", "fair", "ethical", "meaningful",
        "complete", "comprehensive", "reasonable", "sensible",
        "elegant", "efficient", "optimal", "robust",
    ]

    # Words strongly indicating structural / decidable content
    STRUCTURAL_KEYWORDS: List[str] = [
        "sorted", "length", "size", "count", "positive", "negative",
        "non-negative", "non-empty", "unique", "distinct", "range",
        "between", "at least", "at most", "exactly", "returns",
        "type", "instance", "not none", "not null", "empty",
        "contains", "subset", "superset", "equal", "greater",
        "less", "divisible", "even", "odd", "palindrome",
    ]

    COMPLEXITY_KEYWORDS: List[str] = [
        "O(", "Θ(", "Ω(", "big-O", "big-Theta",
        "time complexity", "space complexity",
        "polynomial", "linear", "logarithmic",
        "quadratic", "exponential", "constant time",
    ]

    SENTENCE_SPLIT_RE: re.Pattern[str] = re.compile(
        r'(?<=[.!?;])\s+|(?<=\n)\s*(?=\S)|(?:,\s*and\s+)|(?:;\s*)',
    )

    def __init__(self) -> None:
        self._matcher = StructuralPatternMatcher()
        self._prompt_builder = SemanticPromptBuilder()

    # ============================  public API  ============================

    def parse_guarantee(
        self,
        text: str,
        func_context: Optional[Dict[str, Any]] = None,
    ) -> List[ParsedClaim]:
        """Parse a ``@guarantee(...)`` string into claims."""
        if func_context is None:
            func_context = {}
        sentences = self._split_sentences(text)
        claims: List[ParsedClaim] = []
        for sent in sentences:
            claim = self._parse_single_claim(sent, func_context, source="guarantee")
            claims.append(claim)
        return claims

    def parse_spec(
        self,
        text: str,
        func_context: Optional[Dict[str, Any]] = None,
    ) -> List[ParsedClaim]:
        """Parse a general ``@spec(...)`` annotation."""
        if func_context is None:
            func_context = {}
        sentences = self._split_sentences(text)
        claims: List[ParsedClaim] = []
        for sent in sentences:
            claim = self._parse_single_claim(sent, func_context, source="spec")
            claims.append(claim)
        return claims

    def parse_assume(
        self,
        text: str,
        func_context: Optional[Dict[str, Any]] = None,
    ) -> ParsedClaim:
        """Parse an ``@assume(...)`` into exactly one claim."""
        if func_context is None:
            func_context = {}
        claim = self._parse_single_claim(text, func_context, source="assume")
        claim.kind = NLClaimKind.ASSUMPTION
        return claim

    def parse_check(
        self,
        text: str,
        func_context: Optional[Dict[str, Any]] = None,
    ) -> ParsedClaim:
        """Parse a ``@check(...)`` into exactly one claim."""
        if func_context is None:
            func_context = {}
        return self._parse_single_claim(text, func_context, source="check")

    def parse_given(self, text: str) -> List[ParsedClaim]:
        """
        Parse regulatory / paper axioms supplied via ``@given(...)``.
        These are always treated as assumptions.
        """
        sentences = self._split_sentences(text)
        claims: List[ParsedClaim] = []
        for sent in sentences:
            claim = self._parse_single_claim(sent, {}, source="given")
            claim.kind = NLClaimKind.ASSUMPTION
            claims.append(claim)
        return claims

    def parse_docstring(
        self,
        text: str,
        func_context: Optional[Dict[str, Any]] = None,
    ) -> List[ParsedClaim]:
        """
        Extract verifiable claims from a Python docstring.

        Heuristic: lines in a docstring that look like assertions
        (contain "must", "should", "shall", "always", "never", etc.)
        are treated as guarantee-like claims.
        """
        if func_context is None:
            func_context = {}
        claim_lines = self._extract_docstring_claims(text)
        claims: List[ParsedClaim] = []
        for line in claim_lines:
            claim = self._parse_single_claim(line, func_context, source="docstring")
            claims.append(claim)
        return claims

    # ============================  bulk helpers  ==========================

    def parse_multi(
        self,
        texts: List[str],
        func_context: Optional[Dict[str, Any]] = None,
    ) -> List[ParsedClaim]:
        """Convenience: parse many strings, concatenating all claims."""
        results: List[ParsedClaim] = []
        for t in texts:
            results.extend(self.parse_spec(t, func_context))
        return results

    def classify_claim(self, text: str) -> NLClaimKind:
        """Return the best-guess ``NLClaimKind`` for *text*."""
        lower = text.lower()

        if self._is_complexity(lower):
            return NLClaimKind.COMPLEXITY

        if self._is_structural(lower):
            return self._structural_subkind(lower)

        if self._is_semantic(lower):
            return self._semantic_subkind(lower)

        return NLClaimKind.REFERENCE

    # ============================  internals  =============================

    def _parse_single_claim(
        self,
        text: str,
        func_context: Dict[str, Any],
        source: str = "",
    ) -> ParsedClaim:
        text = text.strip()
        if not text:
            return ParsedClaim(
                text="",
                kind=NLClaimKind.REFERENCE,
                decidable=False,
                confidence=0.0,
            )

        kind = self.classify_claim(text)
        variables = self._extract_variables(text, func_context)

        # Attempt structural matching
        match_result = self._matcher.match(text)
        if match_result is not None:
            pattern_name, bindings = match_result
            var_name = self._guess_primary_variable(text, func_context)
            formula = self._matcher.build_formula(pattern_name, bindings, var_name)
            pat_kind = self._matcher.get_kind(pattern_name)
            if pat_kind is not None:
                kind = pat_kind
            return ParsedClaim(
                text=text,
                kind=kind,
                decidable=True,
                structural_formula=formula,
                semantic_prompt=None,
                variables=variables,
                confidence=self._compute_confidence(text, True),
                source_location=source or None,
            )

        # Semantic claim
        prompt = self._prompt_builder.build_judge_prompt(text, func_context)
        return ParsedClaim(
            text=text,
            kind=kind,
            decidable=False,
            structural_formula=None,
            semantic_prompt=prompt,
            variables=variables,
            confidence=self._compute_confidence(text, False),
            source_location=source or None,
        )

    # ---- sentence splitting ----
    def _split_sentences(self, text: str) -> List[str]:
        text = text.strip()
        if not text:
            return []
        raw = self.SENTENCE_SPLIT_RE.split(text)
        sentences = [s.strip() for s in raw if s and s.strip()]
        if not sentences:
            return [text]
        return sentences

    # ---- docstring extraction ----
    _ASSERTION_WORDS: re.Pattern[str] = re.compile(
        r"\b(?:must|should|shall|always|never|ensures?|guarantees?|requires?|invariant)\b",
        re.IGNORECASE,
    )

    def _extract_docstring_claims(self, docstring: str) -> List[str]:
        lines: List[str] = []
        for raw_line in docstring.splitlines():
            line = raw_line.strip().lstrip("-*•")
            if not line:
                continue
            if self._ASSERTION_WORDS.search(line):
                lines.append(line)
        return lines

    # ---- classification helpers ----
    def _is_structural(self, lower: str) -> bool:
        for kw in self.STRUCTURAL_KEYWORDS:
            if kw in lower:
                return True
        return self._matcher.match(lower) is not None

    def _is_semantic(self, lower: str) -> bool:
        for kw in self.SEMANTIC_KEYWORDS:
            if kw in lower:
                return True
        return False

    def _is_complexity(self, lower: str) -> bool:
        for kw in self.COMPLEXITY_KEYWORDS:
            if kw.lower() in lower:
                return True
        return False

    def _structural_subkind(self, lower: str) -> NLClaimKind:
        bound_words = {"at least", "at most", "exactly", "positive", "negative",
                       "non-negative", "range", "between", "length", "size",
                       "count", "empty", "non-empty"}
        type_words = {"type", "instance", "isinstance"}
        relation_words = {"subset", "superset", "contains", "equal", "greater",
                          "less", "same length", "same size"}

        for w in bound_words:
            if w in lower:
                return NLClaimKind.STRUCTURAL_BOUND
        for w in type_words:
            if w in lower:
                return NLClaimKind.STRUCTURAL_TYPE
        for w in relation_words:
            if w in lower:
                return NLClaimKind.STRUCTURAL_RELATION
        return NLClaimKind.STRUCTURAL_INVARIANT

    def _semantic_subkind(self, lower: str) -> NLClaimKind:
        safety_words = {"safe", "safety", "harmless", "secure", "ethical", "fair"}
        quality_words = {"quality", "well-written", "readable", "clean", "elegant",
                         "novel", "creative"}
        correctness_words = {"correct", "correctly", "accurate", "accurately",
                             "grounded", "complete", "comprehensive"}

        for w in safety_words:
            if w in lower:
                return NLClaimKind.SEMANTIC_SAFETY
        for w in quality_words:
            if w in lower:
                return NLClaimKind.SEMANTIC_QUALITY
        for w in correctness_words:
            if w in lower:
                return NLClaimKind.SEMANTIC_CORRECTNESS
        return NLClaimKind.SEMANTIC_BEHAVIOR

    # ---- variable extraction ----
    _IDENTIFIER_RE: re.Pattern[str] = re.compile(r"\b([a-zA-Z_]\w*)\b")

    _STOP_WORDS: frozenset[str] = frozenset({
        "the", "a", "an", "is", "are", "was", "were", "be", "been",
        "being", "have", "has", "had", "do", "does", "did", "will",
        "would", "shall", "should", "may", "might", "can", "could",
        "must", "need", "and", "or", "but", "if", "then", "else",
        "when", "while", "for", "in", "on", "at", "to", "from",
        "with", "by", "of", "not", "no", "all", "each", "every",
        "any", "some", "this", "that", "it", "its", "than",
        "returns", "return", "output", "input", "value", "result",
        "true", "false", "none", "null", "type", "instance",
        "sorted", "empty", "unique", "positive", "negative",
        "length", "size", "count", "between", "range", "least",
        "most", "exactly", "greater", "less", "equal", "contains",
        "subset", "superset", "same",
    })

    def _extract_variables(
        self,
        text: str,
        func_context: Dict[str, Any],
    ) -> Dict[str, str]:
        variables: Dict[str, str] = {}
        context_vars: Dict[str, str] = func_context.get("variables", {})
        param_names: List[str] = func_context.get("params", [])

        # Direct mentions of known parameter names
        for pname in param_names:
            if pname in text:
                ptype = context_vars.get(pname, "Any")
                variables[pname] = ptype

        # Also scan for identifiers that match context variables
        for match in self._IDENTIFIER_RE.finditer(text):
            ident = match.group(1)
            if ident in context_vars and ident not in self._STOP_WORDS:
                variables[ident] = context_vars[ident]

        return variables

    def _guess_primary_variable(
        self,
        text: str,
        func_context: Dict[str, Any],
    ) -> str:
        """
        Heuristic: pick the first identifier in *text* that appears in
        the function context, falling back to ``'result'``.
        """
        context_vars: Dict[str, str] = func_context.get("variables", {})
        param_names: List[str] = func_context.get("params", [])
        known = set(context_vars) | set(param_names)

        for match in self._IDENTIFIER_RE.finditer(text):
            ident = match.group(1)
            if ident in known:
                return ident

        if "return" in text.lower() or "output" in text.lower():
            return "result"

        return "x"

    # ---- confidence ----
    def _compute_confidence(self, text: str, decidable: bool) -> float:
        """
        Heuristic confidence score for a parse result.

        Structural claims matched by a pattern get high confidence;
        semantic claims get lower confidence because the oracle is
        inherently less reliable.
        """
        base = 0.9 if decidable else 0.6

        # Penalise very short or very long texts
        words = text.split()
        n_words = len(words)
        if n_words < 3:
            base *= 0.8
        elif n_words > 50:
            base *= 0.85

        # Hedge words reduce confidence
        hedge_words = {"maybe", "possibly", "probably", "might", "could",
                       "sometimes", "usually", "often", "approximately"}
        for w in words:
            if w.lower() in hedge_words:
                base *= 0.9
                break

        return round(min(base, 1.0), 4)

    # ============================  utilities  =============================

    def get_structural_matcher(self) -> StructuralPatternMatcher:
        return self._matcher

    def get_prompt_builder(self) -> SemanticPromptBuilder:
        return self._prompt_builder

    def summary(self, claims: List[ParsedClaim]) -> Dict[str, Any]:
        """Quick summary statistics for a list of claims."""
        n_decidable = sum(1 for c in claims if c.decidable)
        n_semantic = sum(1 for c in claims if not c.decidable)
        kinds: Dict[str, int] = {}
        for c in claims:
            k = c.kind.name
            kinds[k] = kinds.get(k, 0) + 1
        return {
            "total": len(claims),
            "decidable": n_decidable,
            "semantic": n_semantic,
            "by_kind": kinds,
            "avg_confidence": (
                round(sum(c.confidence for c in claims) / len(claims), 4)
                if claims else 0.0
            ),
        }

    def partition(
        self,
        claims: List[ParsedClaim],
    ) -> Tuple[List[ParsedClaim], List[ParsedClaim]]:
        """Split claims into (structural, semantic) buckets."""
        structural: List[ParsedClaim] = []
        semantic: List[ParsedClaim] = []
        for c in claims:
            if c.decidable:
                structural.append(c)
            else:
                semantic.append(c)
        return structural, semantic

    def to_json_list(self, claims: List[ParsedClaim]) -> List[Dict[str, Any]]:
        return [c.to_dict() for c in claims]

    # ---- pretty printing ----
    def format_claim(self, claim: ParsedClaim) -> str:
        tag = "DEC" if claim.decidable else "SEM"
        return f"[{tag}:{claim.kind.name}] {claim.text}  (conf={claim.confidence})"

    def format_claims(self, claims: List[ParsedClaim]) -> str:
        lines = [self.format_claim(c) for c in claims]
        return "\n".join(lines)


# ===================================================================
# Module-level convenience
# ===================================================================

_DEFAULT_PARSER: Optional[NLSpecParser] = None


def get_parser() -> NLSpecParser:
    global _DEFAULT_PARSER
    if _DEFAULT_PARSER is None:
        _DEFAULT_PARSER = NLSpecParser()
    return _DEFAULT_PARSER


def parse_guarantee(text: str, func_context: Optional[Dict[str, Any]] = None) -> List[ParsedClaim]:
    return get_parser().parse_guarantee(text, func_context or {})


def parse_spec(text: str, func_context: Optional[Dict[str, Any]] = None) -> List[ParsedClaim]:
    return get_parser().parse_spec(text, func_context or {})


def parse_assume(text: str, func_context: Optional[Dict[str, Any]] = None) -> ParsedClaim:
    return get_parser().parse_assume(text, func_context or {})


def parse_check(text: str, func_context: Optional[Dict[str, Any]] = None) -> ParsedClaim:
    return get_parser().parse_check(text, func_context or {})


def parse_given(text: str) -> List[ParsedClaim]:
    return get_parser().parse_given(text)


def parse_docstring(text: str, func_context: Optional[Dict[str, Any]] = None) -> List[ParsedClaim]:
    return get_parser().parse_docstring(text, func_context or {})
