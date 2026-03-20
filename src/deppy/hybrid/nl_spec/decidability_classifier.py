"""
Classify predicates into the decidability stratification:

    Dec  — decidable, Z3-checkable structural properties
    Oracle — semantic, requires LLM oracle judgment

Provides ``DecidabilityClassifier`` for the top-level routing and
``Z3Encoder`` for best-effort encoding of NL into Z3 Python expressions.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# DecidabilityResult
# ---------------------------------------------------------------------------


# --- Integration with existing deppy codebase ---
try:
    from deppy.solver import ObligationClassifier as _CoreClassifier, FragmentDispatcher
    from deppy.solver.z3_encoder import Z3Encoder as _CoreZ3Encoder
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

@dataclass
class DecidabilityResult:
    """Outcome of classifying a single NL predicate."""

    original: str
    decidable_part: Optional[str] = None
    semantic_part: Optional[str] = None
    split_confidence: float = 1.0
    reasoning: str = ""
    fully_decidable: bool = False

    # -- convenience --

    @property
    def has_decidable(self) -> bool:
        return self.decidable_part is not None

    @property
    def has_semantic(self) -> bool:
        return self.semantic_part is not None

    @property
    def is_mixed(self) -> bool:
        return self.has_decidable and self.has_semantic

    def to_dict(self) -> Dict[str, Any]:
        return {
            "original": self.original,
            "decidable_part": self.decidable_part,
            "semantic_part": self.semantic_part,
            "split_confidence": self.split_confidence,
            "reasoning": self.reasoning,
            "fully_decidable": self.fully_decidable,
        }


# ---------------------------------------------------------------------------
# Z3Encoder  (~400 lines)
# ---------------------------------------------------------------------------

class Z3Encoder(_CoreZ3Encoder if _HAS_DEPPY_CORE else object):
    """
    Best-effort encoder that attempts to translate a natural-language claim
    into a Z3-solver Python expression string.

    Extends the core ``Z3Encoder`` when available, adding NL-to-Z3
    pattern matching and quantifier support.

    Returns ``None`` when the claim cannot be encoded.
    """

    # -- comparison patterns --
    _CMP_PATTERNS: List[Tuple[re.Pattern[str], str]] = [
        (re.compile(r"\b(\w+)\s+(?:is\s+)?greater\s+than\s+(\w+)\b", re.I), "{v0} > {v1}"),
        (re.compile(r"\b(\w+)\s+(?:is\s+)?less\s+than\s+(\w+)\b", re.I), "{v0} < {v1}"),
        (re.compile(r"\b(\w+)\s+(?:is\s+)?(?:>=|greater\s+than\s+or\s+equal(?:\s+to)?)\s+(\w+)\b", re.I), "{v0} >= {v1}"),
        (re.compile(r"\b(\w+)\s+(?:is\s+)?(?:<=|less\s+than\s+or\s+equal(?:\s+to)?)\s+(\w+)\b", re.I), "{v0} <= {v1}"),
        (re.compile(r"\b(\w+)\s+(?:is\s+)?(?:==|equals?(?:\s+to)?)\s+(\w+)\b", re.I), "{v0} == {v1}"),
        (re.compile(r"\b(\w+)\s+(?:is\s+)?(?:!=|not\s+equal(?:\s+to)?)\s+(\w+)\b", re.I), "{v0} != {v1}"),
        (re.compile(r"\b(\w+)\s*>\s*(\d+)\b"), "{v0} > {v1}"),
        (re.compile(r"\b(\w+)\s*<\s*(\d+)\b"), "{v0} < {v1}"),
        (re.compile(r"\b(\w+)\s*>=\s*(\d+)\b"), "{v0} >= {v1}"),
        (re.compile(r"\b(\w+)\s*<=\s*(\d+)\b"), "{v0} <= {v1}"),
        (re.compile(r"\b(\w+)\s*==\s*(\d+)\b"), "{v0} == {v1}"),
        (re.compile(r"\b(\w+)\s*!=\s*(\d+)\b"), "{v0} != {v1}"),
    ]

    # -- quantifier patterns --
    _QUANT_PATTERNS: List[Tuple[re.Pattern[str], str]] = [
        (
            re.compile(
                r"\b(?:for\s+)?all\s+(?:elements?\s+)?(?:of\s+)?(\w+)\s*,?\s*(\w+)\s+(?:is\s+)?(positive|negative|non-negative|non-positive|zero)\b",
                re.I,
            ),
            "ForAll([_i], Implies(_i >= 0, {coll}[_i] {op} 0))",
        ),
        (
            re.compile(
                r"\b(?:for\s+)?all\s+(\w+)\s+in\s+(\w+)\s*,?\s*(\w+)\s*(>|<|>=|<=|==|!=)\s*(\d+)\b",
                re.I,
            ),
            "ForAll([{elem}], Implies(IsMember({elem}, {coll}), {elem} {op} {val}))",
        ),
        (
            re.compile(
                r"\bevery\s+element\s+(?:of\s+)?(\w+)\s+(?:is\s+)?(positive|negative|non-negative|non-positive|zero)\b",
                re.I,
            ),
            "ForAll([_i], Implies(_i >= 0, {coll}[_i] {op} 0))",
        ),
    ]

    # -- collection patterns --
    _COLL_PATTERNS: List[Tuple[re.Pattern[str], str]] = [
        (re.compile(r"\b(\w+)\s+is\s+(?:a\s+)?subset\s+of\s+(\w+)\b", re.I), "IsSubset({v0}, {v1})"),
        (re.compile(r"\b(\w+)\s+is\s+(?:a\s+)?superset\s+of\s+(\w+)\b", re.I), "IsSubset({v1}, {v0})"),
        (re.compile(r"\b(\w+)\s+contains?\s+(\w+)\b", re.I), "IsMember({v1}, {v0})"),
        (re.compile(r"\b(\w+)\s+is\s+(?:in|member\s+of)\s+(\w+)\b", re.I), "IsMember({v0}, {v1})"),
        (re.compile(r"\bunion\s+of\s+(\w+)\s+and\s+(\w+)\b", re.I), "SetUnion({v0}, {v1})"),
        (re.compile(r"\bintersection\s+of\s+(\w+)\s+and\s+(\w+)\b", re.I), "SetIntersect({v0}, {v1})"),
        (re.compile(r"\b(\w+)\s+(?:is\s+)?disjoint\s+(?:from|with)\s+(\w+)\b", re.I),
         "SetIntersect({v0}, {v1}) == EmptySet(IntSort())"),
    ]

    # -- arithmetic patterns --
    _ARITH_PATTERNS: List[Tuple[re.Pattern[str], str]] = [
        (re.compile(r"\b(\w+)\s*\+\s*(\w+)\s*(?:==|equals?)\s*(\w+)\b", re.I), "{v0} + {v1} == {v2}"),
        (re.compile(r"\b(\w+)\s*-\s*(\w+)\s*(?:==|equals?)\s*(\w+)\b", re.I), "{v0} - {v1} == {v2}"),
        (re.compile(r"\b(\w+)\s*\*\s*(\w+)\s*(?:==|equals?)\s*(\w+)\b", re.I), "{v0} * {v1} == {v2}"),
        (re.compile(r"\bsum\s+of\s+(\w+)\s+(?:is|equals?)\s+(\w+)\b", re.I), "Sum({v0}) == {v1}"),
        (re.compile(r"\bproduct\s+of\s+(\w+)\s+(?:is|equals?)\s+(\w+)\b", re.I), "Product({v0}) == {v1}"),
        (re.compile(r"\b(\w+)\s+(?:is\s+)?divisible\s+by\s+(\w+)\b", re.I), "{v0} % {v1} == 0"),
        (re.compile(r"\b(\w+)\s+modulo\s+(\w+)\s+(?:is|equals?)\s+(\w+)\b", re.I), "{v0} % {v1} == {v2}"),
        (re.compile(r"\b(\w+)\s+(?:is\s+)?even\b", re.I), "{v0} % 2 == 0"),
        (re.compile(r"\b(\w+)\s+(?:is\s+)?odd\b", re.I), "{v0} % 2 == 1"),
        (re.compile(r"\babsolute\s+(?:value\s+)?(?:of\s+)?(\w+)\s*(?:==|equals?|is)\s*(\w+)\b", re.I),
         "If({v0} >= 0, {v0}, -{v0}) == {v1}"),
        (re.compile(r"\bmax(?:imum)?\s+of\s+(\w+)\s+(?:is|equals?)\s+(\w+)\b", re.I),
         "Max({v0}) == {v1}"),
        (re.compile(r"\bmin(?:imum)?\s+of\s+(\w+)\s+(?:is|equals?)\s+(\w+)\b", re.I),
         "Min({v0}) == {v1}"),
    ]

    # -- simple keyword → formula templates (catch-all) --
    _KEYWORD_TEMPLATES: List[Tuple[str, str]] = [
        ("sorted", "IsSorted({var})"),
        ("ascending", "IsSorted({var})"),
        ("descending", "IsSortedDesc({var})"),
        ("non-empty", "Length({var}) > 0"),
        ("not empty", "Length({var}) > 0"),
        ("unique", "Distinct({var})"),
        ("no duplicates", "Distinct({var})"),
        ("palindrome", "{var} == Reverse({var})"),
        ("not none", "{var} != None"),
        ("not null", "{var} != None"),
        ("positive", "{var} > 0"),
        ("negative", "{var} < 0"),
        ("non-negative", "{var} >= 0"),
        ("non-positive", "{var} <= 0"),
        ("zero", "{var} == 0"),
        ("empty", "Length({var}) == 0"),
        ("boolean", "Or({var} == True, {var} == False)"),
    ]

    # ---------------------------------------------------------------- encode
    def encode(self, claim: str, variables: Optional[Dict[str, str]] = None) -> Optional[str]:
        """
        Top-level entry: try every strategy and return the first
        successful encoding, or ``None``.
        """
        if variables is None:
            variables = {}

        result = self.encode_comparison(claim, variables)
        if result is not None:
            return result

        result = self.encode_quantifier(claim, variables)
        if result is not None:
            return result

        result = self.encode_collection(claim, variables)
        if result is not None:
            return result

        result = self.encode_arithmetic(claim, variables)
        if result is not None:
            return result

        result = self._encode_keyword(claim, variables)
        if result is not None:
            return result

        result = self._encode_bound_pattern(claim, variables)
        if result is not None:
            return result

        result = self._encode_range_pattern(claim, variables)
        if result is not None:
            return result

        return None

    # ---- comparison ----
    def encode_comparison(self, text: str, vars: Optional[Dict[str, str]] = None) -> Optional[str]:
        if vars is None:
            vars = {}
        for pat, template in self._CMP_PATTERNS:
            m = pat.search(text)
            if m:
                groups = m.groups()
                result = template
                for idx, g in enumerate(groups):
                    result = result.replace(f"{{v{idx}}}", g)
                return self._resolve_vars(result, vars)
        return None

    # ---- quantifier ----
    def encode_quantifier(self, text: str, vars: Optional[Dict[str, str]] = None) -> Optional[str]:
        if vars is None:
            vars = {}
        lower = text.lower()

        # "for all elements of X, ... positive/negative/..."
        for pat, template in self._QUANT_PATTERNS:
            m = pat.search(text)
            if m:
                groups = m.groups()
                result = template
                if len(groups) >= 2:
                    sign_word = groups[-1].lower() if len(groups) >= 3 else ""
                    op = self._sign_word_to_op(sign_word)
                    coll = groups[0] if len(groups) == 2 else groups[1]
                    result = result.replace("{coll}", coll)
                    result = result.replace("{op}", op)
                    if len(groups) >= 4:
                        result = result.replace("{elem}", groups[0])
                        result = result.replace("{val}", groups[-1])
                    elif len(groups) >= 3 and groups[0] != coll:
                        result = result.replace("{elem}", groups[0])
                return self._resolve_vars(result, vars)

        # "there exists" style
        m_exists = re.search(
            r"\bthere\s+exists?\s+(\w+)\s+in\s+(\w+)\s+(?:such\s+that|where)\s+(.+)",
            lower,
        )
        if m_exists:
            elem, coll, body = m_exists.group(1), m_exists.group(2), m_exists.group(3)
            body_enc = self.encode(body.strip(), vars)
            if body_enc is not None:
                return f"Exists([{elem}], And(IsMember({elem}, {coll}), {body_enc}))"

        return None

    # ---- collection ----
    def encode_collection(self, text: str, vars: Optional[Dict[str, str]] = None) -> Optional[str]:
        if vars is None:
            vars = {}
        for pat, template in self._COLL_PATTERNS:
            m = pat.search(text)
            if m:
                groups = m.groups()
                result = template
                for idx, g in enumerate(groups):
                    result = result.replace(f"{{v{idx}}}", g)
                return self._resolve_vars(result, vars)

        # "length of X is/equals N"
        m_len = re.search(r"\blength\s+of\s+(\w+)\s+(?:is|equals?|==)\s+(\d+)\b", text, re.I)
        if m_len:
            return f"Length({m_len.group(1)}) == {m_len.group(2)}"

        # "X has N elements"
        m_has = re.search(r"\b(\w+)\s+has\s+(\d+)\s+elements?\b", text, re.I)
        if m_has:
            return f"Length({m_has.group(1)}) == {m_has.group(2)}"

        return None

    # ---- arithmetic ----
    def encode_arithmetic(self, text: str, vars: Optional[Dict[str, str]] = None) -> Optional[str]:
        if vars is None:
            vars = {}
        for pat, template in self._ARITH_PATTERNS:
            m = pat.search(text)
            if m:
                groups = m.groups()
                result = template
                for idx, g in enumerate(groups):
                    result = result.replace(f"{{v{idx}}}", g)
                return self._resolve_vars(result, vars)
        return None

    # ---- keyword fallback ----
    def _encode_keyword(self, text: str, vars: Dict[str, str]) -> Optional[str]:
        lower = text.lower()
        var = self._guess_var(text, vars)
        for keyword, template in self._KEYWORD_TEMPLATES:
            if keyword in lower:
                return template.replace("{var}", var)
        return None

    # ---- bound pattern ----
    def _encode_bound_pattern(self, text: str, vars: Dict[str, str]) -> Optional[str]:
        m = re.search(r"\b(?:at\s+least|>=?|no\s+fewer\s+than)\s+(\d+)\b", text, re.I)
        if m:
            var = self._guess_var(text, vars)
            return f"{var} >= {m.group(1)}"

        m = re.search(r"\b(?:at\s+most|<=?|no\s+more\s+than)\s+(\d+)\b", text, re.I)
        if m:
            var = self._guess_var(text, vars)
            return f"{var} <= {m.group(1)}"

        m = re.search(r"\b(?:exactly|==)\s+(\d+)\b", text, re.I)
        if m:
            var = self._guess_var(text, vars)
            return f"{var} == {m.group(1)}"

        return None

    # ---- range pattern ----
    def _encode_range_pattern(self, text: str, vars: Dict[str, str]) -> Optional[str]:
        m = re.search(r"\bin\s+(?:the\s+)?range\s*[\[(]\s*(-?\d+)\s*,\s*(-?\d+)\s*[\])]", text, re.I)
        if m:
            var = self._guess_var(text, vars)
            return f"And({var} >= {m.group(1)}, {var} <= {m.group(2)})"

        m = re.search(r"\bbetween\s+(-?\d+)\s+and\s+(-?\d+)\b", text, re.I)
        if m:
            var = self._guess_var(text, vars)
            return f"And({var} >= {m.group(1)}, {var} <= {m.group(2)})"

        return None

    # ---- helpers ----
    @staticmethod
    def _sign_word_to_op(word: str) -> str:
        mapping = {
            "positive": ">",
            "negative": "<",
            "non-negative": ">=",
            "non-positive": "<=",
            "zero": "==",
        }
        return mapping.get(word.lower().strip(), ">")

    @staticmethod
    def _guess_var(text: str, vars: Dict[str, str]) -> str:
        _stop = {
            "the", "a", "an", "is", "are", "all", "each", "every",
            "for", "in", "of", "to", "at", "by", "and", "or", "not",
            "has", "have", "must", "should", "shall", "be", "been",
            "with", "from", "than", "no", "it", "its", "this", "that",
        }
        for word in re.findall(r"\b(\w+)\b", text):
            if word.lower() in vars:
                return word
        for word in re.findall(r"\b([a-zA-Z_]\w*)\b", text):
            if word.lower() not in _stop and not word[0].isupper():
                return word
        return "x"

    @staticmethod
    def _resolve_vars(formula: str, vars: Dict[str, str]) -> str:
        """Annotate known variable types as Z3 sort comments."""
        for vname, vtype in vars.items():
            if vname in formula:
                formula = formula.replace(vname, f"{vname} /*{vtype}*/", 1)
                break
        return formula


# ---------------------------------------------------------------------------
# DecidabilityClassifier  (~500 lines)
# ---------------------------------------------------------------------------

class DecidabilityClassifier:
    """
    Four-step classifier:
        1. Pattern-match against known structural patterns
        2. Scan for semantic indicator words
        3. Attempt Z3 encoding
        4. Anything remaining → semantic
    """

    # -- Semantic indicator words (≥ 20) --
    SEMANTIC_INDICATORS: List[str] = [
        "correct", "correctly", "accurate", "accurately",
        "appropriate", "appropriately", "novel", "creative",
        "well-written", "grounded", "relevant", "helpful",
        "safe", "fair", "ethical", "meaningful",
        "complete", "comprehensive", "reasonable", "sensible",
        "elegant", "idiomatic", "maintainable", "readable",
        "intuitive", "user-friendly", "coherent", "consistent",
        "insightful", "informative",
    ]

    # -- Structural indicator words --
    STRUCTURAL_INDICATORS: List[str] = [
        "sorted", "ascending", "descending", "length", "size",
        "count", "empty", "non-empty", "positive", "negative",
        "non-negative", "unique", "distinct", "range", "between",
        "at least", "at most", "exactly", "greater", "less",
        "equal", "contains", "subset", "superset", "type",
        "instance", "divisible", "even", "odd", "palindrome",
        "returns", "not none", "not null",
    ]

    # -- Split conjunctions --
    _CONJ_RE = re.compile(
        r"\b(?:and\s+also|and\s+additionally|,\s*and\b|;\s*also\b|;\s*and\b)\s*",
        re.I,
    )
    _SIMPLE_AND = re.compile(r"\band\b", re.I)

    def __init__(self) -> None:
        self._encoder = Z3Encoder()
        self._semantic_re = re.compile(
            r"\b(?:" + "|".join(re.escape(w) for w in self.SEMANTIC_INDICATORS) + r")\b",
            re.I,
        )
        self._structural_re = re.compile(
            r"\b(?:" + "|".join(re.escape(w) for w in self.STRUCTURAL_INDICATORS) + r")\b",
            re.I,
        )

    # ========================= public API =================================

    def classify(self, text: str, context: Optional[Dict[str, Any]] = None) -> DecidabilityResult:
        """
        Master classify method.

        Returns a ``DecidabilityResult`` that may split the input into
        a decidable part and a semantic part.
        """
        if context is None:
            context = {}
        text = text.strip()
        if not text:
            return DecidabilityResult(
                original=text,
                fully_decidable=False,
                reasoning="empty input",
            )

        variables = context.get("variables", {})

        # Step 1: pure structural?
        structural_score = self._structural_score(text)
        semantic_score = self._semantic_score(text)

        if structural_score > 0 and semantic_score == 0:
            enc = self._encoder.encode(text, variables)
            if enc is not None:
                return DecidabilityResult(
                    original=text,
                    decidable_part=enc,
                    semantic_part=None,
                    split_confidence=0.95,
                    reasoning="Pure structural claim; Z3-encodable.",
                    fully_decidable=True,
                )
            return DecidabilityResult(
                original=text,
                decidable_part=text,
                semantic_part=None,
                split_confidence=0.80,
                reasoning="Structural indicators present but Z3 encoding failed; "
                          "falling back to runtime assertion.",
                fully_decidable=True,
            )

        # Step 2: pure semantic?
        if semantic_score > 0 and structural_score == 0:
            approx = self.decidable_approximation(text)
            return DecidabilityResult(
                original=text,
                decidable_part=approx,
                semantic_part=text,
                split_confidence=0.70 if approx else 0.85,
                reasoning="Pure semantic claim requiring oracle judgment."
                          + (" A weak decidable approximation was found." if approx else ""),
                fully_decidable=False,
            )

        # Step 3: mixed — try to split
        if structural_score > 0 and semantic_score > 0:
            return self._split_mixed(text, variables)

        # Step 4: neither score fired — attempt Z3 encoding as last resort
        enc = self._encoder.encode(text, variables)
        if enc is not None:
            return DecidabilityResult(
                original=text,
                decidable_part=enc,
                semantic_part=None,
                split_confidence=0.75,
                reasoning="No strong indicators but Z3 encoding succeeded.",
                fully_decidable=True,
            )

        return DecidabilityResult(
            original=text,
            decidable_part=None,
            semantic_part=text,
            split_confidence=0.60,
            reasoning="No structural patterns matched; treating as semantic.",
            fully_decidable=False,
        )

    def is_decidable(self, text: str) -> bool:
        """Quick boolean check."""
        result = self.classify(text)
        return result.fully_decidable

    def decidable_approximation(self, semantic_text: str) -> Optional[str]:
        """
        Attempt to weaken a semantic claim into something decidable.

        Examples:
            "correctly sorts"     → "output is sorted"
            "efficiently computes"→ "terminates within N steps"
            "accurately summarizes"→"output length ≤ input length"
        """
        lower = semantic_text.lower()

        for original, approx in self._APPROXIMATION_TABLE:
            if original in lower:
                return approx

        # Generic weakening: if the text mentions a collection/variable, at
        # least assert non-None.
        m = re.search(r"\b([a-zA-Z_]\w+)\b", semantic_text)
        if m:
            return f"{m.group(1)} is not None"

        return None

    # ---- batch helpers ----
    def classify_many(
        self,
        texts: List[str],
        context: Optional[Dict[str, Any]] = None,
    ) -> List[DecidabilityResult]:
        return [self.classify(t, context) for t in texts]

    def partition(
        self,
        texts: List[str],
        context: Optional[Dict[str, Any]] = None,
    ) -> Tuple[List[str], List[str]]:
        """Partition texts into (decidable, semantic) buckets."""
        dec: List[str] = []
        sem: List[str] = []
        for t in texts:
            r = self.classify(t, context)
            if r.fully_decidable:
                dec.append(t)
            else:
                sem.append(t)
        return dec, sem

    def summary(self, results: List[DecidabilityResult]) -> Dict[str, Any]:
        fully = sum(1 for r in results if r.fully_decidable)
        mixed = sum(1 for r in results if r.is_mixed)
        pure_sem = sum(1 for r in results if not r.has_decidable and r.has_semantic)
        return {
            "total": len(results),
            "fully_decidable": fully,
            "mixed": mixed,
            "purely_semantic": pure_sem,
            "avg_confidence": (
                round(sum(r.split_confidence for r in results) / len(results), 4)
                if results else 0.0
            ),
        }

    # ========================= internals ==================================

    # -- Approximation table --
    _APPROXIMATION_TABLE: List[Tuple[str, str]] = [
        ("correctly sorts", "output is sorted"),
        ("correctly sort", "output is sorted"),
        ("accurately sorts", "output is sorted"),
        ("sorts correctly", "output is sorted"),
        ("efficient", "terminates within N steps"),
        ("efficiently computes", "terminates within N steps"),
        ("efficiently calculates", "terminates within N steps"),
        ("runs efficiently", "terminates within N steps"),
        ("fast", "terminates within N steps"),
        ("optimal", "terminates within N steps"),
        ("accurately summarizes", "output length <= input length"),
        ("accurately summarise", "output length <= input length"),
        ("good summary", "output length <= input length"),
        ("correct summary", "output length <= input length"),
        ("well-formatted", "output is not None"),
        ("well formatted", "output is not None"),
        ("human-readable", "output is not None"),
        ("readable output", "output is not None"),
        ("meaningful", "output is not None"),
        ("appropriate", "output is not None"),
        ("relevant", "output is not None"),
        ("helpful", "output is not None"),
        ("creative", "output is not None"),
        ("novel", "output is not None"),
        ("coherent", "output is not None"),
        ("grammatically correct", "len(output) > 0"),
        ("no hallucination", "output is not None"),
        ("grounded", "output is not None"),
        ("safe", "output is not None"),
        ("ethical", "output is not None"),
        ("fair", "output is not None"),
    ]

    # -- scoring --
    def _structural_score(self, text: str) -> int:
        return len(self._structural_re.findall(text))

    def _semantic_score(self, text: str) -> int:
        return len(self._semantic_re.findall(text))

    # -- mixed splitting --
    def _split_mixed(
        self,
        text: str,
        variables: Dict[str, str],
    ) -> DecidabilityResult:
        """
        When a claim has both structural and semantic indicators,
        try to decompose it into two parts.
        """
        clauses = self._split_clauses(text)
        if len(clauses) < 2:
            enc = self._encoder.encode(text, variables)
            approx = self.decidable_approximation(text)
            return DecidabilityResult(
                original=text,
                decidable_part=enc or approx,
                semantic_part=text,
                split_confidence=0.55,
                reasoning="Mixed claim could not be split into sub-clauses.",
                fully_decidable=False,
            )

        dec_parts: List[str] = []
        sem_parts: List[str] = []
        for clause in clauses:
            clause = clause.strip()
            if not clause:
                continue
            if self._structural_score(clause) > 0 and self._semantic_score(clause) == 0:
                enc = self._encoder.encode(clause, variables)
                dec_parts.append(enc if enc else clause)
            elif self._semantic_score(clause) > 0:
                sem_parts.append(clause)
            else:
                enc = self._encoder.encode(clause, variables)
                if enc is not None:
                    dec_parts.append(enc)
                else:
                    sem_parts.append(clause)

        return DecidabilityResult(
            original=text,
            decidable_part=" AND ".join(dec_parts) if dec_parts else None,
            semantic_part=" AND ".join(sem_parts) if sem_parts else None,
            split_confidence=0.70,
            reasoning=f"Split into {len(dec_parts)} decidable + {len(sem_parts)} semantic clause(s).",
            fully_decidable=len(sem_parts) == 0,
        )

    def _split_clauses(self, text: str) -> List[str]:
        """Split a compound NL sentence into atomic clauses."""
        parts = self._CONJ_RE.split(text)
        if len(parts) > 1:
            return [p.strip() for p in parts if p.strip()]

        parts = self._SIMPLE_AND.split(text)
        if len(parts) > 1:
            return [p.strip() for p in parts if p.strip()]

        parts = text.split(";")
        if len(parts) > 1:
            return [p.strip() for p in parts if p.strip()]

        parts = text.split(",")
        if len(parts) > 1:
            return [p.strip() for p in parts if p.strip()]

        return [text]

    # ---- get encoder ----
    def get_encoder(self) -> Z3Encoder:
        return self._encoder


# ---------------------------------------------------------------------------
# Module-level convenience
# ---------------------------------------------------------------------------

_DEFAULT_CLASSIFIER: Optional[DecidabilityClassifier] = None


def get_classifier() -> DecidabilityClassifier:
    global _DEFAULT_CLASSIFIER
    if _DEFAULT_CLASSIFIER is None:
        _DEFAULT_CLASSIFIER = DecidabilityClassifier()
    return _DEFAULT_CLASSIFIER


def classify(text: str, context: Optional[Dict[str, Any]] = None) -> DecidabilityResult:
    return get_classifier().classify(text, context)


def is_decidable(text: str) -> bool:
    return get_classifier().is_decidable(text)


def decidable_approximation(semantic_text: str) -> Optional[str]:
    return get_classifier().decidable_approximation(semantic_text)


# ===================================================================
# FeatureExtractor — additional NLP features for decidability
# ===================================================================

class FeatureExtractor:
    """
    Extract lightweight NLP features from an NL claim that help
    the ``DecidabilityClassifier`` make better decisions.

    No ML dependencies — purely regex / heuristic.
    """

    # -- POS-like tags (very rough, keyword-based) --
    _NOUN_INDICATORS = re.compile(
        r"\b(?:list|array|set|dict|map|string|number|integer|float|"
        r"value|result|output|input|collection|sequence|matrix|"
        r"vector|tuple|pair|element|item|key|index|length|size|"
        r"count|sum|product|mean|median|mode|max|min|"
        r"table|row|column|field|record|"
        r"graph|node|edge|vertex|path|tree|"
        r"function|method|class|object|variable|parameter|argument)\b",
        re.I,
    )

    _VERB_INDICATORS = re.compile(
        r"\b(?:return|compute|calculate|sort|filter|map|reduce|"
        r"transform|convert|validate|check|verify|ensure|"
        r"contain|include|exclude|produce|generate|create|"
        r"append|insert|remove|delete|update|modify|"
        r"increase|decrease|double|triple|halve|"
        r"satisfy|violate|hold|maintain|preserve)\b",
        re.I,
    )

    _QUANTIFIER_INDICATORS = re.compile(
        r"\b(?:all|every|each|any|some|no|none|"
        r"at least|at most|exactly|for all|there exists)\b",
        re.I,
    )

    _NEGATION_INDICATORS = re.compile(
        r"\b(?:not|no|never|neither|nor|without|"
        r"cannot|can't|won't|doesn't|isn't|aren't)\b",
        re.I,
    )

    _HEDGE_INDICATORS = re.compile(
        r"\b(?:maybe|possibly|probably|might|could|"
        r"sometimes|usually|often|typically|generally|"
        r"approximately|roughly|about|around|nearly)\b",
        re.I,
    )

    _COMPARATIVE_INDICATORS = re.compile(
        r"\b(?:greater|less|more|fewer|larger|smaller|"
        r"higher|lower|better|worse|longer|shorter|"
        r"faster|slower|bigger|deeper|wider|thinner)\b",
        re.I,
    )

    _TEMPORAL_INDICATORS = re.compile(
        r"\b(?:before|after|during|while|until|since|"
        r"first|last|next|previous|always|never|"
        r"eventually|finally|initially|subsequently)\b",
        re.I,
    )

    def extract(self, text: str) -> Dict[str, Any]:
        """Return a feature dict for the given NL text."""
        return {
            "word_count": len(text.split()),
            "char_count": len(text),
            "sentence_count": len(re.split(r'[.!?]+', text.strip())),
            "noun_count": len(self._NOUN_INDICATORS.findall(text)),
            "verb_count": len(self._VERB_INDICATORS.findall(text)),
            "has_quantifier": bool(self._QUANTIFIER_INDICATORS.search(text)),
            "has_negation": bool(self._NEGATION_INDICATORS.search(text)),
            "has_hedge": bool(self._HEDGE_INDICATORS.search(text)),
            "has_comparative": bool(self._COMPARATIVE_INDICATORS.search(text)),
            "has_temporal": bool(self._TEMPORAL_INDICATORS.search(text)),
            "has_number": bool(re.search(r"\b\d+\b", text)),
            "has_math_symbol": bool(re.search(r"[+\-*/=<>≤≥≠∀∃∈⊆∪∩]", text)),
            "noun_to_verb_ratio": self._safe_ratio(
                len(self._NOUN_INDICATORS.findall(text)),
                len(self._VERB_INDICATORS.findall(text)),
            ),
            "structural_keyword_density": self._keyword_density(
                text,
                DecidabilityClassifier.STRUCTURAL_INDICATORS,
            ),
            "semantic_keyword_density": self._keyword_density(
                text,
                DecidabilityClassifier.SEMANTIC_INDICATORS,
            ),
        }

    def decidability_score(self, text: str) -> float:
        """
        Return a [0, 1] heuristic score where 1 = certainly decidable,
        0 = certainly semantic.
        """
        feats = self.extract(text)
        score = 0.5

        score += feats["structural_keyword_density"] * 0.3
        score -= feats["semantic_keyword_density"] * 0.3

        if feats["has_number"]:
            score += 0.05
        if feats["has_math_symbol"]:
            score += 0.1
        if feats["has_quantifier"]:
            score += 0.05
        if feats["has_hedge"]:
            score -= 0.15
        if feats["has_comparative"]:
            score += 0.05

        return max(0.0, min(1.0, score))

    # ---- helpers ----

    @staticmethod
    def _safe_ratio(a: int, b: int) -> float:
        if b == 0:
            return float(a) if a > 0 else 0.0
        return round(a / b, 4)

    @staticmethod
    def _keyword_density(text: str, keywords: List[str]) -> float:
        words = text.lower().split()
        if not words:
            return 0.0
        lower_text = text.lower()
        hits = sum(1 for kw in keywords if kw in lower_text)
        return round(hits / len(words), 4)


# ===================================================================
# DecidabilityReport — detailed analysis for debugging
# ===================================================================

@dataclass
class DecidabilityReport:
    """Extended report combining classification with feature analysis."""

    result: DecidabilityResult
    features: Dict[str, Any] = field(default_factory=dict)
    decidability_score: float = 0.5
    structural_matches: List[str] = field(default_factory=list)
    semantic_matches: List[str] = field(default_factory=list)
    approximation: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "result": self.result.to_dict(),
            "features": self.features,
            "decidability_score": self.decidability_score,
            "structural_matches": self.structural_matches,
            "semantic_matches": self.semantic_matches,
            "approximation": self.approximation,
        }

    def summary_line(self) -> str:
        tag = "DEC" if self.result.fully_decidable else "SEM"
        return (
            f"[{tag} score={self.decidability_score:.2f}] "
            f"{self.result.original[:80]}"
        )


def full_analysis(
    text: str,
    context: Optional[Dict[str, Any]] = None,
) -> DecidabilityReport:
    """
    Run the classifier AND the feature extractor to produce a
    comprehensive ``DecidabilityReport``.
    """
    classifier = get_classifier()
    extractor = FeatureExtractor()

    result = classifier.classify(text, context)
    features = extractor.extract(text)
    score = extractor.decidability_score(text)

    structural_re = classifier._structural_re
    semantic_re = classifier._semantic_re

    structural_matches = structural_re.findall(text)
    semantic_matches = semantic_re.findall(text)

    approx = classifier.decidable_approximation(text) if not result.fully_decidable else None

    return DecidabilityReport(
        result=result,
        features=features,
        decidability_score=score,
        structural_matches=structural_matches,
        semantic_matches=semantic_matches,
        approximation=approx,
    )


def batch_analysis(
    texts: List[str],
    context: Optional[Dict[str, Any]] = None,
) -> List[DecidabilityReport]:
    """Run ``full_analysis`` on many texts."""
    return [full_analysis(t, context) for t in texts]


def format_report(report: DecidabilityReport) -> str:
    """Pretty-print a ``DecidabilityReport``."""
    lines: List[str] = []
    lines.append(report.summary_line())
    lines.append(f"  Reasoning: {report.result.reasoning}")
    if report.result.decidable_part:
        lines.append(f"  Decidable: {report.result.decidable_part}")
    if report.result.semantic_part:
        lines.append(f"  Semantic:  {report.result.semantic_part}")
    if report.approximation:
        lines.append(f"  Approx:    {report.approximation}")
    lines.append(f"  Features:  {report.features}")
    return "\n".join(lines)
