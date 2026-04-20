"""Automatic specification generator — infers specs from code, tests, and docstrings.

Implements the "Auto-interface extraction" construction from the monograph's
Scalable Verification chapter (§ 7.3).  Instead of requiring manual
``@guarantee`` / ``assume`` / ``check`` annotations, the system can *infer*
specifications from four complementary sources:

1. **Type annotations** — mypy-style, including ``Annotated[int, Gt(0)]``
2. **Docstrings** — NumPy, Google, Sphinx, and free-form styles
3. **Test assertions** — ``assert`` statements and ``pytest.raises`` blocks
4. **Code patterns** — guard clauses, accumulators, sort-then-return, etc.

Usage
-----
>>> gen = AutoSpecGenerator()
>>> specs = gen.generate_specs(open("mymodule.py").read(),
...                            open("test_mymodule.py").read())
>>> for name, fspec in specs.items():
...     print(name, fspec.inferred)

The inferred specs are ranked by *confidence* (1.0 = certain, 0.0 = guess)
and can be promoted to first-class ``@guarantee`` annotations by the
verification pipeline.
"""
from __future__ import annotations

import ast
import re
import textwrap
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Sequence

# ═══════════════════════════════════════════════════════════════════
# InferredSpec — the atomic unit produced by every inferrer
# ═══════════════════════════════════════════════════════════════════

class InferredSpecKind(Enum):
    """Classification of inferred specifications."""
    PRECONDITION = auto()
    POSTCONDITION = auto()
    INVARIANT = auto()
    TYPE_CONSTRAINT = auto()
    EXCEPTION = auto()


@dataclass
class InferredSpec:
    """A specification inferred from code analysis.

    Attributes
    ----------
    kind : str
        One of ``"precondition"``, ``"postcondition"``, ``"invariant"``,
        ``"type_constraint"``, ``"exception"``.
    description : str
        Human-readable natural-language description.
    formal : str | None
        Formal predicate expression when available (e.g. ``"x > 0"``).
    source : str
        Short tag indicating *where* the spec was inferred from, such as
        ``"type_annotation"``, ``"docstring"``, ``"test"``, ``"pattern"``.
    confidence : float
        Confidence in ``[0.0, 1.0]``.  ``1.0`` means "certain" (e.g.
        explicit type annotation); ``0.5`` means heuristic inference.
    """
    kind: str
    description: str
    formal: str | None = None
    source: str = ""
    confidence: float = 1.0

    def __repr__(self) -> str:
        conf = f" ({self.confidence:.0%})" if self.confidence < 1.0 else ""
        return f"InferredSpec({self.kind}: {self.description!r}{conf})"


# ═══════════════════════════════════════════════════════════════════
# FunctionAutoSpec — aggregated specs for one function
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FunctionAutoSpec:
    """Complete auto-inferred specification for a single function."""
    name: str
    inferred: list[InferredSpec] = field(default_factory=list)

    # Convenience accessors ------------------------------------------------
    @property
    def preconditions(self) -> list[InferredSpec]:
        return [s for s in self.inferred if s.kind == "precondition"]

    @property
    def postconditions(self) -> list[InferredSpec]:
        return [s for s in self.inferred if s.kind == "postcondition"]

    @property
    def type_constraints(self) -> list[InferredSpec]:
        return [s for s in self.inferred if s.kind == "type_constraint"]

    @property
    def invariants(self) -> list[InferredSpec]:
        return [s for s in self.inferred if s.kind == "invariant"]

    @property
    def exceptions(self) -> list[InferredSpec]:
        return [s for s in self.inferred if s.kind == "exception"]


# ═══════════════════════════════════════════════════════════════════
# 1. Type-Based Spec Inference
# ═══════════════════════════════════════════════════════════════════

# Map from AST annotation text to a human-readable description.
_SIMPLE_TYPE_NAMES: dict[str, str] = {
    "int": "int", "float": "float", "str": "str", "bool": "bool",
    "bytes": "bytes", "None": "None", "NoneType": "None",
}


class TypeSpecInferrer:
    """Infer specifications from type annotations.

    Examples
    --------
    - ``def f(x: int) -> int``  →  ``"input x is int, output is int"``
    - ``def f(x: list[int]) -> list[int]``  →  ``"preserves element type"``
    - ``def f(x: int) -> Optional[int]``  →  ``"may return None"``
    - ``def f(x: Annotated[int, Gt(0)]) -> int``  →  ``"x > 0"``
    """

    def infer_from_annotations(self, func: ast.FunctionDef) -> list[InferredSpec]:
        """Return inferred specs from *func*'s type annotations."""
        specs: list[InferredSpec] = []
        specs.extend(self._infer_param_types(func))
        specs.extend(self._infer_return_type(func))
        specs.extend(self._infer_annotated_constraints(func))
        specs.extend(self._infer_optional_return(func))
        return specs

    # -- helpers -----------------------------------------------------------

    def _infer_param_types(self, func: ast.FunctionDef) -> list[InferredSpec]:
        results: list[InferredSpec] = []
        for arg in func.args.args:
            if arg.annotation is not None:
                type_str = self._annotation_to_str(arg.annotation)
                results.append(InferredSpec(
                    kind="type_constraint",
                    description=f"parameter {arg.arg} is {type_str}",
                    formal=f"isinstance({arg.arg}, {type_str})",
                    source="type_annotation",
                    confidence=1.0,
                ))
        return results

    def _infer_return_type(self, func: ast.FunctionDef) -> list[InferredSpec]:
        if func.returns is None:
            return []
        type_str = self._annotation_to_str(func.returns)
        return [InferredSpec(
            kind="postcondition",
            description=f"returns {type_str}",
            formal=f"isinstance(__result__, {type_str})",
            source="type_annotation",
            confidence=1.0,
        )]

    def _infer_optional_return(self, func: ast.FunctionDef) -> list[InferredSpec]:
        """Detect ``Optional[T]`` or ``T | None`` return type."""
        if func.returns is None:
            return []
        text = self._annotation_to_str(func.returns)
        if "Optional" in text or "None" in text.split(" | "):
            return [InferredSpec(
                kind="postcondition",
                description="may return None",
                source="type_annotation",
                confidence=1.0,
            )]
        return []

    def _infer_annotated_constraints(self, func: ast.FunctionDef) -> list[InferredSpec]:
        """Detect ``Annotated[int, Gt(0)]``-style constraints."""
        results: list[InferredSpec] = []
        for arg in func.args.args:
            ann = arg.annotation
            if ann is None:
                continue
            constraints = self._extract_annotated_meta(ann)
            for c in constraints:
                results.append(InferredSpec(
                    kind="precondition",
                    description=f"{arg.arg} {c}",
                    formal=f"{arg.arg} {c}",
                    source="type_annotation",
                    confidence=1.0,
                ))
        return results

    def _extract_annotated_meta(self, node: ast.expr) -> list[str]:
        """Pull constraint strings out of ``Annotated[base, Meta(...)]``."""
        if not isinstance(node, ast.Subscript):
            return []
        if not (isinstance(node.value, ast.Name) and node.value.id == "Annotated"):
            return []
        slc = node.slice
        elts: list[ast.expr] = []
        if isinstance(slc, ast.Tuple):
            elts = slc.elts[1:]  # skip the base type
        else:
            return []
        constraints: list[str] = []
        for elt in elts:
            constraints.append(self._meta_to_constraint(elt))
        return [c for c in constraints if c]

    @staticmethod
    def _meta_to_constraint(node: ast.expr) -> str:
        """Convert ``Gt(0)`` → ``"> 0"``, ``Ge(1)`` → ``">= 1"``, etc."""
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            name = node.func.id
            if node.args and isinstance(node.args[0], ast.Constant):
                val = node.args[0].value
                ops = {"Gt": ">", "Ge": ">=", "Lt": "<", "Le": "<=",
                       "Eq": "==", "Ne": "!="}
                if name in ops:
                    return f"{ops[name]} {val}"
                if name == "MultipleOf":
                    return f"% {val} == 0"
        return ast.dump(node) if not isinstance(node, ast.Constant) else ""

    @staticmethod
    def _annotation_to_str(node: ast.expr) -> str:
        """Best-effort stringification of an annotation AST node."""
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return node.value
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Subscript):
            base = TypeSpecInferrer._annotation_to_str(node.value)
            slc = TypeSpecInferrer._annotation_to_str(node.slice)
            return f"{base}[{slc}]"
        if isinstance(node, ast.Attribute):
            return f"{TypeSpecInferrer._annotation_to_str(node.value)}.{node.attr}"
        if isinstance(node, ast.Tuple):
            parts = ", ".join(TypeSpecInferrer._annotation_to_str(e) for e in node.elts)
            return parts
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            l = TypeSpecInferrer._annotation_to_str(node.left)
            r = TypeSpecInferrer._annotation_to_str(node.right)
            return f"{l} | {r}"
        if isinstance(node, ast.List):
            parts = ", ".join(TypeSpecInferrer._annotation_to_str(e) for e in node.elts)
            return f"[{parts}]"
        return "object"


# ═══════════════════════════════════════════════════════════════════
# 2. Docstring Spec Extraction
# ═══════════════════════════════════════════════════════════════════

# Constraint-bearing phrases we look for in prose
_CONSTRAINT_PATTERNS: list[tuple[re.Pattern[str], str]] = [
    (re.compile(r"\bnon[- ]?negative\b", re.I), ">= 0"),
    (re.compile(r"\bpositive\b", re.I), "> 0"),
    (re.compile(r"\bnon[- ]?zero\b", re.I), "!= 0"),
    (re.compile(r"\bnon[- ]?empty\b", re.I), "len > 0"),
    (re.compile(r"\bsorted\b", re.I), "sorted"),
    (re.compile(r"\bunique\b", re.I), "unique elements"),
    (re.compile(r"\bnever\s+None\b", re.I), "is not None"),
    (re.compile(r"\bnot\s+None\b", re.I), "is not None"),
    (re.compile(r"\balways\s+positive\b", re.I), "> 0"),
    (re.compile(r"\bimmutable\b", re.I), "immutable"),
    (re.compile(r"\bmonotonic\b", re.I), "monotonic"),
    (re.compile(r"\bidempotent\b", re.I), "idempotent"),
    (re.compile(r"\bnormalized\b", re.I), "normalized"),
]


class DocstringSpecExtractor:
    """Extract specifications from docstrings.

    Supports NumPy-style, Google-style, Sphinx-style, and free-form
    docstrings.  See ``_parse_numpy_style``, ``_parse_google_style``,
    and ``_parse_sphinx_style`` for section-header recognition.
    """

    def extract_from_docstring(
        self, docstring: str, *, func_name: str = ""
    ) -> list[InferredSpec]:
        """Return all specs extractable from *docstring*."""
        if not docstring:
            return []
        specs: list[InferredSpec] = []
        specs.extend(self._parse_numpy_style(docstring, func_name=func_name))
        specs.extend(self._parse_google_style(docstring, func_name=func_name))
        specs.extend(self._parse_sphinx_style(docstring, func_name=func_name))
        specs.extend(self._extract_freeform_constraints(docstring, func_name=func_name))
        return _deduplicate_specs(specs)

    # -- NumPy-style -------------------------------------------------------

    def _parse_numpy_style(
        self, docstring: str, *, func_name: str = ""
    ) -> list[InferredSpec]:
        specs: list[InferredSpec] = []
        sections = self._split_numpy_sections(docstring)

        for param_text in sections.get("parameters", []):
            specs.extend(self._specs_from_param_block(param_text, func_name))

        for ret_text in sections.get("returns", []):
            specs.extend(self._specs_from_return_block(ret_text, func_name))

        for raise_text in sections.get("raises", []):
            specs.extend(self._specs_from_raises_block(raise_text, func_name))

        return specs

    @staticmethod
    def _split_numpy_sections(docstring: str) -> dict[str, list[str]]:
        """Split a NumPy-style docstring into labelled sections."""
        sections: dict[str, list[str]] = {}
        header_re = re.compile(r"^(\w[\w ]*)\s*\n\s*-{3,}", re.M)
        matches = list(header_re.finditer(docstring))
        for i, m in enumerate(matches):
            key = m.group(1).strip().lower()
            start = m.end()
            end = matches[i + 1].start() if i + 1 < len(matches) else len(docstring)
            body = docstring[start:end].strip()
            sections.setdefault(key, []).append(body)
        return sections

    # -- Google-style ------------------------------------------------------

    def _parse_google_style(
        self, docstring: str, *, func_name: str = ""
    ) -> list[InferredSpec]:
        specs: list[InferredSpec] = []
        sections = self._split_google_sections(docstring)

        for param_text in sections.get("args", []):
            specs.extend(self._specs_from_param_block(param_text, func_name))

        for ret_text in sections.get("returns", []):
            specs.extend(self._specs_from_return_block(ret_text, func_name))

        for raise_text in sections.get("raises", []):
            specs.extend(self._specs_from_raises_block(raise_text, func_name))

        return specs

    @staticmethod
    def _split_google_sections(docstring: str) -> dict[str, list[str]]:
        """Split a Google-style docstring into labelled sections."""
        sections: dict[str, list[str]] = {}
        header_re = re.compile(r"^(\w[\w ]*)\s*:\s*$", re.M)
        matches = list(header_re.finditer(docstring))
        for i, m in enumerate(matches):
            key = m.group(1).strip().lower()
            start = m.end()
            end = matches[i + 1].start() if i + 1 < len(matches) else len(docstring)
            body = docstring[start:end].strip()
            sections.setdefault(key, []).append(body)
        return sections

    # -- Sphinx-style ------------------------------------------------------

    def _parse_sphinx_style(
        self, docstring: str, *, func_name: str = ""
    ) -> list[InferredSpec]:
        specs: list[InferredSpec] = []
        param_re = re.compile(r":param\s+(\w+)\s*:\s*(.+)")
        for m in param_re.finditer(docstring):
            pname, desc = m.group(1), m.group(2).strip()
            constraints = self._extract_constraints(desc)
            for c in constraints:
                specs.append(InferredSpec(
                    kind="precondition",
                    description=f"{pname} {c}",
                    source="docstring",
                    confidence=0.8,
                ))
            if not constraints:
                specs.append(InferredSpec(
                    kind="type_constraint",
                    description=f"{pname}: {desc}",
                    source="docstring",
                    confidence=0.7,
                ))
        ret_re = re.compile(r":returns?\s*:\s*(.+)")
        for m in ret_re.finditer(docstring):
            desc = m.group(1).strip()
            constraints = self._extract_constraints(desc)
            for c in constraints:
                specs.append(InferredSpec(
                    kind="postcondition",
                    description=f"returns value that is {c}",
                    source="docstring",
                    confidence=0.8,
                ))
            if not constraints:
                specs.append(InferredSpec(
                    kind="postcondition",
                    description=desc,
                    source="docstring",
                    confidence=0.7,
                ))
        raises_re = re.compile(r":raises?\s+(\w+)\s*:\s*(.+)")
        for m in raises_re.finditer(docstring):
            exc, desc = m.group(1), m.group(2).strip()
            specs.append(InferredSpec(
                kind="exception",
                description=f"raises {exc} when {desc}",
                source="docstring",
                confidence=0.9,
            ))
        return specs

    # -- Free-form ---------------------------------------------------------

    def _extract_freeform_constraints(
        self, docstring: str, *, func_name: str = ""
    ) -> list[InferredSpec]:
        """Look for constraint-bearing phrases anywhere in the docstring."""
        specs: list[InferredSpec] = []
        for pat, tag in _CONSTRAINT_PATTERNS:
            if pat.search(docstring):
                specs.append(InferredSpec(
                    kind="postcondition",
                    description=f"result is {tag}",
                    source="docstring",
                    confidence=0.6,
                ))
        return specs

    # -- shared helpers ----------------------------------------------------

    def _specs_from_param_block(
        self, block: str, func_name: str
    ) -> list[InferredSpec]:
        """Turn a parameter description block into specs."""
        specs: list[InferredSpec] = []
        param_re = re.compile(r"^(\w+)\s*(?::.*?)?\n?\s*(.+)", re.M)
        for m in param_re.finditer(block):
            pname = m.group(1)
            desc = m.group(2).strip()
            constraints = self._extract_constraints(desc)
            for c in constraints:
                specs.append(InferredSpec(
                    kind="precondition",
                    description=f"{pname} {c}",
                    source="docstring",
                    confidence=0.8,
                ))
        return specs

    def _specs_from_return_block(
        self, block: str, func_name: str
    ) -> list[InferredSpec]:
        specs: list[InferredSpec] = []
        constraints = self._extract_constraints(block)
        for c in constraints:
            specs.append(InferredSpec(
                kind="postcondition",
                description=f"return value is {c}",
                source="docstring",
                confidence=0.8,
            ))
        if not constraints and block.strip():
            specs.append(InferredSpec(
                kind="postcondition",
                description=block.strip().split("\n")[0],
                source="docstring",
                confidence=0.6,
            ))
        return specs

    def _specs_from_raises_block(
        self, block: str, func_name: str
    ) -> list[InferredSpec]:
        specs: list[InferredSpec] = []
        exc_re = re.compile(r"^(\w+Error|\w+Exception)\b", re.M)
        for m in exc_re.finditer(block):
            specs.append(InferredSpec(
                kind="exception",
                description=f"may raise {m.group(1)}",
                source="docstring",
                confidence=0.9,
            ))
        return specs

    @staticmethod
    def _extract_constraints(text: str) -> list[str]:
        """Extract constraint phrases from prose text.

        Looks for language like 'non-negative', 'sorted', 'unique',
        'never None', 'always positive', etc.
        """
        found: list[str] = []
        for pat, tag in _CONSTRAINT_PATTERNS:
            if pat.search(text):
                found.append(tag)
        return found


# ═══════════════════════════════════════════════════════════════════
# 3. Test-Derived Specs
# ═══════════════════════════════════════════════════════════════════

class TestSpecExtractor:
    """Extract specifications from test assertions.

    Examples
    --------
    - ``assert f(3) == 9``                     → point spec ``"f(3) = 9"``
    - ``assert len(f(xs)) == len(xs)``         → ``"preserves length"``
    - ``assert all(x >= 0 for x in f(xs))``    → ``"all elements non-negative"``
    - ``assert isinstance(f(x), int)``         → ``"returns int"``
    - ``with pytest.raises(ValueError): …``    → ``"raises ValueError"``
    """

    def extract_from_test(self, test_func: ast.FunctionDef) -> list[InferredSpec]:
        """Walk *test_func* and turn assertions into specs."""
        specs: list[InferredSpec] = []
        for node in ast.walk(test_func):
            if isinstance(node, ast.Assert):
                s = self._analyze_assert(node)
                if s is not None:
                    specs.append(s)
            if isinstance(node, ast.With):
                s = self._analyze_pytest_raises(node)
                if s is not None:
                    specs.append(s)
        return specs

    def extract_from_test_source(self, source: str) -> list[InferredSpec]:
        """Parse a test source file and extract specs from all test functions."""
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return []
        specs: list[InferredSpec] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name.startswith("test_"):
                specs.extend(self.extract_from_test(node))
        return specs

    # -- assertion analysis ------------------------------------------------

    def _analyze_assert(self, node: ast.Assert) -> InferredSpec | None:
        """Convert a single ``assert`` statement into an ``InferredSpec``."""
        test = node.test
        if test is None:
            return None

        # assert f(x) == val  →  point spec
        if isinstance(test, ast.Compare) and len(test.ops) == 1:
            return self._analyze_comparison(test)

        # assert isinstance(expr, T)
        if isinstance(test, ast.Call):
            return self._analyze_assert_call(test)

        # assert all(pred for x in result)
        if isinstance(test, ast.Call):
            return self._analyze_all_any_call(test)

        return None

    def _analyze_comparison(self, cmp: ast.Compare) -> InferredSpec | None:
        """Handle ``assert a OP b`` patterns."""
        left = cmp.left
        op = cmp.ops[0]
        right = cmp.comparators[0]

        left_s = _ast_to_source(left)
        right_s = _ast_to_source(right)

        # assert len(f(xs)) == len(xs)  →  preserves length
        if (self._is_len_call(left) and self._is_len_call(right)
                and isinstance(op, ast.Eq)):
            return InferredSpec(
                kind="postcondition",
                description="preserves length",
                formal=f"len(result) == len(input)",
                source="test",
                confidence=0.85,
            )

        # assert f(args) == value  →  point spec
        if isinstance(left, ast.Call) and isinstance(op, ast.Eq):
            return InferredSpec(
                kind="postcondition",
                description=f"{left_s} == {right_s}",
                formal=f"{left_s} == {right_s}",
                source="test",
                confidence=0.9,
            )

        # assert result >= 0  →  non-negative
        if isinstance(op, ast.GtE) and self._is_zero(right):
            return InferredSpec(
                kind="postcondition",
                description=f"{left_s} is non-negative",
                formal=f"{left_s} >= 0",
                source="test",
                confidence=0.85,
            )

        # assert result > 0  →  positive
        if isinstance(op, ast.Gt) and self._is_zero(right):
            return InferredSpec(
                kind="postcondition",
                description=f"{left_s} is positive",
                formal=f"{left_s} > 0",
                source="test",
                confidence=0.85,
            )

        # Generic comparison fallback
        op_str = _op_to_str(op)
        if op_str:
            return InferredSpec(
                kind="postcondition",
                description=f"{left_s} {op_str} {right_s}",
                formal=f"{left_s} {op_str} {right_s}",
                source="test",
                confidence=0.7,
            )

        return None

    def _analyze_assert_call(self, call: ast.Call) -> InferredSpec | None:
        """Handle ``assert isinstance(x, T)`` and ``assert all(…)``."""
        func = call.func
        if isinstance(func, ast.Name):
            if func.id == "isinstance" and len(call.args) == 2:
                target = _ast_to_source(call.args[0])
                type_name = _ast_to_source(call.args[1])
                return InferredSpec(
                    kind="type_constraint",
                    description=f"{target} is {type_name}",
                    formal=f"isinstance({target}, {type_name})",
                    source="test",
                    confidence=0.9,
                )
            if func.id == "all" and len(call.args) == 1:
                return self._analyze_all_any_call(call)
        return None

    def _analyze_all_any_call(self, call: ast.Call) -> InferredSpec | None:
        """Handle ``assert all(pred for x in seq)``."""
        if not isinstance(call.func, ast.Name):
            return None
        if call.func.id not in ("all", "any"):
            return None
        if not call.args:
            return None
        gen = call.args[0]
        if isinstance(gen, ast.GeneratorExp):
            elt_source = _ast_to_source(gen.elt)
            quantifier = call.func.id
            return InferredSpec(
                kind="postcondition",
                description=f"{quantifier} elements satisfy: {elt_source}",
                formal=f"{quantifier}({elt_source})",
                source="test",
                confidence=0.8,
            )
        return None

    def _analyze_pytest_raises(self, with_node: ast.With) -> InferredSpec | None:
        """Handle ``with pytest.raises(ValueError): …``."""
        for item in with_node.items:
            ctx = item.context_expr
            if not isinstance(ctx, ast.Call):
                continue
            func = ctx.func
            # pytest.raises(SomeError)
            if isinstance(func, ast.Attribute) and func.attr == "raises":
                if ctx.args and isinstance(ctx.args[0], ast.Name):
                    exc_name = ctx.args[0].id
                    return InferredSpec(
                        kind="exception",
                        description=f"raises {exc_name}",
                        formal=f"raises({exc_name})",
                        source="test",
                        confidence=0.9,
                    )
        return None

    # -- helpers -----------------------------------------------------------

    @staticmethod
    def _is_len_call(node: ast.expr) -> bool:
        return (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "len")

    @staticmethod
    def _is_zero(node: ast.expr) -> bool:
        return isinstance(node, ast.Constant) and node.value == 0


# ═══════════════════════════════════════════════════════════════════
# 4. Pattern-Based Spec Inference
# ═══════════════════════════════════════════════════════════════════

class PatternSpecInferrer:
    """Infer specs from common code patterns.

    Patterns detected
    -----------------
    - Guard clause:  ``if x < 0: raise ValueError``  →  precondition x ≥ 0
    - Sort-then-return:  ``xs.sort(); return xs``  →  returns sorted
    - Accumulator loop:  ``total = 0; for …: total += …``  →  aggregation
    - Null check:  ``if x is None: return default``  →  handles None input
    - Validation:  ``if not isinstance(x, int): raise TypeError``  →  type constraint
    """

    def infer_from_body(self, func: ast.FunctionDef) -> list[InferredSpec]:
        specs: list[InferredSpec] = []
        specs.extend(self._detect_guard_clauses(func))
        specs.extend(self._detect_return_patterns(func))
        specs.extend(self._detect_loop_invariants(func))
        specs.extend(self._detect_isinstance_guards(func))
        specs.extend(self._detect_none_handling(func))
        return specs

    # -- guard clauses -----------------------------------------------------

    def _detect_guard_clauses(self, func: ast.FunctionDef) -> list[InferredSpec]:
        """Detect ``if cond: raise`` at the start of the body."""
        specs: list[InferredSpec] = []
        for stmt in func.body:
            if not isinstance(stmt, ast.If):
                # Skip docstrings and simple assignments at the top
                if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant):
                    continue
                break
            if self._body_is_raise(stmt.body):
                negated = self._negate_condition(stmt.test)
                if negated:
                    specs.append(InferredSpec(
                        kind="precondition",
                        description=f"requires {negated}",
                        formal=negated,
                        source="pattern",
                        confidence=0.75,
                    ))
                exc_name = self._get_raise_name(stmt.body)
                if exc_name:
                    cond_src = _ast_to_source(stmt.test)
                    specs.append(InferredSpec(
                        kind="exception",
                        description=f"raises {exc_name} when {cond_src}",
                        source="pattern",
                        confidence=0.85,
                    ))
        return specs

    # -- return patterns ---------------------------------------------------

    def _detect_return_patterns(self, func: ast.FunctionDef) -> list[InferredSpec]:
        """Detect sort-then-return, empty-return, etc."""
        specs: list[InferredSpec] = []
        stmts = func.body
        for i, stmt in enumerate(stmts):
            # pattern: something.sort() ; return something
            if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
                    and isinstance(stmt.value.func, ast.Attribute)
                    and stmt.value.func.attr == "sort"):
                if i + 1 < len(stmts) and isinstance(stmts[i + 1], ast.Return):
                    specs.append(InferredSpec(
                        kind="postcondition",
                        description="returns sorted",
                        source="pattern",
                        confidence=0.85,
                    ))
            # pattern: sorted(...)
            if isinstance(stmt, ast.Return) and stmt.value is not None:
                if (isinstance(stmt.value, ast.Call)
                        and isinstance(stmt.value.func, ast.Name)
                        and stmt.value.func.id == "sorted"):
                    specs.append(InferredSpec(
                        kind="postcondition",
                        description="returns sorted",
                        source="pattern",
                        confidence=0.9,
                    ))
            # pattern: return []  at end
            if (isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.List)
                    and len(stmt.value.elts) == 0 and i == len(stmts) - 1):
                specs.append(InferredSpec(
                    kind="postcondition",
                    description="may return empty list",
                    source="pattern",
                    confidence=0.6,
                ))
        return specs

    # -- loop invariants ---------------------------------------------------

    def _detect_loop_invariants(self, func: ast.FunctionDef) -> list[InferredSpec]:
        """Detect accumulator patterns (``total = 0; for …: total += …``)."""
        specs: list[InferredSpec] = []
        accumulators: set[str] = set()
        for stmt in func.body:
            if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
                tgt = stmt.targets[0]
                if isinstance(tgt, ast.Name) and isinstance(stmt.value, ast.Constant):
                    if stmt.value.value == 0:
                        accumulators.add(tgt.id)

        for stmt in func.body:
            if isinstance(stmt, ast.For):
                for inner in ast.walk(stmt):
                    if isinstance(inner, ast.AugAssign) and isinstance(inner.target, ast.Name):
                        if inner.target.id in accumulators:
                            specs.append(InferredSpec(
                                kind="invariant",
                                description=f"accumulates into {inner.target.id}",
                                source="pattern",
                                confidence=0.6,
                            ))
        return specs

    # -- isinstance guards -------------------------------------------------

    def _detect_isinstance_guards(self, func: ast.FunctionDef) -> list[InferredSpec]:
        """Detect ``if not isinstance(x, T): raise TypeError``."""
        specs: list[InferredSpec] = []
        for stmt in func.body:
            if not isinstance(stmt, ast.If):
                continue
            test = stmt.test
            # if not isinstance(x, T): raise TypeError
            if (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)
                    and isinstance(test.operand, ast.Call)):
                call = test.operand
                if (isinstance(call.func, ast.Name)
                        and call.func.id == "isinstance"
                        and len(call.args) == 2
                        and self._body_is_raise(stmt.body)):
                    pname = _ast_to_source(call.args[0])
                    tname = _ast_to_source(call.args[1])
                    specs.append(InferredSpec(
                        kind="precondition",
                        description=f"{pname} must be {tname}",
                        formal=f"isinstance({pname}, {tname})",
                        source="pattern",
                        confidence=0.85,
                    ))
        return specs

    # -- None handling -----------------------------------------------------

    def _detect_none_handling(self, func: ast.FunctionDef) -> list[InferredSpec]:
        """Detect ``if x is None: return default``."""
        specs: list[InferredSpec] = []
        for stmt in func.body:
            if not isinstance(stmt, ast.If):
                continue
            test = stmt.test
            if isinstance(test, ast.Compare) and len(test.ops) == 1:
                if isinstance(test.ops[0], ast.Is):
                    if (isinstance(test.comparators[0], ast.Constant)
                            and test.comparators[0].value is None):
                        varname = _ast_to_source(test.left)
                        specs.append(InferredSpec(
                            kind="precondition",
                            description=f"handles None input for {varname}",
                            source="pattern",
                            confidence=0.7,
                        ))
        return specs

    # -- helpers -----------------------------------------------------------

    @staticmethod
    def _body_is_raise(body: list[ast.stmt]) -> bool:
        return len(body) >= 1 and isinstance(body[0], ast.Raise)

    @staticmethod
    def _get_raise_name(body: list[ast.stmt]) -> str | None:
        if body and isinstance(body[0], ast.Raise) and body[0].exc is not None:
            exc = body[0].exc
            if isinstance(exc, ast.Call) and isinstance(exc.func, ast.Name):
                return exc.func.id
            if isinstance(exc, ast.Name):
                return exc.id
        return None

    @staticmethod
    def _negate_condition(node: ast.expr) -> str | None:
        """Best-effort negation of a guard condition.

        ``x < 0`` → ``x >= 0``
        ``x is None`` → ``x is not None``
        """
        if isinstance(node, ast.Compare) and len(node.ops) == 1:
            left = _ast_to_source(node.left)
            right = _ast_to_source(node.comparators[0])
            neg_ops = {
                ast.Lt: ">=", ast.LtE: ">", ast.Gt: "<=", ast.GtE: "<",
                ast.Eq: "!=", ast.NotEq: "==", ast.Is: "is not",
                ast.IsNot: "is",
            }
            op_type = type(node.ops[0])
            if op_type in neg_ops:
                return f"{left} {neg_ops[op_type]} {right}"
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return _ast_to_source(node.operand)
        return None


# ═══════════════════════════════════════════════════════════════════
# 5. Combined Spec Generator
# ═══════════════════════════════════════════════════════════════════

class AutoSpecGenerator:
    """Combine all inference sources to generate specifications.

    Priority order (highest → lowest):
    1. Explicit ``@guarantee`` / ``@requires`` / ``@ensures`` annotations
    2. Type annotations
    3. Docstring constraints
    4. Test-derived specs
    5. Code-pattern inference
    """

    def __init__(self) -> None:
        self._type_inferrer = TypeSpecInferrer()
        self._docstring_extractor = DocstringSpecExtractor()
        self._test_extractor = TestSpecExtractor()
        self._pattern_inferrer = PatternSpecInferrer()

    def generate_specs(
        self, source: str, test_source: str = ""
    ) -> dict[str, FunctionAutoSpec]:
        """Generate specs for every function in *source*.

        Parameters
        ----------
        source : str
            Python source code.
        test_source : str
            Optional pytest source whose assertions augment the specs.

        Returns
        -------
        dict[str, FunctionAutoSpec]
            Mapping from function name to its aggregated specification.
        """
        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return {}

        # Gather test functions
        test_funcs: list[ast.FunctionDef] = []
        if test_source:
            try:
                test_tree = ast.parse(textwrap.dedent(test_source))
                for node in ast.walk(test_tree):
                    if isinstance(node, ast.FunctionDef) and node.name.startswith("test_"):
                        test_funcs.append(node)
            except SyntaxError:
                pass

        results: dict[str, FunctionAutoSpec] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                related_tests = self._find_related_tests(node.name, test_funcs)
                fspec = self.generate_for_function(node, related_tests)
                results[node.name] = fspec
        return results

    def generate_for_function(
        self,
        func_ast: ast.FunctionDef,
        test_asts: list[ast.FunctionDef] | None = None,
    ) -> FunctionAutoSpec:
        """Generate a spec for a single function."""
        type_specs = self._type_inferrer.infer_from_annotations(func_ast)

        docstring = ast.get_docstring(func_ast) or ""
        doc_specs = self._docstring_extractor.extract_from_docstring(
            docstring, func_name=func_ast.name
        )

        test_specs: list[InferredSpec] = []
        for tf in (test_asts or []):
            test_specs.extend(self._test_extractor.extract_from_test(tf))

        pattern_specs = self._pattern_inferrer.infer_from_body(func_ast)

        merged = self.merge_specs(type_specs, doc_specs, test_specs, pattern_specs)
        return FunctionAutoSpec(name=func_ast.name, inferred=merged)

    def merge_specs(self, *spec_lists: list[InferredSpec]) -> list[InferredSpec]:
        """Merge and deduplicate specs from multiple sources.

        When two specs are duplicates (same kind + overlapping description),
        the one with higher confidence wins.
        """
        all_specs: list[InferredSpec] = []
        for sl in spec_lists:
            all_specs.extend(sl)
        return _deduplicate_specs(all_specs)

    @staticmethod
    def _find_related_tests(
        func_name: str, test_funcs: list[ast.FunctionDef]
    ) -> list[ast.FunctionDef]:
        """Heuristic: a test is "related" if it contains a call to *func_name*."""
        related: list[ast.FunctionDef] = []
        for tf in test_funcs:
            src = _ast_to_source(tf)
            if func_name in src:
                related.append(tf)
        return related


# ═══════════════════════════════════════════════════════════════════
# Utility helpers
# ═══════════════════════════════════════════════════════════════════

def _ast_to_source(node: ast.AST) -> str:
    """Best-effort unparse of an AST node back to source text."""
    try:
        return ast.unparse(node)
    except Exception:
        return ast.dump(node)


def _op_to_str(op: ast.cmpop) -> str | None:
    """Convert an AST comparison op to its string representation."""
    _map = {
        ast.Eq: "==", ast.NotEq: "!=",
        ast.Lt: "<", ast.LtE: "<=",
        ast.Gt: ">", ast.GtE: ">=",
        ast.Is: "is", ast.IsNot: "is not",
        ast.In: "in", ast.NotIn: "not in",
    }
    return _map.get(type(op))


def _deduplicate_specs(specs: list[InferredSpec]) -> list[InferredSpec]:
    """Remove duplicate specs, keeping the highest-confidence version."""
    seen: dict[tuple[str, str], InferredSpec] = {}
    for s in specs:
        key = (s.kind, s.description)
        existing = seen.get(key)
        if existing is None or s.confidence > existing.confidence:
            seen[key] = s
    # Stable order: type_constraint → precondition → postcondition → invariant → exception
    kind_order = {
        "type_constraint": 0, "precondition": 1, "postcondition": 2,
        "invariant": 3, "exception": 4,
    }
    return sorted(seen.values(), key=lambda s: (kind_order.get(s.kind, 9), -s.confidence))


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Run built-in smoke tests to validate the auto-spec machinery."""
    import sys

    passed = 0
    failed = 0

    def check(label: str, condition: bool) -> None:
        nonlocal passed, failed
        if condition:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {label}")

    # ── 1. TypeSpecInferrer ────────────────────────────────────────
    print("TypeSpecInferrer …")
    src = textwrap.dedent("""\
        from typing import Annotated, Optional
        class Gt:
            def __init__(self, v): ...
        def add(x: int, y: int) -> int: ...
        def maybe(x: int) -> Optional[int]: ...
        def constrained(x: Annotated[int, Gt(0)]) -> int: ...
    """)
    tree = ast.parse(src)
    inferrer = TypeSpecInferrer()
    funcs = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    func_map = {f.name: f for f in funcs}

    add_specs = inferrer.infer_from_annotations(func_map["add"])
    check("add: has param specs", any("parameter x" in s.description for s in add_specs))
    check("add: return spec", any("returns int" in s.description for s in add_specs))

    maybe_specs = inferrer.infer_from_annotations(func_map["maybe"])
    check("maybe: optional return", any("may return None" in s.description for s in maybe_specs))

    const_specs = inferrer.infer_from_annotations(func_map["constrained"])
    check("constrained: Gt(0)", any("> 0" in s.description for s in const_specs))

    # ── 2. DocstringSpecExtractor ──────────────────────────────────
    print("DocstringSpecExtractor …")
    ext = DocstringSpecExtractor()

    numpy_doc = textwrap.dedent("""\
        Sorts the input and removes duplicates.

        Parameters
        ----------
        xs : list[int]
            A non-empty list of integers.

        Returns
        -------
        list[int]
            A sorted list with unique elements.

        Raises
        ------
        ValueError
            If xs is empty.
    """)
    nspecs = ext.extract_from_docstring(numpy_doc)
    check("numpy: non-empty param", any("non-empty" in s.description or "len > 0" in s.description for s in nspecs))
    check("numpy: sorted return", any("sorted" in s.description for s in nspecs))
    check("numpy: unique return", any("unique" in s.description for s in nspecs))
    check("numpy: raises ValueError", any("ValueError" in s.description for s in nspecs))

    sphinx_doc = ":param x: A non-negative integer.\n:returns: A sorted list.\n:raises ValueError: If x is bad."
    sspecs = ext.extract_from_docstring(sphinx_doc)
    check("sphinx: non-negative param", any(">= 0" in s.description for s in sspecs))
    check("sphinx: sorted return", any("sorted" in s.description for s in sspecs))
    check("sphinx: raises ValueError", any("ValueError" in s.description for s in sspecs))

    google_doc = textwrap.dedent("""\
        Sort and filter.

        Args:
            xs: A non-empty list.

        Returns:
            A sorted result.

        Raises:
            ValueError: If xs is empty.
    """)
    gspecs = ext.extract_from_docstring(google_doc)
    check("google: has specs", len(gspecs) > 0)
    check("google: sorted return", any("sorted" in s.description for s in gspecs))

    # ── 3. TestSpecExtractor ──────────────────────────────────────
    print("TestSpecExtractor …")
    test_src = textwrap.dedent("""\
        import pytest

        def test_square():
            assert square(3) == 9
            assert square(0) == 0

        def test_lengths():
            xs = [1, 2, 3]
            assert len(process(xs)) == len(xs)

        def test_non_negative():
            assert all(x >= 0 for x in compute([1, -2, 3]))

        def test_type():
            assert isinstance(get_value(), int)

        def test_raises():
            with pytest.raises(ValueError):
                do_bad_thing(-1)
    """)
    te = TestSpecExtractor()
    tspecs = te.extract_from_test_source(test_src)
    check("test: point spec square(3)==9", any("square(3) == 9" in s.description for s in tspecs))
    check("test: preserves length", any("preserves length" in s.description for s in tspecs))
    check("test: all elements", any("all elements" in s.description for s in tspecs))
    check("test: isinstance int", any("int" in s.description and s.kind == "type_constraint" for s in tspecs))
    check("test: raises ValueError", any("ValueError" in s.description for s in tspecs))

    # ── 4. PatternSpecInferrer ────────────────────────────────────
    print("PatternSpecInferrer …")
    pattern_src = textwrap.dedent("""\
        def guarded(x):
            if x < 0:
                raise ValueError("negative")
            return x * 2

        def sorted_result(xs):
            xs.sort()
            return xs

        def accumulate(xs):
            total = 0
            for v in xs:
                total += v
            return total

        def typed(x):
            if not isinstance(x, int):
                raise TypeError("need int")
            return x

        def nullable(x):
            if x is None:
                return 0
            return x + 1
    """)
    ptree = ast.parse(pattern_src)
    pi = PatternSpecInferrer()
    pfuncs = {f.name: f for f in ast.walk(ptree) if isinstance(f, ast.FunctionDef)}

    gspecs = pi.infer_from_body(pfuncs["guarded"])
    check("pattern: guard precondition", any("precondition" == s.kind for s in gspecs))
    check("pattern: guard raises ValueError", any("ValueError" in s.description for s in gspecs))

    sspecs = pi.infer_from_body(pfuncs["sorted_result"])
    check("pattern: sort return", any("sorted" in s.description for s in sspecs))

    aspecs = pi.infer_from_body(pfuncs["accumulate"])
    check("pattern: accumulator", any("accumulates" in s.description for s in aspecs))

    tspecs_p = pi.infer_from_body(pfuncs["typed"])
    check("pattern: isinstance guard", any("must be int" in s.description for s in tspecs_p))

    nspecs_p = pi.infer_from_body(pfuncs["nullable"])
    check("pattern: None handling", any("None" in s.description for s in nspecs_p))

    # ── 5. AutoSpecGenerator (end-to-end) ─────────────────────────
    print("AutoSpecGenerator …")
    impl_src = textwrap.dedent("""\
        def unique_sorted(xs: list) -> list:
            \"\"\"Return a sorted list with unique elements.

            Parameters
            ----------
            xs : list
                A non-empty input list.

            Returns
            -------
            list
                A sorted list with no duplicates.
            \"\"\"
            if not xs:
                raise ValueError("empty input")
            return sorted(set(xs))
    """)
    test_for_impl = textwrap.dedent("""\
        def test_unique_sorted():
            assert unique_sorted([3, 1, 2, 1]) == [1, 2, 3]
    """)
    gen = AutoSpecGenerator()
    result = gen.generate_specs(impl_src, test_for_impl)
    check("e2e: unique_sorted found", "unique_sorted" in result)
    if "unique_sorted" in result:
        fspec = result["unique_sorted"]
        all_descs = " | ".join(s.description for s in fspec.inferred)
        check("e2e: has type specs", any(s.source == "type_annotation" for s in fspec.inferred))
        check("e2e: has docstring specs", any(s.source == "docstring" for s in fspec.inferred))
        check("e2e: has test specs", any(s.source == "test" for s in fspec.inferred))
        check("e2e: has pattern specs", any(s.source == "pattern" for s in fspec.inferred))
        check("e2e: sorted in specs", "sorted" in all_descs.lower())
        check("e2e: unique in specs", "unique" in all_descs.lower())

    # ── summary ───────────────────────────────────────────────────
    print(f"\n{'='*40}")
    print(f"  {passed} passed, {failed} failed")
    print(f"{'='*40}")
    if failed:
        sys.exit(1)


if __name__ == "__main__":
    _self_test()
