"""Translate deppy HybridTypes into Lean 4 propositions.

Algebraic-semantic bridge
─────────────────────────
A HybridType carries two layers of refinement information:

  1. **Structural** – Z3 predicates over program variables that can be
     machine-checked (decidable).
  2. **Semantic** – Natural-language oracle predicates that capture intent
     but cannot be decided algorithmically.

This module turns each layer into the appropriate Lean 4 artefact:

  Structural predicate  ──►  decidable ``Prop`` (provable by ``omega``/``decide``)
  Semantic predicate    ──►  axiom / ``sorry``-annotated lemma with a trust comment

The entry-point class is `HybridTypeToLean`.  Lower-level helpers live in
`RefinementToLean` (single predicate → Lean) and `ObligationEmitter`
(function contract → Lean theorem statement).  `LeanTacticSuggester` offers
heuristic proof-script suggestions.

Typical usage::

    translator = HybridTypeToLean()
    lean_prop = translator.translate_hybrid_type(ht_dict)

    emitter = ObligationEmitter("MyModule")
    thm = emitter.emit_function_contract("sort", params, pre, post)

    suggester = LeanTacticSuggester()
    tactic = suggester.suggest_proof(thm)
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.types.dependent import PiType, SigmaType, IdentityType, WitnessType, ForallType
    from deppy.types.refinement import RefinementType as _CoreRefinementType, Predicate as _CorePredicate
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import logging
import re
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
    Union,
)

try:
    import z3  # type: ignore[import-untyped]

    _HAS_Z3 = True
except ImportError:
    z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False

logger = logging.getLogger(__name__)

# ════════════════════════════════════════════════════════════════════════
# Constants & mapping tables
# ════════════════════════════════════════════════════════════════════════

# Python / Z3 operator → Lean 4 operator
_OP_MAP: Dict[str, str] = {
    "==": "=",
    "!=": "≠",
    ">=": "≥",
    "<=": "≤",
    ">": ">",
    "<": "<",
    "+": "+",
    "-": "-",
    "*": "*",
    "/": "/",
    "%": "%",
    "**": "^",
    "and": "∧",
    "or": "∨",
    "not": "¬",
    "implies": "→",
    "True": "True",
    "False": "False",
}

# Python built-in type → Lean 4 type
_BASE_TYPE_MAP: Dict[str, str] = {
    "int": "Int",
    "float": "Float",
    "str": "String",
    "bool": "Bool",
    "None": "Unit",
    "NoneType": "Unit",
    "bytes": "ByteArray",
    "list": "List",
    "dict": "Std.HashMap",
    "set": "Finset",
    "tuple": "Prod",
    "Optional": "Option",
    "Any": "Dynamic",
}

# Z3 sort name → Lean 4 type
_Z3_SORT_MAP: Dict[str, str] = {
    "Int": "Int",
    "Real": "Float",
    "Bool": "Bool",
    "BitVec": "BitVec",
    "Array": "Array",
    "String": "String",
    "Seq": "List",
}

# Collection function → Lean equivalent
_COLLECTION_FUNC_MAP: Dict[str, str] = {
    "len": "List.length",
    "sorted": "List.Sorted (· ≤ ·)",
    "reversed": "List.reverse",
    "sum": "List.sum",
    "min": "List.minimum?",
    "max": "List.maximum?",
    "all": "List.all",
    "any": "List.any",
    "map": "List.map",
    "filter": "List.filter",
    "zip": "List.zip",
    "enumerate": "List.enum",
    "append": "List.concat",
    "contains": "List.elem",
    "count": "List.count",
    "index": "List.indexOf?",
}

# Lean 4 tactic keywords for pattern matching
_ARITH_KEYWORDS: FrozenSet[str] = frozenset({
    ">", "<", "≥", "≤", "+", "-", "*", "/", "%", "Nat", "Int", "Float",
})
_DECIDABLE_KEYWORDS: FrozenSet[str] = frozenset({
    "=", "≠", "Bool", "decide", "Decidable", "true", "false",
})
_INDUCTION_KEYWORDS: FrozenSet[str] = frozenset({
    "Nat.rec", "List.rec", "match", "induction", "Nat.succ", "Nat.zero",
})

# ════════════════════════════════════════════════════════════════════════
# Helper utilities
# ════════════════════════════════════════════════════════════════════════

def _indent(text: str, spaces: int = 2) -> str:
    """Indent every line of *text* by *spaces* spaces."""
    prefix = " " * spaces
    return "\n".join(prefix + line if line.strip() else line for line in text.splitlines())

def _lean_ident(name: str) -> str:
    """Sanitise a Python identifier into a valid Lean 4 identifier."""
    name = name.replace(".", "_").replace("-", "_")
    name = re.sub(r"[^A-Za-z0-9_']", "_", name)
    if name and name[0].isdigit():
        name = "x" + name
    # Lean 4 reserved words
    _RESERVED = {
        "def", "theorem", "lemma", "example", "structure", "class",
        "instance", "where", "let", "in", "do", "return", "if", "then",
        "else", "match", "with", "fun", "forall", "exists", "import",
        "open", "namespace", "section", "end", "variable", "axiom",
        "noncomputable", "sorry", "Type", "Prop", "Sort",
    }
    if name in _RESERVED:
        name = name + "'"
    return name

def _lean_comment(text: str) -> str:
    """Wrap *text* in a Lean 4 block comment."""
    escaped = text.replace("-/", "- /")
    return f"/- {escaped} -/"

def _lean_line_comment(text: str) -> str:
    """Create a Lean 4 line comment."""
    return f"-- {text}"

def _parenthesise(expr: str) -> str:
    """Wrap *expr* in parentheses if it contains spaces and is not already wrapped."""
    expr = expr.strip()
    if " " in expr and not (expr.startswith("(") and expr.endswith(")")):
        return f"({expr})"
    return expr

def _is_numeric(s: str) -> bool:
    """Return True if *s* represents a numeric literal."""
    try:
        float(s.strip())
        return True
    except (ValueError, TypeError):

        return False

def _split_binary(expr: str, op: str) -> Optional[Tuple[str, str]]:
    """Split *expr* at the outermost occurrence of binary *op*.

    Returns ``None`` if *op* is not found at depth 0.
    """
    depth = 0
    op_len = len(op)
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and expr[i:i + op_len] == op:
            # Ensure we match whole word for alpha ops
            before = expr[i - 1] if i > 0 else " "
            after = expr[i + op_len] if i + op_len < len(expr) else " "
            if op.isalpha() and (before.isalnum() or after.isalnum()):
                i += 1
                continue
            lhs = expr[:i].strip()
            rhs = expr[i + op_len:].strip()
            if lhs and rhs:
                return lhs, rhs
        i += 1
    return None

def _strip_outer_parens(expr: str) -> str:
    """Remove one layer of matched outer parentheses if present."""
    expr = expr.strip()
    if expr.startswith("(") and expr.endswith(")"):
        depth = 0
        for i, ch in enumerate(expr):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            if depth == 0 and i < len(expr) - 1:
                return expr
        return expr[1:-1].strip()
    return expr

# ════════════════════════════════════════════════════════════════════════
# RefinementToLean
# ════════════════════════════════════════════════════════════════════════

class RefinementToLean:
    """Translate a single refinement predicate into a Lean 4 ``Prop``.

    Handles both Z3 formula strings and natural-language predicates
    (the latter via best-effort pattern matching).

    Attributes
    ----------
    _var_types : Dict[str, str]
        Mapping from variable name → Lean type, used to disambiguate
        overloaded operators.
    """

    def __init__(self, var_types: Optional[Dict[str, str]] = None) -> None:
        self._var_types: Dict[str, str] = dict(var_types or {})
        self._translation_cache: Dict[str, str] = {}

    # ── public API ────────────────────────────────────────────────────

    def translate_predicate(
        self,
        predicate_text: str,
        variables: Dict[str, str],
    ) -> str:
        """Translate a natural-language or Z3 predicate into a Lean Prop.

        Parameters
        ----------
        predicate_text:
            The predicate string.  May be a Z3 expression, a Python
            boolean expression, or a natural-language sentence.
        variables:
            Mapping from variable name → Lean type for context.

        Returns
        -------
        str
            Lean 4 ``Prop`` expression.
        """
        self._var_types.update(variables)
        text = predicate_text.strip()

        cache_key = (text, tuple(sorted(variables.items())))
        if str(cache_key) in self._translation_cache:
            return self._translation_cache[str(cache_key)]

        result = self._translate_predicate_impl(text, variables)
        self._translation_cache[str(cache_key)] = result
        return result

    def translate_z3_to_lean(self, z3_formula_str: str) -> str:
        """Translate a Z3 formula string into a decidable Lean Prop.

        Supports integer/real arithmetic comparisons, boolean
        connectives, quantifiers, array operations, and set membership.

        Parameters
        ----------
        z3_formula_str:
            A Z3-compatible expression string such as ``"And(x > 0, y < 10)"``.

        Returns
        -------
        str
            Lean 4 decidable ``Prop``.
        """
        formula = z3_formula_str.strip()
        if not formula:
            return "True"

        return self._z3_dispatch(formula)

    def translate_arithmetic(self, expr: str) -> str:
        """Translate a Python arithmetic expression into Lean syntax.

        Handles operator precedence, integer division, modulo, and
        exponentiation.
        """
        expr = expr.strip()
        if not expr:
            return expr

        return self._arith_dispatch(expr)

    def translate_collection_pred(self, pred: str) -> str:
        """Translate a Python collection predicate into Lean syntax.

        Handles ``len()``, ``sorted()``, ``in``, ``not in``,
        ``all()``, ``any()``, and list comprehension patterns.
        """
        pred = pred.strip()
        if not pred:
            return "True"
        return self._collection_dispatch(pred)

    # ── private: top-level dispatch ───────────────────────────────────

    def _translate_predicate_impl(
        self,
        text: str,
        variables: Dict[str, str],
    ) -> str:
        """Core dispatcher for predicate translation."""
        # Attempt Z3-style first
        if self._looks_like_z3(text):
            return self.translate_z3_to_lean(text)

        # Attempt arithmetic / comparison
        if self._looks_like_comparison(text):
            return self._translate_comparison(text)

        # Attempt collection predicate
        if self._looks_like_collection(text):
            return self.translate_collection_pred(text)

        # Boolean connective at top level
        if self._looks_like_boolean(text):
            return self._translate_boolean(text)

        # Quantifier
        if self._looks_like_quantifier(text):
            return self._translate_quantifier(text)

        # Membership test
        if " in " in text or " ∈ " in text:
            return self._translate_membership(text)

        # Fall through: treat as NL comment + sorry
        return self._translate_nl_predicate(text)

    # ── private: Z3 translation rules (≥ 30) ─────────────────────────

    def _looks_like_z3(self, text: str) -> bool:
        z3_funcs = {
            "And(", "Or(", "Not(", "Implies(", "ForAll(", "Exists(",
            "If(", "IntVal(", "RealVal(", "BoolVal(", "Select(",
            "Store(", "Length(", "Concat(", "Contains(", "Extract(",
        }
        return any(f in text for f in z3_funcs)

    def _z3_dispatch(self, formula: str) -> str:
        """Recursively translate a Z3-style formula string."""
        formula = _strip_outer_parens(formula)

        # Rule 1: And(a, b, ...) → a ∧ b ∧ ...
        if formula.startswith("And(") and formula.endswith(")"):
            return self._z3_nary("∧", formula[4:-1])

        # Rule 2: Or(a, b, ...) → a ∨ b ∨ ...
        if formula.startswith("Or(") and formula.endswith(")"):
            return self._z3_nary("∨", formula[3:-1])

        # Rule 3: Not(a) → ¬a
        if formula.startswith("Not(") and formula.endswith(")"):
            inner = self._z3_dispatch(formula[4:-1])
            return f"¬{_parenthesise(inner)}"

        # Rule 4: Implies(a, b) → a → b
        if formula.startswith("Implies(") and formula.endswith(")"):
            args = self._z3_split_args(formula[8:-1])
            if len(args) == 2:
                lhs = self._z3_dispatch(args[0])
                rhs = self._z3_dispatch(args[1])
                return f"{_parenthesise(lhs)} → {_parenthesise(rhs)}"

        # Rule 5: ForAll([vars], body) → ∀ vars, body
        if formula.startswith("ForAll(") and formula.endswith(")"):
            return self._z3_forall(formula[7:-1])

        # Rule 6: Exists([vars], body) → ∃ vars, body
        if formula.startswith("Exists(") and formula.endswith(")"):
            return self._z3_exists(formula[7:-1])

        # Rule 7: If(c, t, e) → if c then t else e
        if formula.startswith("If(") and formula.endswith(")"):
            args = self._z3_split_args(formula[3:-1])
            if len(args) == 3:
                cond = self._z3_dispatch(args[0])
                then_b = self._z3_dispatch(args[1])
                else_b = self._z3_dispatch(args[2])
                return f"if {cond} then {then_b} else {else_b}"

        # Rule 8: x > 0 → x > 0 (integer comparison, same syntax)
        for py_op, lean_op in [(">=", "≥"), ("<=", "≤"), ("!=", "≠"),
                                ("==", "="), (">", ">"), ("<", "<")]:
            pair = _split_binary(formula, py_op)
            if pair is not None:
                lhs = self._z3_dispatch(pair[0])
                rhs = self._z3_dispatch(pair[1])
                return f"{lhs} {lean_op} {rhs}"

        # Rule 9: x + y → x + y (arithmetic)
        for op in ["+", "-", "*"]:
            pair = _split_binary(formula, op)
            if pair is not None:
                lhs = self._z3_dispatch(pair[0])
                rhs = self._z3_dispatch(pair[1])
                return f"{lhs} {op} {rhs}"

        # Rule 10: x / y → x / y (integer division)
        pair = _split_binary(formula, "/")
        if pair is not None:
            lhs = self._z3_dispatch(pair[0])
            rhs = self._z3_dispatch(pair[1])
            return f"{lhs} / {rhs}"

        # Rule 11: x % y → x % y (modulo)
        pair = _split_binary(formula, "%")
        if pair is not None:
            lhs = self._z3_dispatch(pair[0])
            rhs = self._z3_dispatch(pair[1])
            return f"{lhs} % {rhs}"

        # Rule 12: x ** y → x ^ y (exponentiation)
        pair = _split_binary(formula, "**")
        if pair is not None:
            lhs = self._z3_dispatch(pair[0])
            rhs = self._z3_dispatch(pair[1])
            return f"{lhs} ^ {rhs}"

        # Rule 13: len(arr) → arr.length (array length)
        m = re.match(r"len\((\w+)\)", formula)
        if m:
            return f"{_lean_ident(m.group(1))}.length"

        # Rule 14: Length(arr) → arr.length (Z3 Seq length)
        m = re.match(r"Length\((\w+)\)", formula)
        if m:
            return f"{_lean_ident(m.group(1))}.length"

        # Rule 15: arr[i] → arr.get! i (array indexing)
        m = re.match(r"(\w+)\[(.+)\]", formula)
        if m:
            arr = _lean_ident(m.group(1))
            idx = self._z3_dispatch(m.group(2))
            return f"{arr}.get! {_parenthesise(idx)}"

        # Rule 16: Select(arr, i) → arr.get! i (Z3 array select)
        if formula.startswith("Select(") and formula.endswith(")"):
            args = self._z3_split_args(formula[7:-1])
            if len(args) == 2:
                arr = self._z3_dispatch(args[0])
                idx = self._z3_dispatch(args[1])
                return f"{arr}.get! {_parenthesise(idx)}"

        # Rule 17: Store(arr, i, v) → arr.set! i v (Z3 array store)
        if formula.startswith("Store(") and formula.endswith(")"):
            args = self._z3_split_args(formula[6:-1])
            if len(args) == 3:
                arr = self._z3_dispatch(args[0])
                idx = self._z3_dispatch(args[1])
                val = self._z3_dispatch(args[2])
                return f"{arr}.set! {_parenthesise(idx)} {_parenthesise(val)}"

        # Rule 18: IntVal(n) → (n : Int)
        m = re.match(r"IntVal\((-?\d+)\)", formula)
        if m:
            return f"({m.group(1)} : Int)"

        # Rule 19: RealVal(n) → (n : Float)
        m = re.match(r"RealVal\(([^)]+)\)", formula)
        if m:
            return f"({m.group(1)} : Float)"

        # Rule 20: BoolVal(True) → True, BoolVal(False) → False
        m = re.match(r"BoolVal\((True|False)\)", formula)
        if m:
            return m.group(1)

        # Rule 21: Concat(a, b) → a ++ b (sequence concatenation)
        if formula.startswith("Concat(") and formula.endswith(")"):
            args = self._z3_split_args(formula[7:-1])
            if len(args) == 2:
                lhs = self._z3_dispatch(args[0])
                rhs = self._z3_dispatch(args[1])
                return f"{lhs} ++ {rhs}"

        # Rule 22: Contains(s, sub) → sub ∈ s (Z3 Seq contains)
        if formula.startswith("Contains(") and formula.endswith(")"):
            args = self._z3_split_args(formula[9:-1])
            if len(args) == 2:
                container = self._z3_dispatch(args[0])
                element = self._z3_dispatch(args[1])
                return f"{element} ∈ {container}"

        # Rule 23: Extract(s, off, len) → s.extract off len
        if formula.startswith("Extract(") and formula.endswith(")"):
            args = self._z3_split_args(formula[8:-1])
            if len(args) == 3:
                s = self._z3_dispatch(args[0])
                off = self._z3_dispatch(args[1])
                ln = self._z3_dispatch(args[2])
                return f"{s}.extract {_parenthesise(off)} {_parenthesise(ln)}"

        # Rule 24: sorted predicate pattern ∀i. arr[i] <= arr[i+1]
        m = re.match(
            r"ForAll\(\[(\w+)\],\s*Implies\(.*?(\w+)\[(\w+)\]\s*<=\s*(\w+)\[(\w+)\s*\+\s*1\]",
            formula,
        )
        if m:
            idx_var = _lean_ident(m.group(1))
            arr = _lean_ident(m.group(2))
            return (
                f"∀ {idx_var}, {idx_var} + 1 < {arr}.length → "
                f"{arr}.get! {idx_var} ≤ {arr}.get! ({idx_var} + 1)"
            )

        # Rule 25: x ∈ S (membership, unicode)
        if " ∈ " in formula:
            lhs, rhs = formula.split(" ∈ ", 1)
            return f"{self._z3_dispatch(lhs.strip())} ∈ {self._z3_dispatch(rhs.strip())}"

        # Rule 26: Distinct(a, b, c) → a ≠ b ∧ a ≠ c ∧ b ≠ c
        if formula.startswith("Distinct(") and formula.endswith(")"):
            return self._z3_distinct(formula[9:-1])

        # Rule 27: x and y → x ∧ y (Python-style boolean)
        pair = _split_binary(formula, "and")
        if pair is not None:
            lhs = self._z3_dispatch(pair[0])
            rhs = self._z3_dispatch(pair[1])
            return f"{_parenthesise(lhs)} ∧ {_parenthesise(rhs)}"

        # Rule 28: x or y → x ∨ y
        pair = _split_binary(formula, "or")
        if pair is not None:
            lhs = self._z3_dispatch(pair[0])
            rhs = self._z3_dispatch(pair[1])
            return f"{_parenthesise(lhs)} ∨ {_parenthesise(rhs)}"

        # Rule 29: not x → ¬x
        if formula.startswith("not "):
            inner = self._z3_dispatch(formula[4:])
            return f"¬{_parenthesise(inner)}"

        # Rule 30: True / False literals
        if formula in ("True", "true"):
            return "True"
        if formula in ("False", "false"):
            return "False"

        # Rule 31: abs(x) → Int.natAbs x
        m = re.match(r"abs\((.+)\)", formula)
        if m:
            inner = self._z3_dispatch(m.group(1))
            return f"Int.natAbs {_parenthesise(inner)}"

        # Rule 32: max(a, b) → max a b
        m = re.match(r"max\((.+)\)", formula)
        if m:
            args = self._z3_split_args(m.group(1))
            if len(args) == 2:
                a = self._z3_dispatch(args[0])
                b = self._z3_dispatch(args[1])
                return f"max {_parenthesise(a)} {_parenthesise(b)}"

        # Rule 33: min(a, b) → min a b
        m = re.match(r"min\((.+)\)", formula)
        if m:
            args = self._z3_split_args(m.group(1))
            if len(args) == 2:
                a = self._z3_dispatch(args[0])
                b = self._z3_dispatch(args[1])
                return f"min {_parenthesise(a)} {_parenthesise(b)}"

        # Rule 34: numeric literal
        if _is_numeric(formula):
            return formula.strip()

        # Rule 35: plain identifier
        if re.match(r"^[A-Za-z_]\w*$", formula):
            return _lean_ident(formula)

        # Fallback: return sanitised
        return _lean_ident(formula) if re.match(r"^\w+$", formula) else formula

    # ── Z3 helper methods ─────────────────────────────────────────────

    def _z3_nary(self, op: str, args_str: str) -> str:
        """Translate an n-ary Z3 connective."""
        args = self._z3_split_args(args_str)
        translated = [self._z3_dispatch(a) for a in args]
        return f" {op} ".join(_parenthesise(t) for t in translated)

    def _z3_forall(self, body: str) -> str:
        """Translate ForAll([vars], body)."""
        parts = self._z3_split_args(body)
        if len(parts) < 2:
            return f"∀ _, {self._z3_dispatch(body)}"
        var_list_str = parts[0].strip()
        vars_ = self._parse_var_list(var_list_str)
        body_lean = self._z3_dispatch(", ".join(parts[1:]))
        var_decls = " ".join(_lean_ident(v) for v in vars_)
        return f"∀ {var_decls}, {body_lean}"

    def _z3_exists(self, body: str) -> str:
        """Translate Exists([vars], body)."""
        parts = self._z3_split_args(body)
        if len(parts) < 2:
            return f"∃ _, {self._z3_dispatch(body)}"
        var_list_str = parts[0].strip()
        vars_ = self._parse_var_list(var_list_str)
        body_lean = self._z3_dispatch(", ".join(parts[1:]))
        var_decls = " ".join(_lean_ident(v) for v in vars_)
        return f"∃ {var_decls}, {body_lean}"

    def _z3_distinct(self, args_str: str) -> str:
        """Translate Distinct(a, b, c, ...) → pairwise ≠ conjunction."""
        args = self._z3_split_args(args_str)
        translated = [self._z3_dispatch(a) for a in args]
        pairs: List[str] = []
        for i in range(len(translated)):
            for j in range(i + 1, len(translated)):
                pairs.append(f"{translated[i]} ≠ {translated[j]}")
        if not pairs:
            return "True"
        return " ∧ ".join(_parenthesise(p) for p in pairs)

    def _z3_split_args(self, s: str) -> List[str]:
        """Split a comma-separated argument string respecting nesting."""
        args: List[str] = []
        depth = 0
        current: List[str] = []
        for ch in s:
            if ch in "([":
                depth += 1
                current.append(ch)
            elif ch in ")]":
                depth -= 1
                current.append(ch)
            elif ch == "," and depth == 0:
                args.append("".join(current).strip())
                current = []
            else:
                current.append(ch)
        tail = "".join(current).strip()
        if tail:
            args.append(tail)
        return args

    def _parse_var_list(self, var_list_str: str) -> List[str]:
        """Parse ``[x, y, z]`` or ``x, y, z`` into a list of names."""
        s = var_list_str.strip().strip("[]")
        return [v.strip() for v in s.split(",") if v.strip()]

    # ── private: comparison / boolean / quantifier detection ──────────

    def _looks_like_comparison(self, text: str) -> bool:
        return bool(re.search(r"[<>=!]=?", text) and not self._looks_like_z3(text))

    def _looks_like_collection(self, text: str) -> bool:
        patterns = ["len(", "sorted(", "all(", "any(", ".append", ".contains",
                     "for ", " in [", "list(", "range("]
        return any(p in text for p in patterns)

    def _looks_like_boolean(self, text: str) -> bool:
        return bool(
            re.search(r"\b(and|or|not)\b", text) and not self._looks_like_z3(text)
        )

    def _looks_like_quantifier(self, text: str) -> bool:
        return bool(re.search(r"\b(for all|forall|for every|∀|exists|there exists|∃)\b", text, re.I))

    # ── private: comparison translation ───────────────────────────────

    def _translate_comparison(self, text: str) -> str:
        """Translate a Python comparison expression."""
        for py_op, lean_op in [(">=", "≥"), ("<=", "≤"), ("!=", "≠"),
                                ("==", "="), (">", ">"), ("<", "<")]:
            pair = _split_binary(text, py_op)
            if pair is not None:
                lhs = self.translate_arithmetic(pair[0])
                rhs = self.translate_arithmetic(pair[1])
                return f"{lhs} {lean_op} {rhs}"
        return text

    # ── private: boolean translation ──────────────────────────────────

    def _translate_boolean(self, text: str) -> str:
        """Translate Python boolean connectives."""
        # Try 'and' first (lowest precedence among and/or)
        pair = _split_binary(text, "and")
        if pair is not None:
            lhs = self._translate_predicate_impl(pair[0], self._var_types)
            rhs = self._translate_predicate_impl(pair[1], self._var_types)
            return f"{_parenthesise(lhs)} ∧ {_parenthesise(rhs)}"

        pair = _split_binary(text, "or")
        if pair is not None:
            lhs = self._translate_predicate_impl(pair[0], self._var_types)
            rhs = self._translate_predicate_impl(pair[1], self._var_types)
            return f"{_parenthesise(lhs)} ∨ {_parenthesise(rhs)}"

        if text.strip().startswith("not "):
            inner = self._translate_predicate_impl(text.strip()[4:], self._var_types)
            return f"¬{_parenthesise(inner)}"

        return text

    # ── private: quantifier translation ───────────────────────────────

    def _translate_quantifier(self, text: str) -> str:
        """Translate NL quantifiers to Lean ∀/∃."""
        # ∀ / forall / for all
        m = re.match(r"(?:for\s+all|forall|∀)\s+(\w+)(?:\s*[,:]\s*|\s+in\s+\S+\s*,\s*)(.+)", text, re.I)
        if m:
            var = _lean_ident(m.group(1))
            body = self._translate_predicate_impl(m.group(2), self._var_types)
            return f"∀ {var}, {body}"

        # ∃ / exists / there exists
        m = re.match(r"(?:there\s+exists|exists|∃)\s+(\w+)(?:\s*[,:]\s*|\s+in\s+\S+\s*,\s*)(.+)", text, re.I)
        if m:
            var = _lean_ident(m.group(1))
            body = self._translate_predicate_impl(m.group(2), self._var_types)
            return f"∃ {var}, {body}"

        return text

    # ── private: membership ───────────────────────────────────────────

    def _translate_membership(self, text: str) -> str:
        """Translate ``x in S`` / ``x not in S``."""
        if " not in " in text:
            lhs, rhs = text.split(" not in ", 1)
            lhs_l = self.translate_arithmetic(lhs.strip())
            rhs_l = self.translate_arithmetic(rhs.strip())
            return f"{lhs_l} ∉ {rhs_l}"
        if " in " in text:
            lhs, rhs = text.split(" in ", 1)
            lhs_l = self.translate_arithmetic(lhs.strip())
            rhs_l = self.translate_arithmetic(rhs.strip())
            return f"{lhs_l} ∈ {rhs_l}"
        if " ∈ " in text:
            lhs, rhs = text.split(" ∈ ", 1)
            lhs_l = self.translate_arithmetic(lhs.strip())
            rhs_l = self.translate_arithmetic(rhs.strip())
            return f"{lhs_l} ∈ {rhs_l}"
        return text

    # ── private: NL fallback ──────────────────────────────────────────

    def _translate_nl_predicate(self, text: str) -> str:
        """Fall back: wrap NL predicate in a sorry-annotated axiom reference."""
        sanitised = re.sub(r"[^A-Za-z0-9_ ]", "", text).strip().replace(" ", "_")[:60]
        ident = _lean_ident(sanitised) if sanitised else "nl_pred"
        return f"{ident} {_lean_comment('NL: ' + text)}"

    # ── private: arithmetic dispatch ──────────────────────────────────

    def _arith_dispatch(self, expr: str) -> str:
        """Recursively translate a Python arithmetic expression to Lean."""
        expr = _strip_outer_parens(expr)

        # Binary operators in precedence order (lowest first)
        for op in ["+", "-", "*", "/", "%", "**"]:
            pair = _split_binary(expr, op)
            if pair is not None:
                lhs = self._arith_dispatch(pair[0])
                rhs = self._arith_dispatch(pair[1])
                lean_op = "^" if op == "**" else op
                return f"{lhs} {lean_op} {rhs}"

        # Unary minus
        if expr.startswith("-") and not _is_numeric(expr):
            inner = self._arith_dispatch(expr[1:].strip())
            return f"-{_parenthesise(inner)}"

        # Function calls
        m = re.match(r"(\w+)\((.+)\)$", expr)
        if m:
            func = m.group(1)
            inner = m.group(2)
            if func == "abs":
                return f"Int.natAbs {_parenthesise(self._arith_dispatch(inner))}"
            if func == "len":
                return f"{_lean_ident(inner)}.length"
            if func in ("max", "min"):
                args = self._z3_split_args(inner)
                if len(args) == 2:
                    a = self._arith_dispatch(args[0])
                    b = self._arith_dispatch(args[1])
                    return f"{func} {_parenthesise(a)} {_parenthesise(b)}"
            return f"{_lean_ident(func)} {_parenthesise(self._arith_dispatch(inner))}"

        # Literal or identifier
        if _is_numeric(expr):
            return expr.strip()
        return _lean_ident(expr)

    # ── private: collection dispatch ──────────────────────────────────

    def _collection_dispatch(self, pred: str) -> str:
        """Translate collection predicates."""
        # len(x) op y
        m = re.match(r"len\((\w+)\)\s*([<>=!]+)\s*(.+)", pred)
        if m:
            arr = _lean_ident(m.group(1))
            op = _OP_MAP.get(m.group(2), m.group(2))
            rhs = self.translate_arithmetic(m.group(3))
            return f"{arr}.length {op} {rhs}"

        # sorted(x) == x  →  List.Sorted (· ≤ ·) x
        m = re.match(r"sorted\((\w+)\)\s*==\s*(\w+)", pred)
        if m:
            arr = _lean_ident(m.group(1))
            return f"List.Sorted (· ≤ ·) {arr}"

        # all(f(x) for x in arr)
        m = re.match(r"all\((.+)\s+for\s+(\w+)\s+in\s+(\w+)\)", pred)
        if m:
            body_py = m.group(1).strip()
            var = _lean_ident(m.group(2))
            arr = _lean_ident(m.group(3))
            body_lean = self._translate_predicate_impl(body_py, self._var_types)
            return f"∀ {var} ∈ {arr}, {body_lean}"

        # any(f(x) for x in arr)
        m = re.match(r"any\((.+)\s+for\s+(\w+)\s+in\s+(\w+)\)", pred)
        if m:
            body_py = m.group(1).strip()
            var = _lean_ident(m.group(2))
            arr = _lean_ident(m.group(3))
            body_lean = self._translate_predicate_impl(body_py, self._var_types)
            return f"∃ {var} ∈ {arr}, {body_lean}"

        # x in arr
        if " in " in pred and not pred.strip().startswith("for"):
            return self._translate_membership(pred)

        # Generic collection function
        for py_func, lean_func in _COLLECTION_FUNC_MAP.items():
            if f"{py_func}(" in pred:
                m2 = re.match(rf"{py_func}\((.+)\)", pred)
                if m2:
                    arg = self.translate_arithmetic(m2.group(1))
                    return f"{lean_func} {_parenthesise(arg)}"

        return pred

# ════════════════════════════════════════════════════════════════════════
# HybridTypeToLean
# ════════════════════════════════════════════════════════════════════════

class HybridTypeToLean:
    """Translate a full HybridType (dict representation) into Lean 4.

    A HybridType dict has the shape::

        {
            "base": "list",               # Python base type
            "type_args": ["int"],          # generic parameters
            "structural": ["len(x) > 0"], # Z3 / decidable predicates
            "semantic": [                  # oracle predicates
                {"text": "returns sorted", "confidence": 0.92}
            ],
            "pi": { ... },                # optional Π-type envelope
            "sigma": { ... },             # optional Σ-type envelope
            "identity": { ... },          # optional identity type
        }

    Attributes
    ----------
    _ref : RefinementToLean
        Refinement translator used for individual predicates.
    """

    def __init__(
        self,
        var_types: Optional[Dict[str, str]] = None,
    ) -> None:
        self._ref = RefinementToLean(var_types)
        self._var_types: Dict[str, str] = dict(var_types or {})

    # ── public API ────────────────────────────────────────────────────

    def translate_hybrid_type(self, ht_dict: Dict[str, Any]) -> str:
        """Translate a complete HybridType dict into a Lean 4 proposition.

        The structural part becomes a decidable Lean Prop (can use
        ``decide``/``omega``); the semantic part is emitted as a
        ``sorry``-annotated axiom with a trust comment.

        Returns
        -------
        str
            A Lean 4 ``Prop`` expression combining structural ∧ semantic.
        """
        base_lean = self._translate_base(ht_dict)
        structural_props = self._translate_structural(ht_dict)
        semantic_props = self._translate_semantic(ht_dict)

        # Handle dependent-type wrappers
        if "pi" in ht_dict and ht_dict["pi"]:
            pi = ht_dict["pi"]
            inner = self._combine_props(structural_props, semantic_props)
            return self.translate_pi_type(
                pi.get("param", "x"),
                pi.get("domain", base_lean),
                inner if inner else base_lean,
            )

        if "sigma" in ht_dict and ht_dict["sigma"]:
            sigma = ht_dict["sigma"]
            pred = self._combine_props(structural_props, semantic_props)
            return self.translate_sigma_type(
                sigma.get("fst_type", base_lean),
                pred if pred else "True",
            )

        if "identity" in ht_dict and ht_dict["identity"]:
            ident = ht_dict["identity"]
            return self.translate_identity_type(
                ident.get("lhs", "_"),
                ident.get("rhs", "_"),
            )

        # Refinement type: {x : Base | structural ∧ semantic}
        combined = self._combine_props(structural_props, semantic_props)
        if combined:
            return self.translate_refinement_type(base_lean, combined)
        return base_lean

    def translate_pi_type(
        self,
        param_name: str,
        domain: str,
        codomain_template: str,
    ) -> str:
        """Translate a Π-type into Lean 4 ``∀`` syntax.

        Parameters
        ----------
        param_name:
            The bound variable name.
        domain:
            Lean type expression for the domain.
        codomain_template:
            Lean expression for the codomain (may reference *param_name*).

        Returns
        -------
        str
            ``∀ (param : Domain), Codomain``
        """
        p = _lean_ident(param_name)
        return f"∀ ({p} : {domain}), {codomain_template}"

    def translate_sigma_type(
        self,
        fst_type: str,
        snd_predicate: str,
    ) -> str:
        """Translate a Σ-type into Lean 4 Subtype/Sigma syntax.

        Returns ``{ x : FstType // SndPredicate x }`` when the second
        component is a predicate, or ``Σ (x : FstType), SndType`` for
        general dependent pairs.

        Parameters
        ----------
        fst_type:
            Lean type for the first component.
        snd_predicate:
            Lean ``Prop`` for the predicate on the first component.
        """
        return f"{{ x : {fst_type} // {snd_predicate} }}"

    def translate_refinement_type(
        self,
        base: str,
        predicate: str,
    ) -> str:
        """Translate ``{x : T | P x}`` into Lean Subtype syntax.

        Parameters
        ----------
        base:
            Lean base type.
        predicate:
            Lean ``Prop`` that the value must satisfy.
        """
        return f"{{ x : {base} // {predicate} }}"

    def translate_identity_type(
        self,
        lhs: str,
        rhs: str,
    ) -> str:
        """Translate ``Id(a, b)`` into Lean propositional equality ``a = b``.

        Parameters
        ----------
        lhs:
            Lean expression for the left-hand side.
        rhs:
            Lean expression for the right-hand side.
        """
        return f"{lhs} = {rhs}"

    # ── private helpers ───────────────────────────────────────────────

    def _translate_base(self, ht_dict: Dict[str, Any]) -> str:
        """Map the Python base type + type_args to a Lean type."""
        base_py = str(ht_dict.get("base", "Any"))
        base_lean = _BASE_TYPE_MAP.get(base_py, _lean_ident(base_py))

        type_args = ht_dict.get("type_args", [])
        if type_args:
            args_lean = " ".join(
                _BASE_TYPE_MAP.get(str(a), _lean_ident(str(a)))
                for a in type_args
            )
            return f"{base_lean} {args_lean}"
        return base_lean

    def _translate_structural(self, ht_dict: Dict[str, Any]) -> List[str]:
        """Translate the structural (Z3) predicates into Lean Props."""
        structural: List[str] = ht_dict.get("structural", [])
        result: List[str] = []
        for pred_text in structural:
            lean_prop = self._ref.translate_predicate(str(pred_text), self._var_types)
            result.append(lean_prop)
        return result

    def _translate_semantic(self, ht_dict: Dict[str, Any]) -> List[str]:
        """Translate semantic (oracle) predicates into sorry-annotated Props.

        Each semantic predicate becomes::

            sorry /- semantic: <text> (oracle confidence <conf>) -/
        """
        semantic: List[Any] = ht_dict.get("semantic", [])
        result: List[str] = []
        for entry in semantic:
            if isinstance(entry, dict):
                text = entry.get("text", "")
                confidence = entry.get("confidence", 0.0)
                comment = _lean_comment(
                    f"semantic: {text} (oracle confidence {confidence})"
                )
                result.append(f"sorry {comment}")
            elif isinstance(entry, str):
                comment = _lean_comment(f"semantic: {entry}")
                result.append(f"sorry {comment}")
        return result

    def _combine_props(
        self,
        structural: List[str],
        semantic: List[str],
    ) -> str:
        """Conjoin structural and semantic propositions.

        Structural Props are combined with ``∧``.  Semantic Props are
        appended after a ``∧`` with a sorry placeholder.
        """
        all_props = structural + semantic
        if not all_props:
            return ""
        if len(all_props) == 1:
            return all_props[0]
        return " ∧ ".join(_parenthesise(p) for p in all_props)

    def translate_list_type(
        self,
        element_type: str,
        predicates: List[str],
    ) -> str:
        """Convenience: translate ``List[T]`` with refinement predicates."""
        base = f"List {element_type}"
        if not predicates:
            return base
        lean_preds = [
            self._ref.translate_predicate(p, self._var_types) for p in predicates
        ]
        combined = " ∧ ".join(_parenthesise(p) for p in lean_preds)
        return f"{{ xs : {base} // {combined} }}"

    def translate_dict_type(
        self,
        key_type: str,
        val_type: str,
        predicates: List[str],
    ) -> str:
        """Convenience: translate ``Dict[K, V]`` with refinement predicates."""
        base = f"Std.HashMap {key_type} {val_type}"
        if not predicates:
            return base
        lean_preds = [
            self._ref.translate_predicate(p, self._var_types) for p in predicates
        ]
        combined = " ∧ ".join(_parenthesise(p) for p in lean_preds)
        return f"{{ m : {base} // {combined} }}"

    def translate_option_type(
        self,
        inner_type: str,
        predicates: List[str],
    ) -> str:
        """Convenience: translate ``Optional[T]`` with predicates."""
        base = f"Option {inner_type}"
        if not predicates:
            return base
        lean_preds = [
            self._ref.translate_predicate(p, self._var_types) for p in predicates
        ]
        combined = " ∧ ".join(_parenthesise(p) for p in lean_preds)
        return f"{{ v : {base} // {combined} }}"

    def translate_union_type(
        self,
        branches: List[str],
        predicates: Optional[List[str]] = None,
    ) -> str:
        """Translate ``Union[A, B, ...]`` into Lean ``Sum`` / ``Or``."""
        if len(branches) == 0:
            return "Empty"
        if len(branches) == 1:
            return branches[0]
        # Build nested Sum
        result = branches[-1]
        for b in reversed(branches[:-1]):
            result = f"Sum {_parenthesise(b)} {_parenthesise(result)}"
        if predicates:
            lean_preds = [
                self._ref.translate_predicate(p, self._var_types) for p in predicates
            ]
            combined = " ∧ ".join(_parenthesise(p) for p in lean_preds)
            return f"{{ v : {result} // {combined} }}"
        return result

    def translate_callable_type(
        self,
        param_types: List[str],
        return_type: str,
    ) -> str:
        """Translate ``Callable[[A, B], R]`` into Lean function type."""
        if not param_types:
            return f"Unit → {return_type}"
        result = return_type
        for pt in reversed(param_types):
            result = f"{pt} → {result}"
        return result

# ════════════════════════════════════════════════════════════════════════
# ObligationEmitter
# ════════════════════════════════════════════════════════════════════════

@dataclass
class _ParamInfo:
    """Internal representation of a function parameter for emission."""
    name: str
    lean_type: str
    default: Optional[str] = None

class ObligationEmitter:
    """Emit Lean 4 theorem / axiom statements from deppy obligations.

    Each deppy obligation (pre/post-condition, guarantee, assumption)
    becomes a Lean 4 ``theorem``, ``axiom``, or ``sorry``-annotated
    ``lemma`` in a dedicated namespace.

    Attributes
    ----------
    module_name : str
        The Lean namespace under which all emitted declarations live.
    """

    def __init__(self, module_name: str) -> None:
        self.module_name = _lean_ident(module_name)
        self._ref = RefinementToLean()
        self._ht = HybridTypeToLean()
        self._counter: int = 0
        self._emitted: List[str] = []

    # ── public API ────────────────────────────────────────────────────

    def emit_function_contract(
        self,
        func_name: str,
        params: List[Dict[str, str]],
        pre: str,
        post: str,
    ) -> str:
        """Emit a Lean theorem statement for a function's contract.

        Parameters
        ----------
        func_name:
            Python function name.
        params:
            List of ``{"name": ..., "type": ...}`` dicts.
        pre:
            Pre-condition predicate string.
        post:
            Post-condition predicate string.

        Returns
        -------
        str
            A Lean 4 theorem statement (without proof body).
        """
        lean_name = _lean_ident(func_name)
        parsed_params = self._parse_params(params)
        param_decls = self._format_param_decls(parsed_params)

        var_types = {p.name: p.lean_type for p in parsed_params}
        pre_lean = self._ref.translate_predicate(pre, var_types) if pre else "True"
        post_lean = self._ref.translate_predicate(post, var_types) if post else "True"

        thm = (
            f"namespace {self.module_name}\n\n"
            f"theorem {lean_name}_contract\n"
            f"  {param_decls}\n"
            f"  (h_pre : {pre_lean}) :\n"
            f"  {post_lean} := by\n"
            f"  sorry\n\n"
            f"end {self.module_name}"
        )
        self._emitted.append(thm)
        return thm

    def emit_guarantee(
        self,
        func_name: str,
        guarantee_text: str,
        parsed_structural: Optional[List[str]] = None,
    ) -> str:
        """Emit a Lean lemma for a deppy ``@guarantee``.

        If *parsed_structural* predicates are provided, the structural
        part becomes a decidable hypothesis and only the semantic
        remainder uses ``sorry``.

        Parameters
        ----------
        func_name:
            The function this guarantee belongs to.
        guarantee_text:
            The full guarantee text (may be NL or Z3).
        parsed_structural:
            Optional list of Z3 / decidable sub-predicates already
            extracted by the hybrid checker.
        """
        lean_name = _lean_ident(func_name)
        self._counter += 1
        lemma_name = f"{lean_name}_guarantee_{self._counter}"

        if parsed_structural:
            struct_props = [
                self._ref.translate_predicate(p, {}) for p in parsed_structural
            ]
            struct_combined = " ∧ ".join(_parenthesise(p) for p in struct_props)
            semantic_comment = _lean_comment(f"guarantee: {guarantee_text}")

            lemma = (
                f"namespace {self.module_name}\n\n"
                f"lemma {lemma_name}\n"
                f"  (h_struct : {struct_combined}) :\n"
                f"  {struct_combined} ∧ sorry {semantic_comment} := by\n"
                f"  exact ⟨h_struct, sorry⟩\n\n"
                f"end {self.module_name}"
            )
        else:
            full_prop = self._ref.translate_predicate(guarantee_text, {})
            lemma = (
                f"namespace {self.module_name}\n\n"
                f"lemma {lemma_name} :\n"
                f"  {full_prop} := by\n"
                f"  sorry {_lean_comment('guarantee: ' + guarantee_text)}\n\n"
                f"end {self.module_name}"
            )

        self._emitted.append(lemma)
        return lemma

    def emit_assumption(
        self,
        assumption_text: str,
        context: Dict[str, Any],
    ) -> str:
        """Emit a Lean axiom or sorry'd theorem for a deppy ``@assume``.

        Assumptions are trusted without proof and thus become either
        a Lean ``axiom`` (if the context marks it as axiomatic) or a
        ``sorry``-annotated lemma.

        Parameters
        ----------
        assumption_text:
            The assumption predicate.
        context:
            Dict with optional keys ``"axiomatic"`` (bool),
            ``"variables"`` (Dict[str, str]).
        """
        self._counter += 1
        axiomatic = context.get("axiomatic", False)
        variables = context.get("variables", {})
        prop = self._ref.translate_predicate(assumption_text, variables)

        var_decls = ""
        if variables:
            parts = [f"({_lean_ident(n)} : {_BASE_TYPE_MAP.get(t, t)})"
                      for n, t in variables.items()]
            var_decls = " ".join(parts) + " "

        if axiomatic:
            decl = (
                f"namespace {self.module_name}\n\n"
                f"axiom assumption_{self._counter}\n"
                f"  {var_decls}:\n"
                f"  {prop}\n\n"
                f"end {self.module_name}"
            )
        else:
            decl = (
                f"namespace {self.module_name}\n\n"
                f"lemma assumption_{self._counter}\n"
                f"  {var_decls}:\n"
                f"  {prop} := by\n"
                f"  sorry {_lean_comment('assumed: ' + assumption_text)}\n\n"
                f"end {self.module_name}"
            )

        self._emitted.append(decl)
        return decl

    def emit_check(
        self,
        check_text: str,
        context: Dict[str, Any],
    ) -> str:
        """Emit a Lean theorem for a deppy ``@check`` (inline assertion).

        Parameters
        ----------
        check_text:
            The assertion predicate.
        context:
            Dict with optional ``"variables"``, ``"function"`` keys.
        """
        self._counter += 1
        variables = context.get("variables", {})
        func = context.get("function", "anon")
        prop = self._ref.translate_predicate(check_text, variables)
        lean_func = _lean_ident(func)

        var_decls = ""
        if variables:
            parts = [f"({_lean_ident(n)} : {_BASE_TYPE_MAP.get(t, t)})"
                      for n, t in variables.items()]
            var_decls = "\n  ".join([""] + parts)

        thm = (
            f"namespace {self.module_name}\n\n"
            f"theorem {lean_func}_check_{self._counter}{var_decls} :\n"
            f"  {prop} := by\n"
            f"  sorry {_lean_comment('check: ' + check_text)}\n\n"
            f"end {self.module_name}"
        )
        self._emitted.append(thm)
        return thm

    def emit_hole_correctness(
        self,
        hole_text: str,
        synthesized_code: str,
        expected_type: str,
    ) -> str:
        """Emit a Lean theorem asserting a synthesised hole is correct.

        Parameters
        ----------
        hole_text:
            The original ``??`` hole specification.
        synthesized_code:
            A string describing what was synthesized.
        expected_type:
            The expected Lean type for the synthesised term.
        """
        self._counter += 1
        lean_type = _BASE_TYPE_MAP.get(expected_type, _lean_ident(expected_type))

        thm = (
            f"namespace {self.module_name}\n\n"
            f"{_lean_line_comment('Hole: ' + hole_text)}\n"
            f"{_lean_line_comment('Synthesized: ' + synthesized_code)}\n"
            f"theorem hole_correct_{self._counter} :\n"
            f"  ∃ (f : {lean_type}), True {_lean_comment('placeholder for spec')} := by\n"
            f"  exact ⟨sorry, trivial⟩\n\n"
            f"end {self.module_name}"
        )
        self._emitted.append(thm)
        return thm

    def emit_equivalence(
        self,
        func1: str,
        func2: str,
    ) -> str:
        """Emit a Lean theorem asserting behavioural equivalence.

        Parameters
        ----------
        func1:
            Name of the first function.
        func2:
            Name of the second function.

        Returns
        -------
        str
            A Lean 4 ``theorem`` stating ``∀ x, f1 x = f2 x``.
        """
        self._counter += 1
        f1 = _lean_ident(func1)
        f2 = _lean_ident(func2)

        thm = (
            f"namespace {self.module_name}\n\n"
            f"{_lean_line_comment(f'Behavioral equivalence: {func1} ≡ {func2}')}\n"
            f"theorem equiv_{f1}_{f2}_{self._counter}\n"
            f"  {{α : Type}} {{β : Type}}\n"
            f"  ({f1} {f2} : α → β) :\n"
            f"  (∀ (x : α), {f1} x = {f2} x) := by\n"
            f"  sorry {_lean_comment(f'equivalence of {func1} and {func2}')}\n\n"
            f"end {self.module_name}"
        )
        self._emitted.append(thm)
        return thm

    def emit_all(self, obligations: List[Dict[str, Any]]) -> str:
        """Batch-emit a list of obligation dicts, grouped by function.

        Each obligation dict must have a ``"kind"`` key (one of
        ``"contract"``, ``"guarantee"``, ``"assumption"``, ``"check"``,
        ``"hole"``, ``"equivalence"``).

        Returns
        -------
        str
            A complete Lean 4 file section.
        """
        # Group by function
        by_func: Dict[str, List[Dict[str, Any]]] = {}
        for ob in obligations:
            func = ob.get("function", "_toplevel")
            by_func.setdefault(func, []).append(ob)

        sections: List[str] = []
        header = (
            f"/-!\n"
            f"  Auto-generated proof obligations for module `{self.module_name}`.\n"
            f"  Generated by deppy Lean translation layer.\n"
            f"-/\n"
        )
        sections.append(header)

        for func_name, obs in by_func.items():
            sections.append(f"-- ── {func_name} ──")
            for ob in obs:
                kind = ob.get("kind", "check")
                section = self._emit_single(kind, ob)
                sections.append(section)
            sections.append("")

        return "\n\n".join(sections)

    # ── private helpers ───────────────────────────────────────────────

    def _emit_single(self, kind: str, ob: Dict[str, Any]) -> str:
        """Dispatch a single obligation dict."""
        if kind == "contract":
            return self.emit_function_contract(
                ob.get("function", "f"),
                ob.get("params", []),
                ob.get("pre", ""),
                ob.get("post", ""),
            )
        if kind == "guarantee":
            return self.emit_guarantee(
                ob.get("function", "f"),
                ob.get("text", ""),
                ob.get("structural", None),
            )
        if kind == "assumption":
            return self.emit_assumption(
                ob.get("text", ""),
                ob.get("context", {}),
            )
        if kind == "check":
            return self.emit_check(
                ob.get("text", ""),
                ob.get("context", {}),
            )
        if kind == "hole":
            return self.emit_hole_correctness(
                ob.get("hole", "??"),
                ob.get("synthesized", ""),
                ob.get("expected_type", "Any"),
            )
        if kind == "equivalence":
            return self.emit_equivalence(
                ob.get("func1", "f"),
                ob.get("func2", "g"),
            )
        logger.warning("Unknown obligation kind %r, emitting as check", kind)
        return self.emit_check(ob.get("text", "True"), ob.get("context", {}))

    def _parse_params(self, params: List[Dict[str, str]]) -> List[_ParamInfo]:
        """Parse obligation param dicts into _ParamInfo objects."""
        result: List[_ParamInfo] = []
        for p in params:
            name = p.get("name", f"arg{len(result)}")
            py_type = p.get("type", "Any")
            lean_type = _BASE_TYPE_MAP.get(py_type, _lean_ident(py_type))
            default = p.get("default")
            result.append(_ParamInfo(
                name=_lean_ident(name),
                lean_type=lean_type,
                default=default,
            ))
        return result

    def _format_param_decls(self, params: List[_ParamInfo]) -> str:
        """Format parameter declarations for a Lean theorem."""
        parts = [f"({p.name} : {p.lean_type})" for p in params]
        return " ".join(parts)

# ════════════════════════════════════════════════════════════════════════
# LeanTacticSuggester
# ════════════════════════════════════════════════════════════════════════

class LeanTacticSuggester:
    """Heuristic suggestion of Lean 4 tactics for proof obligations.

    This is a best-effort helper.  It pattern-matches on the proposition
    structure and suggests an appropriate tactic or tactic combination.
    Complex proofs fall back to ``sorry``.

    Usage::

        s = LeanTacticSuggester()
        tactic = s.suggest_tactic("x + 1 > x")  # "omega"
        proof  = s.suggest_proof("theorem foo : 1 + 1 = 2 := by")
    """

    def __init__(self) -> None:
        self._rules: List[Tuple[str, _TacticRule]] = self._build_rules()

    # ── public API ────────────────────────────────────────────────────

    def suggest_tactic(self, prop: str) -> str:
        """Suggest a single Lean 4 tactic for the given proposition.

        Parameters
        ----------
        prop:
            A Lean 4 ``Prop`` expression.

        Returns
        -------
        str
            A tactic string such as ``"omega"``, ``"decide"``, etc.
        """
        prop = prop.strip()
        for _name, rule in self._rules:
            tactic = rule(prop)
            if tactic is not None:
                return tactic
        return "sorry /- needs manual proof -/"

    def suggest_proof(self, theorem_stmt: str) -> str:
        """Suggest a complete Lean 4 proof for a theorem statement.

        Parameters
        ----------
        theorem_stmt:
            A Lean 4 ``theorem`` or ``lemma`` statement, possibly
            ending with ``by``.

        Returns
        -------
        str
            The theorem with a proof body appended.
        """
        # Extract the proposition after ':'
        prop = self._extract_prop(theorem_stmt)
        tactic = self.suggest_tactic(prop)

        # Build the proof
        stmt = theorem_stmt.rstrip()
        if not stmt.endswith("by"):
            if stmt.endswith(":="):
                stmt += " by"
            else:
                stmt += " := by"

        return f"{stmt}\n  {tactic}"

    def suggest_tactic_sequence(self, prop: str) -> List[str]:
        """Suggest a sequence of tactics (for multi-step proofs).

        Returns
        -------
        List[str]
            Ordered list of tactic strings.
        """
        prop = prop.strip()
        tactics: List[str] = []

        # Conjunction: split then solve each branch
        if "∧" in prop:
            tactics.append("constructor")
            branches = self._split_conjunction(prop)
            for branch in branches:
                t = self.suggest_tactic(branch)
                tactics.append(f"· {t}")
            return tactics

        # Disjunction introduction
        if "∨" in prop:
            tactics.append("left")
            # Try the left branch
            left_prop = prop.split("∨")[0].strip().strip("()")
            t = self.suggest_tactic(left_prop)
            tactics.append(t)
            return tactics

        # Existential
        if prop.startswith("∃"):
            tactics.append("use sorry /- provide witness -/")
            return tactics

        # Implication
        if "→" in prop:
            tactics.append("intro h")
            # Get the conclusion
            parts = prop.rsplit("→", 1)
            if len(parts) == 2:
                conclusion = parts[1].strip()
                t = self.suggest_tactic(conclusion)
                tactics.append(t)
            return tactics

        # Single tactic fallback
        tactics.append(self.suggest_tactic(prop))
        return tactics

    def suggest_tactic_with_confidence(self, prop: str) -> Tuple[str, float]:
        """Suggest a tactic alongside a confidence score (0–1).

        Returns
        -------
        Tuple[str, float]
            (tactic, confidence).
        """
        tactic = self.suggest_tactic(prop)
        if tactic == "sorry /- needs manual proof -/":
            return tactic, 0.0
        if tactic in ("omega", "decide", "simp", "trivial", "rfl"):
            return tactic, 0.9
        if "simp" in tactic:
            return tactic, 0.7
        if "constructor" in tactic:
            return tactic, 0.6
        if "induction" in tactic:
            return tactic, 0.5
        return tactic, 0.4

    # ── private: rule table ───────────────────────────────────────────

    def _build_rules(self) -> List[Tuple[str, _TacticRule]]:
        """Build the ordered list of (name, rule) pairs."""
        return [
            ("trivial_true", self._rule_trivial_true),
            ("rfl_equality", self._rule_rfl),
            ("numeric_equality", self._rule_numeric_eq),
            ("omega_linear", self._rule_omega),
            ("decide_bool", self._rule_decide),
            ("simp_arith", self._rule_simp_arith),
            ("simp_list", self._rule_simp_list),
            ("simp_nat", self._rule_simp_nat),
            ("constructor_and", self._rule_constructor_and),
            ("left_or", self._rule_left_or),
            ("intro_arrow", self._rule_intro),
            ("existential", self._rule_existential),
            ("induction_nat", self._rule_induction_nat),
            ("induction_list", self._rule_induction_list),
            ("cases_sum", self._rule_cases_sum),
            ("cases_option", self._rule_cases_option),
            ("ext_funext", self._rule_funext),
            ("ring_arith", self._rule_ring),
            ("norm_num", self._rule_norm_num),
            ("contradiction", self._rule_contradiction),
            ("exact_trivial", self._rule_exact_trivial),
        ]

    # ── private: individual rules ─────────────────────────────────────

    def _rule_trivial_true(self, prop: str) -> Optional[str]:
        if prop in ("True", "true", "⊤"):
            return "trivial"
        return None

    def _rule_rfl(self, prop: str) -> Optional[str]:
        pair = _split_binary(prop, "=")
        if pair is not None:
            lhs, rhs = pair
            if lhs.strip() == rhs.strip():
                return "rfl"
        return None

    def _rule_numeric_eq(self, prop: str) -> Optional[str]:
        pair = _split_binary(prop, "=")
        if pair is not None:
            lhs, rhs = pair
            if _is_numeric(lhs) and _is_numeric(rhs):
                return "norm_num"
        return None

    def _rule_omega(self, prop: str) -> Optional[str]:
        """Linear integer arithmetic → omega."""
        if any(tok in prop for tok in _ARITH_KEYWORDS):
            if "∀" not in prop and "∃" not in prop:
                # Only simple inequalities / equalities over ints
                if re.search(r"\d", prop):
                    return "omega"
        return None

    def _rule_decide(self, prop: str) -> Optional[str]:
        """Decidable propositions → decide."""
        if any(tok in prop for tok in _DECIDABLE_KEYWORDS):
            if "∀" not in prop and "∃" not in prop and "sorry" not in prop:
                if len(prop) < 80:
                    return "decide"
        return None

    def _rule_simp_arith(self, prop: str) -> Optional[str]:
        """Arithmetic simplification."""
        if any(op in prop for op in ["+", "-", "*", "^"]):
            if "List" not in prop and "Array" not in prop:
                return "simp [Nat.add_comm, Nat.mul_comm, Nat.sub_self]"
        return None

    def _rule_simp_list(self, prop: str) -> Optional[str]:
        """List simplification."""
        if any(kw in prop for kw in ["List", "length", "get!", "map", "filter"]):
            return "simp [List.length, List.get!, List.map, List.filter]"
        return None

    def _rule_simp_nat(self, prop: str) -> Optional[str]:
        """Nat-specific simplification."""
        if "Nat" in prop:
            return "simp [Nat.lt_iff_add_one_le, Nat.succ_eq_add_one]"
        return None

    def _rule_constructor_and(self, prop: str) -> Optional[str]:
        """Conjunction → constructor."""
        if "∧" in prop and "∨" not in prop:
            return "constructor <;> sorry"
        return None

    def _rule_left_or(self, prop: str) -> Optional[str]:
        """Disjunction → try left."""
        if "∨" in prop and "∧" not in prop:
            return "left; sorry"
        return None

    def _rule_intro(self, prop: str) -> Optional[str]:
        """Implication → intro."""
        if "→" in prop and not prop.startswith("∀"):
            return "intro h; sorry"
        return None

    def _rule_existential(self, prop: str) -> Optional[str]:
        """Existential → use + sorry."""
        if prop.startswith("∃"):
            return "use sorry /- provide witness -/"
        return None

    def _rule_induction_nat(self, prop: str) -> Optional[str]:
        """Nat induction."""
        if "Nat.rec" in prop or ("∀" in prop and "Nat" in prop):
            m = re.search(r"∀\s*\((\w+)\s*:\s*Nat\)", prop)
            if m:
                var = m.group(1)
                return f"induction {var} with\n  | zero => sorry\n  | succ n ih => sorry"
        return None

    def _rule_induction_list(self, prop: str) -> Optional[str]:
        """List induction."""
        if "∀" in prop and "List" in prop:
            m = re.search(r"∀\s*\((\w+)\s*:\s*List", prop)
            if m:
                var = m.group(1)
                return f"induction {var} with\n  | nil => sorry\n  | cons hd tl ih => sorry"
        return None

    def _rule_cases_sum(self, prop: str) -> Optional[str]:
        """Sum elimination."""
        if "Sum" in prop:
            return "cases h with\n  | inl a => sorry\n  | inr b => sorry"
        return None

    def _rule_cases_option(self, prop: str) -> Optional[str]:
        """Option elimination."""
        if "Option" in prop:
            return "cases h with\n  | none => sorry\n  | some val => sorry"
        return None

    def _rule_funext(self, prop: str) -> Optional[str]:
        """Function extensionality."""
        pair = _split_binary(prop, "=")
        if pair is not None:
            lhs, rhs = pair
            if "→" in lhs or "→" in rhs or ("fun " in lhs and "fun " in rhs):
                return "funext x; sorry"
        return None

    def _rule_ring(self, prop: str) -> Optional[str]:
        """Ring arithmetic."""
        if "^" in prop or ("*" in prop and "+" in prop):
            if "List" not in prop:
                return "ring"
        return None

    def _rule_norm_num(self, prop: str) -> Optional[str]:
        """Numeric normalisation."""
        if re.search(r"\d\s*[+\-*/]\s*\d", prop):
            return "norm_num"
        return None

    def _rule_contradiction(self, prop: str) -> Optional[str]:
        """False goal → contradiction / exact absurd."""
        if prop in ("False", "false", "⊥"):
            return "contradiction"
        return None

    def _rule_exact_trivial(self, prop: str) -> Optional[str]:
        """Trivial existence / unit."""
        if prop in ("Unit", "PUnit", "⟨⟩"):
            return "exact ⟨⟩"
        return None

    # ── private: helper extractors ────────────────────────────────────

    def _extract_prop(self, theorem_stmt: str) -> str:
        """Extract the proposition from a theorem statement."""
        # Look for the part after ':' and before ':=' or 'by'
        m = re.search(r":\s*\n?\s*(.+?)(?:\s*:=\s*by|\s*by|\s*:=|\s*$)", theorem_stmt, re.DOTALL)
        if m:
            return m.group(1).strip()
        # Fallback: after last ':'
        idx = theorem_stmt.rfind(":")
        if idx >= 0:
            return theorem_stmt[idx + 1:].strip().rstrip("by").rstrip(":=").strip()
        return theorem_stmt

    def _split_conjunction(self, prop: str) -> List[str]:
        """Split a conjunction into its branches."""
        branches: List[str] = []
        depth = 0
        current: List[str] = []
        i = 0
        while i < len(prop):
            ch = prop[i]
            if ch in "([{":
                depth += 1
                current.append(ch)
            elif ch in ")]}":
                depth -= 1
                current.append(ch)
            elif ch == "∧" and depth == 0:
                branches.append("".join(current).strip())
                current = []
            else:
                current.append(ch)
            i += 1
        tail = "".join(current).strip()
        if tail:
            branches.append(tail)
        return [_strip_outer_parens(b) for b in branches]

# Type alias for tactic rules
_TacticRule = type(LeanTacticSuggester._rule_trivial_true)
