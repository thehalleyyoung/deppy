"""
Generate CCTT axiom files from the Mathlib theorem catalog.

Reads the JSON catalog produced by extract_all_mathlib.py, translates each
theorem's proposition into an OTerm rewrite rule, and writes per-category
Python axiom modules into new_src/cctt/axioms/mathlib/.

Usage:
    PYTHONPATH=new_src python3 -m cctt.mathlib_bridge.generate_all_axioms
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import textwrap
import time
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════════════════════════
#  Lean proposition → OTerm rewrite rule translation
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class RewriteRule:
    """A translated OTerm rewrite rule from a Lean theorem."""
    theorem_name: str         # fully qualified Lean name
    lean_prop: str            # original Lean proposition
    lhs_code: str             # Python code for LHS OTerm pattern
    rhs_code: str             # Python code for RHS OTerm pattern
    match_code: str           # Python code for pattern matching
    category: str
    subcategory: str
    is_simp: bool
    is_equality: bool         # is an equational rewrite
    relevance: float          # 0.0 - 1.0
    bidirectional: bool       # can apply in both directions
    file_path: str


@dataclass
class UntranslatableTheorem:
    """A theorem that couldn't be translated to OTerm rewrites."""
    theorem_name: str
    lean_prop: str
    reason: str
    category: str
    file_path: str


# ═══════════════════════════════════════════════════════════════════════════════
#  Lean expression patterns for translation
# ═══════════════════════════════════════════════════════════════════════════════

# Common Lean operations → OTerm operation name
_LEAN_TO_OTERM_OPS: Dict[str, str] = {
    # Arithmetic
    "HAdd.hAdd": "+", "Add.add": "+", "Nat.add": "+", "Int.add": "+",
    "HMul.hMul": "*", "Mul.mul": "*", "Nat.mul": "*", "Int.mul": "*",
    "HSub.hSub": "-", "Sub.sub": "-", "Nat.sub": "-", "Int.sub": "-",
    "HDiv.hDiv": "//", "Div.div": "//", "Nat.div": "//", "Int.div": "//",
    "HMod.hMod": "%", "Mod.mod": "%", "Nat.mod": "%", "Int.mod": "%",
    "HPow.hPow": "**", "Pow.pow": "**",
    "Neg.neg": "neg", "Int.neg": "neg",
    "Abs.abs": "abs", "Int.natAbs": "abs",
    "Nat.succ": "succ", "Nat.pred": "pred",
    "Nat.zero": "0", "Nat.one": "1",
    "max": "max", "min": "min", "Max.max": "max", "Min.min": "min",
    "Nat.gcd": "gcd", "Nat.lcm": "lcm",

    # List operations
    "List.map": "map", "List.filter": "filter", "List.filterMap": "filter_map",
    "List.foldl": "foldl", "List.foldr": "foldr",
    "List.append": "concat", "HAppend.hAppend": "concat", "List.cons": "cons",
    "List.nil": "nil", "List.length": "len",
    "List.reverse": "reverse", "List.head": "head", "List.tail": "tail",
    "List.take": "take", "List.drop": "drop",
    "List.zip": "zip", "List.zipWith": "zip_with",
    "List.join": "flatten", "List.bind": "flat_map",
    "List.get": "get", "List.get!": "get", "List.get?": "get_opt",
    "List.set": "set_at", "List.indexOf": "index_of",
    "List.contains": "contains", "List.elem": "elem",
    "List.replicate": "replicate", "List.range": "range",
    "List.sum": "sum", "List.prod": "prod",
    "List.maximum": "max", "List.minimum": "min",
    "List.sort": "sort", "List.mergeSort": "sort",
    "List.isPerm": "is_perm", "List.Perm": "perm",
    "List.Nodup": "nodup", "List.dedup": "dedup",
    "List.enum": "enumerate", "List.enumFrom": "enumerate_from",
    "List.intercalate": "join", "List.intersperse": "intersperse",
    "List.transpose": "transpose",
    "List.iota": "iota", "List.findIdx": "find_index",
    "List.find?": "find", "List.partition": "partition",
    "List.span": "span", "List.splitAt": "split_at",
    "List.lookup": "lookup", "List.eraseIdx": "erase_idx",
    "List.erase": "erase", "List.insert": "insert",
    "List.Sublist": "sublist", "List.IsPrefix": "is_prefix",
    "List.IsSuffix": "is_suffix",
    "List.rotateLeft": "rotate",
    "List.getLast": "last",
    "List.head!": "head", "List.getLast!": "last",
    "List.Sorted": "is_sorted",

    # Bool
    "Bool.and": "and", "Bool.or": "or", "Bool.not": "not",
    "Bool.xor": "xor", "Bool.true": "True", "Bool.false": "False",
    "band": "and", "bor": "or", "bnot": "not",

    # Function
    "Function.comp": "comp", "Function.id": "id",
    "Function.Injective": "injective", "Function.Surjective": "surjective",
    "Function.Bijective": "bijective",
    "Function.const": "const",

    # Logic
    "Not": "not", "And": "and", "Or": "or",
    "Iff": "iff", "True": "True", "False": "False",

    # Option
    "Option.some": "some", "Option.none": "none",
    "Option.map": "option_map", "Option.bind": "option_bind",
    "Option.getD": "option_get_or", "Option.get!": "option_get",
    "Option.isSome": "is_some", "Option.isNone": "is_none",

    # Prod
    "Prod.fst": "fst", "Prod.snd": "snd",
    "Prod.mk": "pair", "Prod.swap": "swap",

    # Set
    "Set.union": "union", "Set.inter": "inter",
    "Set.diff": "diff", "Set.compl": "complement",
    "Set.mem": "in", "Set.subset": "subset",
    "Set.empty": "empty_set", "Set.univ": "univ_set",
    "Set.insert": "set_insert",
    "Finset.card": "len", "Finset.sum": "sum", "Finset.prod": "prod",
    "Finset.filter": "filter", "Finset.map": "map",
    "Finset.union": "union", "Finset.inter": "inter",
    "Finset.range": "range",

    # String
    "String.length": "len", "String.append": "concat",
    "String.push": "append_char", "String.mk": "str",

    # Multiset
    "Multiset.map": "map", "Multiset.filter": "filter",
    "Multiset.fold": "fold", "Multiset.card": "len",
    "Multiset.sum": "sum",

    # Order
    "LE.le": "<=", "LT.lt": "<", "GE.ge": ">=", "GT.gt": ">",
    "Eq": "==",

    # Category
    "Functor.map": "fmap",
    "CategoryTheory.Functor.map": "fmap",
    "CategoryTheory.NatTrans.app": "nat_trans_app",

    # Algebra
    "CommMonoid": "comm_monoid", "CommGroup": "comm_group",
    "AddCommMonoid": "add_comm_monoid",
}

# Lean infix operators
_LEAN_INFIX: Dict[str, str] = {
    "=": "==", "≠": "!=", "≤": "<=", "≥": ">=", "<": "<", ">": ">",
    "∧": "and", "∨": "or", "↔": "iff", "→": "implies",
    "++": "concat", "+": "+", "*": "*", "-": "-", "/": "//",
    "∈": "in", "∉": "not_in", "⊆": "subset", "⊂": "strict_subset",
    "∪": "union", "∩": "inter", "×": "product",
    "∘": "comp", "⬝": "trans", "▸": "subst",
    "^": "**",
}


def _sanitize_name(name: str) -> str:
    """Make a Lean name safe for Python identifier use."""
    # Common Unicode replacements
    _UNICODE_MAP = {
        '.': '_', "'": '_prime', '!': '_bang', '?': '_q',
        '₀': '_0', '₁': '_1', '₂': '_2', '₃': '_3', '₄': '_4',
        '₅': '_5', '₆': '_6', '₇': '_7', '₈': '_8', '₉': '_9',
        'α': 'a', 'β': 'b', 'γ': 'g', 'δ': 'd', 'ε': 'e',
        'ζ': 'z', 'η': 'eta', 'θ': 'th', 'ι': 'i', 'κ': 'k',
        'λ': 'lam', 'μ': 'mu', 'ν': 'nu', 'ξ': 'xi', 'π': 'pi',
        'ρ': 'rho', 'σ': 'sig', 'τ': 'tau', 'υ': 'ups', 'φ': 'phi',
        'χ': 'chi', 'ψ': 'psi', 'ω': 'omega',
        'Α': 'A', 'Β': 'B', 'Γ': 'G', 'Δ': 'D',
        'Σ': 'Sig', 'Π': 'Pi', 'Ω': 'Omega',
        '→': '_to_', '←': '_from_', '↔': '_iff_',
        '⟨': '', '⟩': '', '⟪': '', '⟫': '',
        '∀': 'forall_', '∃': 'exists_',
        '¬': 'not_', '≤': 'le_', '≥': 'ge_',
        '<': 'lt_', '>': 'gt_', '≠': 'ne_',
        '∧': 'and_', '∨': 'or_',
        '∈': 'in_', '∉': 'notin_',
        '⊆': 'sub_', '⊂': 'ssub_', '⊇': 'sup_',
        '∪': 'union_', '∩': 'inter_',
        '∘': 'comp_', '×': 'times_',
        '+': 'plus_', '-': 'minus_', '*': 'star_', '/': 'slash_',
        '=': 'eq_', '^': 'pow_', '~': 'tilde_',
        '#': 'hash_', '@': 'at_', '&': 'amp_',
        '|': 'pipe_', '\\': 'bsl_', ':': 'colon_',
        ';': '_', ',': '_', ' ': '_',
        '𝟘': '0', '𝟙': '1', '𝟚': '2', '𝟛': '3', '𝟜': '4',
        '⊥': 'bot', '⊤': 'top', '∅': 'empty',
        '∞': 'inf', '†': 'dag', '‡': 'ddag',
        '⁻': 'inv', '⁺': 'pos',
    }
    result = []
    for ch in name:
        if ch in _UNICODE_MAP:
            result.append(_UNICODE_MAP[ch])
        elif ch.isascii() and (ch.isalnum() or ch == '_'):
            result.append(ch)
        elif ch.isdigit():
            # Unicode digit (like ₅) - convert to int
            try:
                result.append(f'_{int(ch)}')
            except ValueError:
                result.append('_')
        else:
            result.append('_')
    name_out = ''.join(result)
    # Collapse multiple underscores
    while '__' in name_out:
        name_out = name_out.replace('__', '_')
    # Strip leading/trailing underscores
    name_out = name_out.strip('_')
    # Ensure it starts with a letter or underscore
    if name_out and not (name_out[0].isalpha() or name_out[0] == '_'):
        name_out = '_' + name_out
    if not name_out:
        name_out = '_unknown'
    return name_out


def _extract_equality(prop: str) -> Optional[Tuple[str, str]]:
    """Try to split an equality proposition into LHS and RHS.

    Returns (lhs, rhs) if the proposition is of the form LHS = RHS.
    """
    # Remove leading quantifiers: ∀ x, ... or ∀ {x : T}, ...
    cleaned = prop.strip()
    while cleaned.startswith('∀') or cleaned.startswith('∀'):
        comma_idx = cleaned.find(',')
        if comma_idx < 0:
            break
        cleaned = cleaned[comma_idx + 1:].strip()

    # Remove leading hypotheses: h : P → ...
    while '→' in cleaned:
        arrow_idx = cleaned.find('→')
        # Check if this is the main implication or a hypothesis
        # Heuristic: if there's an = after the arrow, the arrow is a hypothesis separator
        rest = cleaned[arrow_idx + 1:].strip()
        if '=' in rest:
            cleaned = rest
        else:
            break

    # Now look for top-level = sign
    depth = 0
    for i, ch in enumerate(cleaned):
        if ch in '({[⟨':
            depth += 1
        elif ch in ')}]⟩':
            depth -= 1
        elif ch == '=' and depth == 0 and i > 0:
            # Make sure it's not == or /= or ≠
            if (i + 1 < len(cleaned) and cleaned[i + 1] == '='):
                continue
            if i > 0 and cleaned[i - 1] in '!<>/≤≥≠':
                continue
            lhs = cleaned[:i].strip()
            rhs = cleaned[i + 1:].strip()
            if lhs and rhs:
                return (lhs, rhs)
    return None


def _extract_iff(prop: str) -> Optional[Tuple[str, str]]:
    """Try to split an iff proposition into LHS and RHS."""
    cleaned = prop.strip()
    while cleaned.startswith('∀'):
        comma_idx = cleaned.find(',')
        if comma_idx < 0:
            break
        cleaned = cleaned[comma_idx + 1:].strip()

    depth = 0
    for i, ch in enumerate(cleaned):
        if ch in '({[⟨':
            depth += 1
        elif ch in ')}]⟩':
            depth -= 1
        elif ch == '↔' and depth == 0:
            lhs = cleaned[:i].strip()
            rhs = cleaned[i + 1:].strip()
            if lhs and rhs:
                return (lhs, rhs)
    return None


def _lean_expr_to_oterm_code(expr: str) -> str:
    """Convert a Lean expression string to Python OTerm constructor code.

    This is a best-effort translation that handles common patterns.
    All output is guaranteed to be valid Python with ASCII-safe strings.
    """
    expr = expr.strip()
    if not expr:
        return 'OVar("_")'

    # Sanitize: replace non-ASCII chars that would cause Python syntax errors
    # We keep the logic flow but ensure variable/op names are safe
    def _safe_str(s: str) -> str:
        """Ensure string is safe for embedding in Python source code."""
        return _sanitize_name(s)

    # Handle parenthesized expressions
    if expr.startswith('(') and expr.endswith(')'):
        inner = expr[1:-1].strip()
        depth = 0
        balanced = True
        for ch in inner:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            if depth < 0:
                balanced = False
                break
        if balanced and depth == 0:
            return _lean_expr_to_oterm_code(inner)

    # Handle literals
    if expr.isdigit():
        try:
            return f'OLit({int(expr)})'
        except ValueError:
            pass
    if expr == 'true' or expr == 'True':
        return 'OLit(True)'
    if expr == 'false' or expr == 'False':
        return 'OLit(False)'
    if expr.startswith('"') and expr.endswith('"'):
        # Ensure the string content is ASCII-safe
        safe_content = expr[1:-1].encode('ascii', 'replace').decode('ascii')
        return f'OLit("{safe_content}")'

    # Handle empty list
    if expr == '[]' or expr == 'List.nil':
        return 'OSeq(())'

    # Handle singleton list
    if expr.startswith('[') and expr.endswith(']'):
        inner = expr[1:-1].strip()
        if ',' not in inner:
            return f'OSeq(({_lean_expr_to_oterm_code(inner)},))'

    # Handle infix operators
    for lean_op, oterm_op in sorted(_LEAN_INFIX.items(), key=lambda x: -len(x[0])):
        # Find top-level infix
        depth = 0
        for i in range(len(expr)):
            ch = expr[i]
            if ch in '({[⟨':
                depth += 1
            elif ch in ')}]⟩':
                depth -= 1
            elif depth == 0 and expr[i:i+len(lean_op)] == lean_op:
                # Check it's surrounded by spaces (or at boundary)
                before_ok = (i == 0 or expr[i-1] in ' \t\n)')
                after_ok = (i + len(lean_op) >= len(expr) or
                           expr[i + len(lean_op)] in ' \t\n(')
                if before_ok and after_ok and i > 0:
                    lhs = expr[:i].strip()
                    rhs = expr[i+len(lean_op):].strip()
                    if lhs and rhs:
                        l_code = _lean_expr_to_oterm_code(lhs)
                        r_code = _lean_expr_to_oterm_code(rhs)
                        return f'OOp("{oterm_op}", ({l_code}, {r_code}))'

    # Handle function application: f a b c → OOp("f", (a, b, c))
    parts = _split_lean_app(expr)
    if len(parts) > 1:
        fn_name = parts[0].strip()
        # Look up known operations
        oterm_op = _LEAN_TO_OTERM_OPS.get(fn_name, None)
        if oterm_op is None:
            # Try partial match
            for k, v in _LEAN_TO_OTERM_OPS.items():
                if fn_name.endswith(k) or fn_name == k.split('.')[-1]:
                    oterm_op = v
                    break
        if oterm_op is None:
            oterm_op = _sanitize_name(fn_name)

        args_code = ', '.join(_lean_expr_to_oterm_code(a) for a in parts[1:])
        return f'OOp("{oterm_op}", ({args_code},))'

    # Handle negation
    if expr.startswith('¬') or expr.startswith('!'):
        inner = expr[1:].strip()
        return f'OOp("not", ({_lean_expr_to_oterm_code(inner)},))'

    # Simple variable
    clean_name = _sanitize_name(expr)
    return f'OVar("{clean_name}")'


def _split_lean_app(expr: str) -> List[str]:
    """Split a Lean application `f a b c` into [f, a, b, c].

    Handles parenthesized/bracketed sub-expressions.
    """
    parts: List[str] = []
    current: List[str] = []
    depth = 0
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch in '({[⟨':
            depth += 1
            current.append(ch)
        elif ch in ')}]⟩':
            depth -= 1
            current.append(ch)
        elif ch in ' \t' and depth == 0:
            token = ''.join(current).strip()
            if token:
                parts.append(token)
            current = []
        else:
            current.append(ch)
        i += 1
    token = ''.join(current).strip()
    if token:
        parts.append(token)
    return parts


def _translate_theorem(thm: dict) -> Optional[RewriteRule]:
    """Try to translate a theorem dict into a RewriteRule.

    Returns None if the theorem can't be translated.
    """
    prop = thm["proposition"]
    name = thm["name"]

    if not prop or len(prop) < 3:
        return None

    # Try equality
    eq_parts = _extract_equality(prop)
    if eq_parts:
        lhs_lean, rhs_lean = eq_parts
        try:
            lhs_code = _lean_expr_to_oterm_code(lhs_lean)
            rhs_code = _lean_expr_to_oterm_code(rhs_lean)
        except Exception:
            return None

        # Determine relevance based on category and simp status
        relevance = 0.3
        if thm.get("is_simp"):
            relevance += 0.3
        cat = thm.get("category", "other")
        if cat in ("list", "arithmetic", "boolean", "function", "logic", "string"):
            relevance += 0.2
        elif cat in ("algebra", "order"):
            relevance += 0.1
        relevance = min(relevance, 1.0)

        return RewriteRule(
            theorem_name=name,
            lean_prop=prop[:300],
            lhs_code=lhs_code,
            rhs_code=rhs_code,
            match_code="",  # filled in during code generation
            category=thm.get("category", "other"),
            subcategory=thm.get("subcategory", "general"),
            is_simp=thm.get("is_simp", False),
            is_equality=True,
            relevance=relevance,
            bidirectional=True,
            file_path=thm.get("file_path", ""),
        )

    # Try iff
    iff_parts = _extract_iff(prop)
    if iff_parts:
        lhs_lean, rhs_lean = iff_parts
        try:
            lhs_code = _lean_expr_to_oterm_code(lhs_lean)
            rhs_code = _lean_expr_to_oterm_code(rhs_lean)
        except Exception:
            return None

        relevance = 0.2
        if thm.get("is_simp"):
            relevance += 0.2
        cat = thm.get("category", "other")
        if cat in ("logic", "boolean"):
            relevance += 0.2
        relevance = min(relevance, 1.0)

        return RewriteRule(
            theorem_name=name,
            lean_prop=prop[:300],
            lhs_code=lhs_code,
            rhs_code=rhs_code,
            match_code="",
            category=thm.get("category", "other"),
            subcategory=thm.get("subcategory", "general"),
            is_simp=thm.get("is_simp", False),
            is_equality=False,
            relevance=relevance,
            bidirectional=True,
            file_path=thm.get("file_path", ""),
        )

    return None


# ═══════════════════════════════════════════════════════════════════════════════
#  Category → axiom file mapping
# ═══════════════════════════════════════════════════════════════════════════════

_CATEGORY_TO_FILE: Dict[str, str] = {
    "list": "ml_list",
    "array": "ml_array",
    "string": "ml_string",
    "boolean": "ml_bool",
    "arithmetic": "ml_nat_basic",
    "option": "ml_option",
    "product": "ml_prod",
    "finset": "ml_finset",
    "multiset": "ml_multiset",
    "set": "ml_set_basic",
    "logic": "ml_logic_basic",
    "function": "ml_function",
    "order": "ml_order",
    "algebra": "ml_algebra_group",
    "equivalence": "ml_equiv",
    "categorical": "ml_category",
    "topology": "ml_topology",
    "analysis": "ml_analysis",
    "combinatorics": "ml_combinatorics",
    "number_theory": "ml_number_theory",
    "set_theory": "ml_set_theory",
    "tactic": "ml_other",
    "other": "ml_other",
}

# Further subcategory splitting for large categories
_SUBCATEGORY_SPLITS: Dict[str, Dict[str, str]] = {
    "list": {
        "map": "ml_list_map",
        "filter": "ml_list_filter",
        "fold": "ml_list_fold",
        "sort": "ml_list_sort",
        "zip": "ml_list_zip",
        "append": "ml_list_basic",
        "reverse": "ml_list_misc",
        "length": "ml_list_basic",
        "take_drop": "ml_list_misc",
        "get": "ml_list_misc",
        "nil_cons": "ml_list_basic",
        "mem": "ml_list_basic",
    },
    "arithmetic": {
        "comm": "ml_nat_basic",
        "assoc": "ml_nat_basic",
        "zero_one": "ml_nat_basic",
        "neg_inv": "ml_int_basic",
        "succ_pred": "ml_nat_order",
        "div_mod": "ml_nat_div",
        "le_lt": "ml_nat_order",
        "max_min": "ml_nat_order",
        "abs": "ml_int_basic",
        "pow": "ml_nat_basic",
        "range": "ml_nat_basic",
    },
    "algebra": {
        "comm": "ml_algebra_ring",
        "assoc": "ml_algebra_group",
        "zero_one": "ml_algebra_ring",
        "neg_inv": "ml_algebra_group",
        "distrib": "ml_algebra_ring",
        "pow": "ml_algebra_ring",
    },
    "logic": {
        "not_and_or": "ml_logic_basic",
        "iff": "ml_logic_basic",
        "exists_forall": "ml_logic_quantifier",
    },
}


def _get_axiom_file(category: str, subcategory: str) -> str:
    """Determine which axiom file a theorem should go into."""
    if category in _SUBCATEGORY_SPLITS:
        subcat_map = _SUBCATEGORY_SPLITS[category]
        if subcategory in subcat_map:
            return subcat_map[subcategory]
    return _CATEGORY_TO_FILE.get(category, "ml_other")


# ═══════════════════════════════════════════════════════════════════════════════
#  Code generation for axiom files
# ═══════════════════════════════════════════════════════════════════════════════

def _generate_axiom_file(
    module_name: str,
    rules: List[RewriteRule],
    untranslatable: List[UntranslatableTheorem],
) -> str:
    """Generate the Python source for an axiom module."""
    # Derive human-readable title from module name
    title = module_name.replace("ml_", "Mathlib: ").replace("_", " ").title()

    # Sort rules by relevance (high first)
    rules.sort(key=lambda r: -r.relevance)

    # Cap rules per file to prevent enormous files
    MAX_RULES = 400
    truncated = len(rules) > MAX_RULES
    if truncated:
        rules = rules[:MAX_RULES]

    lines: List[str] = []

    # File header
    lines.append(f'"""{title} — auto-generated from Mathlib4.')
    lines.append(f"")
    lines.append(f"Contains {len(rules)} rewrite rules derived from Mathlib theorems.")
    if untranslatable:
        lines.append(f"Plus {len(untranslatable)} untranslatable theorems stored for reference.")
    if truncated:
        lines.append(f"(Truncated from more rules to keep file manageable)")
    lines.append(f'"""')
    lines.append("from __future__ import annotations")
    lines.append("")
    lines.append("from typing import Any, Dict, List, Optional, Set, Tuple")
    lines.append("")
    lines.append("from cctt.denotation import (")
    lines.append("    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,")
    lines.append("    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,")
    lines.append(")")
    lines.append("from cctt.path_search import FiberCtx")
    lines.append("")
    lines.append("")
    lines.append("# " + "═" * 60)
    lines.append("# Axiom metadata")
    lines.append("# " + "═" * 60)
    lines.append("")
    lines.append(f'AXIOM_NAME = "mathlib_{module_name}"')
    lines.append(f'AXIOM_CATEGORY = "mathlib"')
    lines.append(f"REQUIRES: List[str] = []")
    lines.append(f"COMPOSES_WITH: List[str] = []")
    lines.append("")
    lines.append("")
    lines.append("# " + "═" * 60)
    lines.append("# Pattern matching helpers")
    lines.append("# " + "═" * 60)
    lines.append("")
    lines.append("def _match_op(term: OTerm, name: str, arity: int = -1) -> Optional[Tuple[OTerm, ...]]:")
    lines.append('    """Match an OOp with given name and optional arity."""')
    lines.append("    if not isinstance(term, OOp):")
    lines.append("        return None")
    lines.append("    if term.name != name:")
    lines.append("        return None")
    lines.append("    if arity >= 0 and len(term.args) != arity:")
    lines.append("        return None")
    lines.append("    return term.args")
    lines.append("")
    lines.append("")
    lines.append("def _is_lit(term: OTerm, value: Any = None) -> bool:")
    lines.append('    """Check if term is a literal, optionally with a specific value."""')
    lines.append("    if not isinstance(term, OLit):")
    lines.append("        return False")
    lines.append("    if value is not None:")
    lines.append("        return term.value == value")
    lines.append("    return True")
    lines.append("")
    lines.append("")
    lines.append("def _is_empty_seq(term: OTerm) -> bool:")
    lines.append('    """Check if term is an empty sequence."""')
    lines.append("    return isinstance(term, OSeq) and len(term.elements) == 0")
    lines.append("")
    lines.append("")

    # Generate individual rewrite functions
    lines.append("# " + "═" * 60)
    lines.append(f"# Rewrite rules ({len(rules)} total)")
    lines.append("# " + "═" * 60)
    lines.append("")

    rule_fn_names: List[str] = []
    seen_names: Set[str] = set()

    for idx, rule in enumerate(rules):
        fn_name = f"_r{idx:04d}_{_sanitize_name(rule.theorem_name.split('.')[-1][:40])}"
        # Ensure uniqueness
        base_fn = fn_name
        counter = 0
        while fn_name in seen_names:
            counter += 1
            fn_name = f"{base_fn}_{counter}"
        seen_names.add(fn_name)
        rule_fn_names.append(fn_name)

        # Truncate lean prop for comment
        prop_comment = rule.lean_prop[:120].replace('\n', ' ').replace('"""', '...').replace('\\', '\\\\')

        # Escape the theorem name for use in strings
        safe_thm_name = rule.theorem_name.replace('\\', '\\\\').replace('"', '\\"')

        lines.append(f"def {fn_name}(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:")
        lines.append(f'    # Mathlib: {safe_thm_name}')
        lines.append(f"    # {prop_comment}")
        lines.append(f"    results: List[Tuple[OTerm, str]] = []")

        # Generate the matching and rewrite logic
        _generate_match_and_rewrite(lines, rule, "    ")

        lines.append(f"    return results")
        lines.append("")
        lines.append("")

    # Generate recognizes()
    lines.append("# " + "═" * 60)
    lines.append("# Public API")
    lines.append("# " + "═" * 60)
    lines.append("")
    lines.append("def recognizes(term: OTerm) -> bool:")
    lines.append(f'    """Quick check: could any {module_name} rule apply to term?"""')
    lines.append("    if isinstance(term, OOp):")

    # Collect all operation names from the rules
    op_names = set()
    for rule in rules:
        ops = re.findall(r'OOp\("([^"]+)"', rule.lhs_code)
        op_names.update(ops)
    if op_names:
        op_list = ', '.join(f'"{o}"' for o in sorted(op_names)[:50])
        lines.append(f"        return term.name in ({op_list},)")
    else:
        lines.append("        return True")
    lines.append("    return isinstance(term, (OFold, OCase, OSeq, OLit, OVar))")
    lines.append("")
    lines.append("")

    lines.append("def relevance_score(term: OTerm, other: OTerm) -> float:")
    lines.append(f'    """Relevance score for {module_name} axioms."""')
    lines.append("    if recognizes(term):")
    lines.append(f"        return {rules[0].relevance if rules else 0.3}")
    lines.append("    return 0.0")
    lines.append("")
    lines.append("")

    # Generate main apply()
    lines.append("def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:")
    lines.append(f'    """Apply all {module_name} rewrite rules to term."""')
    lines.append("    results: List[Tuple[OTerm, str]] = []")

    # Group rules by the primary operation they match
    lines.append("    if not recognizes(term):")
    lines.append("        return results")

    # Call each rule function
    for fn_name in rule_fn_names:
        lines.append(f"    results.extend({fn_name}(term, ctx))")
    lines.append("    return results")
    lines.append("")
    lines.append("")

    lines.append("def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:")
    lines.append(f'    """Apply inverse of {module_name} rewrite rules."""')
    lines.append("    return []  # Inverse direction not yet implemented")
    lines.append("")
    lines.append("")

    # Store untranslatable theorems as data
    if untranslatable:
        lines.append("# " + "═" * 60)
        lines.append("# Untranslatable theorems (stored for reference)")
        lines.append("# " + "═" * 60)
        lines.append("")
        lines.append("UNTRANSLATABLE_THEOREMS = [")
        for ut in untranslatable[:200]:  # Cap at 200 per file
            safe_name = _sanitize_name(ut.theorem_name)
            safe_prop = _sanitize_name(ut.lean_prop[:80])
            safe_reason = ut.reason.replace('"', "'").replace('\\', '')
            lines.append(f'    ("{safe_name}", "{safe_prop}", "{safe_reason}"),')
        lines.append("]")
    else:
        lines.append("UNTRANSLATABLE_THEOREMS: list = []")
    lines.append("")

    return "\n".join(lines)


def _generate_match_and_rewrite(
    lines: List[str],
    rule: RewriteRule,
    indent: str,
) -> None:
    """Generate pattern matching and rewrite code for a single rule."""
    lhs = rule.lhs_code
    rhs = rule.rhs_code
    # Escape theorem name for Python string literal
    thm_name = _sanitize_name(rule.theorem_name)

    # Parse the LHS to determine what kind of match we need
    # Strategy: match the outermost OTerm constructor

    if 'OOp("' in lhs:
        # Extract the operation name and arity
        m = re.match(r'OOp\("([^"]+)", \((.+)\)\)', lhs)
        if m:
            op_name = m.group(1)
            # Count args (rough heuristic)
            args_str = m.group(2)
            # Check if args are simple variables
            arg_parts = _count_top_level_args(args_str)
            n_args = len(arg_parts)

            lines.append(f'{indent}args = _match_op(term, "{op_name}", {n_args})')
            lines.append(f"{indent}if args is not None:")

            # Generate bindings for each argument
            _generate_arg_checks(lines, arg_parts, rhs, thm_name, indent + "    ", rule)
            return

    if 'OFold(' in lhs:
        lines.append(f"{indent}if isinstance(term, OFold):")
        lines.append(f'{indent}    try:')
        lines.append(f'{indent}        rhs = {rhs}')
        lines.append(f'{indent}        results.append((rhs, "Mathlib: {thm_name}"))')
        lines.append(f'{indent}    except Exception:')
        lines.append(f'{indent}        pass')
        return

    if 'OSeq(())' in lhs:
        lines.append(f"{indent}if _is_empty_seq(term):")
        lines.append(f'{indent}    try:')
        lines.append(f'{indent}        rhs = {rhs}')
        lines.append(f'{indent}        results.append((rhs, "Mathlib: {thm_name}"))')
        lines.append(f'{indent}    except Exception:')
        lines.append(f'{indent}        pass')
        return

    if 'OLit(' in lhs:
        m = re.match(r'OLit\((.+)\)', lhs)
        if m:
            val = m.group(1)
            lines.append(f"{indent}if _is_lit(term, {val}):")
            lines.append(f'{indent}    try:')
            lines.append(f'{indent}        rhs = {rhs}')
            lines.append(f'{indent}        results.append((rhs, "Mathlib: {thm_name}"))')
            lines.append(f'{indent}    except Exception:')
            lines.append(f'{indent}        pass')
            return

    # Fallback: try a simple structural match
    lines.append(f"{indent}try:")
    lines.append(f"{indent}    lhs_pattern = {lhs}")
    lines.append(f"{indent}    if term.canon() == lhs_pattern.canon():")
    lines.append(f'{indent}        rhs = {rhs}')
    lines.append(f'{indent}        results.append((rhs, "Mathlib: {thm_name}"))')
    lines.append(f"{indent}except Exception:")
    lines.append(f"{indent}    pass")


def _count_top_level_args(args_str: str) -> List[str]:
    """Count and extract top-level comma-separated arguments."""
    parts: List[str] = []
    depth = 0
    current: List[str] = []
    for ch in args_str:
        if ch in '({[':
            depth += 1
            current.append(ch)
        elif ch in ')}]':
            depth -= 1
            current.append(ch)
        elif ch == ',' and depth == 0:
            part = ''.join(current).strip()
            if part:
                parts.append(part)
            current = []
        else:
            current.append(ch)
    part = ''.join(current).strip()
    if part:
        parts.append(part)
    return parts


def _generate_arg_checks(
    lines: List[str],
    arg_parts: List[str],
    rhs_code: str,
    thm_name: str,
    indent: str,
    rule: RewriteRule,
) -> None:
    """Generate argument binding and RHS construction."""
    # Build variable bindings from LHS args
    bindings: Dict[str, str] = {}  # var_name -> access expression

    for i, arg in enumerate(arg_parts):
        arg = arg.strip()
        # Check if it's a simple variable: OVar("x")
        m = re.match(r'OVar\("(\w+)"\)', arg)
        if m:
            var_name = m.group(1)
            bindings[var_name] = f"args[{i}]"
        else:
            # Complex pattern - bind to a temporary
            bindings[f"_arg{i}"] = f"args[{i}]"

    # Substitute bindings into RHS
    rhs_substituted = rhs_code
    for var_name, access in bindings.items():
        # Replace OVar("var_name") with the access expression
        rhs_substituted = rhs_substituted.replace(f'OVar("{var_name}")', access)

    lines.append(f"{indent}try:")
    lines.append(f"{indent}    rhs = {rhs_substituted}")
    lines.append(f'{indent}    results.append((rhs, "Mathlib: {thm_name}"))')
    lines.append(f"{indent}except Exception:")
    lines.append(f"{indent}    pass")


# ═══════════════════════════════════════════════════════════════════════════════
#  Main generation pipeline
# ═══════════════════════════════════════════════════════════════════════════════

def generate_all_axioms(
    catalog_path: str,
    output_dir: str,
    verbose: bool = True,
) -> Dict[str, int]:
    """Read the catalog and generate all axiom files.

    Returns dict mapping module_name → number of rules.
    """
    if verbose:
        print(f"Loading catalog from {catalog_path}...")
    with open(catalog_path, 'r') as f:
        catalog = json.load(f)

    theorems = catalog["theorems"]
    if verbose:
        print(f"  {len(theorems)} theorems in catalog")

    # Translate all theorems
    if verbose:
        print("Translating theorems to OTerm rewrite rules...")

    rules_by_file: Dict[str, List[RewriteRule]] = defaultdict(list)
    untrans_by_file: Dict[str, List[UntranslatableTheorem]] = defaultdict(list)

    translated = 0
    untranslatable_count = 0
    t0 = time.time()

    for i, thm in enumerate(theorems):
        rule = _translate_theorem(thm)
        if rule:
            file_name = _get_axiom_file(rule.category, rule.subcategory)
            rules_by_file[file_name].append(rule)
            translated += 1
        else:
            file_name = _get_axiom_file(
                thm.get("category", "other"),
                thm.get("subcategory", "general"),
            )
            reason = "Not an equality or iff proposition"
            if not thm.get("proposition"):
                reason = "Empty proposition"
            elif len(thm.get("proposition", "")) < 3:
                reason = "Proposition too short"
            untrans_by_file[file_name].append(UntranslatableTheorem(
                theorem_name=thm["name"],
                lean_prop=thm.get("proposition", "")[:200],
                reason=reason,
                category=thm.get("category", "other"),
                file_path=thm.get("file_path", ""),
            ))
            untranslatable_count += 1

        if verbose and (i + 1) % 20000 == 0:
            elapsed = time.time() - t0
            print(f"  [{i+1}/{len(theorems)}] {translated} translated, "
                  f"{untranslatable_count} untranslatable, {elapsed:.1f}s")

    elapsed = time.time() - t0
    if verbose:
        print(f"\nTranslation complete in {elapsed:.1f}s:")
        print(f"  Translated:     {translated}")
        print(f"  Untranslatable: {untranslatable_count}")
        print(f"  Files:          {len(rules_by_file)}")

    # Generate axiom files
    os.makedirs(output_dir, exist_ok=True)

    if verbose:
        print(f"\nGenerating axiom files in {output_dir}/...")

    module_counts: Dict[str, int] = {}
    all_module_names: List[str] = []

    for file_name in sorted(set(list(rules_by_file.keys()) + list(untrans_by_file.keys()))):
        rules = rules_by_file.get(file_name, [])
        untrans = untrans_by_file.get(file_name, [])

        if not rules and not untrans:
            continue

        source = _generate_axiom_file(file_name, rules, untrans)
        file_path = os.path.join(output_dir, f"{file_name}.py")
        with open(file_path, 'w') as f:
            f.write(source)

        module_counts[file_name] = len(rules)
        all_module_names.append(file_name)

        if verbose:
            print(f"  {file_name}.py: {len(rules)} rules, "
                  f"{len(untrans)} untranslatable")

    # Also generate ml_untranslatable.py for all untranslatable theorems
    _generate_untranslatable_file(output_dir, untrans_by_file, verbose)

    # Generate __init__.py
    _generate_init(output_dir, all_module_names, module_counts, verbose)

    if verbose:
        total_rules = sum(module_counts.values())
        print(f"\n{'='*60}")
        print(f"Generation complete!")
        print(f"  Total axiom modules: {len(all_module_names)}")
        print(f"  Total rewrite rules: {total_rules}")
        print(f"  Output directory:    {output_dir}")

    return module_counts


def _generate_untranslatable_file(
    output_dir: str,
    untrans_by_file: Dict[str, List[UntranslatableTheorem]],
    verbose: bool,
) -> None:
    """Generate ml_untranslatable.py with all untranslatable theorems."""
    all_untrans: List[UntranslatableTheorem] = []
    for file_name, untrans in untrans_by_file.items():
        all_untrans.extend(untrans)

    lines: List[str] = []
    lines.append('"""Mathlib theorems that could not be translated to OTerm rewrites.')
    lines.append("")
    lines.append(f"Contains {len(all_untrans)} theorems stored for reference.")
    lines.append('"""')
    lines.append("from __future__ import annotations")
    lines.append("")
    lines.append("from typing import List, Tuple")
    lines.append("from cctt.denotation import OTerm")
    lines.append("from cctt.path_search import FiberCtx")
    lines.append("")
    lines.append("")
    lines.append('AXIOM_NAME = "mathlib_ml_untranslatable"')
    lines.append('AXIOM_CATEGORY = "mathlib"')
    lines.append("REQUIRES: List[str] = []")
    lines.append("COMPOSES_WITH: List[str] = []")
    lines.append("")
    lines.append("")
    lines.append("def recognizes(term: OTerm) -> bool:")
    lines.append("    return False")
    lines.append("")
    lines.append("")
    lines.append("def relevance_score(term: OTerm, other: OTerm) -> float:")
    lines.append("    return 0.0")
    lines.append("")
    lines.append("")
    lines.append("def apply(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:")
    lines.append("    return []")
    lines.append("")
    lines.append("")
    lines.append("def apply_inverse(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:")
    lines.append("    return []")
    lines.append("")
    lines.append("")
    lines.append(f"TOTAL_UNTRANSLATABLE = {len(all_untrans)}")
    lines.append("")
    lines.append("# Sample of untranslatable theorems (first 500):")
    lines.append("UNTRANSLATABLE_SAMPLE = [")
    for ut in all_untrans[:500]:
        safe_name = _sanitize_name(ut.theorem_name)
        safe_prop = _sanitize_name(ut.lean_prop[:80])
        safe_reason = ut.reason.replace('"', "'").replace('\\', '')
        lines.append(f'    ("{safe_name}", "{safe_prop}", "{safe_reason}"),')
    lines.append("]")
    lines.append("")

    path = os.path.join(output_dir, "ml_untranslatable.py")
    with open(path, 'w') as f:
        f.write("\n".join(lines))
    if verbose:
        print(f"  ml_untranslatable.py: {len(all_untrans)} theorems")


def _generate_init(
    output_dir: str,
    module_names: List[str],
    module_counts: Dict[str, int],
    verbose: bool,
) -> None:
    """Generate __init__.py for the mathlib axioms package."""
    total_rules = sum(module_counts.values())

    lines: List[str] = []
    lines.append('"""Mathlib4 axioms for CCTT — auto-generated.')
    lines.append("")
    lines.append(f"Total rewrite rules: {total_rules}")
    lines.append(f"Total axiom modules: {len(module_names)}")
    lines.append('"""')
    lines.append("from __future__ import annotations")
    lines.append("")
    lines.append("from typing import Dict, List, Tuple")
    lines.append("from cctt.denotation import OTerm")
    lines.append("from cctt.path_search import FiberCtx")
    lines.append("")
    lines.append("")
    lines.append("# Import all mathlib axiom modules")
    for name in sorted(module_names):
        lines.append(f"from cctt.axioms.mathlib import {name}")
    lines.append("from cctt.axioms.mathlib import ml_untranslatable")
    lines.append("")
    lines.append("")

    lines.append("_MATHLIB_MODULES = [")
    for name in sorted(module_names):
        lines.append(f"    {name},")
    lines.append("]")
    lines.append("")
    lines.append("")

    lines.append("# Ordered list of (name, apply_fn) pairs")
    lines.append("MATHLIB_AXIOMS: List[Tuple[str, object]] = [")
    lines.append("    (mod.AXIOM_NAME, mod.apply) for mod in _MATHLIB_MODULES")
    lines.append("]")
    lines.append("")
    lines.append("")

    lines.append("# Name → module registry")
    lines.append("MATHLIB_REGISTRY: Dict[str, object] = {")
    lines.append("    mod.AXIOM_NAME: mod for mod in _MATHLIB_MODULES")
    lines.append("}")
    lines.append("")
    lines.append("")

    lines.append("def all_mathlib_rewrites(term: OTerm, ctx: FiberCtx) -> List[Tuple[OTerm, str]]:")
    lines.append('    """Apply all Mathlib rewrite rules to term."""')
    lines.append("    results: List[Tuple[OTerm, str]] = []")
    lines.append("    for mod in _MATHLIB_MODULES:")
    lines.append("        if mod.recognizes(term):")
    lines.append("            results.extend(mod.apply(term, ctx))")
    lines.append("    return results")
    lines.append("")
    lines.append("")

    lines.append(f"TOTAL_RULES = {total_rules}")
    lines.append(f"TOTAL_MODULES = {len(module_names)}")
    lines.append("")
    lines.append("")

    lines.append('def report() -> str:')
    lines.append('    """Return a summary report of Mathlib axiom coverage."""')
    lines.append('    parts = [')
    lines.append(f'        f"Mathlib CCTT Axioms: {total_rules} rewrite rules in {len(module_names)} modules",')
    lines.append('    ]')
    lines.append('    for mod in _MATHLIB_MODULES:')
    lines.append('        name = mod.AXIOM_NAME')
    lines.append('        n_untrans = len(getattr(mod, "UNTRANSLATABLE_THEOREMS", []))')
    lines.append('        parts.append(f"  {name}: {n_untrans} untranslatable stored")')
    lines.append('    return "\\n".join(parts)')
    lines.append("")

    path = os.path.join(output_dir, "__init__.py")
    with open(path, 'w') as f:
        f.write("\n".join(lines))
    if verbose:
        print(f"  __init__.py: {len(module_names)} modules, {total_rules} total rules")


# ═══════════════════════════════════════════════════════════════════════════════
#  CLI
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="Generate CCTT axiom files from Mathlib catalog"
    )
    parser.add_argument(
        "--catalog",
        default=None,
        help="Path to mathlib_full_catalog.json",
    )
    parser.add_argument(
        "--output-dir",
        default=None,
        help="Output directory for axiom files",
    )
    args = parser.parse_args()

    if args.catalog is None:
        args.catalog = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "mathlib_full_catalog.json",
        )
    if args.output_dir is None:
        args.output_dir = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "..", "axioms", "mathlib",
        )
        args.output_dir = os.path.abspath(args.output_dir)

    generate_all_axioms(args.catalog, args.output_dir)


if __name__ == "__main__":
    main()
