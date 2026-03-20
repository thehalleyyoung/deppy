"""
Pillar 5 – Z3 proof extraction and translation to Lean 4 tactic scripts.

After Z3 proves an obligation UNSAT (negation), we extract the proof tree,
simplify it, and translate each Z3 proof rule into corresponding Lean tactics.
We also translate Z3 (SMT-LIB) formulae into Lean propositions.
"""
from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

# ---------------------------------------------------------------------------
# Optional Z3 dependency
# ---------------------------------------------------------------------------
try:
    import z3  # type: ignore

    _HAS_Z3 = True
except ImportError:  # pragma: no cover
    z3 = None  # type: ignore
    _HAS_Z3 = False


# --- Integration with existing deppy codebase ---
try:
    from deppy.solver.z3_encoder import Z3Encoder as _CoreZ3Encoder, encode_predicate
    from deppy.solver.z3_decoder import Z3Decoder as _CoreZ3Decoder, decode_model
    from deppy.solver.proof_certificate import ProofCertificate as _CoreProofCertificate
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False


def _safe_base(core_cls: type) -> type:
    """Return core_cls if it can be safely subclassed by a non-frozen dataclass."""
    import dataclasses as _dc
    if _dc.is_dataclass(core_cls) and getattr(
        getattr(core_cls, "__dataclass_params__", None), "frozen", False
    ):
        return object
    return core_cls

logger = logging.getLogger(__name__)

# ═══════════════════════════════════════════════════════════════════════════
# Z3ProofNode
# ═══════════════════════════════════════════════════════════════════════════


@dataclass
class Z3ProofNode:
    """A single node in a Z3 proof tree.

    Each node records the proof rule applied, the conclusion it establishes,
    and the premises (sub-proofs) it relies on.
    """

    rule: str
    conclusion: str
    premises: List[Z3ProofNode] = field(default_factory=list)
    annotations: Dict[str, str] = field(default_factory=dict)

    # ------------------------------------------------------------------

    @property
    def is_leaf(self) -> bool:
        return len(self.premises) == 0

    @property
    def depth(self) -> int:
        if not self.premises:
            return 0
        return 1 + max(p.depth for p in self.premises)

    @property
    def size(self) -> int:
        return 1 + sum(p.size for p in self.premises)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "rule": self.rule,
            "conclusion": self.conclusion,
            "premises": [p.to_dict() for p in self.premises],
            "annotations": self.annotations,
        }

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> Z3ProofNode:
        return Z3ProofNode(
            rule=d["rule"],
            conclusion=d["conclusion"],
            premises=[Z3ProofNode.from_dict(p) for p in d.get("premises", [])],
            annotations=d.get("annotations", {}),
        )

    def pretty(self, indent: int = 0) -> str:
        pad = "  " * indent
        lines = [f"{pad}[{self.rule}] {self.conclusion}"]
        for p in self.premises:
            lines.append(p.pretty(indent + 1))
        return "\n".join(lines)

    def __str__(self) -> str:
        return self.pretty()


# ═══════════════════════════════════════════════════════════════════════════
# Z3ProofExtractor
# ═══════════════════════════════════════════════════════════════════════════


class Z3ProofExtractor:
    """Extract a Z3 proof tree from a solver that has returned UNSAT.

    The extracted tree is a :class:`Z3ProofNode` hierarchy that mirrors the
    internal Z3 proof certificate.
    """

    # Z3 proof rules we recognise
    KNOWN_RULES: Set[str] = {
        "mp",
        "asserted",
        "hypothesis",
        "lemma",
        "unit-resolution",
        "rewrite",
        "monotonicity",
        "transitivity",
        "commutativity",
        "distributivity",
        "def-intro",
        "apply-def",
        "iff-true",
        "iff-false",
        "iff~",
        "nnf-pos",
        "nnf-neg",
        "sk",
        "quant-intro",
        "quant-inst",
        "pull-quant",
        "push-quant",
        "elim-unused",
        "der",
        "and-elim",
        "or-elim",
        "not-or-elim",
        "refl",
        "symm",
        "trans",
        "mp~",
        "proof-bind",
        "th-lemma",
        "hyper-res",
    }

    def __init__(self) -> None:
        self._seen: Dict[int, Z3ProofNode] = {}

    # ------------------------------------------------------------------
    # Public
    # ------------------------------------------------------------------

    def extract(self, solver_or_proof: Any) -> Optional[Z3ProofNode]:
        """Extract a proof tree from a Z3 solver (after UNSAT) or a Z3 proof object."""
        if not _HAS_Z3:
            logger.warning("Z3 not available – cannot extract proof")
            return None

        self._seen.clear()

        try:
            if isinstance(solver_or_proof, z3.Solver):
                proof_obj = solver_or_proof.proof()
            else:
                proof_obj = solver_or_proof

            if proof_obj is None:
                return None

            return self._extract_node(proof_obj)
        except Exception as exc:  # noqa: BLE001
            logger.warning("Proof extraction failed: %s", exc)
            return None

    def simplify(self, proof_tree: Z3ProofNode) -> Z3ProofNode:
        """Remove redundant nodes from the proof tree."""
        return self._simplify_node(proof_tree)

    # ------------------------------------------------------------------
    # Internal
    # ------------------------------------------------------------------

    def _extract_node(self, expr: Any) -> Z3ProofNode:
        """Recursively convert a Z3 proof expression into our tree."""
        eid = expr.get_id() if hasattr(expr, "get_id") else id(expr)
        if eid in self._seen:
            return self._seen[eid]

        rule = self._get_rule_name(expr)
        conclusion = str(expr.decl()) if hasattr(expr, "decl") else str(expr)

        try:
            conclusion = str(expr)
        except Exception:  # noqa: BLE001
            pass

        # Truncate very long conclusions for readability
        if len(conclusion) > 500:
            conclusion = conclusion[:497] + "..."

        premises: List[Z3ProofNode] = []
        if hasattr(expr, "num_args"):
            for i in range(expr.num_args()):
                child = expr.arg(i)
                if self._is_proof_term(child):
                    premises.append(self._extract_node(child))

        node = Z3ProofNode(rule=rule, conclusion=conclusion, premises=premises)
        self._seen[eid] = node
        return node

    def _get_rule_name(self, expr: Any) -> str:
        """Extract the Z3 proof rule name from an expression."""
        try:
            decl = expr.decl()
            name = str(decl.name())
            if name in self.KNOWN_RULES:
                return name
            return name
        except Exception:  # noqa: BLE001
            return "unknown"

    @staticmethod
    def _is_proof_term(expr: Any) -> bool:
        """Heuristic: does this Z3 expression look like a proof term?"""
        if not _HAS_Z3:
            return False
        try:
            return z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
        except Exception:  # noqa: BLE001
            return True

    def _simplify_node(self, node: Z3ProofNode) -> Z3ProofNode:
        """Recursively simplify a proof tree.

        - Collapse chains of ``rewrite`` into a single rewrite.
        - Remove identity steps (where premise conclusion == node conclusion).
        - Flatten single-child nodes that add no information.
        """
        simplified_premises = [self._simplify_node(p) for p in node.premises]

        # Collapse rewrite chains
        if node.rule == "rewrite" and len(simplified_premises) == 1:
            child = simplified_premises[0]
            if child.rule == "rewrite":
                return Z3ProofNode(
                    rule="rewrite",
                    conclusion=node.conclusion,
                    premises=child.premises,
                    annotations={
                        **child.annotations,
                        "collapsed": "true",
                    },
                )

        # Remove identity steps
        if (
            len(simplified_premises) == 1
            and simplified_premises[0].conclusion == node.conclusion
            and node.rule in ("mp", "mp~", "rewrite")
        ):
            return simplified_premises[0]

        # Flatten trivial pass-through
        if node.rule == "asserted" and not simplified_premises:
            return node

        return Z3ProofNode(
            rule=node.rule,
            conclusion=node.conclusion,
            premises=simplified_premises,
            annotations=node.annotations,
        )


# ═══════════════════════════════════════════════════════════════════════════
# Z3FormulaToLean – translate Z3 / SMT-LIB formulae → Lean propositions
# ═══════════════════════════════════════════════════════════════════════════


class Z3FormulaToLean:
    """Translate Z3 (SMT-LIB2) formula strings into Lean 4 propositions."""

    # SMT-LIB sort → Lean type
    _SORT_MAP: Dict[str, str] = {
        "Int": "Int",
        "Real": "Real",
        "Bool": "Bool",
        "String": "String",
        "Array": "Array",
        "BitVec": "BitVec",
    }

    # SMT-LIB operators → Lean operators / notation
    _OP_MAP: Dict[str, str] = {
        "and": "∧",
        "or": "∨",
        "not": "¬",
        "=>": "→",
        "=": "=",
        "distinct": "≠",
        "+": "+",
        "-": "-",
        "*": "*",
        "/": "/",
        "div": "/",
        "mod": "%",
        "rem": "%",
        ">=": "≥",
        "<=": "≤",
        ">": ">",
        "<": "<",
        "ite": "if … then … else …",
        "true": "True",
        "false": "False",
    }

    def __init__(self) -> None:
        self._var_types: Dict[str, str] = {}

    # ------------------------------------------------------------------
    # Public
    # ------------------------------------------------------------------

    def translate_formula(self, z3_formula_str: str) -> str:
        """Convert an SMT-LIB formula string to a Lean 4 Prop expression."""
        s = z3_formula_str.strip()
        if not s:
            return "True"
        return self._translate_sexpr(self._parse_sexpr(s))

    def translate_sort(self, z3_sort: str) -> str:
        """Map an SMT-LIB sort name to a Lean 4 type."""
        s = z3_sort.strip()
        if s in self._SORT_MAP:
            return self._SORT_MAP[s]
        # Parameterised sorts: (Array Int Int) → Array Int Int
        if s.startswith("("):
            tokens = self._tokenize(s)
            parsed = self._build_tree(tokens)
            if isinstance(parsed, list) and len(parsed) >= 1:
                head = parsed[0]
                if head in self._SORT_MAP:
                    args = " ".join(self.translate_sort(str(a)) for a in parsed[1:])
                    return f"{self._SORT_MAP[head]} {args}".strip()
        return s  # pass-through for unknown sorts

    # ------------------------------------------------------------------
    # S-expression parser
    # ------------------------------------------------------------------

    @staticmethod
    def _tokenize(s: str) -> List[str]:
        """Tokenise an S-expression string."""
        tokens: List[str] = []
        i = 0
        while i < len(s):
            c = s[i]
            if c in " \t\n\r":
                i += 1
            elif c == "(":
                tokens.append("(")
                i += 1
            elif c == ")":
                tokens.append(")")
                i += 1
            elif c == '"':
                j = i + 1
                while j < len(s) and s[j] != '"':
                    if s[j] == "\\":
                        j += 1
                    j += 1
                tokens.append(s[i : j + 1])
                i = j + 1
            else:
                j = i
                while j < len(s) and s[j] not in " \t\n\r()":
                    j += 1
                tokens.append(s[i:j])
                i = j
        return tokens

    @classmethod
    def _parse_sexpr(cls, s: str) -> Any:
        tokens = cls._tokenize(s)
        if not tokens:
            return ""
        return cls._build_tree(tokens)

    @classmethod
    def _build_tree(cls, tokens: List[str]) -> Any:
        """Build a nested list from a flat token list (consuming tokens as we go)."""
        if not tokens:
            return ""
        tok = tokens.pop(0)
        if tok == "(":
            lst: List[Any] = []
            while tokens and tokens[0] != ")":
                lst.append(cls._build_tree(tokens))
            if tokens:
                tokens.pop(0)  # consume ')'
            return lst
        if tok == ")":
            return ""
        return tok

    # ------------------------------------------------------------------
    # Translation core
    # ------------------------------------------------------------------

    def _translate_sexpr(self, expr: Any) -> str:
        """Recursively translate a parsed S-expression to Lean syntax."""
        if isinstance(expr, str):
            return self._translate_atom(expr)

        if not isinstance(expr, list) or len(expr) == 0:
            return "True"

        head = expr[0] if isinstance(expr[0], str) else ""
        args = expr[1:]

        # -- quantifiers ---------------------------------------------------
        if head == "forall":
            return self._translate_quantifier("∀", args)
        if head == "exists":
            return self._translate_quantifier("∃", args)

        # -- let -----------------------------------------------------------
        if head == "let":
            return self._translate_let(args)

        # -- negation (unary) ---------------------------------------------
        if head == "not" and len(args) == 1:
            inner = self._translate_sexpr(args[0])
            if " " in inner and not inner.startswith("("):
                return f"¬({inner})"
            return f"¬{inner}"

        # -- binary / n-ary operators ------------------------------------
        if head in self._OP_MAP:
            lean_op = self._OP_MAP[head]

            if head == "ite" and len(args) == 3:
                cond = self._translate_sexpr(args[0])
                then_ = self._translate_sexpr(args[1])
                else_ = self._translate_sexpr(args[2])
                return f"if {cond} then {then_} else {else_}"

            if head == "distinct" and len(args) == 2:
                lhs = self._translate_sexpr(args[0])
                rhs = self._translate_sexpr(args[1])
                return f"{lhs} ≠ {rhs}"

            if head in ("and", "or") and len(args) > 2:
                translated = [self._translate_sexpr(a) for a in args]
                return f" {lean_op} ".join(
                    f"({t})" if " " in t else t for t in translated
                )

            if head == "=>" and len(args) == 2:
                lhs = self._translate_sexpr(args[0])
                rhs = self._translate_sexpr(args[1])
                return f"{self._wrap(lhs)} → {self._wrap(rhs)}"

            if len(args) == 2:
                lhs = self._translate_sexpr(args[0])
                rhs = self._translate_sexpr(args[1])
                return f"{lhs} {lean_op} {rhs}"

            if len(args) == 1 and head == "-":
                inner = self._translate_sexpr(args[0])
                return f"-{inner}"

        # -- unknown function application ----------------------------------
        translated_args = [self._translate_sexpr(a) for a in args]
        head_t = self._translate_atom(head) if isinstance(head, str) else str(head)
        if translated_args:
            return f"{head_t} {' '.join(translated_args)}"
        return head_t

    def _translate_atom(self, atom: str) -> str:
        """Translate an atomic token."""
        if atom in ("true", "#t"):
            return "True"
        if atom in ("false", "#f"):
            return "False"
        # Numeric literals – pass through
        try:
            int(atom)
            return atom
        except ValueError:
            pass
        try:
            float(atom)
            return atom
        except ValueError:
            pass
        # String literal
        if atom.startswith('"') and atom.endswith('"'):
            return atom
        # Variable / identifier
        return atom.replace("!", "_bang_").replace("@", "_at_").replace(".", "_dot_")

    def _translate_quantifier(self, quant: str, args: List[Any]) -> str:
        """Translate ``(forall ((x Int)) P)`` → ``∀ x : Int, P``."""
        if len(args) < 2:
            return f"{quant} _, True"
        bindings = args[0]
        body = args[1] if len(args) == 2 else ["and"] + args[1:]

        parts: List[str] = []
        if isinstance(bindings, list):
            for b in bindings:
                if isinstance(b, list) and len(b) == 2:
                    var_name = str(b[0])
                    sort = self.translate_sort(str(b[1]))
                    parts.append(f"{var_name} : {sort}")
                    self._var_types[var_name] = sort
                else:
                    parts.append(str(b))
        binding_str = " ".join(f"({p})" for p in parts) if parts else "_"
        body_str = self._translate_sexpr(body)
        return f"{quant} {binding_str}, {body_str}"

    def _translate_let(self, args: List[Any]) -> str:
        """Translate ``(let ((x 5)) body)`` → ``let x := 5; body``."""
        if len(args) < 2:
            return "True"
        bindings = args[0]
        body = args[1]
        parts: List[str] = []
        if isinstance(bindings, list):
            for b in bindings:
                if isinstance(b, list) and len(b) == 2:
                    name = str(b[0])
                    val = self._translate_sexpr(b[1])
                    parts.append(f"let {name} := {val}")
        body_str = self._translate_sexpr(body)
        if parts:
            return "; ".join(parts) + f"; {body_str}"
        return body_str

    @staticmethod
    def _wrap(s: str) -> str:
        """Wrap in parentheses if the expression contains spaces."""
        if " " in s and not (s.startswith("(") and s.endswith(")")):
            return f"({s})"
        return s


# ═══════════════════════════════════════════════════════════════════════════
# Z3ToLeanTranslator — THE CORE
# ═══════════════════════════════════════════════════════════════════════════


class Z3ToLeanTranslator:
    """Translate a Z3 proof tree into a Lean 4 tactic script.

    Each Z3 proof rule is mapped to one or more Lean tactics.  The result
    is a complete ``by`` block that can be pasted into a Lean file.
    """

    # Z3 rule → primary Lean tactic
    _RULE_TACTIC: Dict[str, str] = {
        "mp": "exact",
        "hypothesis": "assumption",
        "asserted": "assumption",
        "unit-resolution": "exact",
        "rewrite": "rw",
        "monotonicity": "mono",
        "transitivity": "trans",
        "commutativity": "ring",
        "distributivity": "ring",
        "def-intro": "unfold",
        "apply-def": "simp",
        "iff-true": "simp",
        "iff-false": "simp",
        "refl": "rfl",
        "symm": "symm",
        "trans": "trans",
        "lemma": "exact",
        "th-lemma": "linarith",
        "and-elim": "exact",
        "or-elim": "rcases",
        "not-or-elim": "push_neg",
        "nnf-pos": "push_neg",
        "nnf-neg": "push_neg",
        "sk": "simp",
        "quant-intro": "intro",
        "quant-inst": "exact",
        "pull-quant": "simp",
        "push-quant": "simp",
        "elim-unused": "simp",
        "der": "exact",
        "hyper-res": "exact",
    }

    def __init__(self) -> None:
        self._formula_translator = Z3FormulaToLean()
        self._tactic_lines: List[str] = []

    # ------------------------------------------------------------------
    # Public
    # ------------------------------------------------------------------

    def translate(self, proof_tree: Z3ProofNode) -> str:
        """Produce a complete Lean ``by`` tactic block from a Z3 proof tree."""
        self._tactic_lines = []
        self._translate_node(proof_tree, depth=0)
        if not self._tactic_lines:
            return "by sorry /- empty Z3 proof -/"
        body = "\n  ".join(self._tactic_lines)
        return f"by\n  {body}"

    def translate_arithmetic_proof(self, formula: str) -> str:
        """Translate an arithmetic formula into omega / linarith."""
        if self._is_linear(formula):
            return "by omega"
        if self._is_nonlinear(formula):
            return "by nlinarith"
        return "by linarith"

    def translate_boolean_proof(self, formula: str) -> str:
        """Translate a boolean formula into decide."""
        return "by decide"

    def translate_quantifier_proof(self, formula: str) -> str:
        """Translate a quantified statement into intro / exact."""
        lines: List[str] = []
        # Count leading quantifiers
        remaining = formula.strip()
        while remaining.startswith("∀") or remaining.startswith("∃"):
            if remaining.startswith("∀"):
                lines.append("intro _")
                # Skip past the comma
                idx = remaining.find(",")
                remaining = remaining[idx + 1 :].strip() if idx >= 0 else ""
            elif remaining.startswith("∃"):
                lines.append("use _")
                idx = remaining.find(",")
                remaining = remaining[idx + 1 :].strip() if idx >= 0 else ""
        if remaining:
            lines.append("sorry /- body: " + remaining[:60] + " -/")
        if not lines:
            lines.append("sorry")
        body = "\n  ".join(lines)
        return f"by\n  {body}"

    def validate_lean_proof(self, lean_code: str) -> bool:
        """Quick regex-based syntax check (not a full Lean parser)."""
        code = lean_code.strip()
        if not code:
            return False

        # Must start with "by" or be a single term
        if not (code.startswith("by") or code.startswith("exact") or code == "rfl"):
            if not re.match(r"^[a-zA-Z_]", code):
                return False

        # Balanced parentheses
        depth = 0
        for ch in code:
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            if depth < 0:
                return False
        if depth != 0:
            return False

        # Balanced brackets
        depth = 0
        for ch in code:
            if ch == "[":
                depth += 1
            elif ch == "]":
                depth -= 1
            if depth < 0:
                return False
        if depth != 0:
            return False

        # No obviously invalid tokens
        _BAD_TOKENS = {"#check", "#eval", "#print", "import", "open", "section"}
        for tok in _BAD_TOKENS:
            if tok in code.split():
                return False

        return True

    # ------------------------------------------------------------------
    # Internal – recursive translation
    # ------------------------------------------------------------------

    def _translate_node(self, node: Z3ProofNode, depth: int) -> None:
        """Emit Lean tactics for a proof tree node."""
        rule = node.rule

        # Base case: known rule with no premises
        if node.is_leaf:
            self._emit_leaf(node)
            return

        # Translate premises first (bottom-up)
        for premise in node.premises:
            self._translate_node(premise, depth + 1)

        # Now emit tactic for this node
        tactic = self._RULE_TACTIC.get(rule)
        if tactic is None:
            self._tactic_lines.append(
                f"sorry /- Z3 rule: {rule} — no Lean mapping -/"
            )
            return

        # Specialised handling per rule
        if rule == "mp":
            self._emit_mp(node)
        elif rule == "unit-resolution":
            self._emit_unit_resolution(node)
        elif rule == "rewrite":
            self._emit_rewrite(node)
        elif rule == "monotonicity":
            self._emit_monotonicity(node)
        elif rule == "transitivity":
            self._emit_transitivity(node)
        elif rule == "th-lemma":
            self._emit_th_lemma(node)
        elif rule in ("and-elim", "or-elim", "not-or-elim"):
            self._emit_elim(node)
        elif rule in ("quant-intro", "quant-inst"):
            self._emit_quantifier(node)
        elif rule in ("def-intro", "apply-def"):
            self._emit_definition(node)
        elif rule in ("nnf-pos", "nnf-neg"):
            self._tactic_lines.append("push_neg")
        elif rule == "commutativity":
            self._tactic_lines.append("ring")
        elif rule == "distributivity":
            self._tactic_lines.append("ring")
        elif rule == "refl":
            self._tactic_lines.append("rfl")
        elif rule == "symm":
            self._tactic_lines.append("symm")
        else:
            self._tactic_lines.append(f"{tactic}")

    def _emit_leaf(self, node: Z3ProofNode) -> None:
        """Emit tactic for a leaf (no premises)."""
        rule = node.rule
        if rule in ("asserted", "hypothesis"):
            self._tactic_lines.append("assumption")
        elif rule == "refl":
            self._tactic_lines.append("rfl")
        elif rule == "th-lemma":
            self._tactic_lines.append("linarith")
        elif rule == "lemma":
            self._tactic_lines.append("assumption")
        else:
            tactic = self._RULE_TACTIC.get(rule, "sorry")
            self._tactic_lines.append(f"{tactic}")

    def _emit_mp(self, node: Z3ProofNode) -> None:
        """Modus ponens → apply / exact."""
        self._tactic_lines.append("apply And.intro")

    def _emit_unit_resolution(self, node: Z3ProofNode) -> None:
        """Unit resolution → exact / assumption."""
        self._tactic_lines.append("assumption")

    def _emit_rewrite(self, node: Z3ProofNode) -> None:
        """Rewrite → rw [...]."""
        conclusion = node.conclusion
        if "=" in conclusion:
            self._tactic_lines.append(f"rw [show {conclusion[:80]}]")
        else:
            self._tactic_lines.append("simp")

    def _emit_monotonicity(self, node: Z3ProofNode) -> None:
        """Monotonicity → mono / gcongr."""
        self._tactic_lines.append("gcongr")

    def _emit_transitivity(self, node: Z3ProofNode) -> None:
        """Transitivity → calc or trans."""
        if len(node.premises) >= 2:
            self._tactic_lines.append("trans")
        else:
            self._tactic_lines.append("exact Trans.trans (by assumption) (by assumption)")

    def _emit_th_lemma(self, node: Z3ProofNode) -> None:
        """Theory lemma → omega / linarith."""
        conclusion = node.conclusion
        if self._is_linear(conclusion):
            self._tactic_lines.append("omega")
        else:
            self._tactic_lines.append("linarith")

    def _emit_elim(self, node: Z3ProofNode) -> None:
        """And/Or/Not-or elimination."""
        rule = node.rule
        if rule == "and-elim":
            self._tactic_lines.append("exact And.left (by assumption)")
        elif rule == "or-elim":
            self._tactic_lines.append("rcases (by assumption) with h | h")
        elif rule == "not-or-elim":
            self._tactic_lines.append("push_neg at *")

    def _emit_quantifier(self, node: Z3ProofNode) -> None:
        """Quantifier introduction / instantiation."""
        if node.rule == "quant-intro":
            self._tactic_lines.append("intro _")
        else:
            self._tactic_lines.append("exact ⟨_, by assumption⟩")

    def _emit_definition(self, node: Z3ProofNode) -> None:
        """Definition introduction → unfold / simp."""
        self._tactic_lines.append("simp only []")

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _is_linear(formula: str) -> bool:
        """Heuristic: does the formula look like linear arithmetic?"""
        nonlinear = {"*", "^", "pow", "Nat.mul"}
        return not any(op in formula for op in nonlinear)

    @staticmethod
    def _is_nonlinear(formula: str) -> bool:
        nonlinear = {"*", "^", "pow"}
        return any(op in formula for op in nonlinear)


# ═══════════════════════════════════════════════════════════════════════════
# ProofCertificate — serialisable proof artifact
# ═══════════════════════════════════════════════════════════════════════════


class ProofCertificateTrustLevel(str, Enum):
    """Trust levels for proof certificates."""

    LEAN_KERNEL = "LEAN_KERNEL"
    Z3_VERIFIED = "Z3_VERIFIED"
    LLM_GENERATED = "LLM_GENERATED"
    ASSUMED = "ASSUMED"


@dataclass
class ProofCertificate(_safe_base(_CoreProofCertificate) if _HAS_DEPPY_CORE else object):
    """A portable, serialisable proof certificate.

    Extends the core ``ProofCertificate`` when available, adding Z3 proof
    tree nodes and Lean translation metadata.

    Bundles the Z3 proof (if any), the Lean proof string, and metadata
    about trust and verification status.
    """

    obligation_id: str
    z3_proof: Optional[Z3ProofNode] = None
    lean_proof: str = ""
    trust_level: str = "ASSUMED"
    verified: bool = False
    metadata: Dict[str, Any] = field(default_factory=dict)

    # ------------------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        return {
            "obligation_id": self.obligation_id,
            "z3_proof": self.z3_proof.to_dict() if self.z3_proof else None,
            "lean_proof": self.lean_proof,
            "trust_level": self.trust_level,
            "verified": self.verified,
            "metadata": self.metadata,
        }

    @staticmethod
    def from_dict(d: Dict[str, Any]) -> ProofCertificate:
        z3_node = None
        if d.get("z3_proof"):
            z3_node = Z3ProofNode.from_dict(d["z3_proof"])
        return ProofCertificate(
            obligation_id=d["obligation_id"],
            z3_proof=z3_node,
            lean_proof=d.get("lean_proof", ""),
            trust_level=d.get("trust_level", "ASSUMED"),
            verified=d.get("verified", False),
            metadata=d.get("metadata", {}),
        )

    # ------------------------------------------------------------------
    # Persistence
    # ------------------------------------------------------------------

    def save(self, path: str) -> None:
        """Write this certificate to *path* as JSON."""
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(self.to_dict(), indent=2), encoding="utf-8")

    @staticmethod
    def load(path: str) -> ProofCertificate:
        """Load a certificate from *path*."""
        p = Path(path)
        data = json.loads(p.read_text(encoding="utf-8"))
        return ProofCertificate.from_dict(data)

    # ------------------------------------------------------------------

    def __str__(self) -> str:
        status = "verified" if self.verified else "unverified"
        return (
            f"ProofCertificate({self.obligation_id}, "
            f"trust={self.trust_level}, {status})"
        )


# ═══════════════════════════════════════════════════════════════════════════
# Convenience / top-level helpers
# ═══════════════════════════════════════════════════════════════════════════


def extract_and_translate(
    solver: Any,
    obligation_id: str = "unknown",
) -> ProofCertificate:
    """One-shot helper: extract Z3 proof → translate → return certificate."""
    extractor = Z3ProofExtractor()
    tree = extractor.extract(solver)
    if tree is None:
        return ProofCertificate(
            obligation_id=obligation_id,
            lean_proof="sorry /- Z3 proof extraction failed -/",
            trust_level="ASSUMED",
        )

    simplified = extractor.simplify(tree)
    translator = Z3ToLeanTranslator()
    lean_proof = translator.translate(simplified)
    valid = translator.validate_lean_proof(lean_proof)

    return ProofCertificate(
        obligation_id=obligation_id,
        z3_proof=simplified,
        lean_proof=lean_proof,
        trust_level="Z3_VERIFIED" if valid else "Z3_UNVERIFIED",
        verified=False,
        metadata={"proof_depth": simplified.depth, "proof_size": simplified.size},
    )


def formula_to_lean(z3_formula: str) -> str:
    """Translate a single Z3 / SMT-LIB formula string to Lean syntax."""
    return Z3FormulaToLean().translate_formula(z3_formula)
