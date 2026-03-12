"""Main expression and predicate normalization.

Provides:

- **ExpressionNormalizer**: Canonicalizes arithmetic, boolean, and comparison
  expressions by collecting like terms, applying algebraic identities, and
  sorting commutative operands lexicographically.
- **PredicateNormalizer**: Normalizes predicates via prenex conversion,
  flattening, commutative sorting, double-negation elimination, and constant
  folding.
- **ContractNormalizer**: Normalizes contract sets by deduplication, overlap
  merging, and canonical ordering.

Under sheaf-descent semantics every section's refinement predicate must be
compared with sections on overlapping opens.  Normalization ensures that
syntactically different but semantically identical predicates are identified
so that the gluing axiom can be checked.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

if TYPE_CHECKING:
    from deppy.predicates.base import Predicate, Term

from deppy.predicates.base import (
    BinOp,
    BoolLit,
    Call,
    FloatLit,
    IntLit,
    NoneLit,
    Predicate,
    StrLit,
    Term,
    UnaryOp,
    Var,
)
from deppy.predicates.arithmetic import (
    Comparison,
    Divisibility,
    IntRange,
    LinearInequality,
    _CMP_FLIP,
)
from deppy.predicates.boolean import (
    And,
    Exists,
    ForAll,
    Iff,
    Implies,
    Not,
    Or,
    _TRUE,
    _FALSE,
    is_true,
    is_false,
)


# ===================================================================
#  Expression normalizer
# ===================================================================


class ExpressionNormalizer:
    """Normalizes expressions (terms) to canonical forms.

    The canonical form has the following properties:

    * Arithmetic sums are collected: ``(x + 2) + (3 + y)`` → ``(x + y + 5)``.
    * Products with a constant factor are written ``c * var``.
    * Commutative operators have operands sorted lexicographically by
      ``pretty()`` representation.
    * Unary ``+`` is eliminated; unary ``-`` on a literal folds to a negative
      literal.
    * Constant sub-expressions are evaluated eagerly.
    """

    # ------------------------------------------------------------------
    # Public entry point
    # ------------------------------------------------------------------

    def normalize(self, expr: Term) -> Term:
        """Normalize *expr* to canonical form by dispatching to
        sub-normalizers for arithmetic, boolean, and general terms."""
        if isinstance(expr, (IntLit, FloatLit, BoolLit, StrLit, NoneLit)):
            return expr
        if isinstance(expr, Var):
            return expr
        if isinstance(expr, UnaryOp):
            inner = self.normalize(expr.operand)
            return self._normalize_unary(expr.op, inner)
        if isinstance(expr, BinOp):
            left = self.normalize(expr.left)
            right = self.normalize(expr.right)
            return self._normalize_binop(expr.op, left, right)
        if isinstance(expr, Call):
            norm_args = tuple(self.normalize(a) for a in expr.args)
            return self._normalize_call(expr.func, norm_args)
        # Structural recursion for container-like terms
        if hasattr(expr, "substitute"):
            return expr  # fall-through for unknown term types
        return expr

    # ------------------------------------------------------------------
    # Arithmetic normalization
    # ------------------------------------------------------------------

    def normalize_arithmetic(self, expr: Term) -> Term:
        """Specifically normalize arithmetic expressions.

        Collects additive terms into ``{var_key: coefficient}`` maps and
        rebuilds a canonical sum sorted by variable name.
        """
        terms = self._collect_additive_terms(expr)
        if terms is None:
            return self.normalize(expr)
        return self._rebuild_sum(terms)

    def _collect_additive_terms(
        self, expr: Term, sign: int = 1
    ) -> Optional[Dict[str, int]]:
        """Attempt to decompose *expr* into a sum of ``coeff * variable``
        plus a constant.  Returns ``None`` if the expression is not purely
        additive/linear."""
        if isinstance(expr, IntLit):
            return {"": sign * expr.value}
        if isinstance(expr, Var):
            return {expr.name: sign}
        if isinstance(expr, UnaryOp) and expr.op == "-":
            return self._collect_additive_terms(expr.operand, -sign)
        if isinstance(expr, UnaryOp) and expr.op == "+":
            return self._collect_additive_terms(expr.operand, sign)
        if isinstance(expr, BinOp) and expr.op == "+":
            left = self._collect_additive_terms(expr.left, sign)
            right = self._collect_additive_terms(expr.right, sign)
            if left is None or right is None:
                return None
            return self._merge_term_maps(left, right)
        if isinstance(expr, BinOp) and expr.op == "-":
            left = self._collect_additive_terms(expr.left, sign)
            right = self._collect_additive_terms(expr.right, -sign)
            if left is None or right is None:
                return None
            return self._merge_term_maps(left, right)
        if isinstance(expr, BinOp) and expr.op == "*":
            # constant * variable  or  variable * constant
            if isinstance(expr.left, IntLit):
                sub = self._collect_additive_terms(expr.right, sign * expr.left.value)
                return sub
            if isinstance(expr.right, IntLit):
                sub = self._collect_additive_terms(expr.left, sign * expr.right.value)
                return sub
            return None
        return None

    @staticmethod
    def _merge_term_maps(a: Dict[str, int], b: Dict[str, int]) -> Dict[str, int]:
        result = dict(a)
        for k, v in b.items():
            result[k] = result.get(k, 0) + v
        return result

    @staticmethod
    def _rebuild_sum(terms: Dict[str, int]) -> Term:
        """Rebuild a canonical sum expression from a coefficient map.

        Variables are sorted lexicographically; zero-coefficient variables
        are dropped; the constant ``""`` key becomes the additive constant.
        """
        constant = terms.get("", 0)
        var_terms: List[Tuple[str, int]] = sorted(
            ((k, v) for k, v in terms.items() if k and v != 0),
            key=lambda kv: kv[0],
        )
        parts: List[Term] = []
        for name, coeff in var_terms:
            if coeff == 1:
                parts.append(Var(name))
            elif coeff == -1:
                parts.append(UnaryOp("-", Var(name)))
            else:
                parts.append(BinOp("*", IntLit(coeff), Var(name)))
        if constant != 0 or not parts:
            parts.append(IntLit(constant))
        result = parts[0]
        for p in parts[1:]:
            if isinstance(p, UnaryOp) and p.op == "-":
                result = BinOp("-", result, p.operand)
            else:
                result = BinOp("+", result, p)
        return result

    # ------------------------------------------------------------------
    # Boolean normalization
    # ------------------------------------------------------------------

    def normalize_boolean(self, expr: Term) -> Term:
        """Normalize boolean-valued terms: fold ``not not x`` → ``x``,
        evaluate ``True and False`` → ``False``, etc."""
        if isinstance(expr, BoolLit):
            return expr
        if isinstance(expr, UnaryOp) and expr.op == "~":
            inner = self.normalize_boolean(expr.operand)
            if isinstance(inner, BoolLit):
                return BoolLit(not inner.value)
            if isinstance(inner, UnaryOp) and inner.op == "~":
                return inner.operand
            return UnaryOp("~", inner)
        if isinstance(expr, BinOp) and expr.op in {"&", "|", "^"}:
            left = self.normalize_boolean(expr.left)
            right = self.normalize_boolean(expr.right)
            if isinstance(left, BoolLit) and isinstance(right, BoolLit):
                if expr.op == "&":
                    return BoolLit(left.value and right.value)
                if expr.op == "|":
                    return BoolLit(left.value or right.value)
                return BoolLit(left.value ^ right.value)
            # Sort commutative operands
            if expr.op in {"&", "|"} and left.pretty() > right.pretty():
                left, right = right, left
            return BinOp(expr.op, left, right)
        return self.normalize(expr)

    # ------------------------------------------------------------------
    # Comparison normalization
    # ------------------------------------------------------------------

    def normalize_comparison(self, expr: Term) -> Term:
        """Normalize comparison terms so the variable appears on the left.

        For BinOp terms that represent comparisons (the ``Comparison``
        predicate normalisation happens in ``PredicateNormalizer``), this
        simply delegates to arithmetic normalisation on both sides.
        """
        if isinstance(expr, BinOp):
            return BinOp(
                expr.op,
                self.normalize_arithmetic(expr.left),
                self.normalize_arithmetic(expr.right),
            )
        return self.normalize(expr)

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    def _normalize_unary(self, op: str, operand: Term) -> Term:
        if op == "+":
            return operand
        if op == "-":
            if isinstance(operand, IntLit):
                return IntLit(-operand.value)
            if isinstance(operand, FloatLit):
                return FloatLit(-operand.value)
            if isinstance(operand, UnaryOp) and operand.op == "-":
                return operand.operand
            return UnaryOp("-", operand)
        if op == "~":
            if isinstance(operand, BoolLit):
                return BoolLit(not operand.value)
            if isinstance(operand, UnaryOp) and operand.op == "~":
                return operand.operand
            return UnaryOp("~", operand)
        return UnaryOp(op, operand)

    def _normalize_binop(self, op: str, left: Term, right: Term) -> Term:
        # Constant folding: int op int
        if isinstance(left, IntLit) and isinstance(right, IntLit):
            result = self._eval_int_binop(op, left.value, right.value)
            if result is not None:
                return IntLit(result)
        # Constant folding: float op float
        if isinstance(left, FloatLit) and isinstance(right, FloatLit):
            result = self._eval_float_binop(op, left.value, right.value)
            if result is not None:
                return FloatLit(result)
        # Algebraic identities
        if op == "+":
            if isinstance(right, IntLit) and right.value == 0:
                return left
            if isinstance(left, IntLit) and left.value == 0:
                return right
        if op == "-":
            if isinstance(right, IntLit) and right.value == 0:
                return left
            if left == right:
                return IntLit(0)
        if op == "*":
            if isinstance(right, IntLit):
                if right.value == 0:
                    return IntLit(0)
                if right.value == 1:
                    return left
            if isinstance(left, IntLit):
                if left.value == 0:
                    return IntLit(0)
                if left.value == 1:
                    return right
        if op == "**":
            if isinstance(right, IntLit) and right.value == 0:
                return IntLit(1)
            if isinstance(right, IntLit) and right.value == 1:
                return left
        # Sort commutative operators
        if op in {"+", "*"} and left.pretty() > right.pretty():
            left, right = right, left
        return BinOp(op, left, right)

    def _normalize_call(self, func: str, args: Tuple[Term, ...]) -> Term:
        """Fold well-known function calls on literal arguments."""
        if func == "abs" and len(args) == 1:
            if isinstance(args[0], IntLit):
                return IntLit(abs(args[0].value))
            if isinstance(args[0], FloatLit):
                return FloatLit(abs(args[0].value))
        if func == "len" and len(args) == 1 and isinstance(args[0], StrLit):
            return IntLit(len(args[0].value))
        if func == "min" and all(isinstance(a, IntLit) for a in args) and args:
            return IntLit(min(a.value for a in args))  # type: ignore[union-attr]
        if func == "max" and all(isinstance(a, IntLit) for a in args) and args:
            return IntLit(max(a.value for a in args))  # type: ignore[union-attr]
        return Call(func, args)

    @staticmethod
    def _eval_int_binop(op: str, a: int, b: int) -> Optional[int]:
        try:
            if op == "+":
                return a + b
            if op == "-":
                return a - b
            if op == "*":
                return a * b
            if op == "//" and b != 0:
                return a // b
            if op == "%" and b != 0:
                return a % b
            if op == "**" and b >= 0:
                return a ** b
            if op == "&":
                return a & b
            if op == "|":
                return a | b
            if op == "^":
                return a ^ b
            if op == "<<" and b >= 0:
                return a << b
            if op == ">>" and b >= 0:
                return a >> b
        except (OverflowError, ValueError):
            pass
        return None

    @staticmethod
    def _eval_float_binop(op: str, a: float, b: float) -> Optional[float]:
        try:
            if op == "+":
                return a + b
            if op == "-":
                return a - b
            if op == "*":
                return a * b
            if op == "//" and b != 0.0:
                return a // b
            if op == "%" and b != 0.0:
                return a % b
            if op == "**":
                return a ** b
        except (OverflowError, ValueError, ZeroDivisionError):
            pass
        return None


# ===================================================================
#  Predicate normalizer
# ===================================================================


class PredicateNormalizer:
    """Normalizes predicates for comparison, deduplication, and solving.

    A fully-normalized predicate satisfies:

    1. **No double negations**: ``Not(Not(p))`` is replaced by ``p``.
    2. **Flat connectives**: ``And([And([a, b]), c])`` → ``And([a, b, c])``.
    3. **Sorted commutative connectives**: conjuncts/disjuncts are sorted
       by their ``pretty()`` representation.
    4. **Implications eliminated** (optionally): ``A → B`` becomes
       ``¬A ∨ B``.
    5. **Comparisons oriented**: ``5 < x`` becomes ``x > 5``.
    6. **Constants folded**: ``True ∧ p`` → ``p``, ``False ∨ p`` → ``p``.
    """

    def __init__(self) -> None:
        self._expr_norm = ExpressionNormalizer()

    # ------------------------------------------------------------------
    # Full normalization pipeline
    # ------------------------------------------------------------------

    def normalize(self, pred: Predicate) -> Predicate:
        """Apply the full normalization pipeline to *pred*.

        The pipeline runs:
        constant_fold → eliminate_double_negation → flatten →
        sort_commutative → orient_comparisons → constant_fold (final).
        """
        p = self.constant_fold(pred)
        p = self.eliminate_double_negation(p)
        p = self.flatten(p)
        p = self._orient_comparisons(p)
        p = self._normalize_terms(p)
        p = self.sort_commutative(p)
        p = self.constant_fold(p)
        return p

    # ------------------------------------------------------------------
    # Prenex normal form
    # ------------------------------------------------------------------

    def to_prenex(self, pred: Predicate) -> Predicate:
        """Convert *pred* to prenex normal form by pulling quantifiers
        out to the front.

        The result has the shape ``Q₁ x₁ . Q₂ x₂ . … . φ`` where
        ``φ`` is quantifier-free.
        """
        normed = self.normalize(pred)
        quantifiers: List[Tuple[str, str]] = []
        body = self._extract_quantifiers(normed, quantifiers)
        body = self.normalize(body)
        # Re-wrap with quantifiers
        result = body
        for kind, var in reversed(quantifiers):
            if kind == "forall":
                result = ForAll(var=var, body=result)
            else:
                result = Exists(var=var, body=result)
        return result

    def _extract_quantifiers(
        self,
        pred: Predicate,
        accum: List[Tuple[str, str]],
    ) -> Predicate:
        """Recursively pull quantifiers from *pred* into *accum*."""
        if isinstance(pred, ForAll):
            accum.append(("forall", pred.var))
            return self._extract_quantifiers(pred.body, accum)
        if isinstance(pred, Exists):
            accum.append(("exists", pred.var))
            return self._extract_quantifiers(pred.body, accum)
        if isinstance(pred, And):
            new_conjuncts = [
                self._extract_quantifiers(c, accum)
                for c in pred.conjuncts
            ]
            return And(new_conjuncts)
        if isinstance(pred, Or):
            new_disjuncts = [
                self._extract_quantifiers(d, accum)
                for d in pred.disjuncts
            ]
            return Or(new_disjuncts)
        if isinstance(pred, Not):
            inner = self._extract_quantifiers(pred.operand, accum)
            return Not(inner)
        return pred

    # ------------------------------------------------------------------
    # Flatten
    # ------------------------------------------------------------------

    def flatten(self, pred: Predicate) -> Predicate:
        """Flatten nested ``And`` and ``Or`` nodes.

        ``And([And([a, b]), c])`` becomes ``And([a, b, c])``.
        ``Or([Or([a, b]), c])`` becomes ``Or([a, b, c])``.
        """
        if isinstance(pred, And):
            flat: List[Predicate] = []
            for c in pred.conjuncts:
                fc = self.flatten(c)
                if isinstance(fc, And):
                    flat.extend(fc.conjuncts)
                else:
                    flat.append(fc)
            if not flat:
                return _TRUE
            if len(flat) == 1:
                return flat[0]
            return And(flat)
        if isinstance(pred, Or):
            flat_d: List[Predicate] = []
            for d in pred.disjuncts:
                fd = self.flatten(d)
                if isinstance(fd, Or):
                    flat_d.extend(fd.disjuncts)
                else:
                    flat_d.append(fd)
            if not flat_d:
                return _FALSE
            if len(flat_d) == 1:
                return flat_d[0]
            return Or(flat_d)
        if isinstance(pred, Not):
            return Not(self.flatten(pred.operand))
        if isinstance(pred, Implies):
            return Implies(
                self.flatten(pred.antecedent),
                self.flatten(pred.consequent),
            )
        if isinstance(pred, Iff):
            return Iff(self.flatten(pred.left), self.flatten(pred.right))
        if isinstance(pred, ForAll):
            return ForAll(var=pred.var, body=self.flatten(pred.body), domain=pred.domain)
        if isinstance(pred, Exists):
            return Exists(var=pred.var, body=self.flatten(pred.body), domain=pred.domain)
        return pred

    # ------------------------------------------------------------------
    # Sort commutative
    # ------------------------------------------------------------------

    def sort_commutative(self, pred: Predicate) -> Predicate:
        """Sort conjuncts and disjuncts lexicographically by ``pretty()``.

        This ensures that ``And([b, a])`` and ``And([a, b])`` normalize
        to the same form.
        """
        if isinstance(pred, And):
            sorted_children = sorted(
                (self.sort_commutative(c) for c in pred.conjuncts),
                key=lambda p: p.pretty(),
            )
            return And(sorted_children)
        if isinstance(pred, Or):
            sorted_children = sorted(
                (self.sort_commutative(d) for d in pred.disjuncts),
                key=lambda p: p.pretty(),
            )
            return Or(sorted_children)
        if isinstance(pred, Not):
            return Not(self.sort_commutative(pred.operand))
        if isinstance(pred, Implies):
            return Implies(
                self.sort_commutative(pred.antecedent),
                self.sort_commutative(pred.consequent),
            )
        if isinstance(pred, Iff):
            left = self.sort_commutative(pred.left)
            right = self.sort_commutative(pred.right)
            if left.pretty() > right.pretty():
                left, right = right, left
            return Iff(left, right)
        if isinstance(pred, ForAll):
            return ForAll(
                var=pred.var,
                body=self.sort_commutative(pred.body),
                domain=pred.domain,
            )
        if isinstance(pred, Exists):
            return Exists(
                var=pred.var,
                body=self.sort_commutative(pred.body),
                domain=pred.domain,
            )
        return pred

    # ------------------------------------------------------------------
    # Double-negation elimination
    # ------------------------------------------------------------------

    def eliminate_double_negation(self, pred: Predicate) -> Predicate:
        """Remove ``Not(Not(p))`` everywhere in the tree."""
        if isinstance(pred, Not):
            inner = self.eliminate_double_negation(pred.operand)
            if isinstance(inner, Not):
                return inner.operand
            return Not(inner)
        if isinstance(pred, And):
            return And([self.eliminate_double_negation(c) for c in pred.conjuncts])
        if isinstance(pred, Or):
            return Or([self.eliminate_double_negation(d) for d in pred.disjuncts])
        if isinstance(pred, Implies):
            return Implies(
                self.eliminate_double_negation(pred.antecedent),
                self.eliminate_double_negation(pred.consequent),
            )
        if isinstance(pred, Iff):
            return Iff(
                self.eliminate_double_negation(pred.left),
                self.eliminate_double_negation(pred.right),
            )
        if isinstance(pred, ForAll):
            return ForAll(
                var=pred.var,
                body=self.eliminate_double_negation(pred.body),
                domain=pred.domain,
            )
        if isinstance(pred, Exists):
            return Exists(
                var=pred.var,
                body=self.eliminate_double_negation(pred.body),
                domain=pred.domain,
            )
        return pred

    # ------------------------------------------------------------------
    # Constant folding
    # ------------------------------------------------------------------

    def constant_fold(self, pred: Predicate) -> Predicate:
        """Evaluate boolean connectives with constant operands.

        - ``True ∧ p`` → ``p``
        - ``False ∧ p`` → ``False``
        - ``True ∨ p`` → ``True``
        - ``False ∨ p`` → ``p``
        - ``¬True`` → ``False``
        """
        if isinstance(pred, And):
            folded: List[Predicate] = []
            for c in pred.conjuncts:
                fc = self.constant_fold(c)
                if is_false(fc):
                    return _FALSE
                if is_true(fc):
                    continue
                folded.append(fc)
            if not folded:
                return _TRUE
            if len(folded) == 1:
                return folded[0]
            return And(folded)
        if isinstance(pred, Or):
            folded_d: List[Predicate] = []
            for d in pred.disjuncts:
                fd = self.constant_fold(d)
                if is_true(fd):
                    return _TRUE
                if is_false(fd):
                    continue
                folded_d.append(fd)
            if not folded_d:
                return _FALSE
            if len(folded_d) == 1:
                return folded_d[0]
            return Or(folded_d)
        if isinstance(pred, Not):
            inner = self.constant_fold(pred.operand)
            if is_true(inner):
                return _FALSE
            if is_false(inner):
                return _TRUE
            if isinstance(inner, Not):
                return inner.operand
            return Not(inner)
        if isinstance(pred, Implies):
            a = self.constant_fold(pred.antecedent)
            b = self.constant_fold(pred.consequent)
            if is_false(a) or is_true(b):
                return _TRUE
            if is_true(a):
                return b
            return Implies(a, b)
        if isinstance(pred, Iff):
            a = self.constant_fold(pred.left)
            b = self.constant_fold(pred.right)
            if a == b:
                return _TRUE
            if is_true(a):
                return b
            if is_true(b):
                return a
            if is_false(a):
                return Not(b)
            if is_false(b):
                return Not(a)
            return Iff(a, b)
        if isinstance(pred, Comparison):
            return pred.simplify()
        if isinstance(pred, LinearInequality):
            return pred.simplify()
        if isinstance(pred, ForAll):
            body = self.constant_fold(pred.body)
            if pred.var not in body.free_variables():
                return body
            return ForAll(var=pred.var, body=body, domain=pred.domain)
        if isinstance(pred, Exists):
            body = self.constant_fold(pred.body)
            if pred.var not in body.free_variables():
                return body
            return Exists(var=pred.var, body=body, domain=pred.domain)
        return pred

    # ------------------------------------------------------------------
    # Comparison orientation
    # ------------------------------------------------------------------

    def _orient_comparisons(self, pred: Predicate) -> Predicate:
        """Rewrite comparisons so the variable is on the left.

        ``5 < x`` becomes ``x > 5``; ``3 == y`` becomes ``y == 3``.
        """
        if isinstance(pred, Comparison):
            left, right = pred.left, pred.right
            left_is_lit = isinstance(left, (IntLit, FloatLit, BoolLit, StrLit, NoneLit))
            right_is_lit = isinstance(right, (IntLit, FloatLit, BoolLit, StrLit, NoneLit))
            if left_is_lit and not right_is_lit:
                return pred.flip()
            # If both are non-literal, sort by pretty() for canonical form
            if not left_is_lit and not right_is_lit:
                if left.pretty() > right.pretty():
                    return pred.flip()
            return pred
        if isinstance(pred, And):
            return And([self._orient_comparisons(c) for c in pred.conjuncts])
        if isinstance(pred, Or):
            return Or([self._orient_comparisons(d) for d in pred.disjuncts])
        if isinstance(pred, Not):
            return Not(self._orient_comparisons(pred.operand))
        if isinstance(pred, Implies):
            return Implies(
                self._orient_comparisons(pred.antecedent),
                self._orient_comparisons(pred.consequent),
            )
        if isinstance(pred, Iff):
            return Iff(
                self._orient_comparisons(pred.left),
                self._orient_comparisons(pred.right),
            )
        if isinstance(pred, ForAll):
            return ForAll(
                var=pred.var,
                body=self._orient_comparisons(pred.body),
                domain=pred.domain,
            )
        if isinstance(pred, Exists):
            return Exists(
                var=pred.var,
                body=self._orient_comparisons(pred.body),
                domain=pred.domain,
            )
        return pred

    # ------------------------------------------------------------------
    # Term normalization inside predicates
    # ------------------------------------------------------------------

    def _normalize_terms(self, pred: Predicate) -> Predicate:
        """Normalize all embedded terms inside *pred*."""
        if isinstance(pred, Comparison):
            return Comparison(
                op=pred.op,
                left=self._expr_norm.normalize(pred.left),
                right=self._expr_norm.normalize(pred.right),
                source_location=pred.source_location,
            )
        if isinstance(pred, And):
            return And([self._normalize_terms(c) for c in pred.conjuncts])
        if isinstance(pred, Or):
            return Or([self._normalize_terms(d) for d in pred.disjuncts])
        if isinstance(pred, Not):
            return Not(self._normalize_terms(pred.operand))
        if isinstance(pred, Implies):
            return Implies(
                self._normalize_terms(pred.antecedent),
                self._normalize_terms(pred.consequent),
            )
        if isinstance(pred, Iff):
            return Iff(
                self._normalize_terms(pred.left),
                self._normalize_terms(pred.right),
            )
        if isinstance(pred, ForAll):
            return ForAll(
                var=pred.var,
                body=self._normalize_terms(pred.body),
                domain=pred.domain,
            )
        if isinstance(pred, Exists):
            return Exists(
                var=pred.var,
                body=self._normalize_terms(pred.body),
                domain=pred.domain,
            )
        return pred


# ===================================================================
#  Contract normalizer
# ===================================================================


class ContractNormalizer:
    """Normalizes contract sets to canonical form.

    Contracts are the boundary seeds of DepPy's sheaf-descent system.
    When multiple contracts attach to the same function, the normalizer
    deduplicates them, merges overlapping pre-/post-conditions, and
    sorts them into a canonical order so that downstream passes see a
    single, minimal representation.
    """

    def __init__(self) -> None:
        self._pred_norm = PredicateNormalizer()

    def normalize_requires(self, contracts: List[Any]) -> List[Any]:
        """Normalize a list of ``@requires`` precondition contracts.

        Each contract is expected to have a ``predicate`` attribute.
        Returns the list with predicates normalized, deduplicated, and
        sorted.
        """
        normed = self._normalize_predicates_on(contracts)
        deduped = self.deduplicate(normed)
        return self._sort_contracts(deduped)

    def normalize_ensures(self, contracts: List[Any]) -> List[Any]:
        """Normalize a list of ``@ensures`` postcondition contracts.

        Same treatment as ``normalize_requires``; postconditions are
        additionally merged when one implies another.
        """
        normed = self._normalize_predicates_on(contracts)
        deduped = self.deduplicate(normed)
        merged = self.merge_overlapping(deduped)
        return self._sort_contracts(merged)

    def merge_overlapping(self, contracts: List[Any]) -> List[Any]:
        """Merge contracts whose predicates overlap.

        Two preconditions ``P₁`` and ``P₂`` overlap when one implies
        the other (syntactically detected via subsumption).  The weaker
        one is dropped.

        For postconditions, overlapping ensures clauses are conjoined.
        """
        if len(contracts) <= 1:
            return list(contracts)

        result: List[Any] = []
        consumed: Set[int] = set()
        for i, c_i in enumerate(contracts):
            if i in consumed:
                continue
            pred_i = self._get_predicate(c_i)
            if pred_i is None:
                result.append(c_i)
                continue
            merged_pred = pred_i
            for j in range(i + 1, len(contracts)):
                if j in consumed:
                    continue
                pred_j = self._get_predicate(contracts[j])
                if pred_j is None:
                    continue
                if self._syntactic_implies(merged_pred, pred_j):
                    consumed.add(j)
                elif self._syntactic_implies(pred_j, merged_pred):
                    merged_pred = pred_j
                    consumed.add(j)
            self._set_predicate(c_i, merged_pred)
            result.append(c_i)
        return result

    def deduplicate(self, contracts: List[Any]) -> List[Any]:
        """Remove duplicate contracts (same normalized predicate)."""
        seen_keys: Set[str] = set()
        result: List[Any] = []
        for c in contracts:
            pred = self._get_predicate(c)
            if pred is not None:
                key = self._pred_norm.normalize(pred).pretty()
            else:
                key = repr(c)
            if key not in seen_keys:
                seen_keys.add(key)
                result.append(c)
        return result

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    def _normalize_predicates_on(self, contracts: List[Any]) -> List[Any]:
        """Normalize the predicate on each contract in place."""
        result: List[Any] = []
        for c in contracts:
            pred = self._get_predicate(c)
            if pred is not None:
                normed = self._pred_norm.normalize(pred)
                self._set_predicate(c, normed)
            result.append(c)
        return result

    def _sort_contracts(self, contracts: List[Any]) -> List[Any]:
        """Sort contracts by their canonical predicate string."""
        def _sort_key(c: Any) -> str:
            pred = self._get_predicate(c)
            if pred is not None:
                return pred.pretty()
            return repr(c)
        return sorted(contracts, key=_sort_key)

    @staticmethod
    def _get_predicate(contract: Any) -> Optional[Predicate]:
        """Extract the predicate from a contract object."""
        if hasattr(contract, "predicate"):
            return contract.predicate  # type: ignore[return-value]
        if hasattr(contract, "statement"):
            return contract.statement  # type: ignore[return-value]
        if isinstance(contract, Predicate):
            return contract
        return None

    @staticmethod
    def _set_predicate(contract: Any, pred: Predicate) -> None:
        """Set the predicate on a contract object."""
        if hasattr(contract, "predicate"):
            try:
                contract.predicate = pred  # type: ignore[attr-defined]
            except (AttributeError, TypeError):
                pass
        elif hasattr(contract, "statement"):
            try:
                contract.statement = pred  # type: ignore[attr-defined]
            except (AttributeError, TypeError):
                pass

    @staticmethod
    def _syntactic_implies(p: Predicate, q: Predicate) -> bool:
        """Conservative syntactic implication check.

        Returns ``True`` only when ``p`` syntactically contains ``q`` as
        a conjunct, or when ``p == q``.
        """
        if p == q:
            return True
        if isinstance(p, And):
            return any(c == q for c in p.conjuncts)
        return False
