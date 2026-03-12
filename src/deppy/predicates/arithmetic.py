"""Arithmetic predicates and normalization.

Provides predicate types for arithmetic relations (comparisons, linear
inequalities, divisibility, integer ranges) and a normalizer that rewrites
compound arithmetic predicates into canonical ``LinearInequality`` form.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.predicates.base import (
    BinOp,
    FloatLit,
    IntLit,
    NoneLit,
    Predicate,
    SourceLocation,
    Term,
    UnaryOp,
    Var,
    _coerce_to_term,
)


# ===================================================================
#  Comparison
# ===================================================================

_CMP_OPS: frozenset[str] = frozenset({"<", "<=", ">", ">=", "==", "!="})
_CMP_NEGATE: dict[str, str] = {
    "<": ">=",
    "<=": ">",
    ">": "<=",
    ">=": "<",
    "==": "!=",
    "!=": "==",
}
_CMP_FLIP: dict[str, str] = {
    "<": ">",
    "<=": ">=",
    ">": "<",
    ">=": "<=",
    "==": "==",
    "!=": "!=",
}


@dataclass(frozen=True)
class Comparison(Predicate):
    """Relational comparison: ``left op right``.

    *op* is one of ``<``, ``<=``, ``>``, ``>=``, ``==``, ``!=``.
    """

    op: str
    left: Term
    right: Term
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def __post_init__(self) -> None:
        if self.op not in _CMP_OPS:
            raise ValueError(f"Unknown comparison operator: {self.op!r}")

    # -- Predicate interface -------------------------------------------

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        return Comparison(
            op=self.op,
            left=self.left.substitute(mapping),
            right=self.right.substitute(mapping),
            source_location=self.source_location,
        )

    def negate(self) -> Predicate:
        return Comparison(
            op=_CMP_NEGATE[self.op],
            left=self.left,
            right=self.right,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        # Evaluate when both sides are literal integers
        if isinstance(self.left, IntLit) and isinstance(self.right, IntLit):
            result = _eval_int_cmp(self.op, self.left.value, self.right.value)
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if result else _FALSE
        # Evaluate literal floats
        if isinstance(self.left, FloatLit) and isinstance(self.right, FloatLit):
            result = _eval_float_cmp(self.op, self.left.value, self.right.value)
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if result else _FALSE
        # x op x  →  True for <=, >=, ==; False for <, >, !=
        if self.left == self.right:
            from deppy.predicates.boolean import _TRUE, _FALSE
            if self.op in {"<=", ">=", "=="}:
                return _TRUE
            return _FALSE
        return self

    def pretty(self) -> str:
        return f"{self.left.pretty()} {self.op} {self.right.pretty()}"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield from self.left.walk_terms()
        yield from self.right.walk_terms()

    def flip(self) -> Comparison:
        """Return the same comparison with operands swapped."""
        return Comparison(
            op=_CMP_FLIP[self.op],
            left=self.right,
            right=self.left,
            source_location=self.source_location,
        )

    def __repr__(self) -> str:
        return f"Comparison({self.op!r}, {self.left!r}, {self.right!r})"


# ===================================================================
#  Linear inequality  a₁x₁ + a₂x₂ + … + c ≥ 0
# ===================================================================

@dataclass(frozen=True)
class LinearInequality(Predicate):
    """Normalised linear integer inequality.

    Semantics: ``Σ (coefficients[v] * v) + constant ≥ 0``.

    Variables with a zero coefficient are omitted.
    """

    coefficients: Tuple[Tuple[str, int], ...]
    constant: int
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def __init__(
        self,
        coefficients: Dict[str, int] | Sequence[Tuple[str, int]],
        constant: int,
        source_location: Optional[SourceLocation] = None,
    ) -> None:
        if isinstance(coefficients, dict):
            coeff_items = coefficients.items()
        else:
            coeff_items = coefficients
        # Canonical: sorted by variable name, drop zeros
        canon = tuple(sorted(
            ((k, v) for k, v in coeff_items if v != 0), key=lambda kv: kv[0]
        ))
        object.__setattr__(self, "coefficients", canon)
        object.__setattr__(self, "constant", constant)
        object.__setattr__(self, "source_location", source_location)

    @property
    def coeff_dict(self) -> Dict[str, int]:
        return dict(self.coefficients)

    def free_variables(self) -> Set[str]:
        return {v for v, _ in self.coefficients}

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        # If all mapped terms are Var, rename; otherwise fall back.
        new_coeffs: Dict[str, int] = {}
        new_const = self.constant
        for var, coeff in self.coefficients:
            replacement = mapping.get(var)
            if replacement is None:
                new_coeffs[var] = new_coeffs.get(var, 0) + coeff
            elif isinstance(replacement, Var):
                new_coeffs[replacement.name] = (
                    new_coeffs.get(replacement.name, 0) + coeff
                )
            elif isinstance(replacement, IntLit):
                new_const += coeff * replacement.value
            else:
                # Cannot substitute non-linear terms; return a Comparison instead
                return _linear_to_comparison(self).substitute(mapping)
        return LinearInequality(
            new_coeffs, new_const, source_location=self.source_location
        )

    def negate(self) -> Predicate:
        # ¬(Σ aᵢxᵢ + c ≥ 0)  ⟺  Σ(-aᵢ)xᵢ + (-c - 1) ≥ 0
        neg_coeffs = {v: -c for v, c in self.coefficients}
        return LinearInequality(
            neg_coeffs, -self.constant - 1,
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        if not self.coefficients:
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if self.constant >= 0 else _FALSE
        return self

    def pretty(self) -> str:
        parts: List[str] = []
        for var, coeff in self.coefficients:
            if coeff == 1:
                parts.append(var)
            elif coeff == -1:
                parts.append(f"-{var}")
            else:
                parts.append(f"{coeff}*{var}")
        if self.constant != 0 or not parts:
            parts.append(str(self.constant))
        return " + ".join(parts) + " >= 0"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        for var, _ in self.coefficients:
            yield Var(var)

    def __repr__(self) -> str:
        return (
            f"LinearInequality({dict(self.coefficients)!r}, {self.constant!r})"
        )


# ===================================================================
#  Divisibility  k | (a*x + b)
# ===================================================================

@dataclass(frozen=True)
class Divisibility(Predicate):
    """Divisibility predicate: ``divisor | (coefficient * variable + offset)``.

    Semantics: ``(coefficient * variable + offset) % divisor == 0``.
    """

    divisor: int
    variable: str
    coefficient: int = 1
    offset: int = 0
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def __post_init__(self) -> None:
        if self.divisor == 0:
            raise ValueError("Divisor must be non-zero")

    def free_variables(self) -> Set[str]:
        return {self.variable}

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        replacement = mapping.get(self.variable)
        if replacement is None:
            return self
        if isinstance(replacement, Var):
            return Divisibility(
                divisor=self.divisor,
                variable=replacement.name,
                coefficient=self.coefficient,
                offset=self.offset,
                source_location=self.source_location,
            )
        if isinstance(replacement, IntLit):
            new_val = self.coefficient * replacement.value + self.offset
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if new_val % self.divisor == 0 else _FALSE
        # General case: fall back to a comparison-style encoding
        inner = BinOp("+", BinOp("*", IntLit(self.coefficient), replacement), IntLit(self.offset))
        mod_term = BinOp("%", inner, IntLit(self.divisor))
        return Comparison("==", mod_term, IntLit(0), source_location=self.source_location)

    def negate(self) -> Predicate:
        inner = BinOp(
            "+",
            BinOp("*", IntLit(self.coefficient), Var(self.variable)),
            IntLit(self.offset),
        )
        mod_term = BinOp("%", inner, IntLit(self.divisor))
        return Comparison(
            "!=", mod_term, IntLit(0),
            source_location=self.source_location,
        )

    def simplify(self) -> Predicate:
        if self.divisor == 1 or self.divisor == -1:
            from deppy.predicates.boolean import _TRUE
            return _TRUE
        if self.coefficient == 0:
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if self.offset % self.divisor == 0 else _FALSE
        return self

    def pretty(self) -> str:
        inner = f"{self.coefficient}*{self.variable}"
        if self.offset > 0:
            inner += f" + {self.offset}"
        elif self.offset < 0:
            inner += f" - {-self.offset}"
        return f"{self.divisor} | ({inner})"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield Var(self.variable)

    def __repr__(self) -> str:
        return (
            f"Divisibility({self.divisor}, {self.variable!r}, "
            f"coeff={self.coefficient}, offset={self.offset})"
        )


# ===================================================================
#  Integer range  lo ≤ x ≤ hi
# ===================================================================

@dataclass(frozen=True)
class IntRange(Predicate):
    """Bounded integer interval: ``lo ≤ variable ≤ hi``.

    Either *lo* or *hi* may be ``None`` to denote an open bound.
    """

    variable: str
    lo: Optional[int] = None
    hi: Optional[int] = None
    source_location: Optional[SourceLocation] = field(
        default=None, compare=False, hash=False
    )

    def free_variables(self) -> Set[str]:
        return {self.variable}

    def substitute(self, mapping: Dict[str, Term]) -> Predicate:
        replacement = mapping.get(self.variable)
        if replacement is None:
            return self
        if isinstance(replacement, Var):
            return IntRange(
                variable=replacement.name, lo=self.lo, hi=self.hi,
                source_location=self.source_location,
            )
        if isinstance(replacement, IntLit):
            v = replacement.value
            ok = True
            if self.lo is not None and v < self.lo:
                ok = False
            if self.hi is not None and v > self.hi:
                ok = False
            from deppy.predicates.boolean import _TRUE, _FALSE
            return _TRUE if ok else _FALSE
        # General: expand to conjunctive comparison
        parts: List[Predicate] = []
        if self.lo is not None:
            parts.append(Comparison(">=", replacement, IntLit(self.lo)))
        if self.hi is not None:
            parts.append(Comparison("<=", replacement, IntLit(self.hi)))
        if not parts:
            from deppy.predicates.boolean import _TRUE
            return _TRUE
        if len(parts) == 1:
            return parts[0]
        from deppy.predicates.boolean import And
        return And(parts)

    def negate(self) -> Predicate:
        # ¬(lo ≤ x ≤ hi)  ⟺  x < lo ∨ x > hi
        parts: List[Predicate] = []
        v = Var(self.variable)
        if self.lo is not None:
            parts.append(Comparison("<", v, IntLit(self.lo)))
        if self.hi is not None:
            parts.append(Comparison(">", v, IntLit(self.hi)))
        if not parts:
            from deppy.predicates.boolean import _FALSE
            return _FALSE
        if len(parts) == 1:
            return parts[0]
        from deppy.predicates.boolean import Or
        return Or(parts)

    def simplify(self) -> Predicate:
        if self.lo is not None and self.hi is not None and self.lo > self.hi:
            from deppy.predicates.boolean import _FALSE
            return _FALSE
        if self.lo is None and self.hi is None:
            from deppy.predicates.boolean import _TRUE
            return _TRUE
        return self

    def pretty(self) -> str:
        lo_str = str(self.lo) if self.lo is not None else "-∞"
        hi_str = str(self.hi) if self.hi is not None else "∞"
        return f"{lo_str} <= {self.variable} <= {hi_str}"

    def walk(self) -> Iterator[Predicate]:
        yield self

    def walk_terms(self) -> Iterator[Term]:
        yield Var(self.variable)

    def contains(self, value: int) -> bool:
        """Return ``True`` when *value* is inside the range."""
        if self.lo is not None and value < self.lo:
            return False
        if self.hi is not None and value > self.hi:
            return False
        return True

    def intersect(self, other: IntRange) -> Optional[IntRange]:
        """Return the intersection of two ranges for the same variable, or ``None``."""
        if self.variable != other.variable:
            return None
        new_lo = _max_opt(self.lo, other.lo)
        new_hi = _min_opt(self.hi, other.hi)
        if new_lo is not None and new_hi is not None and new_lo > new_hi:
            return None
        return IntRange(variable=self.variable, lo=new_lo, hi=new_hi)

    def __repr__(self) -> str:
        return f"IntRange({self.variable!r}, lo={self.lo!r}, hi={self.hi!r})"


# ===================================================================
#  Arithmetic normalizer
# ===================================================================

class ArithmeticNormalizer:
    """Rewrites arithmetic predicates to canonical ``LinearInequality`` form.

    Only predicates whose terms are linear combinations of integer variables
    (with literal coefficients) can be fully normalised.  Non-linear terms
    are left as ``Comparison`` nodes.
    """

    def normalize(self, pred: Predicate) -> List[LinearInequality]:
        """Attempt to rewrite *pred* as a conjunction of ``LinearInequality``.

        Returns:
            A list of linear inequalities whose conjunction is equivalent
            to *pred*.  If normalization fails the list is empty.
        """
        if isinstance(pred, LinearInequality):
            return [pred]
        if isinstance(pred, IntRange):
            return self._range_to_linear(pred)
        if isinstance(pred, Comparison):
            return self._comparison_to_linear(pred)
        from deppy.predicates.boolean import And
        if isinstance(pred, And):
            result: List[LinearInequality] = []
            for c in pred.conjuncts:
                sub = self.normalize(c)
                if not sub:
                    return []
                result.extend(sub)
            return result
        return []

    # -- helpers --------------------------------------------------------

    def _comparison_to_linear(
        self, cmp: Comparison
    ) -> List[LinearInequality]:
        """Rewrite ``left op right`` into ≥ 0 form."""
        left_coeffs = self._linearize(cmp.left)
        right_coeffs = self._linearize(cmp.right)
        if left_coeffs is None or right_coeffs is None:
            return []

        # diff = left - right  →  {var: coeff}  and constant offset
        diff = dict(left_coeffs)
        diff_const = diff.pop("", 0)
        for var, coeff in right_coeffs.items():
            if var == "":
                diff_const -= coeff
            else:
                diff[var] = diff.get(var, 0) - coeff

        src = cmp.source_location

        if cmp.op == ">=":
            # left - right >= 0
            return [LinearInequality(diff, diff_const, source_location=src)]
        if cmp.op == ">":
            # left - right - 1 >= 0
            return [LinearInequality(diff, diff_const - 1, source_location=src)]
        if cmp.op == "<=":
            # right - left >= 0  ⟺  -(left - right) >= 0
            neg = {v: -c for v, c in diff.items()}
            return [LinearInequality(neg, -diff_const, source_location=src)]
        if cmp.op == "<":
            neg = {v: -c for v, c in diff.items()}
            return [LinearInequality(neg, -diff_const - 1, source_location=src)]
        if cmp.op == "==":
            # left - right >= 0 AND right - left >= 0
            neg = {v: -c for v, c in diff.items()}
            return [
                LinearInequality(diff, diff_const, source_location=src),
                LinearInequality(neg, -diff_const, source_location=src),
            ]
        if cmp.op == "!=":
            # Cannot represent ≠ as a single ≥ 0
            return []
        return []

    def _range_to_linear(self, rng: IntRange) -> List[LinearInequality]:
        result: List[LinearInequality] = []
        src = rng.source_location
        if rng.lo is not None:
            # x - lo >= 0
            result.append(
                LinearInequality({rng.variable: 1}, -rng.lo, source_location=src)
            )
        if rng.hi is not None:
            # hi - x >= 0
            result.append(
                LinearInequality({rng.variable: -1}, rng.hi, source_location=src)
            )
        return result

    def _linearize(self, term: Term) -> Optional[Dict[str, int]]:
        """Attempt to extract ``{var: coeff, "": constant}`` from *term*.

        Returns ``None`` if the term is non-linear.
        """
        if isinstance(term, IntLit):
            return {"": term.value}
        if isinstance(term, Var):
            return {term.name: 1}
        if isinstance(term, UnaryOp):
            if term.op == "-":
                inner = self._linearize(term.operand)
                if inner is None:
                    return None
                return {k: -v for k, v in inner.items()}
            if term.op == "+":
                return self._linearize(term.operand)
            return None
        if isinstance(term, BinOp):
            left = self._linearize(term.left)
            right = self._linearize(term.right)
            if left is None or right is None:
                return None
            if term.op == "+":
                merged = dict(left)
                for k, v in right.items():
                    merged[k] = merged.get(k, 0) + v
                return merged
            if term.op == "-":
                merged = dict(left)
                for k, v in right.items():
                    merged[k] = merged.get(k, 0) - v
                return merged
            if term.op == "*":
                # At least one side must be constant
                if set(left.keys()) == {""}:
                    c = left.get("", 0)
                    return {k: v * c for k, v in right.items()}
                if set(right.keys()) == {""}:
                    c = right.get("", 0)
                    return {k: v * c for k, v in left.items()}
                return None  # non-linear
            return None
        return None


# ===================================================================
#  Internal helpers
# ===================================================================

def _eval_int_cmp(op: str, a: int, b: int) -> bool:
    if op == "<":
        return a < b
    if op == "<=":
        return a <= b
    if op == ">":
        return a > b
    if op == ">=":
        return a >= b
    if op == "==":
        return a == b
    if op == "!=":
        return a != b
    raise ValueError(op)


def _eval_float_cmp(op: str, a: float, b: float) -> bool:
    if op == "<":
        return a < b
    if op == "<=":
        return a <= b
    if op == ">":
        return a > b
    if op == ">=":
        return a >= b
    if op == "==":
        return a == b
    if op == "!=":
        return a != b
    raise ValueError(op)


def _max_opt(a: Optional[int], b: Optional[int]) -> Optional[int]:
    if a is None:
        return b
    if b is None:
        return a
    return max(a, b)


def _min_opt(a: Optional[int], b: Optional[int]) -> Optional[int]:
    if a is None:
        return b
    if b is None:
        return a
    return min(a, b)


def _linear_to_comparison(li: LinearInequality) -> Comparison:
    """Convert a ``LinearInequality`` back to a ``Comparison(>=, lhs, 0)``."""
    terms: List[Term] = []
    for var, coeff in li.coefficients:
        if coeff == 1:
            terms.append(Var(var))
        else:
            terms.append(BinOp("*", IntLit(coeff), Var(var)))
    if li.constant != 0:
        terms.append(IntLit(li.constant))
    if not terms:
        lhs: Term = IntLit(0)
    elif len(terms) == 1:
        lhs = terms[0]
    else:
        lhs = terms[0]
        for t in terms[1:]:
            lhs = BinOp("+", lhs, t)
    return Comparison(">=", lhs, IntLit(0), source_location=li.source_location)
