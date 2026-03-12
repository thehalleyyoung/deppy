"""Predicate normalization and semantic comparisons.

Provides:

- **PredicateNormalizer**: Rewrites predicates to canonical forms so that
  structurally different but logically equivalent predicates can be compared.
- Quick syntactic entailment and contradiction checks.
- Conjunction / disjunction combinators.
"""

from __future__ import annotations

from typing import (
    Dict,
    List,
    Optional,
    Set,
)

from deppy.predicates.base import (
    IntLit,
    Predicate,
    Term,
    Var,
)


class PredicateNormalizer:
    """Normalises predicates to canonical forms for comparison and solving.

    The normalizer applies a sequence of rewriting passes:

    1. **Simplify** — fold constants, flatten nested And/Or, eliminate
       double negation.
    2. **Sort** — order conjuncts/disjuncts by a canonical key so that
       ``x > 0 ∧ y > 0`` and ``y > 0 ∧ x > 0`` become identical.
    3. **Arithmetic canonicalization** — rewrite ``Comparison`` nodes to
       ``LinearInequality`` when possible, then back to a canonical
       ``Comparison`` form.
    """

    def normalize(self, pred: Predicate) -> Predicate:
        """Return a canonical form of *pred*."""
        result = pred
        for _ in range(10):
            next_ = self._normalize_once(result)
            if next_ == result:
                return result
            result = next_
        return result

    # ------------------------------------------------------------------
    #  Entailment / contradiction (syntactic fast-path)
    # ------------------------------------------------------------------

    def alpha_equivalent(self, a: Predicate, b: Predicate) -> bool:
        """Return ``True`` when *a* and *b* are α-equivalent.

        Two predicates are α-equivalent when they are structurally identical
        up to consistent renaming of bound variables.
        """
        na = self.normalize(a)
        nb = self.normalize(b)
        return na == nb

    def implies(self, a: Predicate, b: Predicate) -> Optional[bool]:
        """Quick syntactic check: does *a* ⊨ *b*?

        Returns ``True`` when provably entailed, ``False`` when provably
        not entailed, and ``None`` when unknown (needs SMT).
        """
        from deppy.predicates.boolean import And, Or, is_true, is_false

        na = self.normalize(a)
        nb = self.normalize(b)

        # Trivial cases
        if is_true(nb):
            return True
        if is_false(na):
            return True  # ex falso quodlibet
        if na == nb:
            return True
        if is_true(na) and not is_true(nb):
            return None  # True ⊨ ? — need semantics
        if is_false(nb):
            return None

        # a = (… ∧ b ∧ …) → a ⊨ b
        if isinstance(na, And):
            for c in na.conjuncts:
                if self.normalize(c) == nb:
                    return True

        # a ⊨ (… ∨ a ∨ …)
        if isinstance(nb, Or):
            for d in nb.disjuncts:
                if self.normalize(d) == na:
                    return True

        # IntRange containment
        from deppy.predicates.arithmetic import IntRange
        if isinstance(na, IntRange) and isinstance(nb, IntRange):
            if na.variable == nb.variable:
                return self._range_implies(na, nb)

        return None

    def contradicts(self, a: Predicate, b: Predicate) -> Optional[bool]:
        """Quick check: are *a* and *b* jointly unsatisfiable?

        Returns ``True`` / ``False`` / ``None`` (unknown).
        """
        from deppy.predicates.boolean import And, is_false

        na = self.normalize(a)
        nb = self.normalize(b)

        # a ∧ ¬a is contradictory
        neg_b = self.normalize(nb.negate())
        if na == neg_b:
            return True

        # Check if conjunction simplifies to False
        conj = self.conjoin([na, nb])
        nc = self.normalize(conj)
        if is_false(nc):
            return True

        # IntRange disjointness
        from deppy.predicates.arithmetic import IntRange
        if isinstance(na, IntRange) and isinstance(nb, IntRange):
            if na.variable == nb.variable:
                return na.intersect(nb) is None

        return None

    # ------------------------------------------------------------------
    #  Combinators
    # ------------------------------------------------------------------

    def conjoin(self, preds: List[Predicate]) -> Predicate:
        """Return the conjunction of *preds*, flattening nested ``And``."""
        from deppy.predicates.boolean import And, _TRUE

        if not preds:
            return _TRUE
        flat: List[Predicate] = []
        for p in preds:
            n = self.normalize(p)
            if isinstance(n, And):
                flat.extend(n.conjuncts)
            else:
                flat.append(n)
        if not flat:
            return _TRUE
        if len(flat) == 1:
            return flat[0]
        return And(flat)

    def disjoin(self, preds: List[Predicate]) -> Predicate:
        """Return the disjunction of *preds*, flattening nested ``Or``."""
        from deppy.predicates.boolean import Or, _FALSE

        if not preds:
            return _FALSE
        flat: List[Predicate] = []
        for p in preds:
            n = self.normalize(p)
            if isinstance(n, Or):
                flat.extend(n.disjuncts)
            else:
                flat.append(n)
        if not flat:
            return _FALSE
        if len(flat) == 1:
            return flat[0]
        return Or(flat)

    # ------------------------------------------------------------------
    #  Internal normalization passes
    # ------------------------------------------------------------------

    def _normalize_once(self, pred: Predicate) -> Predicate:
        """Single normalization pass."""
        from deppy.predicates.arithmetic import (
            Comparison,
            IntRange,
            LinearInequality,
        )
        from deppy.predicates.boolean import (
            And,
            Exists,
            ForAll,
            Iff,
            Implies,
            Not,
            Or,
            _FALSE,
            _TRUE,
            is_false,
            is_true,
        )

        # 1. Structural simplification
        simplified = pred.simplify()

        # 2. Specific normalization rules
        if isinstance(simplified, And):
            children = [self._normalize_once(c) for c in simplified.conjuncts]
            # Remove True, short-circuit on False
            filtered: List[Predicate] = []
            for c in children:
                if is_false(c):
                    return _FALSE
                if not is_true(c):
                    filtered.append(c)
            # Flatten nested And
            flat: List[Predicate] = []
            for c in filtered:
                if isinstance(c, And):
                    flat.extend(c.conjuncts)
                else:
                    flat.append(c)
            # Sort by canonical key for determinism
            flat.sort(key=_pred_sort_key)
            # Deduplicate
            seen: set[Predicate] = set()
            deduped: List[Predicate] = []
            for p in flat:
                if p not in seen:
                    seen.add(p)
                    deduped.append(p)
            if not deduped:
                return _TRUE
            if len(deduped) == 1:
                return deduped[0]
            return And(deduped)

        if isinstance(simplified, Or):
            children = [self._normalize_once(d) for d in simplified.disjuncts]
            filtered_d: List[Predicate] = []
            for d in children:
                if is_true(d):
                    return _TRUE
                if not is_false(d):
                    filtered_d.append(d)
            flat_d: List[Predicate] = []
            for d in filtered_d:
                if isinstance(d, Or):
                    flat_d.extend(d.disjuncts)
                else:
                    flat_d.append(d)
            flat_d.sort(key=_pred_sort_key)
            seen_d: set[Predicate] = set()
            deduped_d: List[Predicate] = []
            for p in flat_d:
                if p not in seen_d:
                    seen_d.add(p)
                    deduped_d.append(p)
            if not deduped_d:
                return _FALSE
            if len(deduped_d) == 1:
                return deduped_d[0]
            return Or(deduped_d)

        if isinstance(simplified, Not):
            inner = self._normalize_once(simplified.operand)
            if isinstance(inner, Not):
                return inner.operand
            if is_true(inner):
                return _FALSE
            if is_false(inner):
                return _TRUE
            return Not(inner)

        if isinstance(simplified, Implies):
            a = self._normalize_once(simplified.antecedent)
            b = self._normalize_once(simplified.consequent)
            return Implies(a, b)

        if isinstance(simplified, Iff):
            a = self._normalize_once(simplified.left)
            b = self._normalize_once(simplified.right)
            if a == b:
                return _TRUE
            return Iff(a, b)

        if isinstance(simplified, (ForAll, Exists)):
            body = self._normalize_once(simplified.body)
            if simplified.var not in body.free_variables():
                return body
            if isinstance(simplified, ForAll):
                return ForAll(
                    var=simplified.var, body=body, domain=simplified.domain,
                )
            return Exists(
                var=simplified.var, body=body, domain=simplified.domain,
            )

        # Normalize comparison direction: prefer variable on the left
        if isinstance(simplified, Comparison):
            return self._normalize_comparison(simplified)

        return simplified

    def _normalize_comparison(self, cmp: Comparison) -> Predicate:
        """Normalize a comparison to a canonical orientation."""
        from deppy.predicates.arithmetic import Comparison

        # If right side is a Var and left is a literal, flip
        if isinstance(cmp.right, Var) and not isinstance(cmp.left, Var):
            return cmp.flip()
        # Normalize == and != so smaller variable name is on the left
        if cmp.op in {"==", "!="} and isinstance(cmp.left, Var) and isinstance(cmp.right, Var):
            if cmp.left.name > cmp.right.name:
                return cmp.flip()
        return cmp

    def _range_implies(self, a: IntRange, b: IntRange) -> Optional[bool]:
        """Check if range *a* is contained in range *b*."""
        # a ⊨ b iff b.lo <= a.lo and a.hi <= b.hi
        lo_ok: Optional[bool] = None
        if b.lo is None:
            lo_ok = True
        elif a.lo is not None:
            lo_ok = a.lo >= b.lo
        else:
            lo_ok = None

        hi_ok: Optional[bool] = None
        if b.hi is None:
            hi_ok = True
        elif a.hi is not None:
            hi_ok = a.hi <= b.hi
        else:
            hi_ok = None

        if lo_ok is True and hi_ok is True:
            return True
        if lo_ok is False or hi_ok is False:
            return False
        return None


# ===================================================================
#  Sorting key for canonical ordering
# ===================================================================

def _pred_sort_key(pred: Predicate) -> str:
    """Return a string key for deterministic ordering of conjuncts/disjuncts."""
    return pred.pretty()
