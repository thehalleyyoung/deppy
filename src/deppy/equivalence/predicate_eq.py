"""Predicate equivalence checking — the computational core.

This module replaces the shallow ``repr()``-based predicate comparisons
that previously appeared in the cohomology, fiber-product, and naturality
code with genuine **sheaf-type-theoretic predicate equivalence**.

Two predicates ``p, q`` are equivalent when the **biimplication**
``p ⟺ q`` is universally valid:

    p ≡ q   ⟺   ⊢ (p ⟹ q) ∧ (q ⟹ p)

The verification is three-tiered:

1. **Structural identity** — fast AST comparison (sound *and* complete
   when predicates share the same canonical form).
2. **Algebraic simplification** — detect commutativity / absorption /
   idempotence / double-negation before calling the solver.
3. **Solver discharge** — emit the biimplication as a ``VerificationCondition``
   and route it to the Z3 backend (if available).  When Z3 is absent the
   result degrades gracefully to ``UNKNOWN``.

The module exposes a single entry-point :func:`predicates_equivalent` whose
result carries enough categorical information for cohomology (cocycle
composition), naturality (path commutativity), and fiber-product gluing
(equaliser agreement).

Mathematical grounding
~~~~~~~~~~~~~~~~~~~~~~
In the internal language of a presheaf topos **Set^{S^op}**, predicate
equivalence at a site *U* is the statement

    Ω(U) ⊢  [φ] = [ψ]

where ``Ω`` is the subobject classifier and ``[φ]`` is the
characteristic map of the subobject determined by ``φ``.  The
biimplication ``φ ⟺ ψ`` is exactly the condition for the two
characteristic maps to agree, which is what we check.

For the **cocycle condition** ``g_{jk} ∘ g_{ij} = g_{ik}`` in Čech
cohomology, predicate composition is modelled as conjunction of
transition predicates restricted to the triple overlap, and equivalence
of the composed predicate to the direct transition predicate is the
cocycle identity.

For **naturality squares**, path-1 and path-2 predicates encode the two
routes around the square; their equivalence certifies commutativity.

Copyright © 2025 deppy contributors.  MIT licence.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple

from deppy.types.refinement import (
    ConjunctionPred,
    DisjunctionPred,
    FalsePred,
    ImplicationPred,
    NotPred,
    Predicate,
    TruePred,
    VarPred,
)

# ---------------------------------------------------------------------------
# Lazy Z3 import (mirrors pattern used throughout deppy)
# ---------------------------------------------------------------------------

_z3: Any = None
_z3_available: Optional[bool] = None


def _ensure_z3() -> Tuple[Any, bool]:
    global _z3, _z3_available
    if _z3_available is not None:
        return _z3, _z3_available
    try:
        import z3 as z3_mod          # type: ignore[import-untyped]
        _z3 = z3_mod
        _z3_available = True
    except ImportError:
        _z3 = None
        _z3_available = False
    return _z3, _z3_available


# ═══════════════════════════════════════════════════════════════════════════════
# Result types
# ═══════════════════════════════════════════════════════════════════════════════


class PredicateRelation(enum.Enum):
    """Outcome of comparing two predicates."""

    EQUIVALENT = "equivalent"
    """p ⟺ q holds universally."""

    IMPLIES_FORWARD = "implies_forward"
    """p ⟹ q holds but q ⟹ p does not (strict refinement)."""

    IMPLIES_BACKWARD = "implies_backward"
    """q ⟹ p holds but p ⟹ q does not."""

    INEQUIVALENT = "inequivalent"
    """Neither direction holds; a counterexample was found."""

    UNKNOWN = "unknown"
    """Could not be determined (solver timeout or unavailable)."""


@dataclass(frozen=True)
class PredicateEquivalenceResult:
    """Full result of comparing two predicates.

    Carries enough information for:
    - cohomology (is the cocycle identity satisfied?)
    - naturality (do the two paths commute?)
    - gluing (do restricted predicates agree on the overlap?)
    """

    relation: PredicateRelation

    # The biimplication VC that was (or would be) checked.
    biimplication: Optional[Predicate] = None

    # If INEQUIVALENT, a witness model distinguishing p from q.
    counterexample: Optional[Dict[str, Any]] = None

    # The forward / backward VCs individually.
    forward_vc: Optional[Predicate] = None   # p ⟹ q
    backward_vc: Optional[Predicate] = None  # q ⟹ p

    # Whether each direction was discharged.
    forward_holds: Optional[bool] = None
    backward_holds: Optional[bool] = None

    # Proof evidence (for EQUIVALENT / one-directional).
    evidence: Optional[Any] = None

    @property
    def equivalent(self) -> bool:
        return self.relation is PredicateRelation.EQUIVALENT

    @property
    def refines_forward(self) -> bool:
        return self.relation in (
            PredicateRelation.EQUIVALENT,
            PredicateRelation.IMPLIES_FORWARD,
        )

    @property
    def refines_backward(self) -> bool:
        return self.relation in (
            PredicateRelation.EQUIVALENT,
            PredicateRelation.IMPLIES_BACKWARD,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Structural comparison (Tier 1 — fast, sound, incomplete)
# ═══════════════════════════════════════════════════════════════════════════════


def _structural_equal(p: Predicate, q: Predicate) -> Optional[bool]:
    """Return True if *p* and *q* are structurally identical predicates.

    This is a **recursive AST walk** — NOT ``repr()`` comparison.
    Returns ``None`` if structure differs (not necessarily inequivalent).
    """
    if type(p) is not type(q):
        return None

    if isinstance(p, TruePred):
        return True
    if isinstance(p, FalsePred):
        return True
    if isinstance(p, VarPred):
        return p.var_name == q.var_name  # type: ignore[union-attr]

    if isinstance(p, NotPred):
        return _structural_equal(p.inner, q.inner)  # type: ignore[union-attr]

    if isinstance(p, ImplicationPred):
        a = _structural_equal(p.antecedent, q.antecedent)  # type: ignore[union-attr]
        c = _structural_equal(p.consequent, q.consequent)  # type: ignore[union-attr]
        if a is True and c is True:
            return True
        return None

    if isinstance(p, ConjunctionPred):
        pc = p.conjuncts  # type: ignore[union-attr]
        qc = q.conjuncts  # type: ignore[union-attr]
        if len(pc) != len(qc):
            return None
        # Order-sensitive first, then try sorted by repr as fallback
        if all(_structural_equal(a, b) is True for a, b in zip(pc, qc)):
            return True
        # Commutativity: try matching as multisets
        return _multiset_equal(list(pc), list(qc))

    if isinstance(p, DisjunctionPred):
        pd = p.disjuncts  # type: ignore[union-attr]
        qd = q.disjuncts  # type: ignore[union-attr]
        if len(pd) != len(qd):
            return None
        if all(_structural_equal(a, b) is True for a, b in zip(pd, qd)):
            return True
        return _multiset_equal(list(pd), list(qd))

    # ComparisonPred and other subtypes — delegate to repr as last resort
    # (This is still structural, not semantic)
    if repr(p) == repr(q):
        return True
    return None


def _multiset_equal(ps: List[Predicate], qs: List[Predicate]) -> Optional[bool]:
    """Check if two lists of predicates are equal as multisets.

    Handles commutativity of conjunction/disjunction.
    """
    remaining = list(qs)
    for p in ps:
        found = False
        for i, q in enumerate(remaining):
            if _structural_equal(p, q) is True:
                remaining.pop(i)
                found = True
                break
        if not found:
            return None
    return True if not remaining else None


# ═══════════════════════════════════════════════════════════════════════════════
# Algebraic simplification (Tier 2 — detect trivial equivalences)
# ═══════════════════════════════════════════════════════════════════════════════


def _algebraically_equivalent(p: Predicate, q: Predicate) -> Optional[bool]:
    """Detect equivalences via algebraic laws.

    Currently handles:
    - True ≡ True, False ≡ False
    - p ∧ True ≡ p, p ∨ False ≡ p (absorption)
    - ¬¬p ≡ p (double negation)
    - p ∧ p ≡ p, p ∨ p ≡ p (idempotence)
    - p ⟹ True ≡ True, False ⟹ q ≡ True
    """
    # Normalise each predicate and try structural comparison.
    np = _normalise(p)
    nq = _normalise(q)
    return _structural_equal(np, nq)


def _normalise(p: Predicate) -> Predicate:
    """Apply basic algebraic simplifications."""
    if isinstance(p, ConjunctionPred):
        children = [_normalise(c) for c in p.conjuncts]
        # Remove True conjuncts
        children = [c for c in children if not isinstance(c, TruePred)]
        if not children:
            return TruePred()
        if any(isinstance(c, FalsePred) for c in children):
            return FalsePred()
        if len(children) == 1:
            return children[0]
        # Deduplicate (idempotence)
        unique: List[Predicate] = []
        for c in children:
            if not any(_structural_equal(c, u) is True for u in unique):
                unique.append(c)
        if len(unique) == 1:
            return unique[0]
        return ConjunctionPred(conjuncts=tuple(unique))

    if isinstance(p, DisjunctionPred):
        children = [_normalise(c) for c in p.disjuncts]
        children = [c for c in children if not isinstance(c, FalsePred)]
        if not children:
            return FalsePred()
        if any(isinstance(c, TruePred) for c in children):
            return TruePred()
        if len(children) == 1:
            return children[0]
        unique = []
        for c in children:
            if not any(_structural_equal(c, u) is True for u in unique):
                unique.append(c)
        if len(unique) == 1:
            return unique[0]
        return DisjunctionPred(disjuncts=tuple(unique))

    if isinstance(p, NotPred):
        inner = _normalise(p.inner)
        if isinstance(inner, NotPred):
            return inner.inner  # ¬¬p = p
        if isinstance(inner, TruePred):
            return FalsePred()
        if isinstance(inner, FalsePred):
            return TruePred()
        return NotPred(inner=inner)

    if isinstance(p, ImplicationPred):
        ant = _normalise(p.antecedent)
        con = _normalise(p.consequent)
        if isinstance(con, TruePred):
            return TruePred()  # p ⟹ True ≡ True
        if isinstance(ant, FalsePred):
            return TruePred()  # False ⟹ q ≡ True
        if isinstance(ant, TruePred):
            return con          # True ⟹ q ≡ q
        return ImplicationPred(antecedent=ant, consequent=con)

    return p


# ═══════════════════════════════════════════════════════════════════════════════
# Solver discharge (Tier 3 — Z3 for definitive answer)
# ═══════════════════════════════════════════════════════════════════════════════


def _try_z3_equivalence(
    p: Predicate,
    q: Predicate,
    timeout_ms: int = 5000,
) -> PredicateEquivalenceResult:
    """Attempt to prove p ⟺ q via Z3.

    Strategy: check satisfiability of ¬(p ⟺ q), i.e. (p ∧ ¬q) ∨ (¬p ∧ q).
    If UNSAT → equivalent. If SAT → counterexample. If UNKNOWN → degrade.
    """
    z3_mod, available = _ensure_z3()
    if not available:
        fwd = ImplicationPred(antecedent=p, consequent=q)
        bwd = ImplicationPred(antecedent=q, consequent=p)
        biimp = ConjunctionPred(conjuncts=(fwd, bwd))
        return PredicateEquivalenceResult(
            relation=PredicateRelation.UNKNOWN,
            biimplication=biimp,
            forward_vc=fwd,
            backward_vc=bwd,
        )

    # Try to use the deppy Z3 encoder if available
    try:
        from deppy.solver.z3_encoder import Z3Encoder
        encoder = Z3Encoder()

        # Encode both predicates
        z3_p = encoder.encode(p)
        z3_q = encoder.encode(q)

        # Check forward: p ∧ ¬q (counterexample to p ⟹ q)
        solver_fwd = z3_mod.Solver()
        solver_fwd.set("timeout", timeout_ms)
        solver_fwd.add(z3_p)
        solver_fwd.add(z3_mod.Not(z3_q))
        fwd_result = solver_fwd.check()

        # Check backward: ¬p ∧ q (counterexample to q ⟹ p)
        solver_bwd = z3_mod.Solver()
        solver_bwd.set("timeout", timeout_ms)
        solver_bwd.add(z3_mod.Not(z3_p))
        solver_bwd.add(z3_q)
        bwd_result = solver_bwd.check()

        fwd_holds = fwd_result == z3_mod.unsat
        bwd_holds = bwd_result == z3_mod.unsat

        fwd_vc = ImplicationPred(antecedent=p, consequent=q)
        bwd_vc = ImplicationPred(antecedent=q, consequent=p)
        biimp = ConjunctionPred(conjuncts=(fwd_vc, bwd_vc))

        cex = None
        if fwd_result == z3_mod.sat:
            try:
                model = solver_fwd.model()
                cex = {str(d): str(model[d]) for d in model.decls()}
            except Exception:
                cex = {"note": "counterexample extraction failed"}
        elif bwd_result == z3_mod.sat:
            try:
                model = solver_bwd.model()
                cex = {str(d): str(model[d]) for d in model.decls()}
            except Exception:
                cex = {"note": "counterexample extraction failed"}

        if fwd_holds and bwd_holds:
            relation = PredicateRelation.EQUIVALENT
        elif fwd_holds:
            relation = PredicateRelation.IMPLIES_FORWARD
        elif bwd_holds:
            relation = PredicateRelation.IMPLIES_BACKWARD
        elif fwd_result == z3_mod.sat and bwd_result == z3_mod.sat:
            relation = PredicateRelation.INEQUIVALENT
        else:
            relation = PredicateRelation.UNKNOWN

        return PredicateEquivalenceResult(
            relation=relation,
            biimplication=biimp,
            counterexample=cex,
            forward_vc=fwd_vc,
            backward_vc=bwd_vc,
            forward_holds=fwd_holds,
            backward_holds=bwd_holds,
        )

    except Exception:
        # If Z3 encoding fails, degrade gracefully
        fwd = ImplicationPred(antecedent=p, consequent=q)
        bwd = ImplicationPred(antecedent=q, consequent=p)
        biimp = ConjunctionPred(conjuncts=(fwd, bwd))
        return PredicateEquivalenceResult(
            relation=PredicateRelation.UNKNOWN,
            biimplication=biimp,
            forward_vc=fwd,
            backward_vc=bwd,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Public API
# ═══════════════════════════════════════════════════════════════════════════════


def predicates_equivalent(
    p: Predicate,
    q: Predicate,
    *,
    use_solver: bool = True,
    timeout_ms: int = 5000,
) -> PredicateEquivalenceResult:
    """Check whether two predicates are equivalent.

    Three-tiered approach:

    1. **Structural identity** — recursive AST comparison with
       commutativity handling for ∧ and ∨.
    2. **Algebraic simplification** — normalise via absorption,
       idempotence, double-negation, then re-check structurally.
    3. **Solver discharge** — emit ``(p ⟹ q) ∧ (q ⟹ p)`` as a VC
       and route to Z3.

    Parameters
    ----------
    p, q : Predicate
        The two predicates to compare.
    use_solver : bool
        Whether to attempt Z3 discharge (default True).
    timeout_ms : int
        Z3 solver timeout in milliseconds.

    Returns
    -------
    PredicateEquivalenceResult
        Full result including relation, VCs, counterexample, evidence.
    """
    # Tier 0: identity
    if p is q:
        return PredicateEquivalenceResult(
            relation=PredicateRelation.EQUIVALENT,
            forward_holds=True,
            backward_holds=True,
        )

    # Tier 1: structural equality
    struct = _structural_equal(p, q)
    if struct is True:
        return PredicateEquivalenceResult(
            relation=PredicateRelation.EQUIVALENT,
            forward_holds=True,
            backward_holds=True,
        )

    # Tier 2: algebraic simplification
    alg = _algebraically_equivalent(p, q)
    if alg is True:
        return PredicateEquivalenceResult(
            relation=PredicateRelation.EQUIVALENT,
            forward_holds=True,
            backward_holds=True,
        )

    # Tier 3: solver discharge
    if use_solver:
        return _try_z3_equivalence(p, q, timeout_ms=timeout_ms)

    # No solver — generate VCs for deferred checking
    fwd = ImplicationPred(antecedent=p, consequent=q)
    bwd = ImplicationPred(antecedent=q, consequent=p)
    biimp = ConjunctionPred(conjuncts=(fwd, bwd))
    return PredicateEquivalenceResult(
        relation=PredicateRelation.UNKNOWN,
        biimplication=biimp,
        forward_vc=fwd,
        backward_vc=bwd,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Composition helper for cocycle checking
# ═══════════════════════════════════════════════════════════════════════════════


def compose_predicates(p: Predicate, q: Predicate) -> Predicate:
    """Compose two transition predicates.

    In the Čech complex, the composition of transition functions
    ``g_{ij}`` and ``g_{jk}`` is modelled as the conjunction of
    their predicates restricted to the triple overlap:

        g_{jk} ∘ g_{ij}  ↦  g_{ij} ∧ g_{jk}

    This is the **internal composition** in the presheaf topos:
    composition of subobject-classifier maps is intersection (∧).
    """
    # Absorb trivial cases
    if isinstance(p, TruePred):
        return q
    if isinstance(q, TruePred):
        return p
    if isinstance(p, FalsePred) or isinstance(q, FalsePred):
        return FalsePred()

    return ConjunctionPred(conjuncts=(p, q))


def check_cocycle_identity(
    g_ij: Predicate,
    g_jk: Predicate,
    g_ik: Predicate,
    *,
    use_solver: bool = True,
    timeout_ms: int = 5000,
) -> PredicateEquivalenceResult:
    """Check the cocycle condition ``g_{jk} ∘ g_{ij} = g_{ik}``.

    The cocycle condition in Čech cohomology asserts that for every
    triple overlap ``U_i ∩ U_j ∩ U_k``, the composition of transition
    isomorphisms equals the direct transition.

    We model this as predicate equivalence:

        compose(g_ij, g_jk) ≡ g_ik

    Parameters
    ----------
    g_ij, g_jk, g_ik : Predicate
        Transition predicates on the pairwise overlaps.

    Returns
    -------
    PredicateEquivalenceResult
        Whether the cocycle identity holds.
    """
    composed = compose_predicates(g_ij, g_jk)
    return predicates_equivalent(
        composed, g_ik,
        use_solver=use_solver,
        timeout_ms=timeout_ms,
    )
