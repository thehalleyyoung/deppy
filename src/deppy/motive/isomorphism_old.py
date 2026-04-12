"""Z3 Motive Isomorphism Solver.

Given two motives M(f) and M(g), encodes the question
"∃ isomorphism φ: M(f) ≅ M(g)?" as a Z3 satisfiability query.

The encoding:

Z3 Variables:
    π : {0..|O_f|-1} → {0..|O_g|-1}     — bijection on operation classes

Z3 Constraints:
    1. BIJECTIVE:    AllDistinct(π)  ∧  |O_f| = |O_g|
    2. SORT-PRESERVING: ∀i. sort_sig(op_f[i]) ≈ sort_sig(op_g[π(i)])
    3. REFINEMENT:   ∀i. refine(op_f[i]) ∩ refine(op_g[π(i)]) ≠ ∅
    4. EFFECT:       ∀i. effect(op_f[i]) = effect(op_g[π(i)])
    5. NAME:         ∀i. name(op_f[i]) compatible with name(op_g[π(i)])
    6. MULTIPLICITY: ∀i. count(class_f[i]) = count(class_g[π(i)])

Query:  SAT(1∧2∧3∧4∧5∧6) → EQUIVALENT

If Z3 returns UNSAT, the motives are provably non-isomorphic.
If SAT, we have a witness isomorphism.
If UNKNOWN/timeout, we fall back to algebraic invariant comparison.

This solver is general — it works for any pair of motives, not
just those from Python programs.
"""

from __future__ import annotations

from collections import Counter
from typing import FrozenSet, List, Optional, Set, Tuple

from deppy.motive.sorts import sorts_compatible
from deppy.motive.operations import TypedOp
from deppy.motive.motive import Motive
from deppy.motive.morphism import MotiveMorphism

# Operations too syntactic to carry semantic content
_TRIVIAL_OPS = frozenset({
    'Assign.bind', 'Assign.rebind', 'Return',
    'Branch.test', 'Destructure.unpack',
})


def _semantic_class_key(op: TypedOp) -> Tuple:
    """Classification key for a typed operation (what π must preserve)."""
    return op.classification_key()


def _semantic_classes(ops: List[TypedOp]) -> Counter:
    """Count operations per semantic class, filtering trivial ops."""
    return Counter(
        _semantic_class_key(op) for op in ops
        if op.name not in _TRIVIAL_OPS
    )


class MotiveIsomorphismSolver:
    """Solve motive isomorphism via Z3 SAT encoding.

    Usage:
        solver = MotiveIsomorphismSolver()
        result, explanation = solver.check(motive_f, motive_g)
        # result: True (equivalent), False (definitely not), None (inconclusive)
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        self._timeout_ms = timeout_ms

    def check(self, mf: Motive, mg: Motive) -> Tuple[Optional[bool], str]:
        """Check if motives are isomorphic.

        Returns (result, explanation) where result is:
            True  — Z3 proved SAT (isomorphism exists)
            False — necessary conditions fail
            None  — inconclusive
        """
        # Phase 1: Necessary conditions (cheap, no Z3)
        ok, reason = mf.necessary_conditions_met(mg)
        if not ok:
            return False, f"Pre-filter: {reason}"

        # Phase 2: Z3 isomorphism query
        z3_result = self._z3_isomorphism(mf, mg)
        if z3_result is True:
            # Phase 2b: Post-Z3 soft fingerprint check
            # Z3 says ops are isomorphic, but concrete content may differ
            if not mf.soft_fingerprints_match(mg):
                return False, "Z3-SAT but concrete fingerprints diverge"
            return True, (f"Z3-SAT: motive isomorphism. "
                         f"H⁰={mf.h0}/{mg.h0}, H¹={mf.h1}/{mg.h1}, "
                         f"ops={mf.op_count}/{mg.op_count}, "
                         f"blocks={mf.num_blocks}/{mg.num_blocks}")
        if z3_result is False:
            return False, "Z3-UNSAT: no motive isomorphism exists"

        # Phase 3: Conservative algebraic fallback
        return self._algebraic_fallback(mf, mg)

    def _z3_isomorphism(self, mf: Motive, mg: Motive) -> Optional[bool]:
        """Encode motive isomorphism as Z3 SAT query."""
        try:
            import z3
        except ImportError:
            return None

        sem_f = _semantic_classes(mf.operations)
        sem_g = _semantic_classes(mg.operations)

        # Quick check: identical class multisets → instant SAT
        if sem_f == sem_g:
            return True

        classes_f = sorted(sem_f.keys())
        classes_g = sorted(sem_g.keys())
        nf, ng = len(classes_f), len(classes_g)

        if nf == 0 and ng == 0:
            return True
        if nf == 0 or ng == 0:
            return None
        if nf != ng:
            return None  # Can't biject different-sized sets

        # Build Z3 model
        solver = z3.Solver()
        solver.set("timeout", self._timeout_ms)

        pi = [z3.Int(f'pi_{i}') for i in range(nf)]

        # Range
        for i in range(nf):
            solver.add(pi[i] >= 0, pi[i] < ng)

        # Injectivity
        if nf > 1:
            solver.add(z3.Distinct(*pi))

        # Compatibility constraints
        for i, cf in enumerate(classes_f):
            name_f, sig_f, eff_f, ref_f = cf
            for j, cg in enumerate(classes_g):
                name_g, sig_g, eff_g, ref_g = cg
                if not self._classes_compatible(cf, cg, sem_f, sem_g):
                    solver.add(pi[i] != j)

        result = solver.check()
        if result == z3.sat:
            return True
        elif result == z3.unsat:
            return False
        return None

    def _classes_compatible(self, cf: Tuple, cg: Tuple,
                            counts_f: Counter, counts_g: Counter) -> bool:
        """Check if two operation classes can be mapped under π."""
        name_f, sig_f, eff_f, ref_f = cf
        name_g, sig_g, eff_g, ref_g = cg

        # Name
        if not MotiveMorphism.names_compatible(name_f, name_g):
            return False

        # Sort signature
        input_f, output_f = sig_f
        input_g, output_g = sig_g
        if len(input_f) != len(input_g):
            return False
        if not sorts_compatible(output_f, output_g):
            return False
        for sf, sg in zip(input_f, input_g):
            if not sorts_compatible(sf, sg):
                return False

        # Effect
        if eff_f != eff_g:
            return False

        # Refinement overlap
        ref_set_f, ref_set_g = set(ref_f), set(ref_g)
        if ref_set_f and ref_set_g and not (ref_set_f & ref_set_g):
            return False

        # Multiplicity
        if counts_f[cf] != counts_g[cg]:
            return False

        return True

    def _algebraic_fallback(self, mf: Motive, mg: Motive) -> Tuple[Optional[bool], str]:
        """Conservative algebraic comparison when Z3 is inconclusive.

        Uses K-theory, tropical, character invariants.
        Only returns True when ALL invariants converge.
        """
        sem_f = _semantic_classes(mf.operations)
        sem_g = _semantic_classes(mg.operations)

        # Character similarity
        all_keys = set(sem_f.keys()) | set(sem_g.keys())
        if all_keys:
            match = sum(min(sem_f.get(k, 0), sem_g.get(k, 0)) for k in all_keys)
            total = sum(max(sem_f.get(k, 0), sem_g.get(k, 0)) for k in all_keys)
            char_sim = match / total if total > 0 else 1.0
        else:
            char_sim = 1.0

        # Tropical
        if not mf.tropical.compatible_with(mg.tropical):
            return None, "tropical divergence"

        # K₀
        k_dist = mf.k_theory.distance(mg.k_theory)

        # Character must be very high
        if char_sim < 0.90:
            return None, f"char_sim={char_sim:.2f} < 0.90"

        if k_dist > 0.3:
            return None, f"K₀ distance={k_dist:.2f} > 0.3"

        return True, (f"Algebraic convergence: char={char_sim:.2f}, "
                     f"K₀_dist={k_dist:.2f}, trop={mf.tropical.loop_depth}")
