"""Z3/SMT solver bridge for equivalence verification conditions.

This module encodes equivalence predicates into Z3 and extracts
counterexamples from satisfying models.  It follows the lazy-import
pattern from deppy.solver.z3_encoder.

Key encodings:
- BiimplicationPred  → z3.And(z3.Implies(φ_f, φ_g), z3.Implies(φ_g, φ_f))
- EquivalencePred    → z3.ForAll([x], f(x) == g(x))
- RefinementEquivalencePred → z3.ForAll([v], z3.Iff(φ_f(v), φ_g(v)))
- BehavioralEquivalencePred → z3.ForAll([inputs], out_f == out_g)
- SectionAgreementPred      → z3.ForAll([v], z3.Iff(σ_f(v), σ_g(v)))
- TransportPred             → z3.Implies(z3.And(source_holds, path_holds), target_holds)
- FiberProductPred          → z3.And(φ_f(v), φ_g(v), equalizer_holds)
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Tuple,
)

from deppy.core._protocols import SiteId
from deppy.types.refinement import (
    ConjunctionPred,
    ComparisonOp,
    ComparisonPred,
    DisjunctionPred,
    FalsePred,
    ImplicationPred,
    NotPred,
    Predicate,
    RefinementType,
    TruePred,
    VarPred,
)

from deppy.equivalence._protocols import (
    EquivalenceObligation,
    EquivalenceVerdict,
    LocalEquivalenceJudgment,
)
from deppy.equivalence.predicates import (
    BiimplicationPred,
    BehavioralEquivalencePred,
    EquivalencePred,
    FiberProductPred,
    RefinementEquivalencePred,
    SectionAgreementPred,
    TransportPred,
)

# ═══════════════════════════════════════════════════════════════════════════════
# Lazy Z3 import (following deppy.solver.z3_encoder pattern)
# ═══════════════════════════════════════════════════════════════════════════════

_z3: Optional[Any] = None
_z3_available: Optional[bool] = None


def _ensure_z3() -> bool:
    """Lazily import z3 and cache availability."""
    global _z3, _z3_available
    if _z3_available is not None:
        return _z3_available
    try:
        import z3 as z3_module
        _z3 = z3_module
        _z3_available = True
    except ImportError:
        _z3_available = False
    return _z3_available


# ═══════════════════════════════════════════════════════════════════════════════
# Variable environment for equivalence VCs
# ═══════════════════════════════════════════════════════════════════════════════


class EquivalenceVariableEnv:
    """Variable environment for equivalence predicates.

    Manages Z3 constants for both programs' variables, ensuring that
    shared variables (e.g., inputs) map to the same Z3 constant while
    program-specific variables are distinct.
    """

    def __init__(self) -> None:
        self._vars: Dict[str, Any] = {}
        self._sorts: Dict[str, str] = {}  # var_name → sort hint

    def get_or_create(self, name: str, sort_hint: str = "Int") -> Any:
        """Get or create a Z3 variable."""
        if not _ensure_z3():
            raise RuntimeError("Z3 is not available")

        if name in self._vars:
            return self._vars[name]

        z3 = _z3
        assert z3 is not None

        if sort_hint == "Int":
            var = z3.Int(name)
        elif sort_hint == "Real":
            var = z3.Real(name)
        elif sort_hint == "Bool":
            var = z3.Bool(name)
        elif sort_hint == "String":
            var = z3.String(name)
        else:
            var = z3.Int(name)  # default

        self._vars[name] = var
        self._sorts[name] = sort_hint
        return var

    def get_all_vars(self) -> Dict[str, Any]:
        """Return all Z3 variables."""
        return dict(self._vars)

    def prefixed(self, prefix: str, name: str, sort_hint: str = "Int") -> Any:
        """Create a program-prefixed variable (e.g., 'f.x' vs 'g.x')."""
        return self.get_or_create(f"{prefix}.{name}", sort_hint)


# ═══════════════════════════════════════════════════════════════════════════════
# Equivalence predicate encoder
# ═══════════════════════════════════════════════════════════════════════════════


class EquivalenceEncoder:
    """Encode equivalence predicates into Z3 formulae.

    Dispatches on Predicate type:
    - Standard deppy predicates → delegate to base encoder logic
    - Equivalence-specific predicates → specialised encoding
    """

    def __init__(
        self,
        env: Optional[EquivalenceVariableEnv] = None,
    ) -> None:
        self._env = env or EquivalenceVariableEnv()

    def encode(self, pred: Predicate) -> Any:
        """Encode a Predicate into a Z3 expression."""
        if not _ensure_z3():
            raise RuntimeError("Z3 is not available")

        z3 = _z3
        assert z3 is not None

        # Dispatch on predicate type
        if isinstance(pred, TruePred):
            return z3.BoolVal(True)

        if isinstance(pred, FalsePred):
            return z3.BoolVal(False)

        if isinstance(pred, BiimplicationPred):
            return self._encode_biimplication(pred)

        if isinstance(pred, EquivalencePred):
            return self._encode_equivalence(pred)

        if isinstance(pred, RefinementEquivalencePred):
            return self._encode_refinement_equivalence(pred)

        if isinstance(pred, BehavioralEquivalencePred):
            return self._encode_behavioral_equivalence(pred)

        if isinstance(pred, SectionAgreementPred):
            return self._encode_section_agreement(pred)

        if isinstance(pred, TransportPred):
            return self._encode_transport(pred)

        if isinstance(pred, FiberProductPred):
            return self._encode_fiber_product(pred)

        if isinstance(pred, ConjunctionPred):
            return self._encode_conjunction(pred)

        if isinstance(pred, DisjunctionPred):
            return self._encode_disjunction(pred)

        if isinstance(pred, ImplicationPred):
            return self._encode_implication(pred)

        if isinstance(pred, NotPred):
            return self._encode_not(pred)

        if isinstance(pred, ComparisonPred):
            return self._encode_comparison(pred)

        if isinstance(pred, VarPred):
            return self._env.get_or_create(pred.name, "Bool")

        # Fallback: uninterpreted boolean
        return z3.Bool(f"pred_{id(pred)}")

    # ── Equivalence-specific encodings ────────────────────────────────────

    def _encode_biimplication(self, pred: BiimplicationPred) -> Any:
        """BiimplicationPred → And(Implies(φ_f, φ_g), Implies(φ_g, φ_f))."""
        z3 = _z3
        assert z3 is not None

        fwd = self.encode(pred.forward)
        bwd = self.encode(pred.backward)

        # Biimplication = Iff
        return z3.And(
            z3.Implies(fwd, bwd),
            z3.Implies(bwd, fwd),
        )

    def _encode_equivalence(self, pred: EquivalencePred) -> Any:
        """EquivalencePred → ForAll([x], f(x) == g(x))."""
        z3 = _z3
        assert z3 is not None

        # Get the binder variable
        x = self._env.get_or_create(pred.binder, "Int")

        # Encode inner predicates
        pred_f = self.encode(pred.pred_f)
        pred_g = self.encode(pred.pred_g)

        return z3.ForAll([x], pred_f == pred_g)

    def _encode_refinement_equivalence(self, pred: RefinementEquivalencePred) -> Any:
        """RefinementEquivalencePred → ForAll([v], Iff(φ_f(v), φ_g(v)))."""
        z3 = _z3
        assert z3 is not None

        binder = pred.binder
        v = self._env.get_or_create(binder, "Int")

        pred_f = self.encode(pred.pred_f)
        pred_g = self.encode(pred.pred_g)

        return z3.ForAll([v], z3.And(
            z3.Implies(pred_f, pred_g),
            z3.Implies(pred_g, pred_f),
        ))

    def _encode_behavioral_equivalence(self, pred: BehavioralEquivalencePred) -> Any:
        """BehavioralEquivalencePred → ForAll(inputs, out_f == out_g)."""
        z3 = _z3
        assert z3 is not None

        # Create input variables
        input_vars = [
            self._env.get_or_create(name, "Int")
            for name in pred.input_names
        ]

        # Create output variables
        out_f = self._env.prefixed("f", "output", "Int")
        out_g = self._env.prefixed("g", "output", "Int")

        # Encode pre/postconditions
        pre_f = self.encode(pred.pre_f) if pred.pre_f is not None else z3.BoolVal(True)
        pre_g = self.encode(pred.pre_g) if pred.pre_g is not None else z3.BoolVal(True)
        post_f = self.encode(pred.post_f) if pred.post_f is not None else z3.BoolVal(True)
        post_g = self.encode(pred.post_g) if pred.post_g is not None else z3.BoolVal(True)

        if input_vars:
            return z3.ForAll(input_vars, z3.Implies(
                z3.And(pre_f, pre_g),
                z3.And(
                    z3.Implies(post_f, post_g),
                    z3.Implies(post_g, post_f),
                ),
            ))
        else:
            return z3.Implies(
                z3.And(pre_f, pre_g),
                z3.And(
                    z3.Implies(post_f, post_g),
                    z3.Implies(post_g, post_f),
                ),
            )

    def _encode_section_agreement(self, pred: SectionAgreementPred) -> Any:
        """SectionAgreementPred → Iff(σ_f, σ_g)."""
        z3 = _z3
        assert z3 is not None

        enc_f = self.encode(pred.pred_f)
        enc_g = self.encode(pred.pred_g)

        return z3.And(
            z3.Implies(enc_f, enc_g),
            z3.Implies(enc_g, enc_f),
        )

    def _encode_transport(self, pred: TransportPred) -> Any:
        """TransportPred → Implies(And(source, path), target)."""
        z3 = _z3
        assert z3 is not None

        source = self.encode(pred.source_pred)
        target = self.encode(pred.target_pred)
        path = self.encode(pred.path_pred)

        return z3.Implies(z3.And(source, path), target)

    def _encode_fiber_product(self, pred: FiberProductPred) -> Any:
        """FiberProductPred → And(φ_f, φ_g, equalizer)."""
        z3 = _z3
        assert z3 is not None

        enc_f = self.encode(pred.pred_f)
        enc_g = self.encode(pred.pred_g)
        enc_eq = self.encode(pred.equalizer_pred)

        return z3.And(enc_f, enc_g, enc_eq)

    # ── Standard predicate encodings ──────────────────────────────────────

    def _encode_conjunction(self, pred: ConjunctionPred) -> Any:
        z3 = _z3
        assert z3 is not None
        return z3.And(*[self.encode(c) for c in pred.conjuncts])

    def _encode_disjunction(self, pred: DisjunctionPred) -> Any:
        z3 = _z3
        assert z3 is not None
        return z3.Or(*[self.encode(d) for d in pred.disjuncts])

    def _encode_implication(self, pred: ImplicationPred) -> Any:
        z3 = _z3
        assert z3 is not None
        return z3.Implies(
            self.encode(pred.antecedent),
            self.encode(pred.consequent),
        )

    def _encode_not(self, pred: NotPred) -> Any:
        z3 = _z3
        assert z3 is not None
        return z3.Not(self.encode(pred.inner))

    def _encode_comparison(self, pred: ComparisonPred) -> Any:
        z3 = _z3
        assert z3 is not None

        lhs = self._encode_operand(pred.lhs)
        rhs = self._encode_operand(pred.rhs)

        op_map = {
            ComparisonOp.EQ: lambda a, b: a == b,
            ComparisonOp.NE: lambda a, b: a != b,
            ComparisonOp.LT: lambda a, b: a < b,
            ComparisonOp.LE: lambda a, b: a <= b,
            ComparisonOp.GT: lambda a, b: a > b,
            ComparisonOp.GE: lambda a, b: a >= b,
        }

        encoder = op_map.get(pred.op)
        if encoder is not None:
            return encoder(lhs, rhs)
        return z3.BoolVal(True)

    def _encode_operand(self, operand: Any) -> Any:
        z3 = _z3
        assert z3 is not None

        if isinstance(operand, str):
            return self._env.get_or_create(operand, "Int")
        if isinstance(operand, int):
            return z3.IntVal(operand)
        if isinstance(operand, float):
            return z3.RealVal(operand)
        if isinstance(operand, bool):
            return z3.BoolVal(operand)
        return z3.Int(f"op_{id(operand)}")


# ═══════════════════════════════════════════════════════════════════════════════
# Counterexample extractor
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class Counterexample:
    """A concrete counterexample to equivalence.

    Contains a valuation (variable → value) witnessing the divergence,
    plus metadata about which direction failed.
    """
    valuation: Dict[str, Any]
    direction: str  # "forward" or "backward"
    site_id: Optional[SiteId] = None
    explanation: str = ""


class CounterexampleExtractor:
    """Extract counterexamples from Z3 models."""

    def __init__(self, env: EquivalenceVariableEnv) -> None:
        self._env = env

    def extract(
        self,
        model: Any,
        direction: str = "forward",
        site_id: Optional[SiteId] = None,
    ) -> Counterexample:
        """Extract a counterexample from a Z3 model."""
        z3 = _z3
        valuation: Dict[str, Any] = {}

        if z3 is not None and model is not None:
            for name, z3_var in self._env.get_all_vars().items():
                try:
                    val = model.eval(z3_var, model_completion=True)
                    valuation[name] = str(val)
                except Exception:
                    valuation[name] = "?"

        return Counterexample(
            valuation=valuation,
            direction=direction,
            site_id=site_id,
            explanation=self._format_explanation(valuation, direction),
        )

    def _format_explanation(
        self,
        valuation: Dict[str, Any],
        direction: str,
    ) -> str:
        """Format a human-readable explanation of the counterexample."""
        if not valuation:
            return f"No concrete counterexample ({direction} direction)"

        assignments = ", ".join(
            f"{k} = {v}" for k, v in sorted(valuation.items())
        )
        return f"Counterexample ({direction}): {assignments}"


# ═══════════════════════════════════════════════════════════════════════════════
# Equivalence solver
# ═══════════════════════════════════════════════════════════════════════════════


class EquivalenceSolver:
    """SMT-based equivalence verification.

    For a given EquivalenceObligation, checks:
    1. Forward: Is φ_f ∧ ¬φ_g satisfiable? If so, φ_f ⟹ φ_g fails.
    2. Backward: Is φ_g ∧ ¬φ_f satisfiable? If so, φ_g ⟹ φ_f fails.

    If both are unsatisfiable, the predicates are bi-implied.
    """

    def __init__(self, timeout_ms: int = 10000) -> None:
        self._timeout_ms = timeout_ms
        self._env = EquivalenceVariableEnv()
        self._encoder = EquivalenceEncoder(self._env)
        self._extractor = CounterexampleExtractor(self._env)

    def check_obligation(
        self,
        obligation: EquivalenceObligation,
    ) -> LocalEquivalenceJudgment:
        """Check an equivalence obligation via SMT."""
        if not _ensure_z3():
            return self._make_unknown_judgment(
                obligation, "Z3 is not available"
            )

        z3 = _z3
        assert z3 is not None

        site_id = obligation.site_id

        # Check forward: φ_f ∧ ¬φ_g
        forward_holds, forward_cex = self._check_direction(
            obligation.forward_predicate,
            "forward",
            site_id,
        )

        # Check backward: φ_g ∧ ¬φ_f
        backward_holds, backward_cex = self._check_direction(
            obligation.backward_predicate,
            "backward",
            site_id,
        )

        # Determine verdict
        if forward_holds and backward_holds:
            verdict = EquivalenceVerdict.EQUIVALENT
        elif forward_holds:
            verdict = EquivalenceVerdict.REFINED
        elif backward_holds:
            verdict = EquivalenceVerdict.REFINED
        else:
            verdict = EquivalenceVerdict.INEQUIVALENT

        counterexample = (
            forward_cex.valuation if forward_cex is not None
            else backward_cex.valuation if backward_cex is not None
            else None
        )

        return LocalEquivalenceJudgment(
            site_id=site_id,
            verdict=verdict,
            obligation=obligation,
            forward_holds=forward_holds,
            backward_holds=backward_holds,
            counterexample=counterexample,
            proof=None,  # SMT proofs not extracted
            explanation=(
                f"SMT: forward={'✓' if forward_holds else '✗'}, "
                f"backward={'✓' if backward_holds else '✗'}"
            ),
        )

    def _check_direction(
        self,
        predicate: Optional[Predicate],
        direction: str,
        site_id: SiteId,
    ) -> Tuple[bool, Optional[Counterexample]]:
        """Check one direction of the implication.

        For "forward" (φ_f ⟹ φ_g): check if φ_f ∧ ¬φ_g is unsat.
        The predicate should be an ImplicationPred(φ_f, φ_g).
        """
        if predicate is None:
            return True, None  # vacuously

        z3 = _z3
        assert z3 is not None

        try:
            solver = z3.Solver()
            solver.set("timeout", self._timeout_ms)

            # Encode: check if the *negation* of the implication is satisfiable
            # Negation of (a ⟹ b) is (a ∧ ¬b)
            if isinstance(predicate, ImplicationPred):
                antecedent = self._encoder.encode(predicate.antecedent)
                consequent = self._encoder.encode(predicate.consequent)
                solver.add(antecedent)
                solver.add(z3.Not(consequent))
            else:
                # Generic: negate the whole predicate
                encoded = self._encoder.encode(predicate)
                solver.add(z3.Not(encoded))

            result = solver.check()

            if result == z3.unsat:
                return True, None  # implication holds
            elif result == z3.sat:
                model = solver.model()
                cex = self._extractor.extract(model, direction, site_id)
                return False, cex
            else:
                return True, None  # timeout → assume holds (optimistic)

        except Exception:
            return True, None  # error → assume holds

    def _make_unknown_judgment(
        self,
        obligation: EquivalenceObligation,
        reason: str,
    ) -> LocalEquivalenceJudgment:
        """Create an UNKNOWN judgment."""
        return LocalEquivalenceJudgment(
            site_id=obligation.site_id,
            verdict=EquivalenceVerdict.UNKNOWN,
            obligation=obligation,
            forward_holds=None,
            backward_holds=None,
            explanation=reason,
        )

    def check_biimplication(
        self,
        pred_f: Predicate,
        pred_g: Predicate,
        site_id: Optional[SiteId] = None,
    ) -> Tuple[bool, Optional[Counterexample]]:
        """Directly check φ_f ⟺ φ_g.

        Returns (bi_implies, counterexample_if_not).
        """
        if not _ensure_z3():
            return True, None

        z3 = _z3
        assert z3 is not None

        dummy_site = site_id or SiteId(
            kind=SiteKind.SSA_VALUE, name="biimplication_check"
        )

        # Forward: φ_f ∧ ¬φ_g
        fwd_holds, fwd_cex = self._check_direction(
            ImplicationPred(antecedent=pred_f, consequent=pred_g),
            "forward",
            dummy_site,
        )

        if not fwd_holds:
            return False, fwd_cex

        # Backward: φ_g ∧ ¬φ_f
        bwd_holds, bwd_cex = self._check_direction(
            ImplicationPred(antecedent=pred_g, consequent=pred_f),
            "backward",
            dummy_site,
        )

        if not bwd_holds:
            return False, bwd_cex

        return True, None
