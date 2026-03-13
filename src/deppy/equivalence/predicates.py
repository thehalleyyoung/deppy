"""Equivalence-specific Predicate subclasses for sheaf-theoretic program comparison.

This module builds on deppy's existing Predicate hierarchy to express the
verification conditions that arise in equivalence checking.  The core idea:

    Two refinement types  {v : τ_f | φ_f}  and  {v : τ_g | φ_g}  are
    equivalent iff  φ_f ⟺ φ_g  (predicate bi-implication), assuming
    the base types τ_f and τ_g are already equivalent.

We provide:

- **EquivalencePred**: top-level predicate asserting ∀x. f(x) = g(x)
- **BiimplicationPred**: φ ⟺ ψ  (φ ⟹ ψ) ∧ (ψ ⟹ φ)
- **RefinementEquivalencePred**: full refinement-type equivalence
- **BehavioralEquivalencePred**: ∀ inputs. f(inputs) = g(inputs)
- **SectionAgreementPred**: two sections agree on a common refinement site
- **TransportPred**: predicate obtained by transporting along a type path
- **FiberProductPred**: predicate characterising the fiber product equalizer

Each is a proper Predicate subclass that plugs directly into the solver
pipeline, the subtyping checker, and the Z3 encoder.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Set,
    Tuple,
    Union,
)

from deppy.types.refinement import (
    CallPred,
    ComparisonOp,
    ComparisonPred,
    ConjunctionPred,
    DisjunctionPred,
    FalsePred,
    ImplicationPred,
    IsInstancePred,
    IsNonePred,
    IsNotNonePred,
    LengthPred,
    MembershipPred,
    NotPred,
    Predicate,
    RefinementType,
    TruePred,
    VarPred,
)
from deppy.core._protocols import SiteId, LocalSection


# ═══════════════════════════════════════════════════════════════════════════════
# Bi-implication:  φ ⟺ ψ  ≡  (φ ⟹ ψ) ∧ (ψ ⟹ φ)
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class BiimplicationPred(Predicate):
    """φ ⟺ ψ — logical biconditional / if-and-only-if.

    Semantically equivalent to ConjunctionPred of two ImplicationPred,
    but kept as a first-class node so the Z3 encoder can emit z3.Iff
    directly and the obstruction analyser can distinguish forward/backward
    failure.
    """

    left: Predicate
    right: Predicate

    # ── Predicate ABC ─────────────────────────────────────────────────────

    def free_vars(self) -> FrozenSet[str]:
        return self.left.free_vars() | self.right.free_vars()

    def substitute_pred(self, mapping: Mapping[str, Any]) -> Predicate:
        new_left = self.left.substitute_pred(mapping)
        new_right = self.right.substitute_pred(mapping)
        return BiimplicationPred(left=new_left, right=new_right)

    def negate(self) -> Predicate:
        # ¬(φ ⟺ ψ) ≡ (φ ∧ ¬ψ) ∨ (¬φ ∧ ψ)  — XOR
        return DisjunctionPred(disjuncts=(
            ConjunctionPred(conjuncts=(self.left, self.right.negate())),
            ConjunctionPred(conjuncts=(self.left.negate(), self.right)),
        ))

    def __repr__(self) -> str:
        return f"({self.left!r} ⟺ {self.right!r})"

    # ── Decomposition helpers ─────────────────────────────────────────────

    @property
    def forward_implication(self) -> ImplicationPred:
        """φ ⟹ ψ direction."""
        return ImplicationPred(antecedent=self.left, consequent=self.right)

    @property
    def backward_implication(self) -> ImplicationPred:
        """ψ ⟹ φ direction."""
        return ImplicationPred(antecedent=self.right, consequent=self.left)

    def to_conjunction(self) -> ConjunctionPred:
        """Expand to (φ ⟹ ψ) ∧ (ψ ⟹ φ)."""
        return ConjunctionPred(conjuncts=(
            self.forward_implication,
            self.backward_implication,
        ))


# ═══════════════════════════════════════════════════════════════════════════════
# Equivalence predicate: ∀x. f(x) = g(x)
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class EquivalencePred(Predicate):
    """Assert that two expressions / sections produce equivalent values.

    Encodes:  ∀ (binder : domain). expr_f(binder) = expr_g(binder)

    When the domain is a refinement type, the quantification is restricted
    to values satisfying the refinement predicate.
    """

    binder: str
    expr_f: str   # symbolic name for the f-side expression
    expr_g: str   # symbolic name for the g-side expression
    domain_predicate: Predicate = field(default_factory=TruePred)
    site_id: Optional[SiteId] = None

    def free_vars(self) -> FrozenSet[str]:
        base = self.domain_predicate.free_vars() | {self.expr_f, self.expr_g}
        return base - {self.binder}

    def substitute_pred(self, mapping: Mapping[str, Any]) -> Predicate:
        if self.binder in mapping:
            return self  # binder shadows
        new_domain = self.domain_predicate.substitute_pred(mapping)
        new_f = mapping.get(self.expr_f, self.expr_f)
        new_g = mapping.get(self.expr_g, self.expr_g)
        return EquivalencePred(
            binder=self.binder,
            expr_f=str(new_f),
            expr_g=str(new_g),
            domain_predicate=new_domain,
            site_id=self.site_id,
        )

    def negate(self) -> Predicate:
        # ¬(∀x. f(x) = g(x)) ≡ ∃x. f(x) ≠ g(x)
        return NotPred(inner=self)

    def __repr__(self) -> str:
        domain = f" | {self.domain_predicate!r}" if not isinstance(
            self.domain_predicate, TruePred
        ) else ""
        return f"∀{self.binder}{domain}. {self.expr_f} = {self.expr_g}"

    def to_implication_pair(self) -> BiimplicationPred:
        """Lower to a biimplication of comparison predicates."""
        eq_pred = ComparisonPred(
            lhs=self.expr_f, op=ComparisonOp.EQ, rhs=self.expr_g
        )
        domain_guard = self.domain_predicate
        guarded = ImplicationPred(antecedent=domain_guard, consequent=eq_pred)
        # For equivalence, both directions of implication are the same
        # (since equality is symmetric), but we keep the structure
        return BiimplicationPred(left=guarded, right=guarded)


# ═══════════════════════════════════════════════════════════════════════════════
# Refinement equivalence
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class RefinementEquivalencePred(Predicate):
    """Assert that two refinement predicates are equivalent under a base type.

    Given:
        {v : τ_f | φ_f(v)}  and  {v : τ_g | φ_g(v)}

    This asserts (assuming τ_f ≡ τ_g):
        ∀v. φ_f(v) ⟺ φ_g(v)

    Encoded as a BiimplicationPred of the two refinement predicates, with
    binder renaming to a common variable.
    """

    binder: str
    predicate_f: Predicate
    predicate_g: Predicate
    base_type: Optional[Any] = None  # TypeBase, if available
    site_id: Optional[SiteId] = None

    def free_vars(self) -> FrozenSet[str]:
        return (
            self.predicate_f.free_vars() | self.predicate_g.free_vars()
        ) - {self.binder}

    def substitute_pred(self, mapping: Mapping[str, Any]) -> Predicate:
        if self.binder in mapping:
            return self
        new_f = self.predicate_f.substitute_pred(mapping)
        new_g = self.predicate_g.substitute_pred(mapping)
        return RefinementEquivalencePred(
            binder=self.binder,
            predicate_f=new_f,
            predicate_g=new_g,
            base_type=self.base_type,
            site_id=self.site_id,
        )

    def negate(self) -> Predicate:
        return NotPred(inner=self)

    def __repr__(self) -> str:
        return (
            f"RefinEquiv(∀{self.binder}. "
            f"{self.predicate_f!r} ⟺ {self.predicate_g!r})"
        )

    @property
    def biimplication(self) -> BiimplicationPred:
        """The underlying φ_f ⟺ φ_g."""
        return BiimplicationPred(left=self.predicate_f, right=self.predicate_g)

    @property
    def forward_implication(self) -> ImplicationPred:
        """φ_f ⟹ φ_g."""
        return ImplicationPred(
            antecedent=self.predicate_f, consequent=self.predicate_g
        )

    @property
    def backward_implication(self) -> ImplicationPred:
        """φ_g ⟹ φ_f."""
        return ImplicationPred(
            antecedent=self.predicate_g, consequent=self.predicate_f
        )

    def weaken_to_forward_refinement(self) -> ImplicationPred:
        """Weaken to one-directional: f refines g."""
        return self.forward_implication

    def weaken_to_backward_refinement(self) -> ImplicationPred:
        """Weaken to one-directional: g refines f."""
        return self.backward_implication


# ═══════════════════════════════════════════════════════════════════════════════
# Behavioral equivalence
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class BehavioralEquivalencePred(Predicate):
    """∀ inputs ∈ domain. f(inputs) = g(inputs)

    This is the observational / black-box equivalence predicate.
    The domain is characterised by a conjunction of input refinement
    predicates (from the argument boundary sections).
    """

    input_binders: Tuple[str, ...] = ()
    input_predicates: Tuple[Predicate, ...] = ()
    output_predicate_f: Predicate = field(default_factory=TruePred)
    output_predicate_g: Predicate = field(default_factory=TruePred)
    function_name_f: str = "f"
    function_name_g: str = "g"

    def free_vars(self) -> FrozenSet[str]:
        result: Set[str] = set()
        for p in self.input_predicates:
            result |= p.free_vars()
        result |= self.output_predicate_f.free_vars()
        result |= self.output_predicate_g.free_vars()
        return frozenset(result) - frozenset(self.input_binders)

    def substitute_pred(self, mapping: Mapping[str, Any]) -> Predicate:
        safe_mapping = {
            k: v for k, v in mapping.items() if k not in self.input_binders
        }
        new_input_preds = tuple(
            p.substitute_pred(safe_mapping) for p in self.input_predicates
        )
        new_out_f = self.output_predicate_f.substitute_pred(safe_mapping)
        new_out_g = self.output_predicate_g.substitute_pred(safe_mapping)
        return BehavioralEquivalencePred(
            input_binders=self.input_binders,
            input_predicates=new_input_preds,
            output_predicate_f=new_out_f,
            output_predicate_g=new_out_g,
            function_name_f=self.function_name_f,
            function_name_g=self.function_name_g,
        )

    def negate(self) -> Predicate:
        return NotPred(inner=self)

    def __repr__(self) -> str:
        args = ", ".join(self.input_binders)
        return (
            f"∀({args}). {self.function_name_f}({args}) "
            f"= {self.function_name_g}({args})"
        )

    @property
    def domain_predicate(self) -> Predicate:
        """Conjunction of all input predicates."""
        if not self.input_predicates:
            return TruePred()
        if len(self.input_predicates) == 1:
            return self.input_predicates[0]
        return ConjunctionPred(conjuncts=self.input_predicates)

    @property
    def output_biimplication(self) -> BiimplicationPred:
        """Output predicates must be bi-implied."""
        return BiimplicationPred(
            left=self.output_predicate_f,
            right=self.output_predicate_g,
        )

    def to_guarded_biimplication(self) -> ImplicationPred:
        """Lower to: domain ⟹ (output_f ⟺ output_g)."""
        return ImplicationPred(
            antecedent=self.domain_predicate,
            consequent=self.output_biimplication,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Section agreement
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class SectionAgreementPred(Predicate):
    """Assert that two local sections agree at a common site.

    This encodes the gluing condition for the equivalence problem:
    on the overlap U_i ∩ U_j, the paired sections must agree.
    """

    site_id: SiteId
    refinement_keys: Tuple[str, ...] = ()
    predicate_pairs: Tuple[Tuple[Predicate, Predicate], ...] = ()

    def free_vars(self) -> FrozenSet[str]:
        result: Set[str] = set()
        for p_f, p_g in self.predicate_pairs:
            result |= p_f.free_vars() | p_g.free_vars()
        return frozenset(result)

    def substitute_pred(self, mapping: Mapping[str, Any]) -> Predicate:
        new_pairs = tuple(
            (p_f.substitute_pred(mapping), p_g.substitute_pred(mapping))
            for p_f, p_g in self.predicate_pairs
        )
        return SectionAgreementPred(
            site_id=self.site_id,
            refinement_keys=self.refinement_keys,
            predicate_pairs=new_pairs,
        )

    def negate(self) -> Predicate:
        return NotPred(inner=self)

    def __repr__(self) -> str:
        n = len(self.predicate_pairs)
        return f"SectionAgree({self.site_id}, {n} pairs)"

    @property
    def agreement_conjunction(self) -> Predicate:
        """The conjunction of all pair-wise biimplications."""
        if not self.predicate_pairs:
            return TruePred()
        biimps = [
            BiimplicationPred(left=p_f, right=p_g)
            for p_f, p_g in self.predicate_pairs
        ]
        if len(biimps) == 1:
            return biimps[0]
        return ConjunctionPred(conjuncts=tuple(biimps))


# ═══════════════════════════════════════════════════════════════════════════════
# Transport predicate
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class TransportPred(Predicate):
    """A predicate obtained by transporting φ along a type equivalence path.

    Given a path p : τ_f = τ_g (IdentityType), transport_p(φ_f) gives a
    predicate over τ_g that is logically equivalent to φ_f.

    This mirrors the type-theoretic transport operation:
        transport : (p : A = B) → P(A) → P(B)
    """

    source_predicate: Predicate
    path_description: str = ""
    source_type_name: str = ""
    target_type_name: str = ""

    def free_vars(self) -> FrozenSet[str]:
        return self.source_predicate.free_vars()

    def substitute_pred(self, mapping: Mapping[str, Any]) -> Predicate:
        new_source = self.source_predicate.substitute_pred(mapping)
        return TransportPred(
            source_predicate=new_source,
            path_description=self.path_description,
            source_type_name=self.source_type_name,
            target_type_name=self.target_type_name,
        )

    def negate(self) -> Predicate:
        return TransportPred(
            source_predicate=self.source_predicate.negate(),
            path_description=self.path_description,
            source_type_name=self.source_type_name,
            target_type_name=self.target_type_name,
        )

    def __repr__(self) -> str:
        return f"transport({self.source_predicate!r}, {self.path_description})"


# ═══════════════════════════════════════════════════════════════════════════════
# Fiber product predicate (equalizer condition)
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class FiberProductPred(Predicate):
    """Characterises the fiber product equalizer at a site.

    The fiber product (Sem_f ×_S Sem_g)(U_i) consists of pairs (σ_f, σ_g)
    such that:
        restriction_to_base(σ_f) = restriction_to_base(σ_g)

    When σ_f and σ_g are refinement-typed, this becomes:
        base_agreement ∧ φ_f(v) ∧ φ_g(v)

    The fiber product predicate is the conjunction of both refinement
    predicates (they must both hold on the shared value).
    """

    predicate_f: Predicate
    predicate_g: Predicate
    base_agreement: Predicate = field(default_factory=TruePred)
    site_id: Optional[SiteId] = None

    def free_vars(self) -> FrozenSet[str]:
        return (
            self.predicate_f.free_vars()
            | self.predicate_g.free_vars()
            | self.base_agreement.free_vars()
        )

    def substitute_pred(self, mapping: Mapping[str, Any]) -> Predicate:
        return FiberProductPred(
            predicate_f=self.predicate_f.substitute_pred(mapping),
            predicate_g=self.predicate_g.substitute_pred(mapping),
            base_agreement=self.base_agreement.substitute_pred(mapping),
            site_id=self.site_id,
        )

    def negate(self) -> Predicate:
        return NotPred(inner=self)

    def __repr__(self) -> str:
        return (
            f"FiberProd({self.predicate_f!r} ×_S {self.predicate_g!r})"
        )

    @property
    def as_conjunction(self) -> ConjunctionPred:
        """Expand to: base_agreement ∧ φ_f ∧ φ_g."""
        return ConjunctionPred(conjuncts=(
            self.base_agreement,
            self.predicate_f,
            self.predicate_g,
        ))

    @property
    def equalizer_condition(self) -> BiimplicationPred:
        """The equalizer requires φ_f ⟺ φ_g (under base agreement)."""
        return BiimplicationPred(left=self.predicate_f, right=self.predicate_g)


# ═══════════════════════════════════════════════════════════════════════════════
# Builder functions
# ═══════════════════════════════════════════════════════════════════════════════


def build_equivalence_predicate(
    refinement_f: RefinementType,
    refinement_g: RefinementType,
    common_binder: str = "v",
) -> RefinementEquivalencePred:
    """Build an equivalence predicate from two RefinementTypes.

    Renames both refinement predicates to use a common binder variable,
    then constructs the bi-implication.
    """
    pred_f = refinement_f.predicate
    pred_g = refinement_g.predicate

    # Rename binders to the common variable
    if refinement_f.binder != common_binder:
        pred_f = pred_f.substitute_pred({refinement_f.binder: common_binder})
    if refinement_g.binder != common_binder:
        pred_g = pred_g.substitute_pred({refinement_g.binder: common_binder})

    return RefinementEquivalencePred(
        binder=common_binder,
        predicate_f=pred_f,
        predicate_g=pred_g,
        base_type=refinement_f.base,
        site_id=None,
    )


def predicate_biimplication(
    pred_f: Predicate,
    pred_g: Predicate,
) -> BiimplicationPred:
    """Construct φ_f ⟺ φ_g as a first-class predicate node."""
    return BiimplicationPred(left=pred_f, right=pred_g)


def build_section_agreement_predicate(
    section_f: LocalSection,
    section_g: LocalSection,
    site_id: SiteId,
) -> SectionAgreementPred:
    """Build a SectionAgreementPred from two LocalSections.

    For each shared refinement key, if both values are Predicates, pair
    them for bi-implication.  Otherwise, create equality comparison
    predicates.
    """
    shared_keys = sorted(
        set(section_f.refinements.keys()) & set(section_g.refinements.keys())
    )
    pairs: List[Tuple[Predicate, Predicate]] = []
    keys: List[str] = []

    for key in shared_keys:
        val_f = section_f.refinements[key]
        val_g = section_g.refinements[key]
        if isinstance(val_f, Predicate) and isinstance(val_g, Predicate):
            pairs.append((val_f, val_g))
            keys.append(key)
        else:
            # Encode equality as a ComparisonPred
            pred_f_val = ComparisonPred(
                lhs=f"f.{key}", op=ComparisonOp.EQ, rhs=val_f
            )
            pred_g_val = ComparisonPred(
                lhs=f"g.{key}", op=ComparisonOp.EQ, rhs=val_g
            )
            pairs.append((pred_f_val, pred_g_val))
            keys.append(key)

    return SectionAgreementPred(
        site_id=site_id,
        refinement_keys=tuple(keys),
        predicate_pairs=tuple(pairs),
    )


def build_behavioral_equivalence(
    input_sections_f: Dict[SiteId, LocalSection],
    input_sections_g: Dict[SiteId, LocalSection],
    output_section_f: Optional[LocalSection],
    output_section_g: Optional[LocalSection],
    function_name_f: str = "f",
    function_name_g: str = "g",
) -> BehavioralEquivalencePred:
    """Build a behavioral equivalence predicate from boundary sections.

    Extracts input refinement predicates from the argument boundary sections
    and output predicates from the return boundary sections.
    """
    # Collect input binders and predicates
    binders: List[str] = []
    input_preds: List[Predicate] = []

    for sid, sec in sorted(input_sections_f.items(), key=lambda x: str(x[0])):
        binder = sid.name
        binders.append(binder)
        # Collect all Predicate-valued refinements
        for key, val in sec.refinements.items():
            if isinstance(val, Predicate):
                input_preds.append(val)

    # Output predicates
    out_pred_f: Predicate = TruePred()
    out_pred_g: Predicate = TruePred()

    if output_section_f:
        out_preds_f = [
            v for v in output_section_f.refinements.values()
            if isinstance(v, Predicate)
        ]
        if out_preds_f:
            out_pred_f = (
                out_preds_f[0] if len(out_preds_f) == 1
                else ConjunctionPred(conjuncts=tuple(out_preds_f))
            )

    if output_section_g:
        out_preds_g = [
            v for v in output_section_g.refinements.values()
            if isinstance(v, Predicate)
        ]
        if out_preds_g:
            out_pred_g = (
                out_preds_g[0] if len(out_preds_g) == 1
                else ConjunctionPred(conjuncts=tuple(out_preds_g))
            )

    return BehavioralEquivalencePred(
        input_binders=tuple(binders),
        input_predicates=tuple(input_preds),
        output_predicate_f=out_pred_f,
        output_predicate_g=out_pred_g,
        function_name_f=function_name_f,
        function_name_g=function_name_g,
    )


def build_fiber_product_predicate(
    section_f: LocalSection,
    section_g: LocalSection,
    site_id: SiteId,
) -> FiberProductPred:
    """Build the fiber product equalizer predicate from two sections.

    Extracts refinement predicates from both sections and constructs
    the conjunction that characterises the fiber product.
    """
    # Extract predicates from refinements
    preds_f = [
        v for v in section_f.refinements.values()
        if isinstance(v, Predicate)
    ]
    preds_g = [
        v for v in section_g.refinements.values()
        if isinstance(v, Predicate)
    ]

    pred_f: Predicate = TruePred()
    pred_g: Predicate = TruePred()

    if preds_f:
        pred_f = (
            preds_f[0] if len(preds_f) == 1
            else ConjunctionPred(conjuncts=tuple(preds_f))
        )
    if preds_g:
        pred_g = (
            preds_g[0] if len(preds_g) == 1
            else ConjunctionPred(conjuncts=tuple(preds_g))
        )

    # Base agreement: carrier types must match
    base_agreement: Predicate = TruePred()
    if (
        section_f.carrier_type is not None
        and section_g.carrier_type is not None
        and section_f.carrier_type != section_g.carrier_type
    ):
        base_agreement = FalsePred()

    return FiberProductPred(
        predicate_f=pred_f,
        predicate_g=pred_g,
        base_agreement=base_agreement,
        site_id=site_id,
    )
