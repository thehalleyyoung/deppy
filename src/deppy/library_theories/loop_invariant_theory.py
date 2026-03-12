"""Theory Family 12: Loop Invariant & Decreases.

Handle loop invariant checking, ranking functions, and well-founded
decrease for termination proofs.
Forward: maintain invariant through iterations.
Backward: determine loop preconditions.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism

from .theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    TheoryPackBase,
    merge_refinements,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Loop invariant representation
# ═══════════════════════════════════════════════════════════════════════════════


class InvariantStatus(Enum):
    """Status of a loop invariant."""
    CANDIDATE = "candidate"
    ESTABLISHED = "established"
    MAINTAINED = "maintained"
    VIOLATED = "violated"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class LoopInvariant:
    """A loop invariant proposition.

    Attributes:
        name: Identifier for the invariant.
        proposition: Human-readable statement of the invariant.
        variables: Variables involved in the invariant.
        status: Current verification status.
        refinements: Refinement entries implied by the invariant.
    """
    name: str
    proposition: str
    variables: Tuple[str, ...] = ()
    status: InvariantStatus = InvariantStatus.CANDIDATE
    refinements: Dict[str, Any] = field(default_factory=dict)

    def establish(self) -> LoopInvariant:
        return LoopInvariant(
            self.name, self.proposition, self.variables,
            InvariantStatus.ESTABLISHED, self.refinements,
        )

    def maintain(self) -> LoopInvariant:
        if self.status in (InvariantStatus.ESTABLISHED, InvariantStatus.MAINTAINED):
            return LoopInvariant(
                self.name, self.proposition, self.variables,
                InvariantStatus.MAINTAINED, self.refinements,
            )
        return self

    def violate(self) -> LoopInvariant:
        return LoopInvariant(
            self.name, self.proposition, self.variables,
            InvariantStatus.VIOLATED, self.refinements,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Ranking function / termination
# ═══════════════════════════════════════════════════════════════════════════════


class RankingKind(Enum):
    """Kind of ranking function for termination."""
    INTEGER_DECREASE = "integer_decrease"
    LEXICOGRAPHIC = "lexicographic"
    WELL_FOUNDED = "well_founded"
    BOUNDED_ITERATION = "bounded_iteration"
    FUEL = "fuel"


@dataclass(frozen=True)
class RankingFunction:
    """A ranking function proving loop termination.

    Attributes:
        name: Identifier.
        kind: What kind of ranking function.
        expression: The decreasing expression.
        bound: Lower bound (for integer decrease).
        components: Sub-components for lexicographic ranking.
    """
    name: str
    kind: RankingKind
    expression: str = ""
    bound: Optional[int] = None
    components: Tuple[str, ...] = ()

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {
            "ranking_name": self.name,
            "ranking_kind": self.kind.value,
            "ranking_expression": self.expression,
        }
        if self.bound is not None:
            refs["ranking_bound"] = self.bound
        if self.components:
            refs["ranking_components"] = list(self.components)
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> Optional[RankingFunction]:
        name = refs.get("ranking_name")
        if name is None:
            return None
        kind_str = refs.get("ranking_kind", "integer_decrease")
        try:
            kind = RankingKind(kind_str)
        except ValueError:
            kind = RankingKind.INTEGER_DECREASE
        return RankingFunction(
            name=str(name), kind=kind,
            expression=refs.get("ranking_expression", ""),
            bound=refs.get("ranking_bound"),
            components=tuple(refs.get("ranking_components", [])),
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Loop analysis
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class LoopAnalysis:
    """Complete analysis of a loop for invariant/termination checking."""
    invariants: List[LoopInvariant] = field(default_factory=list)
    ranking: Optional[RankingFunction] = None
    iteration_bound: Optional[int] = None
    loop_variables: Set[str] = field(default_factory=set)
    modified_variables: Set[str] = field(default_factory=set)
    is_for_loop: bool = False
    iterable_length: Optional[int] = None
    loop_counter: Optional[str] = None

    @property
    def all_invariants_maintained(self) -> bool:
        return all(
            inv.status in (InvariantStatus.ESTABLISHED, InvariantStatus.MAINTAINED)
            for inv in self.invariants
        )

    @property
    def has_termination_proof(self) -> bool:
        if self.ranking is not None:
            return True
        if self.is_for_loop and self.iterable_length is not None:
            return True
        if self.iteration_bound is not None:
            return True
        return False

    @property
    def violated_invariants(self) -> List[LoopInvariant]:
        return [inv for inv in self.invariants if inv.status == InvariantStatus.VIOLATED]

    def add_invariant(self, inv: LoopInvariant) -> None:
        self.invariants.append(inv)

    def establish_all(self) -> None:
        self.invariants = [inv.establish() for inv in self.invariants]

    def maintain_all(self) -> None:
        self.invariants = [inv.maintain() for inv in self.invariants]

    def check_inductive_step(self, pre_refs: Dict[str, Any], post_refs: Dict[str, Any]) -> List[LoopInvariant]:
        """Check which invariants are maintained from pre to post."""
        result: List[LoopInvariant] = []
        for inv in self.invariants:
            maintained = True
            for key, value in inv.refinements.items():
                if key in post_refs:
                    if post_refs[key] != value:
                        maintained = False
                        break
                elif key in pre_refs:
                    pass
                else:
                    maintained = False
                    break
            if maintained:
                result.append(inv.maintain())
            else:
                result.append(inv.violate())
        return result

    def to_refinements(self) -> Dict[str, Any]:
        refs: Dict[str, Any] = {
            "_invariants": [
                {"name": inv.name, "proposition": inv.proposition,
                 "status": inv.status.value, "variables": list(inv.variables),
                 "refinements": inv.refinements}
                for inv in self.invariants
            ],
            "_all_invariants_maintained": self.all_invariants_maintained,
            "_has_termination": self.has_termination_proof,
            "_loop_variables": list(self.loop_variables),
            "_modified_variables": list(self.modified_variables),
            "_is_for_loop": self.is_for_loop,
        }
        if self.ranking is not None:
            refs.update(self.ranking.to_refinements())
        if self.iteration_bound is not None:
            refs["_iteration_bound"] = self.iteration_bound
        if self.iterable_length is not None:
            refs["_iterable_length"] = self.iterable_length
        if self.loop_counter is not None:
            refs["_loop_counter"] = self.loop_counter
        return refs

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> LoopAnalysis:
        analysis = LoopAnalysis()
        for inv_data in refs.get("_invariants", []):
            if isinstance(inv_data, dict):
                try:
                    status = InvariantStatus(inv_data.get("status", "candidate"))
                except ValueError:
                    status = InvariantStatus.UNKNOWN
                analysis.invariants.append(LoopInvariant(
                    name=inv_data.get("name", ""),
                    proposition=inv_data.get("proposition", ""),
                    variables=tuple(inv_data.get("variables", [])),
                    status=status,
                    refinements=inv_data.get("refinements", {}),
                ))
        analysis.ranking = RankingFunction.from_refinements(refs)
        analysis.iteration_bound = refs.get("_iteration_bound")
        analysis.loop_variables = set(refs.get("_loop_variables", []))
        analysis.modified_variables = set(refs.get("_modified_variables", []))
        analysis.is_for_loop = refs.get("_is_for_loop", False)
        analysis.iterable_length = refs.get("_iterable_length")
        analysis.loop_counter = refs.get("_loop_counter")
        return analysis


# ═══════════════════════════════════════════════════════════════════════════════
# Common loop invariant patterns
# ═══════════════════════════════════════════════════════════════════════════════


def infer_for_loop_invariants(
    counter: str,
    iterable_length: Optional[int],
    body_modified: Set[str],
) -> List[LoopInvariant]:
    """Infer standard invariants for a for-loop."""
    invariants: List[LoopInvariant] = []
    invariants.append(LoopInvariant(
        name=f"{counter}_bound",
        proposition=f"0 <= {counter} < iterable_length",
        variables=(counter,),
        status=InvariantStatus.ESTABLISHED,
        refinements={"lower_bound": 0, "non_negative": True},
    ))
    if iterable_length is not None:
        invariants.append(LoopInvariant(
            name=f"{counter}_upper",
            proposition=f"{counter} < {iterable_length}",
            variables=(counter,),
            status=InvariantStatus.ESTABLISHED,
            refinements={"upper_bound": iterable_length - 1},
        ))
    return invariants


def infer_while_loop_ranking(
    condition_variable: str,
    condition_op: str,
    bound: Optional[int],
) -> Optional[RankingFunction]:
    """Infer a ranking function for a while-loop if possible."""
    if condition_op in ("<", "<=", "!=") and bound is not None:
        return RankingFunction(
            name=f"decrease_{condition_variable}",
            kind=RankingKind.INTEGER_DECREASE,
            expression=f"{bound} - {condition_variable}",
            bound=0,
        )
    return None


# ═══════════════════════════════════════════════════════════════════════════════
# LoopInvariantTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class LoopInvariantTheoryPack(TheoryPackBase):
    """Theory Family 12: Loop Invariant & Decreases.

    Handles LOOP_HEADER_INVARIANT sites for invariant checking
    and termination proofs.
    """

    pack_name = "loop_invariant"
    pack_priority = 50

    _APPLICABLE = frozenset({
        SiteKind.LOOP_HEADER_INVARIANT,
        SiteKind.SSA_VALUE,
        SiteKind.BRANCH_GUARD,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        refs = section.refinements
        analysis = LoopAnalysis.from_refinements(refs)

        if not analysis.invariants and not analysis.ranking:
            if refs.get("_is_for_loop"):
                counter = refs.get("_loop_counter", "i")
                iterable_len = refs.get("_iterable_length")
                modified = set(refs.get("_modified_variables", []))
                inferred = infer_for_loop_invariants(counter, iterable_len, modified)
                analysis.invariants = inferred
                analysis.is_for_loop = True
                analysis.loop_counter = counter
                analysis.iterable_length = iterable_len
                if iterable_len is not None:
                    analysis.ranking = RankingFunction(
                        name="for_loop_termination",
                        kind=RankingKind.BOUNDED_ITERATION,
                        expression=f"{iterable_len} - {counter}",
                        bound=0,
                    )
                    analysis.iteration_bound = iterable_len
            elif refs.get("_condition_variable"):
                cond_var = refs["_condition_variable"]
                cond_op = refs.get("_condition_op", "<")
                bound = refs.get("_condition_bound")
                ranking = infer_while_loop_ranking(str(cond_var), str(cond_op), bound)
                if ranking is not None:
                    analysis.ranking = ranking

        if not analysis.invariants and not analysis.ranking:
            return SolverResult(
                status=SolverStatus.UNCHANGED,
                section=section,
                explanation="no loop invariant/ranking information",
            )

        pre_iteration = refs.get("_pre_iteration_refs", {})
        post_iteration = refs.get("_post_iteration_refs", {})
        if pre_iteration and post_iteration:
            checked = analysis.check_inductive_step(pre_iteration, post_iteration)
            analysis.invariants = checked

        new_refs = dict(refs)
        new_refs.update(analysis.to_refinements())

        violated = analysis.violated_invariants
        if violated:
            return SolverResult(
                status=SolverStatus.REFINED,
                section=LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=section.trust,
                    provenance=f"loop: {len(violated)} violated invariant(s)",
                    witnesses=dict(section.witnesses),
                ),
                constraints_remaining=[
                    f"invariant violated: {inv.name} ({inv.proposition})"
                    for inv in violated
                ],
                explanation=f"{len(violated)} invariant(s) violated",
            )

        if analysis.all_invariants_maintained and analysis.has_termination_proof:
            return SolverResult(
                status=SolverStatus.SOLVED,
                section=LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=TrustLevel.PROOF_BACKED,
                    provenance="loop: invariants maintained, terminates",
                    witnesses=dict(section.witnesses),
                ),
                explanation=(
                    f"all {len(analysis.invariants)} invariant(s) maintained, "
                    f"termination proven"
                ),
            )

        obligations: List[str] = []
        if not analysis.all_invariants_maintained:
            for inv in analysis.invariants:
                if inv.status == InvariantStatus.CANDIDATE:
                    obligations.append(f"establish invariant: {inv.name}")
        if not analysis.has_termination_proof:
            obligations.append("prove termination (ranking function)")

        return SolverResult(
            status=SolverStatus.REFINED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance="loop: partial analysis",
                witnesses=dict(section.witnesses),
            ),
            constraints_remaining=obligations,
            proof_obligations=obligations,
            explanation=f"{len(obligations)} loop obligation(s) remain",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        analysis = LoopAnalysis.from_refinements(section.refinements)

        if not analysis.invariants:
            return restricted

        inv_refs: Dict[str, Any] = {}
        for inv in analysis.invariants:
            if inv.status in (InvariantStatus.ESTABLISHED, InvariantStatus.MAINTAINED):
                inv_refs = merge_refinements(inv_refs, inv.refinements, "meet")

        new_refs = merge_refinements(restricted.refinements, inv_refs, "meet")
        new_refs.update(analysis.to_refinements())

        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="loop forward: invariants propagated",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        analysis = LoopAnalysis.from_refinements(section.refinements)
        required_refs: Dict[str, Any] = {}

        for inv in analysis.invariants:
            required_refs = merge_refinements(required_refs, inv.refinements, "meet")

        if analysis.ranking is not None:
            required_refs["_requires_ranking_decrease"] = True
            required_refs.update(analysis.ranking.to_refinements())

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="loop pullback: invariant establishment required",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        name = error_site.name
        if "invariant" in name.lower():
            return "loop invariant holds"
        if "termination" in name.lower() or "decrease" in name.lower():
            return "ranking function decreases"
        return f"loop precondition for {name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        analysis = LoopAnalysis.from_refinements(section.refinements)
        if analysis.all_invariants_maintained and analysis.has_termination_proof:
            return BoundaryClassification.FULLY_PROVEN
        if analysis.all_invariants_maintained:
            return BoundaryClassification.CONDITIONALLY_PROVEN
        if analysis.violated_invariants:
            return BoundaryClassification.INCONSISTENT
        return BoundaryClassification.REQUIRES_PROOF
