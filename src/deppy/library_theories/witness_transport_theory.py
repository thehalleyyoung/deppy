"""Theory Family 11: Witness & Equality Transport.

Handle proof terms, equality witnesses, and transport maps.
Forward: transport proofs along equalities.
Backward: determine proof obligations.
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
# Proof obligation representation
# ═══════════════════════════════════════════════════════════════════════════════


class ObligationStatus(Enum):
    """Status of a proof obligation."""
    PENDING = "pending"
    DISCHARGED = "discharged"
    ASSUMED = "assumed"
    FAILED = "failed"
    DEFERRED = "deferred"


@dataclass(frozen=True)
class ProofObligation:
    """A proof obligation that must be discharged."""
    name: str
    proposition: str
    status: ObligationStatus = ObligationStatus.PENDING
    source_site: Optional[str] = None
    witness_key: Optional[str] = None
    trust_required: TrustLevel = TrustLevel.BOUNDED_AUTO

    def discharge(self, witness_key: str) -> ProofObligation:
        return ProofObligation(
            name=self.name, proposition=self.proposition,
            status=ObligationStatus.DISCHARGED,
            source_site=self.source_site, witness_key=witness_key,
            trust_required=self.trust_required,
        )

    def assume(self) -> ProofObligation:
        return ProofObligation(
            name=self.name, proposition=self.proposition,
            status=ObligationStatus.ASSUMED,
            source_site=self.source_site, witness_key=self.witness_key,
            trust_required=self.trust_required,
        )

    def fail(self) -> ProofObligation:
        return ProofObligation(
            name=self.name, proposition=self.proposition,
            status=ObligationStatus.FAILED,
            source_site=self.source_site, witness_key=self.witness_key,
            trust_required=self.trust_required,
        )

    @property
    def is_resolved(self) -> bool:
        return self.status in (ObligationStatus.DISCHARGED, ObligationStatus.ASSUMED)


# ═══════════════════════════════════════════════════════════════════════════════
# Equality witness representation
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class EqualityWitness:
    """Witness that two types/values are equal."""
    lhs: str
    rhs: str
    proof_kind: str = "refl"
    evidence: Any = None

    def reverse(self) -> EqualityWitness:
        return EqualityWitness(self.rhs, self.lhs, "sym", self)

    def compose(self, other: EqualityWitness) -> Optional[EqualityWitness]:
        if self.rhs == other.lhs:
            return EqualityWitness(self.lhs, other.rhs, "trans", (self, other))
        return None


@dataclass(frozen=True)
class TransportMap:
    """A map for transporting values/proofs along an equality."""
    source_type: str
    target_type: str
    equality: EqualityWitness
    coercion: Optional[str] = None

    def transport_refinements(self, refs: Dict[str, Any]) -> Dict[str, Any]:
        """Transport refinements from source to target type context."""
        new_refs = dict(refs)
        new_refs["_transported_from"] = self.source_type
        new_refs["_transported_to"] = self.target_type
        new_refs["_transport_equality"] = f"{self.equality.lhs} = {self.equality.rhs}"
        if self.coercion:
            new_refs["_transport_coercion"] = self.coercion
        return new_refs

    def compose(self, other: TransportMap) -> Optional[TransportMap]:
        if self.target_type == other.source_type:
            eq = self.equality.compose(other.equality)
            if eq is not None:
                return TransportMap(self.source_type, other.target_type, eq)
        return None


# ═══════════════════════════════════════════════════════════════════════════════
# Witness environment
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class WitnessEnvironment:
    """Environment tracking available witnesses and proof obligations."""
    witnesses: Dict[str, Any] = field(default_factory=dict)
    equalities: List[EqualityWitness] = field(default_factory=list)
    transports: List[TransportMap] = field(default_factory=list)
    obligations: List[ProofObligation] = field(default_factory=list)

    def add_witness(self, key: str, value: Any) -> None:
        self.witnesses[key] = value

    def add_equality(self, eq: EqualityWitness) -> None:
        self.equalities.append(eq)
        self.equalities.append(eq.reverse())

    def add_transport(self, transport: TransportMap) -> None:
        self.transports.append(transport)

    def add_obligation(self, obligation: ProofObligation) -> None:
        self.obligations.append(obligation)

    def lookup_witness(self, key: str) -> Optional[Any]:
        return self.witnesses.get(key)

    def find_equality(self, lhs: str, rhs: str) -> Optional[EqualityWitness]:
        for eq in self.equalities:
            if eq.lhs == lhs and eq.rhs == rhs:
                return eq
        for eq1 in self.equalities:
            for eq2 in self.equalities:
                if eq1.rhs == eq2.lhs:
                    composed = eq1.compose(eq2)
                    if composed and composed.lhs == lhs and composed.rhs == rhs:
                        return composed
        return None

    def find_transport(self, source: str, target: str) -> Optional[TransportMap]:
        for t in self.transports:
            if t.source_type == source and t.target_type == target:
                return t
        for t1 in self.transports:
            for t2 in self.transports:
                composed = t1.compose(t2)
                if composed and composed.source_type == source and composed.target_type == target:
                    return composed
        return None

    def discharge_obligation(self, name: str, witness_key: str) -> bool:
        for i, obl in enumerate(self.obligations):
            if obl.name == name and obl.status == ObligationStatus.PENDING:
                self.obligations[i] = obl.discharge(witness_key)
                return True
        return False

    @property
    def pending_obligations(self) -> List[ProofObligation]:
        return [o for o in self.obligations if o.status == ObligationStatus.PENDING]

    @property
    def all_discharged(self) -> bool:
        return all(o.is_resolved for o in self.obligations)

    def to_refinements(self) -> Dict[str, Any]:
        return {
            "_witness_keys": list(self.witnesses.keys()),
            "_equalities": [
                {"lhs": e.lhs, "rhs": e.rhs, "kind": e.proof_kind}
                for e in self.equalities
            ],
            "_obligations": [
                {"name": o.name, "prop": o.proposition,
                 "status": o.status.value}
                for o in self.obligations
            ],
            "_all_discharged": self.all_discharged,
            "_pending_count": len(self.pending_obligations),
        }

    @staticmethod
    def from_refinements(refs: Dict[str, Any]) -> WitnessEnvironment:
        env = WitnessEnvironment()
        for key in refs.get("_witness_keys", []):
            env.witnesses[key] = refs.get(f"_witness_{key}")
        for eq_data in refs.get("_equalities", []):
            if isinstance(eq_data, dict):
                env.equalities.append(EqualityWitness(
                    lhs=eq_data.get("lhs", ""),
                    rhs=eq_data.get("rhs", ""),
                    proof_kind=eq_data.get("kind", "refl"),
                ))
        for obl_data in refs.get("_obligations", []):
            if isinstance(obl_data, dict):
                try:
                    status = ObligationStatus(obl_data.get("status", "pending"))
                except ValueError:
                    status = ObligationStatus.PENDING
                env.obligations.append(ProofObligation(
                    name=obl_data.get("name", ""),
                    proposition=obl_data.get("prop", ""),
                    status=status,
                ))
        return env


# ═══════════════════════════════════════════════════════════════════════════════
# WitnessTransportTheoryPack
# ═══════════════════════════════════════════════════════════════════════════════


class WitnessTransportTheoryPack(TheoryPackBase):
    """Theory Family 11: Witness & Equality Transport.

    Handles PROOF and TRACE sites for proof obligation tracking and
    witness transport.
    """

    pack_name = "witness_transport"
    pack_priority = 45

    _APPLICABLE = frozenset({
        SiteKind.PROOF,
        SiteKind.TRACE,
        SiteKind.SSA_VALUE,
        SiteKind.ERROR,
    })

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._APPLICABLE

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        refs = section.refinements
        env = WitnessEnvironment.from_refinements(refs)

        for obl in env.pending_obligations:
            witness = env.lookup_witness(obl.name)
            if witness is not None:
                env.discharge_obligation(obl.name, obl.name)
            else:
                eq = env.find_equality(obl.proposition, "True")
                if eq is not None:
                    env.discharge_obligation(obl.name, f"eq:{eq.lhs}={eq.rhs}")

        required_type = refs.get("_required_type")
        actual_type = refs.get("_actual_type")
        if required_type and actual_type and required_type != actual_type:
            transport = env.find_transport(str(actual_type), str(required_type))
            if transport is not None:
                env.add_witness(
                    f"transport_{actual_type}_to_{required_type}",
                    transport,
                )

        new_refs = dict(refs)
        new_refs.update(env.to_refinements())

        if env.all_discharged:
            return SolverResult(
                status=SolverStatus.SOLVED,
                section=LocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    refinements=new_refs,
                    trust=TrustLevel.PROOF_BACKED,
                    provenance="witness: all obligations discharged",
                    witnesses=dict(section.witnesses),
                ),
                explanation="all proof obligations discharged",
            )

        pending = env.pending_obligations
        return SolverResult(
            status=SolverStatus.REFINED,
            section=LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=new_refs,
                trust=section.trust,
                provenance=f"witness: {len(pending)} obligation(s) pending",
                witnesses=dict(section.witnesses),
            ),
            constraints_remaining=[
                f"obligation: {o.name} ({o.proposition})" for o in pending
            ],
            proof_obligations=[o.proposition for o in pending],
            explanation=f"{len(pending)} proof obligation(s) remain",
        )

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        restricted = morphism.restrict(section)
        env = WitnessEnvironment.from_refinements(section.refinements)

        transport_type = None
        if morphism.metadata:
            transport_type = morphism.metadata.get("transport_type")

        if transport_type is not None:
            source = morphism.metadata.get("source_type", "") if morphism.metadata else ""
            target = str(transport_type)
            transport = env.find_transport(source, target)
            if transport is not None:
                new_refs = transport.transport_refinements(restricted.refinements)
                new_refs.update(env.to_refinements())
                return LocalSection(
                    site_id=restricted.site_id,
                    carrier_type=restricted.carrier_type,
                    refinements=new_refs,
                    trust=restricted.trust,
                    provenance=f"witness transport: {source} -> {target}",
                    witnesses=dict(restricted.witnesses),
                )

        new_refs = merge_refinements(restricted.refinements, env.to_refinements(), "meet")
        return LocalSection(
            site_id=restricted.site_id,
            carrier_type=restricted.carrier_type,
            refinements=new_refs,
            trust=restricted.trust,
            provenance="witness forward: carried",
            witnesses=dict(restricted.witnesses),
        )

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        env = WitnessEnvironment.from_refinements(section.refinements)
        required_refs: Dict[str, Any] = {}

        for obl in env.pending_obligations:
            required_refs[f"_requires_witness_{obl.name}"] = obl.proposition

        if section.refinements.get("_required_type"):
            required_refs["_required_type"] = section.refinements["_required_type"]

        return LocalSection(
            site_id=morphism.source,
            carrier_type=section.carrier_type,
            refinements=required_refs,
            trust=TrustLevel.RESIDUAL,
            provenance="witness pullback: proof obligations",
        )

    def viability_predicate(self, error_site: SiteId) -> str:
        return f"all proof obligations discharged at {error_site.name}"

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        env = WitnessEnvironment.from_refinements(section.refinements)
        if env.all_discharged:
            return BoundaryClassification.FULLY_PROVEN
        if env.pending_obligations:
            return BoundaryClassification.REQUIRES_PROOF
        if section.trust == TrustLevel.ASSUMED:
            return BoundaryClassification.ASSUMED
        return BoundaryClassification.CONDITIONALLY_PROVEN
