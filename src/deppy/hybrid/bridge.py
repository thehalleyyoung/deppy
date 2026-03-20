"""deppy.hybrid.bridge — Integration bridges between deppy core and hybrid types.

Provides bidirectional conversion between the original deppy type system
and the hybrid extensions.  Each bridge handles one conceptual mapping:

- **TrustLevelBridge**: CoreTrustLevel ↔ HybridTrustLevel
- **PresheafBridge**: ConcretePresheaf ↔ HybridPresheaf
- **TypeBridge**: TypeBase ↔ HybridType (wraps any deppy type in hybrid metadata)
- **ObstructionBridge**: ObstructionData ↔ IntentGap
- **PipelineBridge**: PipelineResult → hybrid-enriched result
- **SolverBridge**: Obligation ↔ ProofObligation
"""

from __future__ import annotations

import enum
import time
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterable,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Type,
    Union,
)

# ---------------------------------------------------------------------------
# Conditional imports from deppy core
# ---------------------------------------------------------------------------
try:
    from deppy.core._protocols import (
        TrustLevel as CoreTrustLevel,
        SiteId,
        LocalSection,
        GlobalSection,
        Cover,
        Morphism,
        ObstructionData,
        CechCochainData,
        CohomologyClass,
        RepairSuggestion,
    )
    _HAS_PROTOCOLS = True
except ImportError:
    _HAS_PROTOCOLS = False
    CoreTrustLevel = None  # type: ignore[assignment,misc]

try:
    from deppy.core.presheaf import ConcretePresheaf, GluingResult, SheafConditionChecker
    _HAS_PRESHEAF = True
except ImportError:
    _HAS_PRESHEAF = False

try:
    from deppy.types.base import TypeBase
    _HAS_BASE = True
except ImportError:
    _HAS_BASE = False
    TypeBase = object  # type: ignore[assignment,misc]

try:
    from deppy.types.dependent import (
        PiType,
        SigmaType,
        IdentityType,
        WitnessType,
        ForallType,
        ExistsType,
        DependentRecordType,
    )
    _HAS_DEPENDENT = True
except ImportError:
    _HAS_DEPENDENT = False

try:
    from deppy.types.refinement import RefinementType, Predicate
    _HAS_REFINEMENT = True
except ImportError:
    _HAS_REFINEMENT = False

try:
    from deppy.pipeline import AnalysisPipeline
    _HAS_PIPELINE = True
except ImportError:
    try:
        from deppy.pipeline.pipeline import AnalysisPipeline, PipelineResult
        _HAS_PIPELINE = True
    except ImportError:
        _HAS_PIPELINE = False

try:
    from deppy.pipeline.pipeline import PipelineResult
    _HAS_PIPELINE_RESULT = True
except ImportError:
    _HAS_PIPELINE_RESULT = False

try:
    from deppy.kernel._protocols import (
        Obligation,
        VerificationResult,
        VerificationStatus,
    )
    _HAS_KERNEL = True
except ImportError:
    _HAS_KERNEL = False

try:
    from deppy.solver.solver_interface import SolverObligation
    _HAS_SOLVER_OBLIGATION = True
except ImportError:
    _HAS_SOLVER_OBLIGATION = False

try:
    from deppy.kernel.trust_classifier import (
        TrustClassifier,
        TrustClassification,
        ProvenanceChain,
        ProvenanceTag,
    )
    _HAS_TRUST_CLASSIFIER = True
except ImportError:
    _HAS_TRUST_CLASSIFIER = False

# ---------------------------------------------------------------------------
# Hybrid imports (always available — these live in the same package)
# ---------------------------------------------------------------------------
from deppy.hybrid import HybridLayer, HybridTrustLevel

from deppy.hybrid.extensions import (
    DecidabilityClass,
    OraclePolicy,
    OracleResult,
    TrustAnnotation,
    IntentGap,
    HybridLocalSection,
    HybridCheckResult,
    ProofObligation,
    DispatchResult,
    HybridPiType,
    HybridSigmaType,
    HybridIdentityType,
    HybridRefinementType,
    HybridForallType,
    HybridExistsType,
    HybridPresheaf,
    HybridSheafChecker,
    HybridTopology,
    HybridPipeline,
    HybridDispatcher,
)

# ═══════════════════════════════════════════════════════════════════════════
#  1. TrustLevelBridge — CoreTrustLevel ↔ HybridTrustLevel
# ═══════════════════════════════════════════════════════════════════════════

# Canonical mapping tables
_HYBRID_TO_CORE: Dict[HybridTrustLevel, Any] = {}
_CORE_TO_HYBRID: Dict[Any, HybridTrustLevel] = {}

if _HAS_PROTOCOLS and CoreTrustLevel is not None:
    _HYBRID_TO_CORE = {
        HybridTrustLevel.UNTRUSTED: CoreTrustLevel.ASSUMED,
        HybridTrustLevel.LLM_RAW: CoreTrustLevel.RESIDUAL,
        HybridTrustLevel.LLM_JUDGED: CoreTrustLevel.TRACE_BACKED,
        HybridTrustLevel.PROPERTY_CHECKED: CoreTrustLevel.BOUNDED_AUTO,
        HybridTrustLevel.Z3_PROVEN: CoreTrustLevel.PROOF_BACKED,
        HybridTrustLevel.LEAN_VERIFIED: CoreTrustLevel.TRUSTED_AUTO,
        HybridTrustLevel.HUMAN_VERIFIED: CoreTrustLevel.TRUSTED_AUTO,
    }
    _CORE_TO_HYBRID = {
        CoreTrustLevel.ASSUMED: HybridTrustLevel.UNTRUSTED,
        CoreTrustLevel.RESIDUAL: HybridTrustLevel.LLM_RAW,
        CoreTrustLevel.TRACE_BACKED: HybridTrustLevel.LLM_JUDGED,
        CoreTrustLevel.BOUNDED_AUTO: HybridTrustLevel.PROPERTY_CHECKED,
        CoreTrustLevel.PROOF_BACKED: HybridTrustLevel.Z3_PROVEN,
        CoreTrustLevel.TRUSTED_AUTO: HybridTrustLevel.LEAN_VERIFIED,
    }


class TrustLevelBridge:
    """Bidirectional mapping between CoreTrustLevel and HybridTrustLevel.

    The core deppy system uses a 6-level trust enum::

        TRUSTED_AUTO > PROOF_BACKED > TRACE_BACKED > BOUNDED_AUTO > RESIDUAL > ASSUMED

    The hybrid system uses a finer 7-level IntEnum::

        HUMAN_VERIFIED > LEAN_VERIFIED > Z3_PROVEN > PROPERTY_CHECKED > LLM_JUDGED > LLM_RAW > UNTRUSTED

    The bridge handles the many-to-one mapping (LEAN_VERIFIED and
    HUMAN_VERIFIED both map to TRUSTED_AUTO) and the inverse (TRUSTED_AUTO
    maps to LEAN_VERIFIED by default).
    """

    # -- Forward: Hybrid → Core -------------------------------------------

    @staticmethod
    def to_core(hybrid: HybridTrustLevel) -> Any:
        """Convert a HybridTrustLevel to the corresponding CoreTrustLevel.

        Returns ``None`` if the core library is not available.
        """
        if not _HAS_PROTOCOLS or CoreTrustLevel is None:
            return None
        return _HYBRID_TO_CORE.get(hybrid)

    @staticmethod
    def to_core_or_default(
        hybrid: HybridTrustLevel,
        default: Any = None,
    ) -> Any:
        """Convert, falling back to *default* on missing core."""
        result = TrustLevelBridge.to_core(hybrid)
        return result if result is not None else default

    @staticmethod
    def batch_to_core(
        levels: Iterable[HybridTrustLevel],
    ) -> List[Any]:
        """Convert a sequence of hybrid trust levels to core levels."""
        return [TrustLevelBridge.to_core(lv) for lv in levels]

    # -- Reverse: Core → Hybrid -------------------------------------------

    @staticmethod
    def from_core(core: Any) -> HybridTrustLevel:
        """Convert a CoreTrustLevel to the corresponding HybridTrustLevel.

        Returns ``UNTRUSTED`` for unrecognized values.
        """
        if core is None:
            return HybridTrustLevel.UNTRUSTED
        return _CORE_TO_HYBRID.get(core, HybridTrustLevel.UNTRUSTED)

    @staticmethod
    def batch_from_core(levels: Iterable[Any]) -> List[HybridTrustLevel]:
        """Convert a sequence of core trust levels to hybrid levels."""
        return [TrustLevelBridge.from_core(lv) for lv in levels]

    # -- Comparison utilities ----------------------------------------------

    @staticmethod
    def trust_leq(a: HybridTrustLevel, b: HybridTrustLevel) -> bool:
        """Check whether *a* ≤ *b* in the trust lattice."""
        return a.value <= b.value

    @staticmethod
    def trust_meet(a: HybridTrustLevel, b: HybridTrustLevel) -> HybridTrustLevel:
        """Greatest lower bound (weakest link)."""
        return min(a, b, key=lambda x: x.value)

    @staticmethod
    def trust_join(a: HybridTrustLevel, b: HybridTrustLevel) -> HybridTrustLevel:
        """Least upper bound."""
        return max(a, b, key=lambda x: x.value)

    @staticmethod
    def hybrid_rank(level: HybridTrustLevel) -> int:
        """Numeric rank (0–6) for a hybrid trust level."""
        return level.value

    @staticmethod
    def core_rank(core: Any) -> int:
        """Numeric rank (0–5) for a core trust level.

        Uses the existing ``trust_rank`` function if available.
        """
        if _HAS_TRUST_CLASSIFIER:
            from deppy.kernel.trust_classifier import trust_rank
            return trust_rank(core)
        # Fallback ordering
        _RANK: Dict[str, int] = {
            "ASSUMED": 0,
            "RESIDUAL": 1,
            "BOUNDED_AUTO": 2,
            "TRACE_BACKED": 3,
            "PROOF_BACKED": 4,
            "TRUSTED_AUTO": 5,
        }
        name = core.name if hasattr(core, "name") else str(core)
        return _RANK.get(name, 0)

    # -- Annotation bridge -------------------------------------------------

    @staticmethod
    def annotation_from_core(core_trust: Any, source: str = "core") -> TrustAnnotation:
        """Create a TrustAnnotation from a core TrustLevel."""
        hybrid = TrustLevelBridge.from_core(core_trust)
        return TrustAnnotation(level=hybrid, source=source)

    @staticmethod
    def annotation_to_core(annotation: TrustAnnotation) -> Any:
        """Extract the CoreTrustLevel from a TrustAnnotation."""
        return TrustLevelBridge.to_core(annotation.level)

    # -- Provenance bridge -------------------------------------------------

    @staticmethod
    def provenance_to_hybrid(
        provenance_chain: Any,
    ) -> Tuple[HybridTrustLevel, List[str]]:
        """Convert a core ProvenanceChain to hybrid trust + step descriptions.

        Returns ``(effective_trust, step_descriptions)``.
        """
        if _HAS_TRUST_CLASSIFIER and provenance_chain is not None:
            core_trust = provenance_chain.effective_trust()
            hybrid_trust = TrustLevelBridge.from_core(core_trust)
            steps = [
                f"{tag.step_kind}@{tag.source_site}"
                for tag in provenance_chain.tags
            ]
            return (hybrid_trust, steps)
        return (HybridTrustLevel.UNTRUSTED, [])

    @staticmethod
    def classification_to_hybrid(
        classification: Any,
    ) -> Dict[str, Any]:
        """Convert a core TrustClassification to a hybrid-friendly dict."""
        if _HAS_TRUST_CLASSIFIER and classification is not None:
            return {
                "site": str(classification.section_site),
                "trust": TrustLevelBridge.from_core(
                    classification.assigned_trust
                ).name,
                "reasoning": classification.reasoning,
                "provenance_length": classification.provenance_chain.length,
            }
        return {"site": None, "trust": "UNTRUSTED", "reasoning": "", "provenance_length": 0}


# ═══════════════════════════════════════════════════════════════════════════
#  2. PresheafBridge — ConcretePresheaf ↔ HybridPresheaf
# ═══════════════════════════════════════════════════════════════════════════

class PresheafBridge:
    """Convert between ConcretePresheaf and HybridPresheaf.

    The core presheaf stores sections at SiteId keys.
    The hybrid presheaf indexes by (SiteId, HybridLayer) pairs.

    Lifting: sections from the core presheaf are placed in the
    STRUCTURAL layer by default.

    Projection: the hybrid presheaf can be projected to a single layer,
    yielding a core-compatible presheaf.
    """

    # -- Lift: Core → Hybrid -----------------------------------------------

    @staticmethod
    def lift(
        presheaf: Any,
        default_layer: HybridLayer = HybridLayer.STRUCTURAL,
        default_trust: HybridTrustLevel = HybridTrustLevel.UNTRUSTED,
    ) -> HybridPresheaf:
        """Lift a ConcretePresheaf into a HybridPresheaf.

        All sections are assigned to *default_layer* with *default_trust*.
        """
        name = getattr(presheaf, "name", "")
        hybrid = HybridPresheaf(name=f"hybrid_{name}")

        if not _HAS_PRESHEAF or not _HAS_PROTOCOLS:
            return hybrid

        for site_id in presheaf.site_ids():
            for section in presheaf.sections_at(site_id):
                core_trust = getattr(section, "trust", None)
                if core_trust is not None:
                    h_trust = TrustLevelBridge.from_core(core_trust)
                else:
                    h_trust = default_trust
                hybrid_section = HybridLocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    trust=TrustAnnotation(level=h_trust, source="lifted"),
                    layer=default_layer,
                    refinements=dict(getattr(section, "refinements", {})),
                    provenance=getattr(section, "provenance", None),
                )
                hybrid.add_hybrid_section(hybrid_section)

        return hybrid

    @staticmethod
    def lift_with_layers(
        presheaf: Any,
        layer_mapping: Dict[Any, HybridLayer],
    ) -> HybridPresheaf:
        """Lift with an explicit per-site layer assignment.

        Parameters
        ----------
        layer_mapping
            Mapping from SiteId to HybridLayer.  Sites not in the mapping
            are assigned to STRUCTURAL.
        """
        name = getattr(presheaf, "name", "")
        hybrid = HybridPresheaf(name=f"hybrid_{name}")

        if not _HAS_PRESHEAF or not _HAS_PROTOCOLS:
            return hybrid

        for site_id in presheaf.site_ids():
            layer = layer_mapping.get(site_id, HybridLayer.STRUCTURAL)
            for section in presheaf.sections_at(site_id):
                core_trust = getattr(section, "trust", None)
                h_trust = (
                    TrustLevelBridge.from_core(core_trust)
                    if core_trust is not None
                    else HybridTrustLevel.UNTRUSTED
                )
                hybrid_section = HybridLocalSection(
                    site_id=section.site_id,
                    carrier_type=section.carrier_type,
                    trust=TrustAnnotation(level=h_trust, source="lifted"),
                    layer=layer,
                    refinements=dict(getattr(section, "refinements", {})),
                    provenance=getattr(section, "provenance", None),
                )
                hybrid.add_hybrid_section(hybrid_section)

        return hybrid

    # -- Project: Hybrid → Core --------------------------------------------

    @staticmethod
    def project(
        hybrid: HybridPresheaf,
        layer: HybridLayer = HybridLayer.STRUCTURAL,
    ) -> Any:
        """Project a HybridPresheaf to a ConcretePresheaf at a single layer.

        Only sections in the specified layer are included.
        """
        if not _HAS_PRESHEAF or not _HAS_PROTOCOLS:
            return None

        presheaf = ConcretePresheaf(name=f"proj_{layer.value}_{hybrid.hybrid_name}")

        for (sid, l) in hybrid.layer_site_ids():
            if l != layer:
                continue
            for h_sec in hybrid.sections_at_layer(sid, l):
                core_trust = TrustLevelBridge.to_core(h_sec.hybrid_trust_level)
                if core_trust is None:
                    core_trust = CoreTrustLevel.ASSUMED
                core_section = LocalSection(
                    site_id=sid,
                    carrier_type=h_sec.carrier_type,
                    refinements=h_sec.refinements,
                    trust=core_trust,
                    provenance=h_sec.provenance,
                    witnesses={},
                )
                presheaf.add_section(core_section)

        return presheaf

    @staticmethod
    def project_all_layers(
        hybrid: HybridPresheaf,
    ) -> Dict[HybridLayer, Any]:
        """Project the hybrid presheaf into per-layer core presheaves."""
        result: Dict[HybridLayer, Any] = {}
        for layer in HybridLayer:
            presheaf = PresheafBridge.project(hybrid, layer)
            if presheaf is not None:
                result[layer] = presheaf
        return result

    # -- Merge & diff utilities -------------------------------------------

    @staticmethod
    def merge(
        a: HybridPresheaf,
        b: HybridPresheaf,
    ) -> HybridPresheaf:
        """Merge two hybrid presheaves, taking the higher-trust section on conflicts."""
        merged = HybridPresheaf(name=f"merge({a.hybrid_name},{b.hybrid_name})")

        all_keys: Set[Tuple[Any, HybridLayer]] = set()
        all_keys.update(a.layer_site_ids())
        all_keys.update(b.layer_site_ids())

        for (sid, layer) in all_keys:
            secs_a = a.sections_at_layer(sid, layer)
            secs_b = b.sections_at_layer(sid, layer)

            if secs_a and secs_b:
                # Take the higher-trust section
                best_a = max(secs_a, key=lambda s: s.hybrid_trust_level.value)
                best_b = max(secs_b, key=lambda s: s.hybrid_trust_level.value)
                winner = (
                    best_a
                    if best_a.hybrid_trust_level.value >= best_b.hybrid_trust_level.value
                    else best_b
                )
                merged.add_hybrid_section(winner)
            else:
                for sec in (secs_a or secs_b):
                    merged.add_hybrid_section(sec)

        return merged

    @staticmethod
    def diff(
        old: HybridPresheaf,
        new: HybridPresheaf,
    ) -> Dict[str, List[Tuple[Any, HybridLayer]]]:
        """Compute the difference between two hybrid presheaves.

        Returns a dict with keys ``added``, ``removed``, ``changed``.
        """
        old_keys = old.layer_site_ids()
        new_keys = new.layer_site_ids()

        added = new_keys - old_keys
        removed = old_keys - new_keys
        common = old_keys & new_keys

        changed: List[Tuple[Any, HybridLayer]] = []
        for key in common:
            sid, layer = key
            old_secs = old.sections_at_layer(sid, layer)
            new_secs = new.sections_at_layer(sid, layer)
            if len(old_secs) != len(new_secs):
                changed.append(key)
            elif old_secs and new_secs:
                old_best = max(old_secs, key=lambda s: s.hybrid_trust_level.value)
                new_best = max(new_secs, key=lambda s: s.hybrid_trust_level.value)
                if old_best.hybrid_trust_level != new_best.hybrid_trust_level:
                    changed.append(key)
                elif old_best.carrier_type != new_best.carrier_type:
                    changed.append(key)

        return {
            "added": sorted(added, key=str),
            "removed": sorted(removed, key=str),
            "changed": sorted(changed, key=str),
        }

    # -- Section conversion helpers ----------------------------------------

    @staticmethod
    def local_section_to_hybrid(
        section: Any,
        layer: HybridLayer = HybridLayer.STRUCTURAL,
    ) -> HybridLocalSection:
        """Convert a core LocalSection to a HybridLocalSection."""
        core_trust = getattr(section, "trust", None)
        h_trust = (
            TrustLevelBridge.from_core(core_trust)
            if core_trust is not None
            else HybridTrustLevel.UNTRUSTED
        )
        return HybridLocalSection(
            site_id=getattr(section, "site_id", None),
            carrier_type=getattr(section, "carrier_type", None),
            trust=TrustAnnotation(level=h_trust, source="bridge"),
            layer=layer,
            refinements=dict(getattr(section, "refinements", {})),
            provenance=getattr(section, "provenance", None),
        )

    @staticmethod
    def hybrid_section_to_core(section: HybridLocalSection) -> Any:
        """Convert a HybridLocalSection to a core LocalSection."""
        if not _HAS_PROTOCOLS:
            return None
        core_trust = TrustLevelBridge.to_core(section.hybrid_trust_level)
        if core_trust is None:
            core_trust = CoreTrustLevel.ASSUMED
        return LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=section.refinements,
            trust=core_trust,
            provenance=section.provenance,
            witnesses={},
        )


# ═══════════════════════════════════════════════════════════════════════════
#  3. TypeBridge — TypeBase ↔ HybridType wrapping
# ═══════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class HybridTypeWrapper:
    """Wraps any deppy TypeBase in hybrid metadata.

    This is used when a type does not have a dedicated hybrid subclass
    (e.g., ListType, DictType, ClassType) but still needs trust and
    layer annotations.
    """

    inner: Any
    trust: TrustAnnotation = field(default_factory=TrustAnnotation.untrusted)
    layer: HybridLayer = HybridLayer.STRUCTURAL
    decidability: DecidabilityClass = DecidabilityClass.UNKNOWN
    oracle_policy: OraclePolicy = OraclePolicy.FALLBACK
    metadata: Dict[str, Any] = field(default_factory=dict)

    @property
    def effective_trust(self) -> TrustAnnotation:
        return self.trust

    @property
    def is_hybrid(self) -> bool:
        return True

    def unwrap(self) -> Any:
        """Return the inner TypeBase, stripping hybrid metadata."""
        return self.inner

    def with_trust(self, trust: TrustAnnotation) -> HybridTypeWrapper:
        return HybridTypeWrapper(
            inner=self.inner,
            trust=trust,
            layer=self.layer,
            decidability=self.decidability,
            oracle_policy=self.oracle_policy,
            metadata=self.metadata,
        )

    def with_layer(self, layer: HybridLayer) -> HybridTypeWrapper:
        return HybridTypeWrapper(
            inner=self.inner,
            trust=self.trust,
            layer=layer,
            decidability=self.decidability,
            oracle_policy=self.oracle_policy,
            metadata=self.metadata,
        )

    def __repr__(self) -> str:
        return (
            f"Hybrid[{self.inner!r}] "
            f"⟨{self.trust.level.name}⟩ @{self.layer.value}"
        )


class TypeBridge:
    """Convert between core deppy types and hybrid types.

    Handles:
    - Wrapping arbitrary TypeBase in HybridTypeWrapper for metadata
    - Converting PiType → HybridPiType, SigmaType → HybridSigmaType, etc.
    - Unwrapping hybrid types back to their core form
    """

    # -- Core → Hybrid conversion ------------------------------------------

    @staticmethod
    def to_hybrid(
        core_type: Any,
        trust: Optional[TrustAnnotation] = None,
        layer: HybridLayer = HybridLayer.STRUCTURAL,
    ) -> Any:
        """Convert a core deppy type to its hybrid equivalent.

        Uses the specific hybrid subclass when available (PiType → HybridPiType),
        otherwise wraps in HybridTypeWrapper.
        """
        ann = trust or TrustAnnotation.untrusted()

        # Already hybrid?
        if isinstance(core_type, (
            HybridPiType, HybridSigmaType, HybridIdentityType,
            HybridRefinementType, HybridForallType, HybridExistsType,
            HybridTypeWrapper,
        )):
            return core_type

        if _HAS_DEPENDENT:
            if isinstance(core_type, PiType):
                return HybridPiType(
                    param_name=core_type.param_name,
                    param_type=core_type.param_type,
                    return_type=core_type.return_type,
                    domain_trust=ann,
                    codomain_trust=ann,
                    layer=layer,
                )
            if isinstance(core_type, SigmaType):
                return HybridSigmaType(
                    fst_name=core_type.fst_name,
                    fst_type=core_type.fst_type,
                    snd_type=core_type.snd_type,
                    fst_trust=ann,
                    snd_trust=ann,
                    fst_layer=layer,
                    snd_layer=layer,
                )
            if isinstance(core_type, IdentityType):
                return HybridIdentityType(
                    carrier=core_type.carrier,
                    lhs=core_type.lhs,
                    rhs=core_type.rhs,
                    trust=ann,
                    layer=layer,
                )
            if isinstance(core_type, ForallType):
                return HybridForallType(
                    var_name=core_type.var_name,
                    body=core_type.body,
                    bound=core_type.bound,
                    trust=ann,
                    layer=layer,
                )
            if isinstance(core_type, ExistsType):
                return HybridExistsType(
                    var_name=core_type.var_name,
                    body=core_type.body,
                    bound=core_type.bound,
                    trust=ann,
                    layer=layer,
                )

        if _HAS_REFINEMENT and isinstance(core_type, RefinementType):
            return HybridRefinementType(
                base=core_type.base,
                binder=core_type.binder,
                predicate=core_type.predicate,
                trust=ann,
                layer=layer,
            )

        # Generic fallback: wrap in HybridTypeWrapper
        return HybridTypeWrapper(inner=core_type, trust=ann, layer=layer)

    @staticmethod
    def batch_to_hybrid(
        types: Iterable[Any],
        trust: Optional[TrustAnnotation] = None,
        layer: HybridLayer = HybridLayer.STRUCTURAL,
    ) -> List[Any]:
        """Convert a sequence of core types to hybrid types."""
        return [TypeBridge.to_hybrid(t, trust, layer) for t in types]

    # -- Hybrid → Core conversion ------------------------------------------

    @staticmethod
    def from_hybrid(hybrid_type: Any) -> Any:
        """Convert a hybrid type back to its core deppy equivalent.

        Strips all hybrid metadata (trust, layer, oracle policy).
        """
        if isinstance(hybrid_type, HybridTypeWrapper):
            return hybrid_type.unwrap()

        if isinstance(hybrid_type, HybridPiType) and _HAS_DEPENDENT:
            return PiType(
                hybrid_type._h_param_name,
                hybrid_type._h_param_type,
                hybrid_type._h_return_type,
            )

        if isinstance(hybrid_type, HybridSigmaType) and _HAS_DEPENDENT:
            return SigmaType(
                hybrid_type._h_fst_name,
                hybrid_type._h_fst_type,
                hybrid_type._h_snd_type,
            )

        if isinstance(hybrid_type, HybridIdentityType) and _HAS_DEPENDENT:
            return IdentityType(
                hybrid_type._h_carrier,
                hybrid_type._h_lhs,
                hybrid_type._h_rhs,
            )

        if isinstance(hybrid_type, HybridForallType) and _HAS_DEPENDENT:
            return ForallType(
                hybrid_type._h_var_name,
                hybrid_type._h_body,
                hybrid_type._h_bound,
            )

        if isinstance(hybrid_type, HybridExistsType) and _HAS_DEPENDENT:
            return ExistsType(
                hybrid_type._h_var_name,
                hybrid_type._h_body,
                hybrid_type._h_bound,
            )

        if isinstance(hybrid_type, HybridRefinementType) and _HAS_REFINEMENT:
            return RefinementType(
                hybrid_type._h_base,
                hybrid_type._h_binder,
                hybrid_type._h_predicate,
            )

        # Already a core type or unknown
        return hybrid_type

    @staticmethod
    def batch_from_hybrid(types: Iterable[Any]) -> List[Any]:
        """Convert a sequence of hybrid types back to core types."""
        return [TypeBridge.from_hybrid(t) for t in types]

    # -- Trust extraction --------------------------------------------------

    @staticmethod
    def extract_trust(hybrid_type: Any) -> TrustAnnotation:
        """Extract the trust annotation from a hybrid type."""
        if isinstance(hybrid_type, HybridTypeWrapper):
            return hybrid_type.trust
        if hasattr(hybrid_type, "effective_trust"):
            return hybrid_type.effective_trust
        if hasattr(hybrid_type, "_trust"):
            return hybrid_type._trust
        return TrustAnnotation.untrusted()

    @staticmethod
    def extract_layer(hybrid_type: Any) -> HybridLayer:
        """Extract the layer from a hybrid type."""
        if isinstance(hybrid_type, HybridTypeWrapper):
            return hybrid_type.layer
        if hasattr(hybrid_type, "layer"):
            return hybrid_type.layer
        if hasattr(hybrid_type, "_layer"):
            return hybrid_type._layer
        return HybridLayer.STRUCTURAL

    # -- Type comparison with trust ----------------------------------------

    @staticmethod
    def types_compatible(a: Any, b: Any) -> Tuple[bool, TrustAnnotation]:
        """Check if two (possibly hybrid) types are compatible.

        Returns ``(compatible, combined_trust)`` where trust is the
        weakest link of both types' trust annotations.
        """
        core_a = TypeBridge.from_hybrid(a)
        core_b = TypeBridge.from_hybrid(b)
        trust_a = TypeBridge.extract_trust(a)
        trust_b = TypeBridge.extract_trust(b)
        combined = trust_a.meet(trust_b)

        compatible = (core_a == core_b)
        return (compatible, combined)

    @staticmethod
    def roundtrip_check(core_type: Any) -> bool:
        """Verify that core → hybrid → core is identity.

        Useful for testing the bridge correctness.
        """
        hybrid = TypeBridge.to_hybrid(core_type)
        back = TypeBridge.from_hybrid(hybrid)
        return back == core_type


# ═══════════════════════════════════════════════════════════════════════════
#  4. ObstructionBridge — ObstructionData ↔ IntentGap
# ═══════════════════════════════════════════════════════════════════════════

class ObstructionBridge:
    """Convert between core ObstructionData and hybrid IntentGap.

    Core obstructions represent non-trivial H¹ classes (sections that
    cannot be glued).  Hybrid IntentGaps represent mismatches between
    layers (intent vs. structure vs. proof).

    The bridge translates overlap conflicts into layer-aware gap descriptions.
    """

    @staticmethod
    def to_intent_gap(
        obstruction: Any,
        layer_from: HybridLayer = HybridLayer.STRUCTURAL,
        layer_to: HybridLayer = HybridLayer.PROOF,
    ) -> IntentGap:
        """Convert a core ObstructionData to an IntentGap.

        The obstruction's explanation is used as the gap description.
        Severity is computed from the number of conflicting overlaps.
        """
        explanation = getattr(obstruction, "explanation", str(obstruction))
        conflicts = getattr(obstruction, "conflicting_overlaps", [])
        is_trivial = getattr(obstruction, "is_trivial", True)

        if is_trivial:
            severity = 0.0
        elif len(conflicts) == 0:
            severity = 0.3
        else:
            severity = min(1.0, len(conflicts) * 0.2)

        site_id = conflicts[0][0] if conflicts else None

        return IntentGap(
            layer_from=layer_from,
            layer_to=layer_to,
            description=explanation,
            severity=severity,
            site_id=site_id,
        )

    @staticmethod
    def batch_to_intent_gaps(
        obstructions: Iterable[Any],
        layer_from: HybridLayer = HybridLayer.STRUCTURAL,
        layer_to: HybridLayer = HybridLayer.PROOF,
    ) -> List[IntentGap]:
        """Convert a sequence of core obstructions to IntentGaps."""
        return [
            ObstructionBridge.to_intent_gap(obs, layer_from, layer_to)
            for obs in obstructions
        ]

    @staticmethod
    def from_intent_gap(
        gap: IntentGap,
    ) -> Any:
        """Convert an IntentGap to a core ObstructionData (if available).

        Returns ``None`` if the core library is not installed.
        """
        if not _HAS_PROTOCOLS:
            return None

        conflicts: List[Tuple[Any, Any]] = []
        if gap.site_id is not None:
            conflicts.append((gap.site_id, gap.site_id))

        cohomology = None
        if gap.severity > 0.5:
            cochain = CechCochainData(degree=1, values={})
            cohomology = CohomologyClass(
                degree=1,
                representative=cochain,
                is_trivial=(gap.severity < 0.1),
            )

        return ObstructionData(
            cohomology_class=cohomology,
            conflicting_overlaps=conflicts,
            explanation=gap.description,
        )

    @staticmethod
    def batch_from_intent_gaps(gaps: Iterable[IntentGap]) -> List[Any]:
        """Convert a sequence of IntentGaps to core ObstructionData."""
        results = [ObstructionBridge.from_intent_gap(g) for g in gaps]
        return [r for r in results if r is not None]

    # -- Severity mapping --------------------------------------------------

    @staticmethod
    def severity_to_trust(severity: float) -> HybridTrustLevel:
        """Map gap severity to the maximum achievable trust level.

        Higher severity means lower achievable trust:
        - 0.0 → LEAN_VERIFIED (no gap)
        - 0.0–0.3 → Z3_PROVEN
        - 0.3–0.5 → PROPERTY_CHECKED
        - 0.5–0.7 → LLM_JUDGED
        - 0.7–0.9 → LLM_RAW
        - 0.9–1.0 → UNTRUSTED
        """
        if severity <= 0.0:
            return HybridTrustLevel.LEAN_VERIFIED
        if severity <= 0.3:
            return HybridTrustLevel.Z3_PROVEN
        if severity <= 0.5:
            return HybridTrustLevel.PROPERTY_CHECKED
        if severity <= 0.7:
            return HybridTrustLevel.LLM_JUDGED
        if severity <= 0.9:
            return HybridTrustLevel.LLM_RAW
        return HybridTrustLevel.UNTRUSTED

    @staticmethod
    def gap_to_repair_suggestion(gap: IntentGap) -> Dict[str, Any]:
        """Convert an IntentGap to a repair suggestion dict."""
        max_trust = ObstructionBridge.severity_to_trust(gap.severity)
        return {
            "gap": {
                "from": gap.layer_from.value,
                "to": gap.layer_to.value,
                "description": gap.description,
                "severity": gap.severity,
            },
            "max_achievable_trust": max_trust.name,
            "suggested_action": (
                "oracle_verify" if gap.severity < 0.5
                else "human_review" if gap.severity < 0.8
                else "redesign"
            ),
        }

    # -- Cohomology bridge -------------------------------------------------

    @staticmethod
    def cohomology_to_gaps(
        cohomology: Any,
    ) -> List[IntentGap]:
        """Convert a CohomologyClass to a list of IntentGaps.

        Non-trivial cohomology indicates obstructions to gluing.
        """
        if cohomology is None:
            return []
        is_trivial = getattr(cohomology, "is_trivial", True)
        if is_trivial:
            return []

        degree = getattr(cohomology, "degree", 0)
        return [IntentGap(
            layer_from=HybridLayer.STRUCTURAL,
            layer_to=HybridLayer.PROOF,
            description=f"Non-trivial H^{degree} obstruction",
            severity=0.7 if degree >= 1 else 0.3,
        )]


# ═══════════════════════════════════════════════════════════════════════════
#  5. PipelineBridge — PipelineResult → HybridPipeline enrichment
# ═══════════════════════════════════════════════════════════════════════════

class PipelineBridge:
    """Enrich PipelineResult with hybrid trust and layer information.

    The core pipeline produces a PipelineResult with cover, sections,
    obstructions, and diagnostics.  This bridge adds:
    - Per-section trust annotations
    - Layer assignments based on site kind
    - Intent gap detection from obstructions
    - Overall hybrid trust computation
    """

    # -- Site-kind to layer mapping ----------------------------------------

    _SITE_KIND_TO_LAYER: Dict[str, HybridLayer] = {
        "ARGUMENT_BOUNDARY": HybridLayer.STRUCTURAL,
        "RETURN_OUTPUT_BOUNDARY": HybridLayer.STRUCTURAL,
        "SSA_VALUE": HybridLayer.CODE,
        "BRANCH_GUARD": HybridLayer.SEMANTIC,
        "CALL_RESULT": HybridLayer.CODE,
        "TENSOR_SHAPE": HybridLayer.SEMANTIC,
        "TENSOR_ORDER": HybridLayer.SEMANTIC,
        "TENSOR_INDEXING": HybridLayer.SEMANTIC,
        "HEAP_PROTOCOL": HybridLayer.STRUCTURAL,
        "PROOF": HybridLayer.PROOF,
        "TRACE": HybridLayer.PROOF,
        "ERROR": HybridLayer.CODE,
        "LOOP_HEADER_INVARIANT": HybridLayer.SEMANTIC,
        "MODULE_SUMMARY": HybridLayer.INTENT,
    }

    @staticmethod
    def site_kind_to_layer(site_kind: Any) -> HybridLayer:
        """Map a SiteKind to a HybridLayer."""
        kind_name = site_kind.name if hasattr(site_kind, "name") else str(site_kind)
        return PipelineBridge._SITE_KIND_TO_LAYER.get(
            kind_name, HybridLayer.STRUCTURAL
        )

    # -- Full enrichment ---------------------------------------------------

    @staticmethod
    def enrich(
        pipeline_result: Any,
        oracle_fn: Optional[Callable[..., OracleResult]] = None,
    ) -> Dict[str, Any]:
        """Enrich a PipelineResult with hybrid metadata.

        Returns a dictionary compatible with HybridPipeline.run_hybrid() output.
        """
        hybrid_presheaf = HybridPresheaf(name="enriched")
        all_gaps: List[IntentGap] = []

        # Lift sections to hybrid presheaf with layer info
        sections = getattr(pipeline_result, "_sections", None)
        if sections is None:
            sections = getattr(pipeline_result, "sections", None)

        if sections and _HAS_PROTOCOLS:
            if isinstance(sections, dict):
                section_iter = sections.values() if isinstance(
                    next(iter(sections.values()), None), list
                ) else [sections.values()]
                for section_group in section_iter:
                    if isinstance(section_group, list):
                        for section in section_group:
                            PipelineBridge._add_section_to_hybrid(
                                section, hybrid_presheaf
                            )
                    else:
                        PipelineBridge._add_section_to_hybrid(
                            section_group, hybrid_presheaf
                        )

        # Convert obstructions to intent gaps
        obstructions = getattr(pipeline_result, "_obstructions", None)
        if obstructions is None:
            obstructions = getattr(pipeline_result, "obstructions", None)

        if obstructions:
            for obs in obstructions:
                gap = ObstructionBridge.to_intent_gap(obs)
                all_gaps.append(gap)

        # Compute H¹
        _, h1_gaps = hybrid_presheaf.compute_h1()
        all_gaps.extend(h1_gaps)

        # Compute overall trust
        all_trusts: List[HybridTrustLevel] = []
        for key, secs in hybrid_presheaf._layer_sections.items():
            for sec in secs:
                all_trusts.append(sec.hybrid_trust_level)

        overall_trust = (
            min(all_trusts, key=lambda x: x.value)
            if all_trusts
            else HybridTrustLevel.UNTRUSTED
        )

        return {
            "base_result": pipeline_result,
            "presheaf": hybrid_presheaf,
            "intent_gaps": all_gaps,
            "overall_trust": overall_trust.name,
            "section_count": len(all_trusts),
            "gap_count": len(all_gaps),
            "critical_gaps": [g for g in all_gaps if g.is_critical],
            "trust_distribution": {
                level.name: sum(1 for t in all_trusts if t == level)
                for level in HybridTrustLevel
                if any(t == level for t in all_trusts)
            },
        }

    @staticmethod
    def _add_section_to_hybrid(
        section: Any,
        presheaf: HybridPresheaf,
    ) -> None:
        """Convert and add a single core section to the hybrid presheaf."""
        site_id = getattr(section, "site_id", None)
        if site_id is None:
            return

        kind = getattr(site_id, "kind", None)
        layer = PipelineBridge.site_kind_to_layer(kind) if kind else HybridLayer.STRUCTURAL

        core_trust = getattr(section, "trust", None)
        h_trust = (
            TrustLevelBridge.from_core(core_trust)
            if core_trust is not None
            else HybridTrustLevel.UNTRUSTED
        )

        hybrid_section = HybridLocalSection(
            site_id=site_id,
            carrier_type=getattr(section, "carrier_type", None),
            trust=TrustAnnotation(level=h_trust, source="pipeline_bridge"),
            layer=layer,
            refinements=dict(getattr(section, "refinements", {})),
            provenance=getattr(section, "provenance", None),
        )
        presheaf.add_hybrid_section(hybrid_section)

    # -- Incremental enrichment --------------------------------------------

    @staticmethod
    def enrich_incremental(
        old_enriched: Dict[str, Any],
        new_pipeline_result: Any,
    ) -> Dict[str, Any]:
        """Incrementally enrich: only update sections that changed."""
        new_enriched = PipelineBridge.enrich(new_pipeline_result)

        old_presheaf = old_enriched.get("presheaf")
        new_presheaf = new_enriched.get("presheaf")

        if old_presheaf and new_presheaf:
            diff = PresheafBridge.diff(old_presheaf, new_presheaf)
            new_enriched["diff"] = diff
            new_enriched["changed_count"] = (
                len(diff["added"]) + len(diff["removed"]) + len(diff["changed"])
            )

        return new_enriched

    # -- Timing summary ----------------------------------------------------

    @staticmethod
    def timing_summary(pipeline_result: Any) -> Dict[str, Any]:
        """Extract timing information and annotate with hybrid stage info."""
        timing = getattr(pipeline_result, "_timing", None)
        if timing is None:
            timing = getattr(pipeline_result, "timing", None)
        if timing is None:
            return {"total_ms": 0.0, "stages": []}

        total = getattr(timing, "total_elapsed", 0.0)
        stages = []
        for st in getattr(timing, "stage_timings", []):
            stages.append({
                "name": getattr(st, "_stage_name", "unknown"),
                "elapsed_ms": (
                    getattr(st, "_end_time", 0) - getattr(st, "_start_time", 0)
                ) * 1000,
                "status": getattr(st, "_status", "unknown"),
            })
        return {"total_ms": total * 1000, "stages": stages}


# ═══════════════════════════════════════════════════════════════════════════
#  6. SolverBridge — Obligation ↔ ProofObligation
# ═══════════════════════════════════════════════════════════════════════════

class SolverBridge:
    """Convert between core solver obligations and hybrid ProofObligations.

    Core system:
    - ``Obligation``: proposition, site_id, context, trust_required (core TrustLevel)
    - ``SolverObligation``: similar but solver-specific
    - ``VerificationResult``: status, model, unsat_core, proof_term

    Hybrid system:
    - ``ProofObligation``: adds decidability, hybrid trust
    - ``DispatchResult``: adds backend, hybrid trust, evidence
    """

    # -- Core → Hybrid -----------------------------------------------------

    @staticmethod
    def obligation_to_hybrid(
        obligation: Any,
        decidability: DecidabilityClass = DecidabilityClass.UNKNOWN,
    ) -> ProofObligation:
        """Convert a core Obligation to a hybrid ProofObligation.

        Extracts proposition, site_id, context and maps trust_required.
        """
        proposition = getattr(obligation, "proposition", obligation)
        site_id = getattr(obligation, "site_id", None)
        context = dict(getattr(obligation, "context", {}))
        source_location = getattr(obligation, "source_location", None)

        core_trust = getattr(obligation, "trust_required", None)
        h_trust = (
            TrustLevelBridge.from_core(core_trust)
            if core_trust is not None
            else HybridTrustLevel.PROPERTY_CHECKED
        )

        return ProofObligation(
            proposition=proposition,
            site_id=site_id,
            context=context,
            decidability=decidability,
            trust_required=h_trust,
            source_location=source_location,
        )

    @staticmethod
    def batch_obligation_to_hybrid(
        obligations: Iterable[Any],
        decidability: DecidabilityClass = DecidabilityClass.UNKNOWN,
    ) -> List[ProofObligation]:
        """Convert a batch of core obligations to hybrid form."""
        return [
            SolverBridge.obligation_to_hybrid(ob, decidability)
            for ob in obligations
        ]

    @staticmethod
    def solver_obligation_to_hybrid(
        obligation: Any,
        decidability: DecidabilityClass = DecidabilityClass.UNKNOWN,
    ) -> ProofObligation:
        """Convert a SolverObligation to a hybrid ProofObligation."""
        return SolverBridge.obligation_to_hybrid(obligation, decidability)

    # -- Hybrid → Core -----------------------------------------------------

    @staticmethod
    def hybrid_to_obligation(
        hybrid_ob: ProofObligation,
    ) -> Any:
        """Convert a hybrid ProofObligation to a core Obligation.

        Returns ``None`` if the core library is not installed.
        """
        if not _HAS_KERNEL:
            return None

        core_trust = TrustLevelBridge.to_core(hybrid_ob.trust_required)
        if core_trust is None:
            core_trust = CoreTrustLevel.BOUNDED_AUTO if _HAS_PROTOCOLS else None

        return Obligation(
            proposition=hybrid_ob.proposition,
            site_id=hybrid_ob.site_id,
            context=hybrid_ob.context,
            source_location=hybrid_ob.source_location,
            trust_required=core_trust,
        )

    @staticmethod
    def batch_hybrid_to_obligation(
        obligations: Iterable[ProofObligation],
    ) -> List[Any]:
        """Convert a batch of hybrid obligations to core form."""
        results = [SolverBridge.hybrid_to_obligation(ob) for ob in obligations]
        return [r for r in results if r is not None]

    # -- Result conversion -------------------------------------------------

    @staticmethod
    def verification_result_to_dispatch(
        result: Any,
        obligation: ProofObligation,
    ) -> DispatchResult:
        """Convert a core VerificationResult to a hybrid DispatchResult."""
        status = getattr(result, "status", None)
        elapsed = getattr(result, "elapsed_ms", 0.0)

        # Map VerificationStatus to success + trust
        success = False
        trust = HybridTrustLevel.UNTRUSTED
        backend = "unknown"

        if status is not None:
            status_value = status.value if hasattr(status, "value") else str(status)
            if status_value == "SAT":
                success = True
                trust = HybridTrustLevel.Z3_PROVEN
                backend = "z3"
            elif status_value == "UNSAT":
                success = False
                trust = HybridTrustLevel.Z3_PROVEN
                backend = "z3"
            elif status_value == "UNKNOWN":
                success = False
                trust = HybridTrustLevel.UNTRUSTED
                backend = "z3_unknown"
            elif status_value == "TIMEOUT":
                success = False
                trust = HybridTrustLevel.UNTRUSTED
                backend = "z3_timeout"

        evidence = None
        proof_term = getattr(result, "proof_term", None)
        if proof_term is not None:
            evidence = str(proof_term)[:500]

        model = None
        raw_model = getattr(result, "model", None)
        if raw_model is not None:
            model = dict(raw_model) if isinstance(raw_model, dict) else {"raw": str(raw_model)}

        return DispatchResult(
            obligation=obligation,
            success=success,
            trust=trust,
            backend=backend,
            evidence=evidence,
            elapsed_ms=elapsed,
            model=model,
        )

    @staticmethod
    def dispatch_to_verification_result(
        dispatch: DispatchResult,
    ) -> Any:
        """Convert a hybrid DispatchResult to a core VerificationResult.

        Returns ``None`` if the core library is not installed.
        """
        if not _HAS_KERNEL:
            return None

        # Map hybrid trust back to verification status
        if dispatch.success and dispatch.trust >= HybridTrustLevel.Z3_PROVEN:
            status = VerificationStatus.SAT
        elif not dispatch.success and dispatch.trust >= HybridTrustLevel.Z3_PROVEN:
            status = VerificationStatus.UNSAT
        elif dispatch.backend == "z3_timeout":
            status = VerificationStatus.TIMEOUT
        else:
            status = VerificationStatus.UNKNOWN

        core_ob = SolverBridge.hybrid_to_obligation(dispatch.obligation)

        return VerificationResult(
            status=status,
            obligation=core_ob,
            model=dispatch.model,
            unsat_core=None,
            proof_term=dispatch.evidence,
            elapsed_ms=dispatch.elapsed_ms,
        )

    # -- Batch dispatch ↔ batch verify -------------------------------------

    @staticmethod
    def batch_results_to_dispatch(
        results: Iterable[Any],
        obligations: Iterable[ProofObligation],
    ) -> List[DispatchResult]:
        """Convert a sequence of VerificationResults to DispatchResults."""
        return [
            SolverBridge.verification_result_to_dispatch(r, ob)
            for r, ob in zip(results, obligations)
        ]

    @staticmethod
    def batch_dispatch_to_results(
        dispatches: Iterable[DispatchResult],
    ) -> List[Any]:
        """Convert a sequence of DispatchResults to VerificationResults."""
        results = [
            SolverBridge.dispatch_to_verification_result(d)
            for d in dispatches
        ]
        return [r for r in results if r is not None]

    # -- Statistics summary ------------------------------------------------

    @staticmethod
    def summarize_dispatches(dispatches: Sequence[DispatchResult]) -> Dict[str, Any]:
        """Produce a summary of dispatch results."""
        total = len(dispatches)
        success = sum(1 for d in dispatches if d.success)
        by_backend: Dict[str, int] = {}
        by_trust: Dict[str, int] = {}
        total_ms = 0.0

        for d in dispatches:
            by_backend[d.backend] = by_backend.get(d.backend, 0) + 1
            by_trust[d.trust.name] = by_trust.get(d.trust.name, 0) + 1
            total_ms += d.elapsed_ms

        return {
            "total": total,
            "success": success,
            "failure": total - success,
            "success_rate": success / total if total > 0 else 0.0,
            "by_backend": by_backend,
            "by_trust": by_trust,
            "total_elapsed_ms": total_ms,
            "avg_elapsed_ms": total_ms / total if total > 0 else 0.0,
        }

    # -- Decidability heuristics -------------------------------------------

    @staticmethod
    def classify_obligation_decidability(
        obligation: Any,
        dispatcher: Optional[HybridDispatcher] = None,
    ) -> DecidabilityClass:
        """Classify a core obligation's decidability using the hybrid dispatcher.

        Falls back to heuristics if the dispatcher is not available.
        """
        if dispatcher is not None:
            hybrid_ob = SolverBridge.obligation_to_hybrid(obligation)
            return dispatcher.classify_obligation(hybrid_ob)

        # Heuristic fallback
        prop = getattr(obligation, "proposition", obligation)
        prop_str = str(prop).lower()

        if any(kw in prop_str for kw in (
            "qf_lia", "qf_lra", "linear", "integer",
        )):
            return DecidabilityClass.DECIDABLE_Z3
        if any(kw in prop_str for kw in ("finite", "enum", "bool")):
            return DecidabilityClass.DECIDABLE_FINITE
        if any(kw in prop_str for kw in ("forall", "exists", "induction")):
            return DecidabilityClass.SEMI_DECIDABLE
        if any(kw in prop_str for kw in ("intent", "meaning", "natural")):
            return DecidabilityClass.UNDECIDABLE_ORACLE
        return DecidabilityClass.UNKNOWN


class BridgeIntentCompiler:
    """Adapter combining mixed-mode compilation with intent bridging."""

    @staticmethod
    def compile_with_intent(source: str, *, file_path: str = "<string>") -> Any:
        from deppy.hybrid.mixed_mode.compiler import compile_source_with_intent_bridge

        return compile_source_with_intent_bridge(source, file_path=file_path)


# ═══════════════════════════════════════════════════════════════════════════
# Module-level exports
# ═══════════════════════════════════════════════════════════════════════════

__all__ = [
    "TrustLevelBridge",
    "PresheafBridge",
    "TypeBridge",
    "HybridTypeWrapper",
    "ObstructionBridge",
    "PipelineBridge",
    "SolverBridge",
    "BridgeIntentCompiler",
]
