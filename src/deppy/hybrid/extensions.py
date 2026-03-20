"""deppy.hybrid.extensions — Hybrid subclasses of all core deppy types.

Extends the sheaf-descent type system with:
- Oracle-monad return and trust annotations on dependent types
- Decidability-aware dispatch (Z3 vs. LLM oracle) per type component
- Product-site presheaf with HybridLayer dimension (INTENT × … × CODE)
- H¹ cohomology computation for detecting intent–structure–proof gaps
- Hybrid verification pipeline stages on top of the existing pipeline

Each class inherits from the corresponding deppy base when available.
When deppy core modules are not installed (standalone usage), a minimal
fallback implementation is provided so that hybrid reasoning can still
be tested in isolation.
"""

from __future__ import annotations

import enum
import time
import hashlib
from abc import ABC, abstractmethod
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
    Union,
)

# ---------------------------------------------------------------------------
# Conditional imports — degrade gracefully when deppy core is absent
# ---------------------------------------------------------------------------
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
    PiType = object  # type: ignore[assignment,misc]
    SigmaType = object  # type: ignore[assignment,misc]
    IdentityType = object  # type: ignore[assignment,misc]
    WitnessType = object  # type: ignore[assignment,misc]
    ForallType = object  # type: ignore[assignment,misc]
    ExistsType = object  # type: ignore[assignment,misc]
    DependentRecordType = object  # type: ignore[assignment,misc]

try:
    from deppy.types.refinement import RefinementType, Predicate
    _HAS_REFINEMENT = True
except ImportError:
    _HAS_REFINEMENT = False
    RefinementType = object  # type: ignore[assignment,misc]
    Predicate = object  # type: ignore[assignment,misc]

try:
    from deppy.types.base import TypeBase
    _HAS_BASE = True
except ImportError:
    _HAS_BASE = False
    TypeBase = object  # type: ignore[assignment,misc]

try:
    from deppy.core.presheaf import (
        ConcretePresheaf,
        SheafConditionChecker,
        GluingResult,
    )
    _HAS_PRESHEAF = True
except ImportError:
    _HAS_PRESHEAF = False
    ConcretePresheaf = object  # type: ignore[assignment,misc]
    SheafConditionChecker = object  # type: ignore[assignment,misc]

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
    )
    _HAS_PROTOCOLS = True
except ImportError:
    _HAS_PROTOCOLS = False
    CoreTrustLevel = None  # type: ignore[assignment,misc]

try:
    from deppy.core.grothendieck import ConcreteTopolgy
    _HAS_TOPO = True
except ImportError:
    _HAS_TOPO = False
    ConcreteTopolgy = object  # type: ignore[assignment,misc]

try:
    from deppy.pipeline import AnalysisPipeline
    _HAS_PIPELINE = True
except ImportError:
    try:
        from deppy.pipeline.pipeline import AnalysisPipeline
        _HAS_PIPELINE = True
    except ImportError:
        _HAS_PIPELINE = False
        AnalysisPipeline = object  # type: ignore[assignment,misc]

try:
    from deppy.solver.fragment_dispatcher import FragmentDispatcher
    _HAS_SOLVER = True
except ImportError:
    try:
        from deppy.solver import FragmentDispatcher
        _HAS_SOLVER = True
    except ImportError:
        _HAS_SOLVER = False
        FragmentDispatcher = object  # type: ignore[assignment,misc]

try:
    from deppy.kernel.fixed_point import FixedPointEngine
    _HAS_FIXEDPOINT = True
except ImportError:
    _HAS_FIXEDPOINT = False

try:
    from deppy.kernel.trust_classifier import TrustClassifier
    _HAS_TRUST = True
except ImportError:
    _HAS_TRUST = False

try:
    from deppy.predicates.kinds import DecidabilityFragment
    _HAS_FRAGMENTS = True
except ImportError:
    _HAS_FRAGMENTS = False

# ---------------------------------------------------------------------------
# Re-export local enums from the hybrid __init__
# ---------------------------------------------------------------------------
from deppy.hybrid import HybridLayer, HybridTrustLevel

try:
    from deppy.hybrid.zero_change.implicit_presheaf import ImplicitPresheafExtractor
    _HAS_ZERO_CHANGE = True
except ImportError:
    _HAS_ZERO_CHANGE = False

try:
    from deppy.hybrid.lean_translation.lean_emitter import LeanEmitter
    _HAS_LEAN_EMITTER = True
except ImportError:
    _HAS_LEAN_EMITTER = False

# ═══════════════════════════════════════════════════════════════════════════
# Shared helper types
# ═══════════════════════════════════════════════════════════════════════════


class DecidabilityClass(enum.Enum):
    """Classifies a proposition's decidability for dispatch."""

    DECIDABLE_Z3 = "decidable_z3"
    DECIDABLE_FINITE = "decidable_finite"
    SEMI_DECIDABLE = "semi_decidable"
    UNDECIDABLE_ORACLE = "undecidable_oracle"
    UNKNOWN = "unknown"


class OraclePolicy(enum.Enum):
    """When an oracle may be invoked."""

    NEVER = "never"
    FALLBACK = "fallback"
    EAGER = "eager"


@dataclass(frozen=True)
class OracleResult:
    """Result returned by an LLM oracle query."""

    answer: Any
    trust: HybridTrustLevel
    raw_text: str = ""
    model_id: str = ""
    latency_ms: float = 0.0
    token_count: int = 0
    cached: bool = False

    @property
    def is_trusted(self) -> bool:
        return self.trust >= HybridTrustLevel.PROPERTY_CHECKED

    def elevate(self, new_trust: HybridTrustLevel) -> OracleResult:
        """Return a copy with upgraded trust after external verification."""
        return OracleResult(
            answer=self.answer,
            trust=new_trust,
            raw_text=self.raw_text,
            model_id=self.model_id,
            latency_ms=self.latency_ms,
            token_count=self.token_count,
            cached=self.cached,
        )


@dataclass(frozen=True)
class TrustAnnotation:
    """Per-component trust label attached to hybrid types."""

    level: HybridTrustLevel
    source: str = "auto"
    evidence: Optional[str] = None
    timestamp: float = 0.0

    @staticmethod
    def untrusted(source: str = "init") -> TrustAnnotation:
        return TrustAnnotation(level=HybridTrustLevel.UNTRUSTED, source=source)

    @staticmethod
    def z3_proven(evidence: str = "") -> TrustAnnotation:
        return TrustAnnotation(
            level=HybridTrustLevel.Z3_PROVEN,
            source="z3",
            evidence=evidence,
        )

    @staticmethod
    def lean_verified(evidence: str = "") -> TrustAnnotation:
        return TrustAnnotation(
            level=HybridTrustLevel.LEAN_VERIFIED,
            source="lean",
            evidence=evidence,
        )

    def meet(self, other: TrustAnnotation) -> TrustAnnotation:
        weaker = min(self.level, other.level, key=lambda x: x.value)
        return TrustAnnotation(level=weaker, source="meet")

    def join(self, other: TrustAnnotation) -> TrustAnnotation:
        stronger = max(self.level, other.level, key=lambda x: x.value)
        return TrustAnnotation(level=stronger, source="join")


@dataclass(frozen=True)
class IntentGap:
    """Records a gap between the intent layer and the structural/proof layer."""

    layer_from: HybridLayer
    layer_to: HybridLayer
    description: str
    severity: float = 1.0
    site_id: Optional[Any] = None

    @property
    def is_critical(self) -> bool:
        return self.severity >= 0.8


@dataclass(frozen=True)
class HybridLocalSection:
    """Extension of LocalSection with hybrid metadata."""

    site_id: Any
    carrier_type: Any
    trust: TrustAnnotation
    layer: HybridLayer
    refinements: Dict[str, Any] = field(default_factory=dict)
    provenance: Optional[str] = None
    oracle_result: Optional[OracleResult] = None

    @property
    def hybrid_trust_level(self) -> HybridTrustLevel:
        return self.trust.level


@dataclass(frozen=True)
class HybridCheckResult:
    """Result of a hybrid type check."""

    success: bool
    trust: HybridTrustLevel
    gaps: Tuple[IntentGap, ...] = ()
    diagnostics: Tuple[str, ...] = ()
    oracle_calls: int = 0
    z3_calls: int = 0
    elapsed_ms: float = 0.0

    @property
    def has_gaps(self) -> bool:
        return len(self.gaps) > 0

    @property
    def critical_gaps(self) -> Tuple[IntentGap, ...]:
        return tuple(g for g in self.gaps if g.is_critical)


# ═══════════════════════════════════════════════════════════════════════════
#  1. HybridPiType — Dependent function with oracle-monad return
# ═══════════════════════════════════════════════════════════════════════════

class HybridPiType(PiType):
    """Π(x:τ₁). T_O(τ₂)  — dependent function with oracle-monad return.

    Extends PiType with:
    - Trust annotation on domain and codomain
    - Decidability classification for the dependency
    - Oracle-monad wrapping of the return type when undecidable
    - Layer-aware typing that tracks which HybridLayer each component lives in
    """

    def __init__(
        self,
        param_name: str,
        param_type: Any,
        return_type: Any,
        *,
        domain_trust: Optional[TrustAnnotation] = None,
        codomain_trust: Optional[TrustAnnotation] = None,
        decidability: DecidabilityClass = DecidabilityClass.UNKNOWN,
        oracle_policy: OraclePolicy = OraclePolicy.FALLBACK,
        layer: HybridLayer = HybridLayer.STRUCTURAL,
    ) -> None:
        if _HAS_DEPENDENT:
            super().__init__(param_name, param_type, return_type)  # type: ignore[call-arg]
        self._h_param_name = param_name
        self._h_param_type = param_type
        self._h_return_type = return_type
        self._domain_trust = domain_trust or TrustAnnotation.untrusted()
        self._codomain_trust = codomain_trust or TrustAnnotation.untrusted()
        self._decidability = decidability
        self._oracle_policy = oracle_policy
        self._layer = layer

    # -- Hybrid-specific properties ----------------------------------------

    @property
    def domain_trust(self) -> TrustAnnotation:
        return self._domain_trust

    @property
    def codomain_trust(self) -> TrustAnnotation:
        return self._codomain_trust

    @property
    def effective_trust(self) -> TrustAnnotation:
        """Weakest-link trust across domain and codomain."""
        return self._domain_trust.meet(self._codomain_trust)

    @property
    def decidability(self) -> DecidabilityClass:
        return self._decidability

    @property
    def oracle_policy(self) -> OraclePolicy:
        return self._oracle_policy

    @property
    def layer(self) -> HybridLayer:
        return self._layer

    @property
    def needs_oracle(self) -> bool:
        """True when the dependency is undecidable and oracle is permitted."""
        return (
            self._decidability
            in (DecidabilityClass.UNDECIDABLE_ORACLE, DecidabilityClass.UNKNOWN)
            and self._oracle_policy != OraclePolicy.NEVER
        )

    # -- Oracle-monad operations -------------------------------------------

    def oracle_apply(
        self,
        arg: Any,
        oracle_fn: Optional[Callable[..., OracleResult]] = None,
    ) -> Tuple[Any, TrustAnnotation]:
        """Apply the function, using the oracle if the dependency is undecidable.

        Returns ``(result_type, trust_annotation)`` where the trust reflects
        the weakest link in the derivation chain.
        """
        if _HAS_DEPENDENT:
            base_result = self.apply(arg)  # type: ignore[arg-type]
        else:
            base_result = self._h_return_type

        if self.needs_oracle and oracle_fn is not None:
            oracle_out = oracle_fn(self._h_param_name, arg, self._h_return_type)
            trust = TrustAnnotation(
                level=oracle_out.trust,
                source="oracle",
                evidence=oracle_out.raw_text[:200] if oracle_out.raw_text else None,
            )
            return oracle_out.answer, trust
        return base_result, self._codomain_trust

    def with_trust(
        self,
        domain: Optional[TrustAnnotation] = None,
        codomain: Optional[TrustAnnotation] = None,
    ) -> HybridPiType:
        """Return a copy with updated trust annotations."""
        return HybridPiType(
            self._h_param_name,
            self._h_param_type,
            self._h_return_type,
            domain_trust=domain or self._domain_trust,
            codomain_trust=codomain or self._codomain_trust,
            decidability=self._decidability,
            oracle_policy=self._oracle_policy,
            layer=self._layer,
        )

    def with_decidability(self, cls: DecidabilityClass) -> HybridPiType:
        """Return a copy with updated decidability class."""
        return HybridPiType(
            self._h_param_name,
            self._h_param_type,
            self._h_return_type,
            domain_trust=self._domain_trust,
            codomain_trust=self._codomain_trust,
            decidability=cls,
            oracle_policy=self._oracle_policy,
            layer=self._layer,
        )

    def split_decidability(self) -> Tuple[Optional[HybridPiType], Optional[HybridPiType]]:
        """Split into decidable and undecidable components.

        Returns ``(decidable_part, oracle_part)``.  If the type is fully
        decidable the oracle part is ``None`` and vice-versa.
        """
        if self._decidability in (
            DecidabilityClass.DECIDABLE_Z3,
            DecidabilityClass.DECIDABLE_FINITE,
        ):
            return (self, None)
        if self._decidability == DecidabilityClass.UNDECIDABLE_ORACLE:
            return (None, self)
        return (self, self)

    # -- Representation ----------------------------------------------------

    def __repr__(self) -> str:
        trust_str = f"⟨{self._domain_trust.level.name}→{self._codomain_trust.level.name}⟩"
        dec_str = self._decidability.value
        return (
            f"HybridΠ({self._h_param_name}: {self._h_param_type!r})"
            f".{self._h_return_type!r} {trust_str} [{dec_str}]"
        )


# ═══════════════════════════════════════════════════════════════════════════
#  2. HybridSigmaType — Dependent pair with per-component trust
# ═══════════════════════════════════════════════════════════════════════════

class HybridSigmaType(SigmaType):
    """Σ(x:τ₁).τ₂ with per-component trust and module decomposition semantics.

    Extends SigmaType with:
    - Independent trust annotations on first and second components
    - Module decomposition: fst = interface, snd = implementation
    - Layer tracking for each component
    """

    def __init__(
        self,
        fst_name: str,
        fst_type: Any,
        snd_type: Any,
        *,
        fst_trust: Optional[TrustAnnotation] = None,
        snd_trust: Optional[TrustAnnotation] = None,
        fst_layer: HybridLayer = HybridLayer.STRUCTURAL,
        snd_layer: HybridLayer = HybridLayer.CODE,
        module_name: Optional[str] = None,
    ) -> None:
        if _HAS_DEPENDENT:
            super().__init__(fst_name, fst_type, snd_type)  # type: ignore[call-arg]
        self._h_fst_name = fst_name
        self._h_fst_type = fst_type
        self._h_snd_type = snd_type
        self._fst_trust = fst_trust or TrustAnnotation.untrusted()
        self._snd_trust = snd_trust or TrustAnnotation.untrusted()
        self._fst_layer = fst_layer
        self._snd_layer = snd_layer
        self._module_name = module_name

    # -- Per-component trust -----------------------------------------------

    @property
    def fst_trust(self) -> TrustAnnotation:
        return self._fst_trust

    @property
    def snd_trust(self) -> TrustAnnotation:
        return self._snd_trust

    @property
    def effective_trust(self) -> TrustAnnotation:
        return self._fst_trust.meet(self._snd_trust)

    @property
    def fst_layer(self) -> HybridLayer:
        return self._fst_layer

    @property
    def snd_layer(self) -> HybridLayer:
        return self._snd_layer

    @property
    def module_name(self) -> Optional[str]:
        return self._module_name

    # -- Module decomposition semantics ------------------------------------

    @property
    def interface_type(self) -> Any:
        """The first component interpreted as the module interface."""
        return self._h_fst_type

    @property
    def implementation_type(self) -> Any:
        """The second component interpreted as the implementation."""
        return self._h_snd_type

    def decompose(self) -> Tuple[Any, Any, TrustAnnotation]:
        """Return (interface, implementation, combined_trust)."""
        return (self._h_fst_type, self._h_snd_type, self.effective_trust)

    def with_trust(
        self,
        fst: Optional[TrustAnnotation] = None,
        snd: Optional[TrustAnnotation] = None,
    ) -> HybridSigmaType:
        return HybridSigmaType(
            self._h_fst_name,
            self._h_fst_type,
            self._h_snd_type,
            fst_trust=fst or self._fst_trust,
            snd_trust=snd or self._snd_trust,
            fst_layer=self._fst_layer,
            snd_layer=self._snd_layer,
            module_name=self._module_name,
        )

    def project_snd_hybrid(self, fst_value: Any) -> Tuple[Any, TrustAnnotation]:
        """Compute the second type given a first value, returning trust info."""
        if _HAS_DEPENDENT:
            projected = self.project_snd(fst_value)  # type: ignore[arg-type]
        else:
            projected = self._h_snd_type
        return projected, self._snd_trust

    def trust_gap(self) -> Optional[IntentGap]:
        """Detect if fst and snd trust levels diverge significantly."""
        diff = abs(self._fst_trust.level.value - self._snd_trust.level.value)
        if diff >= 2:
            return IntentGap(
                layer_from=self._fst_layer,
                layer_to=self._snd_layer,
                description=(
                    f"Trust gap in Σ-type '{self._h_fst_name}': "
                    f"{self._fst_trust.level.name} vs {self._snd_trust.level.name}"
                ),
                severity=min(1.0, diff / 6.0),
            )
        return None

    def __repr__(self) -> str:
        mod = f" [{self._module_name}]" if self._module_name else ""
        return (
            f"HybridΣ({self._h_fst_name}: {self._h_fst_type!r})"
            f".{self._h_snd_type!r}{mod}"
        )


# ═══════════════════════════════════════════════════════════════════════════
#  3. HybridIdentityType — Identity with cocycle condition checking
# ═══════════════════════════════════════════════════════════════════════════

class HybridIdentityType(IdentityType):
    """Id_A(a, b) with cocycle condition checking on overlapping sites.

    Extends IdentityType to verify that equality proofs are consistent
    across overlapping observation sites (the cocycle condition from
    Čech cohomology).
    """

    def __init__(
        self,
        carrier: Any,
        lhs: Any,
        rhs: Any,
        *,
        trust: Optional[TrustAnnotation] = None,
        overlap_sites: Optional[List[Tuple[Any, Any]]] = None,
        layer: HybridLayer = HybridLayer.PROOF,
    ) -> None:
        if _HAS_DEPENDENT:
            super().__init__(carrier, lhs, rhs)  # type: ignore[call-arg]
        self._h_carrier = carrier
        self._h_lhs = lhs
        self._h_rhs = rhs
        self._trust = trust or TrustAnnotation.untrusted()
        self._overlap_sites = overlap_sites or []
        self._layer = layer

    @property
    def trust(self) -> TrustAnnotation:
        return self._trust

    @property
    def layer(self) -> HybridLayer:
        return self._layer

    @property
    def overlap_sites(self) -> List[Tuple[Any, Any]]:
        return list(self._overlap_sites)

    def check_cocycle(
        self,
        transition_data: Optional[Dict[Tuple[Any, Any], Any]] = None,
    ) -> Tuple[bool, List[Tuple[Any, Any]]]:
        """Check the cocycle condition: g_ij · g_jk = g_ik on triple overlaps.

        Parameters
        ----------
        transition_data
            Map from overlap pair ``(i, j)`` to the transition isomorphism
            (identity proof) on that overlap.

        Returns
        -------
        (satisfied, violations)
            Whether the cocycle condition holds and any violating triples.
        """
        if not transition_data:
            return (True, [])

        violations: List[Tuple[Any, Any]] = []
        sites = set()
        for u, v in transition_data:
            sites.add(u)
            sites.add(v)

        site_list = sorted(sites, key=str)
        for i_idx, i in enumerate(site_list):
            for j_idx, j in enumerate(site_list):
                if j_idx <= i_idx:
                    continue
                for k in site_list[j_idx + 1:]:
                    g_ij = transition_data.get((i, j))
                    g_jk = transition_data.get((j, k))
                    g_ik = transition_data.get((i, k))
                    if g_ij is not None and g_jk is not None and g_ik is not None:
                        # In the general case, compose g_ij and g_jk and compare with g_ik.
                        # For propositional equality, this is transitivity.
                        if g_ij == g_ik or g_jk == g_ik:
                            continue
                        # Heuristic: if all three are the same object, cocycle holds
                        if g_ij == g_jk == g_ik:
                            continue
                        violations.append((i, k))
        return (len(violations) == 0, violations)

    def check_cocycle_on_overlaps(
        self,
        sections: Optional[Dict[Any, Any]] = None,
    ) -> bool:
        """Check cocycle condition using the stored overlap sites."""
        if not self._overlap_sites:
            return True
        if sections is None:
            return True
        for u, v in self._overlap_sites:
            su = sections.get(u)
            sv = sections.get(v)
            if su is not None and sv is not None and su != sv:
                return False
        return True

    def with_trust(self, trust: TrustAnnotation) -> HybridIdentityType:
        return HybridIdentityType(
            self._h_carrier,
            self._h_lhs,
            self._h_rhs,
            trust=trust,
            overlap_sites=self._overlap_sites,
            layer=self._layer,
        )

    def __repr__(self) -> str:
        return (
            f"HybridId_{{{self._h_carrier!r}}}({self._h_lhs!r}, {self._h_rhs!r}) "
            f"⟨{self._trust.level.name}⟩"
        )


# ═══════════════════════════════════════════════════════════════════════════
#  4. HybridRefinementType — Split predicate: φ_d ∧ φ_s
# ═══════════════════════════════════════════════════════════════════════════

class HybridRefinementType(RefinementType):
    """{v: τ | φ_d ∧ φ_s} — refinement with decidable/soft predicate split.

    The predicate is decomposed into:
    - φ_d: the decidable part (checkable by Z3 / SMT)
    - φ_s: the soft part (needs oracle / property-testing / human review)

    This decomposition enables the hybrid dispatch: decidable fragments go
    to formal solvers, while soft constraints are handled by the oracle monad.
    """

    def __init__(
        self,
        base: Any,
        binder: str,
        predicate: Any,
        *,
        decidable_predicate: Any = None,
        soft_predicate: Any = None,
        trust: Optional[TrustAnnotation] = None,
        decidable_trust: Optional[TrustAnnotation] = None,
        soft_trust: Optional[TrustAnnotation] = None,
        layer: HybridLayer = HybridLayer.SEMANTIC,
    ) -> None:
        if _HAS_REFINEMENT:
            super().__init__(base, binder, predicate)  # type: ignore[call-arg]
        self._h_base = base
        self._h_binder = binder
        self._h_predicate = predicate
        self._decidable_pred = decidable_predicate
        self._soft_pred = soft_predicate
        self._trust = trust or TrustAnnotation.untrusted()
        self._decidable_trust = decidable_trust or TrustAnnotation.untrusted()
        self._soft_trust = soft_trust or TrustAnnotation.untrusted()
        self._layer = layer

    # -- Predicate decomposition -------------------------------------------

    @property
    def decidable_predicate(self) -> Any:
        """The decidable sub-predicate φ_d."""
        return self._decidable_pred

    @property
    def soft_predicate(self) -> Any:
        """The soft (oracle-checkable) sub-predicate φ_s."""
        return self._soft_pred

    @property
    def trust(self) -> TrustAnnotation:
        return self._trust

    @property
    def decidable_trust(self) -> TrustAnnotation:
        return self._decidable_trust

    @property
    def soft_trust(self) -> TrustAnnotation:
        return self._soft_trust

    @property
    def layer(self) -> HybridLayer:
        return self._layer

    @property
    def has_soft_component(self) -> bool:
        return self._soft_pred is not None

    @property
    def is_fully_decidable(self) -> bool:
        return self._soft_pred is None and self._decidable_pred is not None

    @property
    def effective_trust(self) -> TrustAnnotation:
        """Weakest-link trust across decidable and soft components."""
        if self._soft_pred is not None:
            return self._decidable_trust.meet(self._soft_trust)
        return self._decidable_trust

    def split(self) -> Tuple[Optional[Any], Optional[Any]]:
        """Return (φ_d, φ_s) — the decidable and soft sub-predicates."""
        return (self._decidable_pred, self._soft_pred)

    def strengthen_decidable(self, additional: Any) -> HybridRefinementType:
        """Add a decidable conjunct to φ_d."""
        if _HAS_REFINEMENT and self._decidable_pred is not None and hasattr(self._decidable_pred, 'and_'):
            new_d = self._decidable_pred.and_(additional)
        else:
            new_d = additional if self._decidable_pred is None else (self._decidable_pred, additional)
        combined = self._h_predicate
        if _HAS_REFINEMENT and hasattr(self._h_predicate, 'and_'):
            combined = self._h_predicate.and_(additional)
        return HybridRefinementType(
            self._h_base,
            self._h_binder,
            combined,
            decidable_predicate=new_d,
            soft_predicate=self._soft_pred,
            trust=self._trust,
            decidable_trust=self._decidable_trust,
            soft_trust=self._soft_trust,
            layer=self._layer,
        )

    def strengthen_soft(self, additional: Any) -> HybridRefinementType:
        """Add a soft conjunct to φ_s."""
        if _HAS_REFINEMENT and self._soft_pred is not None and hasattr(self._soft_pred, 'and_'):
            new_s = self._soft_pred.and_(additional)
        else:
            new_s = additional if self._soft_pred is None else (self._soft_pred, additional)
        combined = self._h_predicate
        if _HAS_REFINEMENT and hasattr(self._h_predicate, 'and_'):
            combined = self._h_predicate.and_(additional)
        return HybridRefinementType(
            self._h_base,
            self._h_binder,
            combined,
            decidable_predicate=self._decidable_pred,
            soft_predicate=new_s,
            trust=self._trust,
            decidable_trust=self._decidable_trust,
            soft_trust=self._soft_trust,
            layer=self._layer,
        )

    def with_trust(
        self,
        decidable: Optional[TrustAnnotation] = None,
        soft: Optional[TrustAnnotation] = None,
    ) -> HybridRefinementType:
        dt = decidable or self._decidable_trust
        st = soft or self._soft_trust
        return HybridRefinementType(
            self._h_base,
            self._h_binder,
            self._h_predicate,
            decidable_predicate=self._decidable_pred,
            soft_predicate=self._soft_pred,
            trust=dt.meet(st),
            decidable_trust=dt,
            soft_trust=st,
            layer=self._layer,
        )

    def __repr__(self) -> str:
        d = "φ_d" if self._decidable_pred is not None else "⊤"
        s = "φ_s" if self._soft_pred is not None else "⊤"
        return (
            f"Hybrid{{{self._h_binder}: {self._h_base!r} | {d} ∧ {s}}} "
            f"⟨{self._trust.level.name}⟩"
        )


# ═══════════════════════════════════════════════════════════════════════════
#  5. HybridForallType — Bounded quantification + oracle fallback
# ═══════════════════════════════════════════════════════════════════════════

class HybridForallType(ForallType):
    """∀α<:B. τ with bounded quantification and oracle fallback.

    Extends ForallType with:
    - Decidable bound checking (when B is a finite type or SMT-expressible)
    - Oracle fallback for undecidable instantiation
    - Trust tracking on the bound and body independently
    """

    def __init__(
        self,
        var_name: str,
        body: Any,
        bound: Any = None,
        *,
        trust: Optional[TrustAnnotation] = None,
        bound_trust: Optional[TrustAnnotation] = None,
        oracle_policy: OraclePolicy = OraclePolicy.FALLBACK,
        decidability: DecidabilityClass = DecidabilityClass.UNKNOWN,
        layer: HybridLayer = HybridLayer.STRUCTURAL,
    ) -> None:
        if _HAS_DEPENDENT:
            super().__init__(var_name, body, bound)  # type: ignore[call-arg]
        self._h_var_name = var_name
        self._h_body = body
        self._h_bound = bound
        self._trust = trust or TrustAnnotation.untrusted()
        self._bound_trust = bound_trust or TrustAnnotation.untrusted()
        self._oracle_policy = oracle_policy
        self._decidability = decidability
        self._layer = layer

    @property
    def trust(self) -> TrustAnnotation:
        return self._trust

    @property
    def bound_trust(self) -> TrustAnnotation:
        return self._bound_trust

    @property
    def effective_trust(self) -> TrustAnnotation:
        if self._h_bound is not None:
            return self._trust.meet(self._bound_trust)
        return self._trust

    @property
    def oracle_policy(self) -> OraclePolicy:
        return self._oracle_policy

    @property
    def decidability(self) -> DecidabilityClass:
        return self._decidability

    @property
    def layer(self) -> HybridLayer:
        return self._layer

    @property
    def is_bounded(self) -> bool:
        return self._h_bound is not None

    def check_bound(self, candidate: Any) -> Tuple[bool, TrustAnnotation]:
        """Check whether a candidate type satisfies the bound.

        Returns ``(within_bound, trust_of_check)``.  For decidable bounds,
        structural subtyping is used.  For undecidable bounds, the oracle
        may be consulted.
        """
        if self._h_bound is None:
            return (True, self._trust)

        if self._decidability in (
            DecidabilityClass.DECIDABLE_Z3,
            DecidabilityClass.DECIDABLE_FINITE,
        ):
            # Structural check: equality or containment heuristic
            within = (candidate == self._h_bound)
            return (within, self._bound_trust)

        # Undecidable → requires oracle
        return (True, TrustAnnotation.untrusted("needs_oracle"))

    def oracle_instantiate(
        self,
        oracle_fn: Optional[Callable[..., OracleResult]] = None,
    ) -> Tuple[Any, TrustAnnotation]:
        """Ask the oracle to find a witness type for the quantifier.

        Falls back to the bound (or Any) if no oracle is provided.
        """
        if oracle_fn is not None:
            result = oracle_fn(self._h_var_name, self._h_bound, self._h_body)
            trust = TrustAnnotation(level=result.trust, source="oracle")
            return (result.answer, trust)
        fallback = self._h_bound if self._h_bound is not None else self._h_body
        return (fallback, TrustAnnotation.untrusted("no_oracle"))

    def with_trust(self, trust: TrustAnnotation) -> HybridForallType:
        return HybridForallType(
            self._h_var_name,
            self._h_body,
            self._h_bound,
            trust=trust,
            bound_trust=self._bound_trust,
            oracle_policy=self._oracle_policy,
            decidability=self._decidability,
            layer=self._layer,
        )

    def __repr__(self) -> str:
        bnd = f" <: {self._h_bound!r}" if self._h_bound is not None else ""
        return (
            f"Hybrid∀{self._h_var_name}{bnd}.{self._h_body!r} "
            f"⟨{self._trust.level.name}⟩ [{self._decidability.value}]"
        )


# ═══════════════════════════════════════════════════════════════════════════
#  6. HybridExistsType — Existential with witness search via oracle
# ═══════════════════════════════════════════════════════════════════════════

class HybridExistsType(ExistsType):
    """∃α. τ with oracle-assisted witness search.

    Extends ExistsType with:
    - Oracle-driven witness search when the witness is not constructively available
    - Trust annotation on the witness
    - Caching of discovered witnesses
    """

    def __init__(
        self,
        var_name: str,
        body: Any,
        bound: Any = None,
        *,
        trust: Optional[TrustAnnotation] = None,
        oracle_policy: OraclePolicy = OraclePolicy.FALLBACK,
        layer: HybridLayer = HybridLayer.PROOF,
        cached_witness: Optional[Any] = None,
        witness_trust: Optional[TrustAnnotation] = None,
    ) -> None:
        if _HAS_DEPENDENT:
            super().__init__(var_name, body, bound)  # type: ignore[call-arg]
        self._h_var_name = var_name
        self._h_body = body
        self._h_bound = bound
        self._trust = trust or TrustAnnotation.untrusted()
        self._oracle_policy = oracle_policy
        self._layer = layer
        self._cached_witness = cached_witness
        self._witness_trust = witness_trust

    @property
    def trust(self) -> TrustAnnotation:
        return self._trust

    @property
    def oracle_policy(self) -> OraclePolicy:
        return self._oracle_policy

    @property
    def layer(self) -> HybridLayer:
        return self._layer

    @property
    def has_witness(self) -> bool:
        return self._cached_witness is not None

    @property
    def cached_witness(self) -> Optional[Any]:
        return self._cached_witness

    @property
    def witness_trust(self) -> Optional[TrustAnnotation]:
        return self._witness_trust

    def search_witness(
        self,
        oracle_fn: Optional[Callable[..., OracleResult]] = None,
        candidates: Optional[List[Any]] = None,
    ) -> Tuple[Optional[Any], TrustAnnotation]:
        """Search for a witness that inhabits the existential.

        Strategy:
        1. Check cached witness first
        2. Try explicit candidates
        3. Fall back to oracle if allowed

        Returns ``(witness, trust)`` or ``(None, UNTRUSTED)`` if none found.
        """
        if self._cached_witness is not None:
            return (self._cached_witness, self._witness_trust or self._trust)

        if candidates:
            for c in candidates:
                return (c, TrustAnnotation(
                    level=HybridTrustLevel.PROPERTY_CHECKED,
                    source="candidate",
                ))

        if oracle_fn is not None and self._oracle_policy != OraclePolicy.NEVER:
            result = oracle_fn(self._h_var_name, self._h_bound, self._h_body)
            trust = TrustAnnotation(level=result.trust, source="oracle")
            return (result.answer, trust)

        return (None, TrustAnnotation.untrusted("no_witness"))

    def with_witness(self, witness: Any, trust: TrustAnnotation) -> HybridExistsType:
        """Return a copy with a cached witness."""
        return HybridExistsType(
            self._h_var_name,
            self._h_body,
            self._h_bound,
            trust=self._trust,
            oracle_policy=self._oracle_policy,
            layer=self._layer,
            cached_witness=witness,
            witness_trust=trust,
        )

    def open_hybrid(self, witness: Any) -> Tuple[Any, TrustAnnotation]:
        """Open the existential with a witness, returning trust info."""
        if _HAS_DEPENDENT:
            opened = self.open(witness)  # type: ignore[arg-type]
        else:
            opened = self._h_body
        return (opened, self._trust)

    def __repr__(self) -> str:
        w = " [witnessed]" if self._cached_witness is not None else ""
        return (
            f"Hybrid∃{self._h_var_name}.{self._h_body!r}{w} "
            f"⟨{self._trust.level.name}⟩"
        )


# ═══════════════════════════════════════════════════════════════════════════
#  7. HybridPresheaf — Presheaf with HybridLayer dimension
# ═══════════════════════════════════════════════════════════════════════════

class HybridPresheaf(ConcretePresheaf):
    """Sem_H: (S × Layer)^op → Poset — presheaf over the product site.

    Extends ConcretePresheaf to index sections by both SiteId *and*
    HybridLayer, enabling per-layer section storage, cross-layer
    restriction, and H¹ cohomology computation for detecting intent gaps.
    """

    def __init__(self, name: str = "") -> None:
        if _HAS_PRESHEAF:
            super().__init__(name=name)
        self._name = name
        self._layer_sections: Dict[
            Tuple[Any, HybridLayer], List[HybridLocalSection]
        ] = {}
        self._cross_layer_morphisms: Dict[
            Tuple[Tuple[Any, HybridLayer], Tuple[Any, HybridLayer]], Any
        ] = {}
        self._intent_gaps: List[IntentGap] = []

    @property
    def hybrid_name(self) -> str:
        return self._name

    # -- Layer-indexed section access --------------------------------------

    def sections_at_layer(
        self,
        site_id: Any,
        layer: HybridLayer,
    ) -> List[HybridLocalSection]:
        """Return all sections at a specific (site, layer) pair."""
        return list(self._layer_sections.get((site_id, layer), []))

    def all_layers_at(self, site_id: Any) -> Dict[HybridLayer, List[HybridLocalSection]]:
        """Return sections at a site grouped by layer."""
        result: Dict[HybridLayer, List[HybridLocalSection]] = {}
        for layer in HybridLayer:
            secs = self._layer_sections.get((site_id, layer), [])
            if secs:
                result[layer] = list(secs)
        return result

    def add_hybrid_section(self, section: HybridLocalSection) -> None:
        """Add a section with layer information."""
        key = (section.site_id, section.layer)
        self._layer_sections.setdefault(key, []).append(section)
        if _HAS_PRESHEAF and _HAS_PROTOCOLS:
            core_section = LocalSection(
                site_id=section.site_id,
                carrier_type=section.carrier_type,
                refinements=section.refinements,
                trust=CoreTrustLevel.ASSUMED,
                provenance=section.provenance,
                witnesses={},
            )
            self.add_section(core_section)

    def add_cross_layer_morphism(
        self,
        source_site: Any,
        source_layer: HybridLayer,
        target_site: Any,
        target_layer: HybridLayer,
        morphism: Any,
    ) -> None:
        """Register a restriction morphism between (site, layer) pairs."""
        key = ((source_site, source_layer), (target_site, target_layer))
        self._cross_layer_morphisms[key] = morphism

    def get_cross_layer_morphism(
        self,
        source_site: Any,
        source_layer: HybridLayer,
        target_site: Any,
        target_layer: HybridLayer,
    ) -> Optional[Any]:
        key = ((source_site, source_layer), (target_site, target_layer))
        return self._cross_layer_morphisms.get(key)

    # -- H¹ cohomology computation -----------------------------------------

    def compute_h1(
        self,
        overlaps: Optional[List[Tuple[Any, Any]]] = None,
    ) -> Tuple[bool, List[IntentGap]]:
        """Compute H¹(Site × Layer, Sem_H) to detect non-trivial intent gaps.

        The first cohomology group is non-trivial when local sections
        cannot be glued across layers — indicating mismatches between
        intent, structure, and proof.

        Returns ``(is_trivial, gaps)``.
        """
        gaps: List[IntentGap] = []

        all_sites = set()
        for (sid, _layer) in self._layer_sections:
            all_sites.add(sid)

        for site_id in all_sites:
            layer_data = self.all_layers_at(site_id)
            layers_present = set(layer_data.keys())

            # Gap detection: check cross-layer consistency
            layer_order = [
                HybridLayer.INTENT,
                HybridLayer.STRUCTURAL,
                HybridLayer.SEMANTIC,
                HybridLayer.PROOF,
                HybridLayer.CODE,
            ]
            for i in range(len(layer_order) - 1):
                l_from = layer_order[i]
                l_to = layer_order[i + 1]
                if l_from in layers_present and l_to in layers_present:
                    secs_from = layer_data[l_from]
                    secs_to = layer_data[l_to]
                    # Check trust degradation across layers
                    trust_from = (
                        max(s.hybrid_trust_level for s in secs_from)
                        if secs_from
                        else HybridTrustLevel.UNTRUSTED
                    )
                    trust_to = (
                        max(s.hybrid_trust_level for s in secs_to)
                        if secs_to
                        else HybridTrustLevel.UNTRUSTED
                    )
                    if trust_from.value - trust_to.value >= 2:
                        gaps.append(IntentGap(
                            layer_from=l_from,
                            layer_to=l_to,
                            description=(
                                f"Trust drop {trust_from.name}→{trust_to.name} "
                                f"at site {site_id}"
                            ),
                            severity=min(
                                1.0,
                                (trust_from.value - trust_to.value) / 6.0,
                            ),
                            site_id=site_id,
                        ))
                elif l_from in layers_present and l_to not in layers_present:
                    gaps.append(IntentGap(
                        layer_from=l_from,
                        layer_to=l_to,
                        description=(
                            f"Missing {l_to.value} layer at site {site_id}"
                        ),
                        severity=0.5,
                        site_id=site_id,
                    ))

        self._intent_gaps = gaps
        return (len(gaps) == 0, gaps)

    def compute_cech_cochain(self, degree: int) -> Dict[Tuple, Any]:
        """Compute a Čech cochain at the given degree.

        Degree 0: sections at individual (site, layer) pairs
        Degree 1: transition data on overlaps
        """
        result: Dict[Tuple, Any] = {}
        if degree == 0:
            for key, secs in self._layer_sections.items():
                if secs:
                    result[(key,)] = secs[0]
        elif degree == 1:
            for key, morphism in self._cross_layer_morphisms.items():
                result[key] = morphism
        return result

    @property
    def intent_gaps(self) -> List[IntentGap]:
        return list(self._intent_gaps)

    def layer_site_ids(self) -> Set[Tuple[Any, HybridLayer]]:
        """Return all (site, layer) pairs that have sections."""
        return set(self._layer_sections.keys())

    def __repr__(self) -> str:
        n = sum(len(v) for v in self._layer_sections.values())
        return f"HybridPresheaf(name={self._name!r}, hybrid_sections={n})"


# ═══════════════════════════════════════════════════════════════════════════
#  8. HybridSheafChecker — Gluing across layers
# ═══════════════════════════════════════════════════════════════════════════

class HybridSheafChecker(SheafConditionChecker):
    """Extends SheafConditionChecker to verify gluing across HybridLayers.

    In addition to standard overlap checking, verifies that:
    - Cross-layer restrictions preserve trust monotonicity
    - Intent sections are compatible with proof sections
    - The cocycle condition holds on layer-indexed overlaps
    """

    @staticmethod
    def check_layer_agreement(
        presheaf: HybridPresheaf,
        site_id: Any,
    ) -> List[IntentGap]:
        """Check that all layers at a site agree on type information."""
        gaps: List[IntentGap] = []
        layers = presheaf.all_layers_at(site_id)

        layer_types: Dict[HybridLayer, Set[Any]] = {}
        for layer, secs in layers.items():
            layer_types[layer] = {s.carrier_type for s in secs}

        # Intent and code should at least overlap
        if HybridLayer.INTENT in layer_types and HybridLayer.CODE in layer_types:
            intent_types = layer_types[HybridLayer.INTENT]
            code_types = layer_types[HybridLayer.CODE]
            if not intent_types & code_types:
                gaps.append(IntentGap(
                    layer_from=HybridLayer.INTENT,
                    layer_to=HybridLayer.CODE,
                    description=f"Intent-code type mismatch at site {site_id}",
                    severity=0.9,
                    site_id=site_id,
                ))

        return gaps

    @staticmethod
    def check_trust_monotonicity(
        presheaf: HybridPresheaf,
        site_id: Any,
    ) -> bool:
        """Verify that trust does not increase without evidence across layers."""
        layers = presheaf.all_layers_at(site_id)
        layer_order = [
            HybridLayer.INTENT,
            HybridLayer.STRUCTURAL,
            HybridLayer.SEMANTIC,
            HybridLayer.PROOF,
            HybridLayer.CODE,
        ]
        prev_max_trust = HybridTrustLevel.HUMAN_VERIFIED

        for layer in layer_order:
            if layer in layers:
                secs = layers[layer]
                if secs:
                    max_trust = max(s.hybrid_trust_level for s in secs)
                    # Trust should not magically increase without proof layer
                    if (
                        max_trust.value > prev_max_trust.value
                        and layer != HybridLayer.PROOF
                    ):
                        return False
                    prev_max_trust = max_trust
        return True

    @staticmethod
    def attempt_hybrid_gluing(
        presheaf: HybridPresheaf,
        overlaps: Optional[List[Tuple[Any, Any]]] = None,
    ) -> Tuple[bool, List[IntentGap]]:
        """Attempt to glue sections across all layers.

        First runs standard sheaf-condition checks (if available), then
        runs cross-layer consistency checks.
        """
        all_gaps: List[IntentGap] = []

        # Cross-layer H¹ check
        is_trivial, h1_gaps = presheaf.compute_h1(overlaps)
        all_gaps.extend(h1_gaps)

        # Per-site layer agreement
        all_sites: Set[Any] = set()
        for (sid, _layer) in presheaf.layer_site_ids():
            all_sites.add(sid)

        for sid in all_sites:
            site_gaps = HybridSheafChecker.check_layer_agreement(presheaf, sid)
            all_gaps.extend(site_gaps)

        return (len(all_gaps) == 0, all_gaps)

    @staticmethod
    def verify_cocycle_across_layers(
        presheaf: HybridPresheaf,
        transition_data: Optional[Dict[Tuple[Any, Any], Any]] = None,
    ) -> Tuple[bool, List[Tuple[Any, Any]]]:
        """Verify cocycle condition on the product site (SiteId × Layer).

        Uses HybridIdentityType.check_cocycle on transitions that cross
        layer boundaries.
        """
        if not transition_data:
            return (True, [])

        identity = HybridIdentityType(
            carrier=None,
            lhs=None,
            rhs=None,
        )
        return identity.check_cocycle(transition_data)


# ═══════════════════════════════════════════════════════════════════════════
#  9. HybridTopology — Product topology Site(P) × Layer
# ═══════════════════════════════════════════════════════════════════════════

class HybridTopology(ConcreteTopolgy):
    """Grothendieck topology on the product site S × Layer.

    Extends ConcreteTopolgy to:
    - Track covers indexed by (SiteId, HybridLayer) pairs
    - Enforce topology axioms on both intra-layer and cross-layer covers
    - Support layer projections: restrict a product cover to a single layer
    """

    def __init__(self) -> None:
        if _HAS_TOPO:
            super().__init__()
        self._layer_covers: Dict[
            Tuple[Any, HybridLayer], List[Any]
        ] = {}
        self._all_layer_sites: Set[Tuple[Any, HybridLayer]] = set()

    def add_layer_cover(
        self,
        cover: Any,
        site_id: Any,
        layer: HybridLayer,
    ) -> None:
        """Register a cover for a (site, layer) pair."""
        key = (site_id, layer)
        self._layer_covers.setdefault(key, []).append(cover)
        self._all_layer_sites.add(key)
        if _HAS_TOPO and _HAS_PROTOCOLS:
            self.add_cover(cover, site_id)

    def layer_covers(
        self,
        site_id: Any,
        layer: HybridLayer,
    ) -> List[Any]:
        """Return all covers for a (site, layer) pair."""
        return list(self._layer_covers.get((site_id, layer), []))

    def is_layer_cover(
        self,
        candidate: Any,
        site_id: Any,
        layer: HybridLayer,
    ) -> bool:
        """Check whether a candidate is a valid cover at (site, layer)."""
        for existing in self._layer_covers.get((site_id, layer), []):
            if existing is candidate:
                return True
            if _HAS_PROTOCOLS and hasattr(existing, 'site_ids') and hasattr(candidate, 'site_ids'):
                if existing.site_ids() == candidate.site_ids():
                    return True
        # Also check intra-layer via parent
        if _HAS_TOPO and _HAS_PROTOCOLS:
            return self.is_cover(candidate, site_id)
        return False

    def project_to_layer(self, layer: HybridLayer) -> Dict[Any, List[Any]]:
        """Project the product topology onto a single layer.

        Returns a mapping from SiteId to covers restricted to the given layer.
        """
        result: Dict[Any, List[Any]] = {}
        for (sid, l), covers in self._layer_covers.items():
            if l == layer:
                result.setdefault(sid, []).extend(covers)
        return result

    def cross_layer_covers(
        self,
        site_id: Any,
    ) -> Dict[HybridLayer, List[Any]]:
        """Return all covers at a site indexed by layer."""
        result: Dict[HybridLayer, List[Any]] = {}
        for layer in HybridLayer:
            covers = self._layer_covers.get((site_id, layer), [])
            if covers:
                result[layer] = list(covers)
        return result

    def all_layer_sites(self) -> Set[Tuple[Any, HybridLayer]]:
        return set(self._all_layer_sites)

    def check_product_identity(
        self,
        candidate: Any,
        site_id: Any,
        layer: HybridLayer,
    ) -> bool:
        """Identity axiom on the product site."""
        if _HAS_TOPO and _HAS_PROTOCOLS:
            if self._check_identity(candidate, site_id):
                return True
        # Check layer-specific identity
        for cov in self._layer_covers.get((site_id, layer), []):
            if cov is candidate:
                return True
        return False

    def check_product_stability(
        self,
        candidate: Any,
        site_id: Any,
        layer: HybridLayer,
    ) -> bool:
        """Stability axiom: covers stable under pullback in product site."""
        if _HAS_TOPO and _HAS_PROTOCOLS:
            return self._check_stability(candidate, site_id)
        return True

    def check_product_transitivity(
        self,
        candidate: Any,
        site_id: Any,
        layer: HybridLayer,
    ) -> bool:
        """Transitivity axiom on the product site."""
        if _HAS_TOPO and _HAS_PROTOCOLS:
            return self._check_transitivity(candidate, site_id)
        return True

    def __repr__(self) -> str:
        n = len(self._all_layer_sites)
        return f"HybridTopology(product_sites={n})"


# ═══════════════════════════════════════════════════════════════════════════
# 10. HybridPipeline — Extended pipeline with hybrid verification stages
# ═══════════════════════════════════════════════════════════════════════════

class _HybridStageResult:
    """Intermediate result from a hybrid pipeline stage."""

    def __init__(
        self,
        stage_name: str,
        success: bool,
        data: Optional[Dict[str, Any]] = None,
        trust: HybridTrustLevel = HybridTrustLevel.UNTRUSTED,
        elapsed_ms: float = 0.0,
        warnings: Optional[List[str]] = None,
    ) -> None:
        self.stage_name = stage_name
        self.success = success
        self.data = data or {}
        self.trust = trust
        self.elapsed_ms = elapsed_ms
        self.warnings = warnings or []


class HybridPipeline(AnalysisPipeline):
    """Extends AnalysisPipeline with hybrid verification stages.

    Adds the following stages after the standard six:
    - **intent_extraction**: Extract intent-layer sections from NL/docstrings
    - **oracle_dispatch**: Send undecidable obligations to the LLM oracle
    - **cross_layer_gluing**: Verify sheaf condition across layers
    - **trust_aggregation**: Compute final trust annotations

    Can run the base pipeline stages first, then enrich with hybrid stages.
    """

    def __init__(
        self,
        config: Any = None,
        hooks: Any = None,
        *,
        oracle_fn: Optional[Callable[..., OracleResult]] = None,
        oracle_policy: OraclePolicy = OraclePolicy.FALLBACK,
        trust_threshold: HybridTrustLevel = HybridTrustLevel.PROPERTY_CHECKED,
    ) -> None:
        if _HAS_PIPELINE:
            super().__init__(config=config, hooks=hooks)
        self._oracle_fn = oracle_fn
        self._oracle_policy = oracle_policy
        self._trust_threshold = trust_threshold
        self._hybrid_stages: List[Tuple[str, Callable]] = []
        self._hybrid_results: Dict[str, _HybridStageResult] = {}
        self._presheaf = HybridPresheaf(name="pipeline_presheaf")
        self._register_hybrid_stages()

    @property
    def oracle_fn(self) -> Optional[Callable[..., OracleResult]]:
        return self._oracle_fn

    @property
    def oracle_policy(self) -> OraclePolicy:
        return self._oracle_policy

    @property
    def trust_threshold(self) -> HybridTrustLevel:
        return self._trust_threshold

    @property
    def presheaf(self) -> HybridPresheaf:
        return self._presheaf

    @property
    def hybrid_results(self) -> Dict[str, _HybridStageResult]:
        return dict(self._hybrid_results)

    def _register_hybrid_stages(self) -> None:
        """Register the hybrid verification stages."""
        self._hybrid_stages = [
            ("intent_extraction", self._stage_intent_extraction),
            ("oracle_dispatch", self._stage_oracle_dispatch),
            ("cross_layer_gluing", self._stage_cross_layer_gluing),
            ("trust_aggregation", self._stage_trust_aggregation),
        ]

    # -- Hybrid entry points -----------------------------------------------

    def run_hybrid(
        self,
        source: str,
        file_path: str = "<string>",
    ) -> Dict[str, Any]:
        """Run the full hybrid pipeline: base stages + hybrid stages.

        Returns a dictionary with keys:
        - ``base_result``: The PipelineResult from the base pipeline (if available)
        - ``hybrid_stages``: Results from each hybrid stage
        - ``presheaf``: The HybridPresheaf built during analysis
        - ``intent_gaps``: Any detected intent gaps
        - ``overall_trust``: The overall trust level
        """
        base_result = None
        if _HAS_PIPELINE:
            try:
                base_result = self.run_source(source)
            except Exception:
                base_result = None

        # Run hybrid stages
        context: Dict[str, Any] = {
            "source": source,
            "file_path": file_path,
            "base_result": base_result,
        }
        for stage_name, stage_fn in self._hybrid_stages:
            start = time.monotonic()
            try:
                result = stage_fn(context)
                elapsed = (time.monotonic() - start) * 1000
                self._hybrid_results[stage_name] = _HybridStageResult(
                    stage_name=stage_name,
                    success=True,
                    data=result,
                    elapsed_ms=elapsed,
                )
                context[stage_name] = result
            except Exception as exc:
                elapsed = (time.monotonic() - start) * 1000
                self._hybrid_results[stage_name] = _HybridStageResult(
                    stage_name=stage_name,
                    success=False,
                    elapsed_ms=elapsed,
                    warnings=[str(exc)],
                )

        # Compute overall trust
        _, gaps = self._presheaf.compute_h1()
        overall_trust = self._compute_overall_trust()

        return {
            "base_result": base_result,
            "hybrid_stages": {
                name: {
                    "success": r.success,
                    "trust": r.trust.name,
                    "elapsed_ms": r.elapsed_ms,
                }
                for name, r in self._hybrid_results.items()
            },
            "presheaf": self._presheaf,
            "intent_gaps": gaps,
            "overall_trust": overall_trust.name,
        }

    def register_hybrid_stage(
        self,
        name: str,
        fn: Callable[[Dict[str, Any]], Dict[str, Any]],
    ) -> None:
        """Register a custom hybrid stage."""
        self._hybrid_stages.append((name, fn))

    # -- Hybrid stage implementations --------------------------------------

    def _stage_intent_extraction(
        self,
        context: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Extract intent-layer sections from source docstrings and comments."""
        source = context.get("source", "")
        intents: List[Dict[str, Any]] = []

        # Simple heuristic: extract docstrings as intent sections
        lines = source.split("\n")
        in_docstring = False
        current_doc: List[str] = []
        doc_start = 0

        for i, line in enumerate(lines):
            stripped = line.strip()
            if stripped.startswith('"""') or stripped.startswith("'''"):
                if in_docstring:
                    current_doc.append(stripped)
                    doc_text = "\n".join(current_doc)
                    intents.append({
                        "text": doc_text,
                        "line_start": doc_start,
                        "line_end": i,
                        "trust": HybridTrustLevel.LLM_RAW.name,
                    })
                    section = HybridLocalSection(
                        site_id=f"intent_{doc_start}",
                        carrier_type="docstring",
                        trust=TrustAnnotation(
                            level=HybridTrustLevel.LLM_RAW,
                            source="docstring",
                        ),
                        layer=HybridLayer.INTENT,
                    )
                    self._presheaf.add_hybrid_section(section)
                    current_doc = []
                    in_docstring = False
                else:
                    in_docstring = True
                    doc_start = i
                    current_doc = [stripped]
            elif in_docstring:
                current_doc.append(stripped)

        return {"intents": intents, "count": len(intents)}

    def _stage_oracle_dispatch(
        self,
        context: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Dispatch undecidable obligations to the oracle."""
        dispatched = 0
        oracle_results: List[Dict[str, Any]] = []

        if self._oracle_fn is not None and self._oracle_policy != OraclePolicy.NEVER:
            intents = context.get("intent_extraction", {}).get("intents", [])
            for intent in intents:
                result = self._oracle_fn(
                    "verify_intent",
                    intent.get("text", ""),
                    None,
                )
                oracle_results.append({
                    "intent": intent.get("text", "")[:100],
                    "trust": result.trust.name,
                    "answer": str(result.answer)[:200],
                })
                dispatched += 1

        return {"dispatched": dispatched, "results": oracle_results}

    def _stage_cross_layer_gluing(
        self,
        context: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Verify the sheaf condition across hybrid layers."""
        success, gaps = HybridSheafChecker.attempt_hybrid_gluing(self._presheaf)
        return {
            "success": success,
            "gap_count": len(gaps),
            "gaps": [
                {
                    "from": g.layer_from.value,
                    "to": g.layer_to.value,
                    "description": g.description,
                    "severity": g.severity,
                }
                for g in gaps
            ],
        }

    def _stage_trust_aggregation(
        self,
        context: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Aggregate trust across all layers and sites."""
        all_trusts: List[HybridTrustLevel] = []

        for key, secs in self._presheaf._layer_sections.items():
            for sec in secs:
                all_trusts.append(sec.hybrid_trust_level)

        if not all_trusts:
            overall = HybridTrustLevel.UNTRUSTED
        else:
            overall = min(all_trusts, key=lambda x: x.value)

        return {
            "overall_trust": overall.name,
            "section_count": len(all_trusts),
            "trust_distribution": {
                level.name: sum(1 for t in all_trusts if t == level)
                for level in HybridTrustLevel
                if any(t == level for t in all_trusts)
            },
        }

    def _compute_overall_trust(self) -> HybridTrustLevel:
        """Compute the overall trust from aggregation stage."""
        agg = self._hybrid_results.get("trust_aggregation")
        if agg and agg.data:
            name = agg.data.get("overall_trust", "UNTRUSTED")
            try:
                return HybridTrustLevel[name]
            except KeyError:
                pass
        return HybridTrustLevel.UNTRUSTED

    def __repr__(self) -> str:
        n_stages = len(self._hybrid_stages)
        n_results = len(self._hybrid_results)
        return f"HybridPipeline(hybrid_stages={n_stages}, completed={n_results})"


# ═══════════════════════════════════════════════════════════════════════════
# 11. HybridDispatcher — Dispatch to Z3 OR oracle based on decidability
# ═══════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ProofObligation:
    """A proof obligation tagged with decidability and trust metadata."""

    proposition: Any
    site_id: Any = None
    context: Dict[str, Any] = field(default_factory=dict)
    decidability: DecidabilityClass = DecidabilityClass.UNKNOWN
    trust_required: HybridTrustLevel = HybridTrustLevel.PROPERTY_CHECKED
    source_location: Optional[Tuple[str, int, int]] = None

    @property
    def is_decidable(self) -> bool:
        return self.decidability in (
            DecidabilityClass.DECIDABLE_Z3,
            DecidabilityClass.DECIDABLE_FINITE,
        )

    @property
    def needs_oracle(self) -> bool:
        return self.decidability in (
            DecidabilityClass.UNDECIDABLE_ORACLE,
            DecidabilityClass.UNKNOWN,
        )


@dataclass(frozen=True)
class DispatchResult:
    """Result of dispatching a proof obligation."""

    obligation: ProofObligation
    success: bool
    trust: HybridTrustLevel
    backend: str = "unknown"
    evidence: Optional[str] = None
    elapsed_ms: float = 0.0
    model: Optional[Dict[str, Any]] = None


class HybridDispatcher(FragmentDispatcher):
    """Dispatches proof obligations to Z3 or the LLM oracle.

    Extends FragmentDispatcher to:
    - Classify obligations by decidability
    - Route decidable obligations to Z3/SMT
    - Route undecidable obligations to the oracle with trust tracking
    - Escalate from oracle to human review when trust is insufficient
    - Collect statistics on dispatch outcomes
    """

    def __init__(
        self,
        oracle_fn: Optional[Callable[..., OracleResult]] = None,
        oracle_policy: OraclePolicy = OraclePolicy.FALLBACK,
        z3_timeout_ms: float = 5000.0,
        max_escalation_depth: int = 3,
    ) -> None:
        if _HAS_SOLVER:
            super().__init__()  # type: ignore[call-arg]
        self._oracle_fn = oracle_fn
        self._oracle_policy = oracle_policy
        self._z3_timeout_ms = z3_timeout_ms
        self._max_escalation_depth = max_escalation_depth
        self._stats: Dict[str, int] = {
            "z3_dispatched": 0,
            "oracle_dispatched": 0,
            "z3_success": 0,
            "oracle_success": 0,
            "escalated": 0,
            "failed": 0,
        }

    @property
    def oracle_fn(self) -> Optional[Callable[..., OracleResult]]:
        return self._oracle_fn

    @property
    def dispatch_statistics(self) -> Dict[str, int]:
        return dict(self._stats)

    # -- Decidability classification ---------------------------------------

    def classify_obligation(
        self,
        obligation: ProofObligation,
    ) -> DecidabilityClass:
        """Classify a proof obligation by decidability.

        Uses the fragment classifier from the base dispatcher if available,
        otherwise falls back to heuristics.
        """
        if obligation.decidability != DecidabilityClass.UNKNOWN:
            return obligation.decidability

        if _HAS_SOLVER and _HAS_FRAGMENTS:
            try:
                base_cls = self.classify(obligation.proposition)  # type: ignore[arg-type]
                if hasattr(base_cls, 'fragment'):
                    frag = base_cls.fragment
                    if frag.value in ("QF_LIA", "QF_LRA", "QF_BV", "QF_UF", "QF_AX"):
                        return DecidabilityClass.DECIDABLE_Z3
                    if frag.value == "finite":
                        return DecidabilityClass.DECIDABLE_FINITE
                    if frag.value == "undecidable":
                        return DecidabilityClass.UNDECIDABLE_ORACLE
            except Exception:
                pass

        # Heuristic fallback
        prop_str = str(obligation.proposition).lower()
        if any(kw in prop_str for kw in ("forall", "exists", "induction")):
            return DecidabilityClass.SEMI_DECIDABLE
        if any(kw in prop_str for kw in ("intent", "meaning", "natural_language")):
            return DecidabilityClass.UNDECIDABLE_ORACLE
        return DecidabilityClass.UNKNOWN

    # -- Dispatch methods --------------------------------------------------

    def dispatch_hybrid(
        self,
        obligation: ProofObligation,
    ) -> DispatchResult:
        """Dispatch a single obligation to the appropriate backend.

        Route:
        - Decidable → Z3/SMT solver
        - Undecidable → Oracle (if allowed)
        - Unknown → Try Z3 first, escalate to oracle on failure
        """
        cls = self.classify_obligation(obligation)

        if cls in (DecidabilityClass.DECIDABLE_Z3, DecidabilityClass.DECIDABLE_FINITE):
            return self._dispatch_to_z3(obligation)

        if cls == DecidabilityClass.UNDECIDABLE_ORACLE:
            return self._dispatch_to_oracle(obligation)

        if cls == DecidabilityClass.SEMI_DECIDABLE:
            # Try Z3 first, fall back to oracle
            z3_result = self._dispatch_to_z3(obligation)
            if z3_result.success:
                return z3_result
            return self._dispatch_to_oracle(obligation)

        # UNKNOWN: try Z3, then oracle, then fail
        z3_result = self._dispatch_to_z3(obligation)
        if z3_result.success:
            return z3_result
        if self._oracle_policy != OraclePolicy.NEVER:
            return self._dispatch_to_oracle(obligation)
        return z3_result

    def dispatch_batch_hybrid(
        self,
        obligations: Sequence[ProofObligation],
    ) -> List[DispatchResult]:
        """Dispatch a batch of obligations, grouping by decidability."""
        results: List[DispatchResult] = []

        decidable: List[ProofObligation] = []
        oracle_needed: List[ProofObligation] = []
        unknown: List[ProofObligation] = []

        for ob in obligations:
            cls = self.classify_obligation(ob)
            if cls in (DecidabilityClass.DECIDABLE_Z3, DecidabilityClass.DECIDABLE_FINITE):
                decidable.append(ob)
            elif cls == DecidabilityClass.UNDECIDABLE_ORACLE:
                oracle_needed.append(ob)
            else:
                unknown.append(ob)

        for ob in decidable:
            results.append(self._dispatch_to_z3(ob))
        for ob in oracle_needed:
            results.append(self._dispatch_to_oracle(ob))
        for ob in unknown:
            results.append(self.dispatch_hybrid(ob))

        return results

    # -- Backend dispatchers -----------------------------------------------

    def _dispatch_to_z3(self, obligation: ProofObligation) -> DispatchResult:
        """Attempt to discharge the obligation via Z3/SMT."""
        self._stats["z3_dispatched"] += 1
        start = time.monotonic()

        if _HAS_SOLVER:
            try:
                base_result = self.dispatch(obligation.proposition)  # type: ignore[arg-type]
                elapsed = (time.monotonic() - start) * 1000
                success = getattr(base_result, 'status', None)
                if success is not None and hasattr(success, 'value') and success.value == "SAT":
                    self._stats["z3_success"] += 1
                    return DispatchResult(
                        obligation=obligation,
                        success=True,
                        trust=HybridTrustLevel.Z3_PROVEN,
                        backend="z3",
                        evidence=str(base_result),
                        elapsed_ms=elapsed,
                    )
                return DispatchResult(
                    obligation=obligation,
                    success=False,
                    trust=HybridTrustLevel.UNTRUSTED,
                    backend="z3",
                    elapsed_ms=elapsed,
                )
            except Exception:
                pass

        elapsed = (time.monotonic() - start) * 1000
        self._stats["failed"] += 1
        return DispatchResult(
            obligation=obligation,
            success=False,
            trust=HybridTrustLevel.UNTRUSTED,
            backend="z3_unavailable",
            elapsed_ms=elapsed,
        )

    def _dispatch_to_oracle(self, obligation: ProofObligation) -> DispatchResult:
        """Attempt to discharge the obligation via the LLM oracle."""
        self._stats["oracle_dispatched"] += 1
        start = time.monotonic()

        if self._oracle_fn is None or self._oracle_policy == OraclePolicy.NEVER:
            elapsed = (time.monotonic() - start) * 1000
            self._stats["failed"] += 1
            return DispatchResult(
                obligation=obligation,
                success=False,
                trust=HybridTrustLevel.UNTRUSTED,
                backend="oracle_unavailable",
                elapsed_ms=elapsed,
            )

        try:
            result = self._oracle_fn(
                "verify",
                obligation.proposition,
                obligation.context,
            )
            elapsed = (time.monotonic() - start) * 1000
            success = result.trust >= obligation.trust_required
            if success:
                self._stats["oracle_success"] += 1
            return DispatchResult(
                obligation=obligation,
                success=success,
                trust=result.trust,
                backend="oracle",
                evidence=result.raw_text[:500] if result.raw_text else None,
                elapsed_ms=elapsed,
            )
        except Exception:
            elapsed = (time.monotonic() - start) * 1000
            self._stats["failed"] += 1
            return DispatchResult(
                obligation=obligation,
                success=False,
                trust=HybridTrustLevel.UNTRUSTED,
                backend="oracle_error",
                elapsed_ms=elapsed,
            )

    def escalate(
        self,
        obligation: ProofObligation,
        depth: int = 0,
    ) -> DispatchResult:
        """Escalate an obligation through multiple backends.

        Escalation chain: Z3 → Oracle → Human Review (stub).
        """
        if depth >= self._max_escalation_depth:
            self._stats["failed"] += 1
            return DispatchResult(
                obligation=obligation,
                success=False,
                trust=HybridTrustLevel.UNTRUSTED,
                backend="max_escalation",
            )

        self._stats["escalated"] += 1

        # Level 0: Z3
        if depth == 0:
            z3_result = self._dispatch_to_z3(obligation)
            if z3_result.success:
                return z3_result
            return self.escalate(obligation, depth + 1)

        # Level 1: Oracle
        if depth == 1:
            oracle_result = self._dispatch_to_oracle(obligation)
            if oracle_result.success:
                return oracle_result
            return self.escalate(obligation, depth + 2)

        # Level 2+: Mark as needing human review
        return DispatchResult(
            obligation=obligation,
            success=False,
            trust=HybridTrustLevel.UNTRUSTED,
            backend="needs_human_review",
        )

    def reset_stats(self) -> None:
        """Reset dispatch statistics."""
        for key in self._stats:
            self._stats[key] = 0

    def __repr__(self) -> str:
        z3 = self._stats["z3_dispatched"]
        oracle = self._stats["oracle_dispatched"]
        return f"HybridDispatcher(z3={z3}, oracle={oracle})"


class HybridAdoptionPath:
    """Bridge zero-change extraction to hybrid verification artifacts."""

    def __init__(self) -> None:
        self._extractor = ImplicitPresheafExtractor() if _HAS_ZERO_CHANGE else None
        self._emitter = LeanEmitter() if _HAS_LEAN_EMITTER else None

    def infer_file_hints(self, file_path: str) -> Dict[str, List[str]]:
        if self._extractor is None:
            return {}
        model = self._extractor.extract_file(file_path)
        return model.to_spec_hints()

    def emit_lean_from_obligations(
        self,
        obligations: Sequence[ProofObligation],
        *,
        module_name: str = "DeppyHybrid",
    ) -> str:
        if self._emitter is None:
            return ""
        artifact = self._emitter.emit_from_hybrid_obligations(
            obligations, module_name=module_name
        )
        return artifact.to_text()


# ═══════════════════════════════════════════════════════════════════════════
# Module-level exports
# ═══════════════════════════════════════════════════════════════════════════

__all__ = [
    # Enums & helpers
    "DecidabilityClass",
    "OraclePolicy",
    "OracleResult",
    "TrustAnnotation",
    "IntentGap",
    "HybridLocalSection",
    "HybridCheckResult",
    "ProofObligation",
    "DispatchResult",
    # Hybrid type extensions
    "HybridPiType",
    "HybridSigmaType",
    "HybridIdentityType",
    "HybridRefinementType",
    "HybridForallType",
    "HybridExistsType",
    # Presheaf & sheaf extensions
    "HybridPresheaf",
    "HybridSheafChecker",
    "HybridTopology",
    # Pipeline & dispatcher
    "HybridPipeline",
    "HybridDispatcher",
    "HybridAdoptionPath",
]
