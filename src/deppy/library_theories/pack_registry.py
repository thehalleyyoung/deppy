"""Registry for theory packs in the sheaf-descent semantic typing system.

The PackRegistry maintains a mapping from site kinds to theory packs,
enabling the system to dispatch site-level operations to the appropriate
domain-specific theory. It supports:
  - Registering packs by name
  - Looking up packs by site kind
  - Composing multiple packs for sites that span theory boundaries
  - A default registry pre-populated with all 12 theory families
"""

from __future__ import annotations

import threading
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Type,
)

from deppy.core._protocols import (
    Cover,
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
)


# ═══════════════════════════════════════════════════════════════════════════════
# Composed pack
# ═══════════════════════════════════════════════════════════════════════════════


class ComposedPack(TheoryPackBase):
    """A theory pack composed from multiple delegate packs.

    Routes each operation to the appropriate delegate based on the
    site kind of the section or site being operated upon.
    """

    pack_name = "composed"
    pack_priority = 50

    def __init__(self, delegates: Sequence[TheoryPackBase]) -> None:
        super().__init__()
        self._delegates: List[TheoryPackBase] = sorted(
            delegates, key=lambda p: p.pack_priority
        )
        self._kind_to_pack: Dict[SiteKind, TheoryPackBase] = {}
        for pack in self._delegates:
            for kind in pack.applicable_site_kinds():
                if kind not in self._kind_to_pack:
                    self._kind_to_pack[kind] = pack
                else:
                    existing = self._kind_to_pack[kind]
                    if pack.pack_priority < existing.pack_priority:
                        self._kind_to_pack[kind] = pack
        all_kinds: Set[SiteKind] = set()
        for pack in self._delegates:
            all_kinds |= pack.applicable_site_kinds()
        self._all_kinds = frozenset(all_kinds)

    def applicable_site_kinds(self) -> FrozenSet[SiteKind]:
        return self._all_kinds

    def _get_delegate(self, site_id: SiteId) -> Optional[TheoryPackBase]:
        """Find the delegate pack for a site."""
        return self._kind_to_pack.get(site_id.kind)

    def _get_delegate_for_kind(self, kind: SiteKind) -> Optional[TheoryPackBase]:
        """Find the delegate pack for a site kind."""
        return self._kind_to_pack.get(kind)

    def solve_local(self, site: SiteId, section: LocalSection) -> SolverResult:
        delegate = self._get_delegate(site)
        if delegate is None:
            return SolverResult(
                status=SolverStatus.UNKNOWN,
                section=section,
                explanation=f"no delegate for site kind {site.kind.value}",
            )
        return delegate.solve_local(site, section)

    def forward_refine(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        source_delegate = self._get_delegate(morphism.source)
        target_delegate = self._get_delegate(morphism.target)
        delegate = source_delegate or target_delegate
        if delegate is None:
            return self.identity_forward(section, morphism)
        return delegate.forward_refine(section, morphism)

    def backward_pullback(
        self, section: LocalSection, morphism: ConcreteMorphism
    ) -> LocalSection:
        target_delegate = self._get_delegate(morphism.target)
        source_delegate = self._get_delegate(morphism.source)
        delegate = target_delegate or source_delegate
        if delegate is None:
            return self.identity_backward(section, morphism)
        return delegate.backward_pullback(section, morphism)

    def viability_predicate(self, error_site: SiteId) -> str:
        delegate = self._get_delegate(error_site)
        if delegate is None:
            return f"unknown viability for {error_site}"
        return delegate.viability_predicate(error_site)

    def classify_proof_boundary(self, section: LocalSection) -> BoundaryClassification:
        delegate = self._get_delegate(section.site_id)
        if delegate is None:
            return BoundaryClassification.ASSUMED
        return delegate.classify_proof_boundary(section)

    @property
    def delegates(self) -> List[TheoryPackBase]:
        """Return the list of delegate packs in priority order."""
        return list(self._delegates)

    def get_pack_for_kind(self, kind: SiteKind) -> Optional[TheoryPackBase]:
        """Get the delegate handling a specific site kind."""
        return self._kind_to_pack.get(kind)

    def __repr__(self) -> str:
        names = ", ".join(d.pack_name for d in self._delegates)
        return f"ComposedPack([{names}])"


# ═══════════════════════════════════════════════════════════════════════════════
# Pack registry
# ═══════════════════════════════════════════════════════════════════════════════


class PackRegistryImpl:
    """Registry of theory packs, mapping site kinds to domain-specific theories.

    Thread-safe singleton that allows registering packs, looking up packs
    by site kind, and composing packs for multi-theory contexts.
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._packs: Dict[str, TheoryPackBase] = {}
        self._kind_index: Dict[SiteKind, List[TheoryPackBase]] = {}
        self._composed_cache: Dict[FrozenSet[str], ComposedPack] = {}

    def register(self, pack: TheoryPackBase) -> None:
        """Register a theory pack.

        If a pack with the same name is already registered, it is replaced.
        Clears the composition cache on mutation.
        """
        with self._lock:
            self._packs[pack.pack_name] = pack
            for kind in pack.applicable_site_kinds():
                if kind not in self._kind_index:
                    self._kind_index[kind] = []
                packs_for_kind = self._kind_index[kind]
                packs_for_kind = [p for p in packs_for_kind if p.pack_name != pack.pack_name]
                packs_for_kind.append(pack)
                packs_for_kind.sort(key=lambda p: p.pack_priority)
                self._kind_index[kind] = packs_for_kind
            self._composed_cache.clear()

    def unregister(self, pack_name: str) -> bool:
        """Remove a pack by name. Returns True if found."""
        with self._lock:
            pack = self._packs.pop(pack_name, None)
            if pack is None:
                return False
            for kind in pack.applicable_site_kinds():
                if kind in self._kind_index:
                    self._kind_index[kind] = [
                        p for p in self._kind_index[kind] if p.pack_name != pack_name
                    ]
                    if not self._kind_index[kind]:
                        del self._kind_index[kind]
            self._composed_cache.clear()
            return True

    def get_pack(self, name: str) -> Optional[TheoryPackBase]:
        """Look up a pack by name."""
        return self._packs.get(name)

    def get_pack_for_site(self, site_kind: SiteKind) -> Optional[TheoryPackBase]:
        """Get the highest-priority pack for a site kind."""
        packs = self._kind_index.get(site_kind, [])
        if not packs:
            return None
        return packs[0]

    def get_all_packs_for_site(self, site_kind: SiteKind) -> List[TheoryPackBase]:
        """Get all packs handling a site kind, in priority order."""
        return list(self._kind_index.get(site_kind, []))

    def get_all_packs(self) -> List[TheoryPackBase]:
        """Get all registered packs."""
        return list(self._packs.values())

    def get_pack_names(self) -> List[str]:
        """Get names of all registered packs."""
        return list(self._packs.keys())

    def compose_packs(self, kinds: FrozenSet[SiteKind]) -> ComposedPack:
        """Compose packs covering the given site kinds.

        Uses a cache to avoid redundant composition.
        """
        cache_key = kinds
        if cache_key in self._composed_cache:
            return self._composed_cache[cache_key]

        delegates: Dict[str, TheoryPackBase] = {}
        for kind in kinds:
            packs = self._kind_index.get(kind, [])
            for pack in packs:
                if pack.pack_name not in delegates:
                    delegates[pack.pack_name] = pack

        composed = ComposedPack(list(delegates.values()))
        with self._lock:
            self._composed_cache[cache_key] = composed
        return composed

    def compose_all(self) -> ComposedPack:
        """Compose all registered packs."""
        all_kinds: Set[SiteKind] = set()
        for kind_list in self._kind_index:
            all_kinds.add(kind_list)
        return self.compose_packs(frozenset(all_kinds))

    def compose_for_cover(self, cover: Cover) -> ComposedPack:
        """Compose packs for all site kinds present in a cover."""
        kinds: Set[SiteKind] = set()
        for site_id in cover.sites:
            kinds.add(site_id.kind)
        return self.compose_packs(frozenset(kinds))

    def has_pack_for(self, kind: SiteKind) -> bool:
        """Check if any pack handles a site kind."""
        return kind in self._kind_index and len(self._kind_index[kind]) > 0

    def covered_kinds(self) -> FrozenSet[SiteKind]:
        """Return the set of site kinds covered by registered packs."""
        return frozenset(
            k for k, v in self._kind_index.items() if v
        )

    def uncovered_kinds(self) -> FrozenSet[SiteKind]:
        """Return site kinds not covered by any registered pack."""
        all_kinds = frozenset(SiteKind)
        return all_kinds - self.covered_kinds()

    def clear(self) -> None:
        """Remove all registered packs."""
        with self._lock:
            self._packs.clear()
            self._kind_index.clear()
            self._composed_cache.clear()

    def __len__(self) -> int:
        return len(self._packs)

    def __contains__(self, name: str) -> bool:
        return name in self._packs

    def __repr__(self) -> str:
        pack_names = ", ".join(sorted(self._packs.keys()))
        return f"PackRegistry({len(self._packs)} packs: [{pack_names}])"


# ═══════════════════════════════════════════════════════════════════════════════
# Default registry factory
# ═══════════════════════════════════════════════════════════════════════════════

_global_registry: Optional[PackRegistryImpl] = None
_registry_lock = threading.Lock()


def get_default_registry() -> PackRegistryImpl:
    """Get or create the default global registry, pre-populated with all packs.

    Lazy-loads the 12 theory family packs on first access.
    """
    global _global_registry
    if _global_registry is not None:
        return _global_registry
    with _registry_lock:
        if _global_registry is not None:
            return _global_registry
        registry = PackRegistryImpl()
        _populate_default_registry(registry)
        _global_registry = registry
        return registry


def reset_default_registry() -> None:
    """Reset the global registry (mainly for testing)."""
    global _global_registry
    with _registry_lock:
        _global_registry = None


def _populate_default_registry(registry: PackRegistryImpl) -> None:
    """Lazily import and register all 12 theory family packs."""
    try:
        from .arithmetic_theory import ArithmeticTheoryPack
        registry.register(ArithmeticTheoryPack())
    except ImportError:
        pass

    try:
        from .boolean_guard_theory import BooleanGuardTheoryPack
        registry.register(BooleanGuardTheoryPack())
    except ImportError:
        pass

    try:
        from .nullability_theory import NullabilityTheoryPack
        registry.register(NullabilityTheoryPack())
    except ImportError:
        pass

    try:
        from .heap_protocol_theory import HeapProtocolTheoryPack
        registry.register(HeapProtocolTheoryPack())
    except ImportError:
        pass

    try:
        from .tensor_shape_theory import TensorShapeTheoryPack
        registry.register(TensorShapeTheoryPack())
    except ImportError:
        pass

    try:
        from .tensor_order_theory import TensorOrderTheoryPack
        registry.register(TensorOrderTheoryPack())
    except ImportError:
        pass

    try:
        from .tensor_indexing_theory import TensorIndexingTheoryPack
        registry.register(TensorIndexingTheoryPack())
    except ImportError:
        pass

    try:
        from .device_dtype_theory import DeviceDtypeTheoryPack
        registry.register(DeviceDtypeTheoryPack())
    except ImportError:
        pass

    try:
        from .sequence_collection_theory import SequenceCollectionTheoryPack
        registry.register(SequenceCollectionTheoryPack())
    except ImportError:
        pass

    try:
        from .exception_theory import ExceptionTheoryPack
        registry.register(ExceptionTheoryPack())
    except ImportError:
        pass

    try:
        from .witness_transport_theory import WitnessTransportTheoryPack
        registry.register(WitnessTransportTheoryPack())
    except ImportError:
        pass

    try:
        from .loop_invariant_theory import LoopInvariantTheoryPack
        registry.register(LoopInvariantTheoryPack())
    except ImportError:
        pass
