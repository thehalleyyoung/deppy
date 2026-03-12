"""Transport seeds: inter-site fact transportation.

A *transport seed* declares that a proposition holding at one site can
be transported to another site.  In the sheaf framework this corresponds
to a morphism between sites that preserves a specific section property.
Transport seeds are used by the descent machinery to propagate
refinement information across call boundaries.
"""

from __future__ import annotations

import copy
import enum
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.contracts.base import (
    Predicate,
    PredicateKind,
    SourceLocation,
    Term,
    TypeBase,
)
from deppy.core._protocols import TrustLevel

if TYPE_CHECKING:
    from deppy.core._protocols import SiteId


# ---------------------------------------------------------------------------
# TransportJustification
# ---------------------------------------------------------------------------


class TransportJustification(enum.Enum):
    """How a transport is justified."""

    PROOF = "proof"
    THEOREM = "theorem"
    LIBRARY = "library"
    OBSERVATION = "observation"
    ASSUMPTION = "assumption"


# Justification to trust-level mapping
_JUSTIFICATION_TRUST: Dict[TransportJustification, TrustLevel] = {
    TransportJustification.PROOF: TrustLevel.PROOF_BACKED,
    TransportJustification.THEOREM: TrustLevel.PROOF_BACKED,
    TransportJustification.LIBRARY: TrustLevel.TRUSTED_AUTO,
    TransportJustification.OBSERVATION: TrustLevel.TRACE_BACKED,
    TransportJustification.ASSUMPTION: TrustLevel.ASSUMED,
}


# ---------------------------------------------------------------------------
# TransportSeed
# ---------------------------------------------------------------------------


@dataclass
class TransportSeed:
    """Declares that a fact can be transported between sites.

    A transport seed expresses: if ``source_prop`` holds at
    ``source_site``, then ``target_prop`` holds at ``target_site``.
    This is used by the sheaf descent machinery to propagate refinement
    information across function boundaries and call chains.

    Attributes:
        source_site: Where the fact originates (None if unassigned).
        target_site: Where the fact is needed (None if unassigned).
        source_prop: Proposition at the source.
        target_prop: Proposition at the target.
        justification: How the transport is justified.
        source_location: Where in source code this was declared.
        description: Optional human-readable gloss.
    """

    source_prop: Predicate
    target_prop: Predicate
    justification: TransportJustification = TransportJustification.ASSUMPTION
    source_site: Optional[Any] = None  # Optional[SiteId]
    target_site: Optional[Any] = None  # Optional[SiteId]
    source_location: Optional[SourceLocation] = None
    description: Optional[str] = None

    @property
    def trust(self) -> TrustLevel:
        """Derive trust level from justification."""
        return _JUSTIFICATION_TRUST.get(self.justification, TrustLevel.ASSUMED)

    @property
    def is_identity(self) -> bool:
        """True if source and target propositions are the same."""
        return self.source_prop.pretty() == self.target_prop.pretty()

    @property
    def is_site_bound(self) -> bool:
        """True if both source and target sites are assigned."""
        return self.source_site is not None and self.target_site is not None

    def as_implication(self) -> Predicate:
        """View the transport as a logical implication."""
        return Predicate.implication(self.source_prop, self.target_prop)

    def reversed(self) -> TransportSeed:
        """Return the reverse transport."""
        return TransportSeed(
            source_prop=self.target_prop,
            target_prop=self.source_prop,
            justification=self.justification,
            source_site=self.target_site,
            target_site=self.source_site,
            source_location=self.source_location,
            description=f"reverse({self.description})" if self.description else None,
        )

    def chain(self, other: TransportSeed) -> TransportSeed:
        """Chain: ``self ; other``.

        The result transports from ``self.source`` to ``other.target``.
        """
        weaker = min(
            self.justification,
            other.justification,
            key=lambda j: _JUST_ORD.get(j, 0),
        )
        return TransportSeed(
            source_prop=self.source_prop,
            target_prop=other.target_prop,
            justification=weaker,
            source_site=self.source_site,
            target_site=other.target_site,
            source_location=self.source_location,
            description=f"chain({self.description or '?'}, {other.description or '?'})",
        )

    def bind_sites(
        self, source_site: Any, target_site: Any,
    ) -> TransportSeed:
        """Return a copy with sites assigned."""
        return TransportSeed(
            source_prop=self.source_prop,
            target_prop=self.target_prop,
            justification=self.justification,
            source_site=source_site,
            target_site=target_site,
            source_location=self.source_location,
            description=self.description,
        )

    def substitute(self, bindings: Dict[str, Term]) -> TransportSeed:
        """Substitute variables in both propositions."""
        return TransportSeed(
            source_prop=self.source_prop.substitute(bindings),
            target_prop=self.target_prop.substitute(bindings),
            justification=self.justification,
            source_site=self.source_site,
            target_site=self.target_site,
            source_location=self.source_location,
            description=self.description,
        )

    def pretty(self) -> str:
        src = f"@{self.source_site}" if self.source_site else "@?"
        tgt = f"@{self.target_site}" if self.target_site else "@?"
        desc = f"  # {self.description}" if self.description else ""
        return (
            f"transport {src}→{tgt} "
            f"[{self.justification.value}]: "
            f"{self.source_prop.pretty()} ⊢ {self.target_prop.pretty()}{desc}"
        )

    def __repr__(self) -> str:
        return (
            f"<TransportSeed [{self.justification.value}] "
            f"{self.source_prop.pretty()!r} → {self.target_prop.pretty()!r}>"
        )


# Justification ordering (higher = more trusted)
_JUST_ORD: Dict[TransportJustification, int] = {
    TransportJustification.ASSUMPTION: 0,
    TransportJustification.OBSERVATION: 1,
    TransportJustification.LIBRARY: 2,
    TransportJustification.THEOREM: 3,
    TransportJustification.PROOF: 4,
}


# ---------------------------------------------------------------------------
# TransportSeedBuilder (fluent API)
# ---------------------------------------------------------------------------


class TransportSeedBuilder:
    """Fluent API for building transport seeds.

    Usage::

        seed = (
            TransportSeedBuilder()
            .from_source(site_a, pred_a)
            .to_target(site_b, pred_b)
            .justified_by(TransportJustification.PROOF)
            .with_description("int embeds into float")
            .build()
        )
    """

    def __init__(self) -> None:
        self._source_site: Optional[Any] = None
        self._target_site: Optional[Any] = None
        self._source_prop: Optional[Predicate] = None
        self._target_prop: Optional[Predicate] = None
        self._justification: TransportJustification = TransportJustification.ASSUMPTION
        self._source_location: Optional[SourceLocation] = None
        self._description: Optional[str] = None

    def from_source(
        self,
        site: Optional[Any] = None,
        prop: Optional[Predicate] = None,
    ) -> TransportSeedBuilder:
        """Set the source site and proposition."""
        self._source_site = site
        if prop is not None:
            self._source_prop = prop
        return self

    def to_target(
        self,
        site: Optional[Any] = None,
        prop: Optional[Predicate] = None,
    ) -> TransportSeedBuilder:
        """Set the target site and proposition."""
        self._target_site = site
        if prop is not None:
            self._target_prop = prop
        return self

    def justified_by(self, justification: TransportJustification) -> TransportSeedBuilder:
        """Set the justification kind."""
        self._justification = justification
        return self

    def at_location(self, loc: SourceLocation) -> TransportSeedBuilder:
        """Set the source-code location."""
        self._source_location = loc
        return self

    def with_description(self, desc: str) -> TransportSeedBuilder:
        """Set a human-readable description."""
        self._description = desc
        return self

    def from_callable(
        self,
        source_fn: Callable[..., bool],
        target_fn: Callable[..., bool],
    ) -> TransportSeedBuilder:
        """Set source and target from callables."""
        self._source_prop = Predicate.from_callable(source_fn)
        self._target_prop = Predicate.from_callable(target_fn)
        return self

    def build(self) -> TransportSeed:
        """Build the TransportSeed.

        Raises ValueError if source or target proposition is missing.
        """
        if self._source_prop is None:
            raise ValueError("TransportSeedBuilder: source proposition is required")
        if self._target_prop is None:
            raise ValueError("TransportSeedBuilder: target proposition is required")

        return TransportSeed(
            source_prop=self._source_prop,
            target_prop=self._target_prop,
            justification=self._justification,
            source_site=self._source_site,
            target_site=self._target_site,
            source_location=self._source_location,
            description=self._description,
        )

    def __repr__(self) -> str:
        src = "set" if self._source_prop else "unset"
        tgt = "set" if self._target_prop else "unset"
        return f"<TransportSeedBuilder source={src} target={tgt}>"


# ---------------------------------------------------------------------------
# TransportSeedCollection
# ---------------------------------------------------------------------------


class TransportSeedCollection:
    """Collection of transport seeds with lookup and chaining utilities.

    Used by the descent machinery to accumulate all known transports
    and find paths between sites.
    """

    def __init__(self, seeds: Optional[List[TransportSeed]] = None) -> None:
        self._seeds: List[TransportSeed] = seeds if seeds is not None else []
        self._by_source_site: Dict[Any, List[TransportSeed]] = {}
        self._by_target_site: Dict[Any, List[TransportSeed]] = {}
        for s in self._seeds:
            self._index(s)

    def _index(self, seed: TransportSeed) -> None:
        if seed.source_site is not None:
            self._by_source_site.setdefault(seed.source_site, []).append(seed)
        if seed.target_site is not None:
            self._by_target_site.setdefault(seed.target_site, []).append(seed)

    def add(self, seed: TransportSeed) -> None:
        """Add a transport seed to the collection."""
        self._seeds.append(seed)
        self._index(seed)

    def add_all(self, seeds: Sequence[TransportSeed]) -> None:
        for s in seeds:
            self.add(s)

    def from_site(self, site: Any) -> List[TransportSeed]:
        """Get all transports originating from *site*."""
        return list(self._by_source_site.get(site, []))

    def to_site(self, site: Any) -> List[TransportSeed]:
        """Get all transports targeting *site*."""
        return list(self._by_target_site.get(site, []))

    def between(self, source: Any, target: Any) -> List[TransportSeed]:
        """Get direct transports from *source* to *target*."""
        candidates = self._by_source_site.get(source, [])
        return [s for s in candidates if s.target_site == target]

    def find_path(
        self, source: Any, target: Any, max_depth: int = 5,
    ) -> Optional[List[TransportSeed]]:
        """Find a chain of transports from *source* to *target*.

        Uses BFS with depth limit. Returns the chain (list of seeds) or
        None if no path exists.
        """
        if source == target:
            return []

        from collections import deque

        # BFS: queue of (current_site, path_so_far)
        queue: deque[Tuple[Any, List[TransportSeed]]] = deque()
        queue.append((source, []))
        visited: Set[Any] = {source}

        while queue:
            current, path = queue.popleft()
            if len(path) >= max_depth:
                continue

            for seed in self._by_source_site.get(current, []):
                next_site = seed.target_site
                if next_site is None:
                    continue
                new_path = path + [seed]
                if next_site == target:
                    return new_path
                if next_site not in visited:
                    visited.add(next_site)
                    queue.append((next_site, new_path))

        return None

    def chain_path(self, path: List[TransportSeed]) -> Optional[TransportSeed]:
        """Chain a sequence of transports into a single composite transport."""
        if not path:
            return None
        result = path[0]
        for step in path[1:]:
            result = result.chain(step)
        return result

    def all_seeds(self) -> List[TransportSeed]:
        return list(self._seeds)

    def filter_by_justification(
        self, *justifications: TransportJustification,
    ) -> TransportSeedCollection:
        """Return only seeds with one of the given justifications."""
        just_set = set(justifications)
        return TransportSeedCollection([s for s in self._seeds if s.justification in just_set])

    def merge(self, other: TransportSeedCollection) -> TransportSeedCollection:
        return TransportSeedCollection(self._seeds + other._seeds)

    def is_empty(self) -> bool:
        return len(self._seeds) == 0

    def __len__(self) -> int:
        return len(self._seeds)

    def __iter__(self):
        return iter(self._seeds)

    def pretty(self) -> str:
        if not self._seeds:
            return "<empty TransportSeedCollection>"
        lines = [f"TransportSeedCollection ({len(self._seeds)} seeds):"]
        for s in self._seeds:
            lines.append(f"  {s.pretty()}")
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"<TransportSeedCollection n={len(self._seeds)}>"
