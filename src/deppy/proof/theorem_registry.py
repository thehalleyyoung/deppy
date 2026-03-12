"""Theorem registry: store and query available theorems and lemmas.

Maintains a registry of theorems that can be looked up by name,
searched by predicate patterns, and matched against proof obligations.
"""

from __future__ import annotations

import enum
import logging
import re
from dataclasses import dataclass, field
from typing import (
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

from deppy.core._protocols import SiteId, SiteKind, TrustLevel
from deppy.types.base import TypeBase, AnyType, ANY_TYPE
from deppy.types.witnesses import ProofTerm, ReflProof, AssumptionProof
from deppy.proof._protocols import ProofObligation, ObligationStatus

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Theorem kind
# ---------------------------------------------------------------------------


class TheoremKind(enum.Enum):
    """Classification of registered theorems."""

    AXIOM = "axiom"
    THEOREM = "theorem"
    LEMMA = "lemma"
    COROLLARY = "corollary"
    DEFINITION = "definition"
    RULE = "rule"
    TACTIC = "tactic"


# ---------------------------------------------------------------------------
# Theorem info
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TheoremHypothesis:
    """A hypothesis (premise) of a theorem.

    Attributes:
        _name: Name of the hypothesis variable.
        _type_constraint: Optional type constraint on the variable.
        _predicate: The predicate that must hold.
        _description: Human-readable description.
    """

    _name: str
    _type_constraint: Optional[TypeBase] = None
    _predicate: Any = None
    _description: str = ""

    @property
    def name(self) -> str:
        return self._name

    @property
    def type_constraint(self) -> Optional[TypeBase]:
        return self._type_constraint

    @property
    def predicate(self) -> Any:
        return self._predicate

    @property
    def description(self) -> str:
        return self._description

    def __repr__(self) -> str:
        return f"Hypothesis({self._name}: {self._description})"


@dataclass(frozen=True)
class TheoremConclusion:
    """The conclusion of a theorem.

    Attributes:
        _proposition: The proposition that the theorem establishes.
        _type_result: Optional resulting type.
        _description: Human-readable description.
    """

    _proposition: Any = None
    _type_result: Optional[TypeBase] = None
    _description: str = ""

    @property
    def proposition(self) -> Any:
        return self._proposition

    @property
    def type_result(self) -> Optional[TypeBase]:
        return self._type_result

    @property
    def description(self) -> str:
        return self._description

    def __repr__(self) -> str:
        return f"Conclusion({self._description})"


@dataclass(frozen=True)
class TheoremInfo:
    """Complete information about a registered theorem.

    Attributes:
        _name: Unique name of the theorem.
        _kind: Whether it is an axiom, theorem, lemma, etc.
        _hypotheses: The premises of the theorem.
        _conclusion: The conclusion of the theorem.
        _proof: Optional proof term (None for axioms).
        _tags: Tags for search and classification.
        _source_module: Where the theorem was defined.
        _trust_level: Trust level of the theorem.
        _description: Human-readable description.
        _priority: Priority for theorem selection (higher = preferred).
    """

    _name: str
    _kind: TheoremKind = TheoremKind.THEOREM
    _hypotheses: Tuple[TheoremHypothesis, ...] = ()
    _conclusion: Optional[TheoremConclusion] = None
    _proof: Optional[ProofTerm] = None
    _tags: FrozenSet[str] = frozenset()
    _source_module: str = ""
    _trust_level: TrustLevel = TrustLevel.PROOF_BACKED
    _description: str = ""
    _priority: int = 0

    @property
    def name(self) -> str:
        return self._name

    @property
    def kind(self) -> TheoremKind:
        return self._kind

    @property
    def hypotheses(self) -> Tuple[TheoremHypothesis, ...]:
        return self._hypotheses

    @property
    def conclusion(self) -> Optional[TheoremConclusion]:
        return self._conclusion

    @property
    def proof(self) -> Optional[ProofTerm]:
        return self._proof

    @property
    def tags(self) -> FrozenSet[str]:
        return self._tags

    @property
    def source_module(self) -> str:
        return self._source_module

    @property
    def trust_level(self) -> TrustLevel:
        return self._trust_level

    @property
    def description(self) -> str:
        return self._description

    @property
    def priority(self) -> int:
        return self._priority

    @property
    def is_axiom(self) -> bool:
        return self._kind == TheoremKind.AXIOM

    @property
    def has_proof(self) -> bool:
        return self._proof is not None

    @property
    def hypothesis_count(self) -> int:
        return len(self._hypotheses)

    def matches_tag(self, tag: str) -> bool:
        """Check if the theorem has the given tag."""
        return tag in self._tags

    def matches_any_tag(self, tags: Set[str]) -> bool:
        """Check if the theorem has any of the given tags."""
        return bool(self._tags & tags)

    def __repr__(self) -> str:
        return (
            f"TheoremInfo({self._name!r}, kind={self._kind.value}, "
            f"hyps={len(self._hypotheses)})"
        )


# ---------------------------------------------------------------------------
# Match result
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TheoremMatch:
    """Result of matching a theorem against an obligation.

    Attributes:
        _theorem: The matched theorem.
        _score: Match quality score (0.0 to 1.0).
        _bindings: Variable bindings discovered during matching.
        _remaining_hypotheses: Hypotheses not yet discharged.
        _explanation: Why this theorem was matched.
    """

    _theorem: TheoremInfo
    _score: float = 0.0
    _bindings: Dict[str, Any] = field(default_factory=dict)
    _remaining_hypotheses: Tuple[TheoremHypothesis, ...] = ()
    _explanation: str = ""

    @property
    def theorem(self) -> TheoremInfo:
        return self._theorem

    @property
    def score(self) -> float:
        return self._score

    @property
    def bindings(self) -> Dict[str, Any]:
        return dict(self._bindings)

    @property
    def remaining_hypotheses(self) -> Tuple[TheoremHypothesis, ...]:
        return self._remaining_hypotheses

    @property
    def explanation(self) -> str:
        return self._explanation

    @property
    def is_exact(self) -> bool:
        return self._score >= 1.0 and len(self._remaining_hypotheses) == 0

    def __repr__(self) -> str:
        return (
            f"TheoremMatch({self._theorem.name!r}, "
            f"score={self._score:.2f})"
        )


# ---------------------------------------------------------------------------
# Predicate pattern matching
# ---------------------------------------------------------------------------


def _extract_obligation_tags(obligation: ProofObligation) -> Set[str]:
    """Extract tags from an obligation for matching purposes."""
    tags: Set[str] = set()
    prop = obligation.prop
    if isinstance(prop, tuple) and len(prop) >= 1:
        tags.add(str(prop[0]))
        if len(prop) >= 3:
            tags.add(str(prop[2]))
    context = obligation.context
    if "kind" in context:
        tags.add(str(context["kind"]))
    if "function" in context:
        tags.add(str(context["function"]))
    tags.add(obligation.site_id.kind.value)
    return tags


def _match_predicate_pattern(
    pattern: str, theorem: TheoremInfo
) -> float:
    """Match a predicate pattern against a theorem.

    Returns a score between 0.0 (no match) and 1.0 (exact match).
    """
    pattern_lower = pattern.lower()
    name_lower = theorem.name.lower()
    desc_lower = theorem.description.lower()

    # Exact name match
    if pattern_lower == name_lower:
        return 1.0

    # Name contains pattern
    if pattern_lower in name_lower:
        return 0.8

    # Description contains pattern
    if pattern_lower in desc_lower:
        return 0.6

    # Tag match
    if pattern_lower in {t.lower() for t in theorem.tags}:
        return 0.7

    # Regex match on name
    try:
        if re.search(pattern, theorem.name, re.IGNORECASE):
            return 0.5
    except re.error:
        pass

    # Regex match on description
    try:
        if re.search(pattern, theorem.description, re.IGNORECASE):
            return 0.3
    except re.error:
        pass

    return 0.0


def _match_obligation_to_theorem(
    obligation: ProofObligation, theorem: TheoremInfo
) -> float:
    """Score how well a theorem matches an obligation.

    Returns a score from 0.0 (no match) to 1.0 (perfect match).
    """
    score = 0.0
    obl_tags = _extract_obligation_tags(obligation)

    # Tag overlap
    if theorem.tags:
        overlap = len(obl_tags & {t.lower() for t in theorem.tags})
        if overlap > 0:
            score += 0.3 * min(overlap / len(theorem.tags), 1.0)

    # Kind matching
    prop = obligation.prop
    if isinstance(prop, tuple) and len(prop) >= 1:
        prop_kind = str(prop[0]).lower()
        if prop_kind in theorem.name.lower():
            score += 0.3
        if theorem.conclusion is not None:
            concl_desc = theorem.conclusion.description.lower()
            if prop_kind in concl_desc:
                score += 0.2

    # Hypothesis count: prefer theorems with fewer unmatched hypotheses
    if theorem.hypothesis_count == 0:
        score += 0.1
    elif theorem.hypothesis_count <= 2:
        score += 0.05

    # Priority boost
    score += theorem.priority * 0.01

    return min(score, 1.0)


# ---------------------------------------------------------------------------
# Theorem registry
# ---------------------------------------------------------------------------


class TheoremRegistry:
    """Registry of available theorems and lemmas.

    Supports registration, lookup by name, search by predicate pattern,
    and matching against proof obligations. Theorems are indexed by name
    and by tag for efficient retrieval.

    Attributes:
        _theorems: Primary storage, name -> TheoremInfo.
        _by_tag: Index from tag -> set of theorem names.
        _by_kind: Index from kind -> set of theorem names.
        _by_module: Index from module -> set of theorem names.
    """

    def __init__(self) -> None:
        self._theorems: Dict[str, TheoremInfo] = {}
        self._by_tag: Dict[str, Set[str]] = {}
        self._by_kind: Dict[TheoremKind, Set[str]] = {}
        self._by_module: Dict[str, Set[str]] = {}

    @property
    def size(self) -> int:
        """Number of registered theorems."""
        return len(self._theorems)

    def register(self, name: str, theorem: TheoremInfo) -> None:
        """Register a theorem by name.

        If a theorem with the same name already exists, it is replaced.
        """
        self._theorems[name] = theorem
        # Update tag index
        for tag in theorem.tags:
            self._by_tag.setdefault(tag, set()).add(name)
        # Update kind index
        self._by_kind.setdefault(theorem.kind, set()).add(name)
        # Update module index
        if theorem.source_module:
            self._by_module.setdefault(theorem.source_module, set()).add(name)

    def register_axiom(
        self,
        name: str,
        conclusion: TheoremConclusion,
        tags: Optional[Set[str]] = None,
        description: str = "",
    ) -> None:
        """Convenience: register an axiom (theorem without proof)."""
        info = TheoremInfo(
            _name=name,
            _kind=TheoremKind.AXIOM,
            _conclusion=conclusion,
            _tags=frozenset(tags or set()),
            _trust_level=TrustLevel.ASSUMED,
            _description=description,
        )
        self.register(name, info)

    def register_lemma(
        self,
        name: str,
        hypotheses: List[TheoremHypothesis],
        conclusion: TheoremConclusion,
        proof: Optional[ProofTerm] = None,
        tags: Optional[Set[str]] = None,
        description: str = "",
    ) -> None:
        """Convenience: register a lemma."""
        info = TheoremInfo(
            _name=name,
            _kind=TheoremKind.LEMMA,
            _hypotheses=tuple(hypotheses),
            _conclusion=conclusion,
            _proof=proof,
            _tags=frozenset(tags or set()),
            _trust_level=TrustLevel.PROOF_BACKED if proof else TrustLevel.ASSUMED,
            _description=description,
        )
        self.register(name, info)

    def unregister(self, name: str) -> bool:
        """Remove a theorem from the registry. Returns True if found."""
        theorem = self._theorems.pop(name, None)
        if theorem is None:
            return False
        for tag in theorem.tags:
            if tag in self._by_tag:
                self._by_tag[tag].discard(name)
        if theorem.kind in self._by_kind:
            self._by_kind[theorem.kind].discard(name)
        if theorem.source_module and theorem.source_module in self._by_module:
            self._by_module[theorem.source_module].discard(name)
        return True

    def lookup(self, name: str) -> Optional[TheoremInfo]:
        """Look up a theorem by its exact name."""
        return self._theorems.get(name)

    def lookup_by_kind(self, kind: TheoremKind) -> List[TheoremInfo]:
        """Look up all theorems of a given kind."""
        names = self._by_kind.get(kind, set())
        return [self._theorems[n] for n in names if n in self._theorems]

    def lookup_by_tag(self, tag: str) -> List[TheoremInfo]:
        """Look up all theorems with a given tag."""
        names = self._by_tag.get(tag, set())
        return [self._theorems[n] for n in names if n in self._theorems]

    def lookup_by_module(self, module: str) -> List[TheoremInfo]:
        """Look up all theorems from a given source module."""
        names = self._by_module.get(module, set())
        return [self._theorems[n] for n in names if n in self._theorems]

    def search(self, predicate_pattern: str) -> List[TheoremInfo]:
        """Search for theorems matching a predicate pattern.

        The pattern is matched against theorem names, descriptions,
        and tags. Results are sorted by match quality.
        """
        scored: List[Tuple[float, TheoremInfo]] = []
        for theorem in self._theorems.values():
            score = _match_predicate_pattern(predicate_pattern, theorem)
            if score > 0.0:
                scored.append((score, theorem))
        scored.sort(key=lambda x: (-x[0], x[1].name))
        return [t for _, t in scored]

    def applicable_theorems(
        self, obligation: ProofObligation
    ) -> List[TheoremInfo]:
        """Find theorems that could help discharge a proof obligation.

        Returns theorems sorted by relevance to the obligation.
        """
        scored: List[Tuple[float, TheoremInfo]] = []
        for theorem in self._theorems.values():
            score = _match_obligation_to_theorem(obligation, theorem)
            if score > 0.0:
                scored.append((score, theorem))
        scored.sort(key=lambda x: (-x[0], x[1].name))
        return [t for _, t in scored]

    def match_obligation(
        self, obligation: ProofObligation
    ) -> List[TheoremMatch]:
        """Match an obligation against all theorems, producing TheoremMatch objects."""
        matches: List[TheoremMatch] = []
        for theorem in self._theorems.values():
            score = _match_obligation_to_theorem(obligation, theorem)
            if score > 0.0:
                remaining = theorem.hypotheses
                match = TheoremMatch(
                    _theorem=theorem,
                    _score=score,
                    _remaining_hypotheses=remaining,
                    _explanation=f"Score {score:.2f}: matched against {theorem.name}",
                )
                matches.append(match)
        matches.sort(key=lambda m: -m.score)
        return matches

    def all_theorems(self) -> List[TheoremInfo]:
        """Return all registered theorems."""
        return list(self._theorems.values())

    def all_names(self) -> List[str]:
        """Return all registered theorem names."""
        return list(self._theorems.keys())

    def all_tags(self) -> Set[str]:
        """Return the set of all tags in the registry."""
        return set(self._by_tag.keys())

    def clear(self) -> None:
        """Remove all registered theorems."""
        self._theorems.clear()
        self._by_tag.clear()
        self._by_kind.clear()
        self._by_module.clear()

    def merge(self, other: TheoremRegistry) -> None:
        """Merge all theorems from another registry into this one."""
        for name, theorem in other._theorems.items():
            self.register(name, theorem)

    def statistics(self) -> Dict[str, Any]:
        """Return registry statistics."""
        kind_counts: Dict[str, int] = {}
        for kind, names in self._by_kind.items():
            kind_counts[kind.value] = len(names)
        return {
            "total_theorems": len(self._theorems),
            "total_tags": len(self._by_tag),
            "total_modules": len(self._by_module),
            "by_kind": kind_counts,
        }

    def __repr__(self) -> str:
        return f"TheoremRegistry({len(self._theorems)} theorems)"


# ---------------------------------------------------------------------------
# Built-in theorems
# ---------------------------------------------------------------------------


def create_default_registry() -> TheoremRegistry:
    """Create a registry pre-populated with standard mathematical axioms.

    Includes reflexivity, symmetry, transitivity of equality, and basic
    logical axioms.
    """
    registry = TheoremRegistry()

    # Equality axioms
    registry.register_axiom(
        "eq_refl",
        TheoremConclusion(
            _proposition=("eq", "a", "a"),
            _description="For all a, a = a",
        ),
        tags={"equality", "reflexivity"},
        description="Reflexivity of equality",
    )

    registry.register(
        "eq_sym",
        TheoremInfo(
            _name="eq_sym",
            _kind=TheoremKind.AXIOM,
            _hypotheses=(
                TheoremHypothesis(_name="h", _description="a = b"),
            ),
            _conclusion=TheoremConclusion(
                _proposition=("eq", "b", "a"),
                _description="b = a",
            ),
            _tags=frozenset({"equality", "symmetry"}),
            _trust_level=TrustLevel.ASSUMED,
            _description="Symmetry of equality",
        ),
    )

    registry.register(
        "eq_trans",
        TheoremInfo(
            _name="eq_trans",
            _kind=TheoremKind.AXIOM,
            _hypotheses=(
                TheoremHypothesis(_name="h1", _description="a = b"),
                TheoremHypothesis(_name="h2", _description="b = c"),
            ),
            _conclusion=TheoremConclusion(
                _proposition=("eq", "a", "c"),
                _description="a = c",
            ),
            _tags=frozenset({"equality", "transitivity"}),
            _trust_level=TrustLevel.ASSUMED,
            _description="Transitivity of equality",
        ),
    )

    # Logical axioms
    registry.register_axiom(
        "true_intro",
        TheoremConclusion(
            _proposition="True",
            _description="True holds trivially",
        ),
        tags={"logic", "trivial"},
        description="Introduction of True",
    )

    registry.register(
        "false_elim",
        TheoremInfo(
            _name="false_elim",
            _kind=TheoremKind.AXIOM,
            _hypotheses=(
                TheoremHypothesis(_name="h", _description="False"),
            ),
            _conclusion=TheoremConclusion(
                _proposition="P",
                _description="Any proposition P",
            ),
            _tags=frozenset({"logic", "absurdity", "ex_falso"}),
            _trust_level=TrustLevel.ASSUMED,
            _description="Ex falso quodlibet: from False, derive anything",
        ),
    )

    registry.register(
        "and_intro",
        TheoremInfo(
            _name="and_intro",
            _kind=TheoremKind.RULE,
            _hypotheses=(
                TheoremHypothesis(_name="hp", _description="P"),
                TheoremHypothesis(_name="hq", _description="Q"),
            ),
            _conclusion=TheoremConclusion(
                _proposition=("and", "P", "Q"),
                _description="P and Q",
            ),
            _tags=frozenset({"logic", "conjunction", "and"}),
            _trust_level=TrustLevel.ASSUMED,
            _description="Conjunction introduction",
        ),
    )

    registry.register(
        "modus_ponens",
        TheoremInfo(
            _name="modus_ponens",
            _kind=TheoremKind.RULE,
            _hypotheses=(
                TheoremHypothesis(_name="h_impl", _description="P => Q"),
                TheoremHypothesis(_name="h_p", _description="P"),
            ),
            _conclusion=TheoremConclusion(
                _proposition="Q",
                _description="Q",
            ),
            _tags=frozenset({"logic", "implication", "modus_ponens"}),
            _trust_level=TrustLevel.ASSUMED,
            _description="Modus ponens: from P => Q and P, derive Q",
        ),
    )

    # Refinement type axioms
    registry.register(
        "subtype_refl",
        TheoremInfo(
            _name="subtype_refl",
            _kind=TheoremKind.AXIOM,
            _conclusion=TheoremConclusion(
                _proposition=("subtype", "T", "T"),
                _description="T <: T",
            ),
            _tags=frozenset({"subtype", "reflexivity"}),
            _trust_level=TrustLevel.ASSUMED,
            _description="Reflexivity of subtyping",
        ),
    )

    registry.register(
        "subtype_trans",
        TheoremInfo(
            _name="subtype_trans",
            _kind=TheoremKind.AXIOM,
            _hypotheses=(
                TheoremHypothesis(_name="h1", _description="A <: B"),
                TheoremHypothesis(_name="h2", _description="B <: C"),
            ),
            _conclusion=TheoremConclusion(
                _proposition=("subtype", "A", "C"),
                _description="A <: C",
            ),
            _tags=frozenset({"subtype", "transitivity"}),
            _trust_level=TrustLevel.ASSUMED,
            _description="Transitivity of subtyping",
        ),
    )

    return registry
