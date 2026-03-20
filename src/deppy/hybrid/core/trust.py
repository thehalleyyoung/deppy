"""Trust lattice and evidence system for hybrid dependent type checking.

The trust system forms a bounded lattice where:
  - LEAN_VERIFIED is the top element (⊤),
  - CONTRADICTED is the bottom element (⊥),
  - join (∨) computes least upper bound,
  - meet (∧) computes greatest lower bound.

Evidence chains model derivations as a DAG (forming a category where
morphisms are "supports" edges).  Trust propagation follows a
sheaf-theoretic restriction: the trust level of a composite judgment
is bounded above by the weakest link in any supporting path, mirroring
the restriction map of a presheaf from a larger open to a smaller one.

This module is intentionally decoupled from the prover back-ends;
Evidence objects carry serialised proof artefacts as opaque strings
so that the trust lattice can be evaluated without importing Lean,
Z3, or any LLM client.
"""

from __future__ import annotations

import enum
import hashlib
import json
import time
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
    Any,
    Dict,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
)

if TYPE_CHECKING:
    from deppy.core._protocols import TrustLevel


# ═══════════════════════════════════════════════════════════════════
#  §1  Hybrid Trust Level — bounded lattice with 6 elements
# ═══════════════════════════════════════════════════════════════════

# Ordering index used by lattice operations.  Higher ↔ more trusted.

# --- Integration with existing deppy codebase ---
try:
    from deppy.kernel.trust_classifier import TrustClassifier as _CoreTrustClassifier, ProvenanceTag, trust_rank, trust_leq
    from deppy.core._protocols import TrustLevel as _CoreTrustLevel
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

_TRUST_ORDER: Dict[str, int] = {
    "CONTRADICTED": 0,
    "UNTRUSTED": 1,
    "RUNTIME_CHECKED": 2,
    "LLM_JUDGED": 3,
    "Z3_PROVEN": 4,
    "LEAN_VERIFIED": 5,
}


class HybridTrustLevel(enum.Enum):
    """Trust levels for the hybrid dependent type system.

    The levels form a total order (and therefore a lattice):

        CONTRADICTED < UNTRUSTED < RUNTIME_CHECKED
            < LLM_JUDGED < Z3_PROVEN < LEAN_VERIFIED

    CONTRADICTED is ⊥ — evidence exists that the predicate is *false*.
    LEAN_VERIFIED is ⊤ — the Lean kernel accepted a proof term.
    """

    LEAN_VERIFIED = "lean_verified"
    Z3_PROVEN = "z3_proven"
    LLM_JUDGED = "llm_judged"
    RUNTIME_CHECKED = "runtime_checked"
    UNTRUSTED = "untrusted"
    CONTRADICTED = "contradicted"

    # -- lattice helpers ------------------------------------------------

    @property
    def _rank(self) -> int:
        """Numeric rank used for ordering comparisons."""
        return _TRUST_ORDER[self.name]

    def __le__(self, other: object) -> bool:
        if not isinstance(other, HybridTrustLevel):
            return NotImplemented
        return self._rank <= other._rank

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, HybridTrustLevel):
            return NotImplemented
        return self._rank < other._rank

    def __ge__(self, other: object) -> bool:
        if not isinstance(other, HybridTrustLevel):
            return NotImplemented
        return self._rank >= other._rank

    def __gt__(self, other: object) -> bool:
        if not isinstance(other, HybridTrustLevel):
            return NotImplemented
        return self._rank > other._rank

    # join and meet are idempotent, commutative, associative ⇒ lattice

    def join(self, other: HybridTrustLevel) -> HybridTrustLevel:
        """Least upper bound (∨).

        ``a.join(b)`` returns the *weaker* guarantee that still
        dominates both ``a`` and ``b``.  Because the order is total
        this is simply ``max``.
        """
        if self._rank >= other._rank:
            return self
        return other

    def meet(self, other: HybridTrustLevel) -> HybridTrustLevel:
        """Greatest lower bound (∧).

        ``a.meet(b)`` returns the *stronger* guarantee that is
        dominated by both ``a`` and ``b``.  Because the order is total
        this is simply ``min``.
        """
        if self._rank <= other._rank:
            return self
        return other

    # -- backward compatibility ----------------------------------------

    def to_deppy_trust(self) -> TrustLevel:
        """Map to the original six-valued ``deppy.core._protocols.TrustLevel``.

        The mapping is necessarily lossy:

        ==============================  =========================
        HybridTrustLevel                deppy TrustLevel
        ==============================  =========================
        LEAN_VERIFIED                   PROOF_BACKED
        Z3_PROVEN                       PROOF_BACKED
        LLM_JUDGED                      BOUNDED_AUTO
        RUNTIME_CHECKED                 TRACE_BACKED
        UNTRUSTED                       ASSUMED
        CONTRADICTED                    RESIDUAL
        ==============================  =========================
        """
        from deppy.core._protocols import TrustLevel as _TL

        _MAP = {
            HybridTrustLevel.LEAN_VERIFIED: _TL.PROOF_BACKED,
            HybridTrustLevel.Z3_PROVEN: _TL.PROOF_BACKED,
            HybridTrustLevel.LLM_JUDGED: _TL.BOUNDED_AUTO,
            HybridTrustLevel.RUNTIME_CHECKED: _TL.TRACE_BACKED,
            HybridTrustLevel.UNTRUSTED: _TL.ASSUMED,
            HybridTrustLevel.CONTRADICTED: _TL.RESIDUAL,
        }
        return _MAP[self]

    @classmethod
    def from_deppy_trust(cls, level: TrustLevel) -> HybridTrustLevel:
        """Best-effort inverse of :meth:`to_deppy_trust`.

        Because the mapping is not injective the reconstruction is
        conservative: ``PROOF_BACKED`` maps to ``Z3_PROVEN`` rather
        than ``LEAN_VERIFIED`` since we cannot know whether a Lean
        kernel check actually occurred.
        """
        from deppy.core._protocols import TrustLevel as _TL

        _INV: Dict[Any, HybridTrustLevel] = {
            _TL.TRUSTED_AUTO: cls.Z3_PROVEN,
            _TL.BOUNDED_AUTO: cls.LLM_JUDGED,
            _TL.PROOF_BACKED: cls.Z3_PROVEN,
            _TL.TRACE_BACKED: cls.RUNTIME_CHECKED,
            _TL.RESIDUAL: cls.CONTRADICTED,
            _TL.ASSUMED: cls.UNTRUSTED,
        }
        return _INV.get(level, cls.UNTRUSTED)


# ═══════════════════════════════════════════════════════════════════
#  §2  Evidence kinds
# ═══════════════════════════════════════════════════════════════════

class EvidenceKind(enum.Enum):
    """Kinds of evidence that can support a trust judgment."""

    LEAN_PROOF = "lean_proof"
    Z3_CERTIFICATE = "z3_certificate"
    LLM_JUDGMENT = "llm_judgment"
    RUNTIME_TEST = "runtime_test"
    MANUAL_AUDIT = "manual_audit"
    ASSUMPTION = "assumption"
    TRANSPORT = "transport"  # transported from another proof context


# Canonical map: what trust level does a *single* piece of evidence confer?
_EVIDENCE_TRUST: Dict[EvidenceKind, HybridTrustLevel] = {
    EvidenceKind.LEAN_PROOF: HybridTrustLevel.LEAN_VERIFIED,
    EvidenceKind.Z3_CERTIFICATE: HybridTrustLevel.Z3_PROVEN,
    EvidenceKind.LLM_JUDGMENT: HybridTrustLevel.LLM_JUDGED,
    EvidenceKind.RUNTIME_TEST: HybridTrustLevel.RUNTIME_CHECKED,
    EvidenceKind.MANUAL_AUDIT: HybridTrustLevel.LEAN_VERIFIED,
    EvidenceKind.ASSUMPTION: HybridTrustLevel.UNTRUSTED,
    EvidenceKind.TRANSPORT: HybridTrustLevel.LLM_JUDGED,
}


# ═══════════════════════════════════════════════════════════════════
#  §3  Evidence — a single piece of evidence
# ═══════════════════════════════════════════════════════════════════

def _content_hash(content: str) -> str:
    """Deterministic SHA-256 hash of a content string."""
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def _iso_now() -> str:
    """Current UTC time in ISO-8601 format with milliseconds."""
    return time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime()) + (
        ".%03dZ" % (int(time.time() * 1000) % 1000)
    )


@dataclass(frozen=True)
class Evidence:
    """A single piece of evidence supporting (or refuting) a predicate.

    Evidence is *content-addressed*: two ``Evidence`` values with the
    same ``content_hash`` are considered interchangeable.  This enables
    efficient caching and deduplication across obligation-discharge
    pipelines.
    """

    kind: EvidenceKind
    trust_level: HybridTrustLevel
    content: str
    content_hash: str
    timestamp: str
    source: str
    inputs: Tuple[str, ...] = ()
    metadata: Dict[str, Any] = field(default_factory=dict)

    # -- factory -------------------------------------------------------

    @classmethod
    def create(
        cls,
        kind: EvidenceKind,
        content: str,
        source: str,
        *,
        trust_level: Optional[HybridTrustLevel] = None,
        inputs: Sequence[str] = (),
        metadata: Optional[Dict[str, Any]] = None,
    ) -> Evidence:
        """Create a new evidence node with auto-computed hash and timestamp.

        Parameters
        ----------
        kind:
            The kind of evidence (``LEAN_PROOF``, ``Z3_CERTIFICATE``, …).
        content:
            The serialised proof artefact, certificate, or judgment text.
        source:
            Human-readable identifier for the producer (e.g. ``"lean4"``).
        trust_level:
            Override the canonical trust level for this evidence kind.
            Defaults to the canonical mapping in ``_EVIDENCE_TRUST``.
        inputs:
            Content hashes of evidence nodes this one depends on.
        metadata:
            Arbitrary key-value metadata.
        """
        resolved_trust = trust_level if trust_level is not None else _EVIDENCE_TRUST.get(
            kind, HybridTrustLevel.UNTRUSTED
        )
        return cls(
            kind=kind,
            trust_level=resolved_trust,
            content=content,
            content_hash=_content_hash(content),
            timestamp=_iso_now(),
            source=source,
            inputs=tuple(inputs),
            metadata=metadata or {},
        )

    # -- queries -------------------------------------------------------

    def is_valid(self) -> bool:
        """Basic well-formedness check.

        Returns ``True`` when:
        * the content is non-empty,
        * the content hash matches a recomputation,
        * the source is non-empty,
        * the trust level is consistent with the evidence kind.
        """
        if not self.content:
            return False
        if self.content_hash != _content_hash(self.content):
            return False
        if not self.source:
            return False
        # Trust level must not exceed the canonical ceiling for this kind.
        canonical_ceiling = _EVIDENCE_TRUST.get(self.kind, HybridTrustLevel.UNTRUSTED)
        if self.trust_level > canonical_ceiling:
            return False
        return True

    def depends_on(self, other: Evidence) -> bool:
        """Return ``True`` if *this* evidence directly depends on *other*."""
        return other.content_hash in self.inputs

    # -- serialisation -------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        """Serialise to a JSON-friendly dictionary."""
        return {
            "kind": self.kind.value,
            "trust_level": self.trust_level.value,
            "content": self.content,
            "content_hash": self.content_hash,
            "timestamp": self.timestamp,
            "source": self.source,
            "inputs": list(self.inputs),
            "metadata": self.metadata,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> Evidence:
        """Deserialise from a dictionary (inverse of :meth:`to_dict`)."""
        return cls(
            kind=EvidenceKind(d["kind"]),
            trust_level=HybridTrustLevel(d["trust_level"]),
            content=d["content"],
            content_hash=d["content_hash"],
            timestamp=d["timestamp"],
            source=d["source"],
            inputs=tuple(d.get("inputs", ())),
            metadata=d.get("metadata", {}),
        )

    def __repr__(self) -> str:
        abbrev = self.content_hash[:12]
        return (
            f"Evidence(kind={self.kind.name}, trust={self.trust_level.name}, "
            f"hash={abbrev}…, source={self.source!r})"
        )


# ═══════════════════════════════════════════════════════════════════
#  §4  Evidence Chain — a derivation DAG
# ═══════════════════════════════════════════════════════════════════

@dataclass
class EvidenceChain:
    """A directed acyclic graph of :class:`Evidence` nodes.

    The ``root`` is the final conclusion.  Each interior node may be
    supported by zero or more children (premises).  Leaf nodes are
    axioms or assumptions.

    Trust propagation follows the *weakest-link principle*: the trust
    level of the chain is the meet (∧) of all node trust levels along
    the worst path from root to any leaf.
    """

    root: Evidence
    children: Dict[str, List[Evidence]] = field(default_factory=dict)
    _nodes: Dict[str, Evidence] = field(default_factory=dict, repr=False)

    def __post_init__(self) -> None:
        if self.root.content_hash not in self._nodes:
            self._nodes[self.root.content_hash] = self.root

    # -- mutators ------------------------------------------------------

    def add(self, evidence: Evidence, supports: Evidence) -> None:
        """Record that *evidence* is a premise supporting *supports*.

        Both nodes are registered in the internal node index.  If
        *supports* is not already known the caller is responsible for
        ensuring eventual consistency (i.e. *supports* must be the
        root or must itself be added as a premise of another node).

        Parameters
        ----------
        evidence:
            The supporting evidence (premise).
        supports:
            The evidence node that *evidence* supports (conclusion).
        """
        self._nodes[evidence.content_hash] = evidence
        self._nodes[supports.content_hash] = supports
        self.children.setdefault(supports.content_hash, []).append(evidence)

    def add_root_support(self, evidence: Evidence) -> None:
        """Convenience: add *evidence* as a direct premise of the root."""
        self.add(evidence, self.root)

    # -- queries -------------------------------------------------------

    @property
    def all_nodes(self) -> Dict[str, Evidence]:
        """Return a shallow copy of the internal node index."""
        return dict(self._nodes)

    def trust_level(self) -> HybridTrustLevel:
        """Compute the overall trust level of the chain.

        This is the *meet* (greatest lower bound) of all node trust
        levels, which realises the weakest-link principle: a chain is
        only as trustworthy as its least trusted node.
        """
        if not self._nodes:
            return HybridTrustLevel.UNTRUSTED
        result = HybridTrustLevel.LEAN_VERIFIED  # start at ⊤
        for node in self._nodes.values():
            result = result.meet(node.trust_level)
            if result == HybridTrustLevel.CONTRADICTED:
                return result  # early exit — can't go lower
        return result

    def trace(self, evidence_hash: str) -> List[Evidence]:
        """Trace from *evidence_hash* back to axioms (leaves).

        Returns the evidence nodes in a depth-first, pre-order
        traversal of the sub-DAG rooted at *evidence_hash*.  Nodes
        with no children in the DAG are axioms / assumptions.
        """
        result: List[Evidence] = []
        visited: Set[str] = set()

        def _dfs(h: str) -> None:
            if h in visited:
                return
            visited.add(h)
            node = self._nodes.get(h)
            if node is None:
                return
            result.append(node)
            for child in self.children.get(h, []):
                _dfs(child.content_hash)

        _dfs(evidence_hash)
        return result

    def leaves(self) -> List[Evidence]:
        """Return all leaf nodes (axioms / assumptions)."""
        parent_hashes = set()
        for kids in self.children.values():
            for kid in kids:
                parent_hashes.add(kid.content_hash)
        # A leaf is a node whose hash never appears as a *parent* key
        # in children AND has no children list of its own.
        return [
            n
            for h, n in self._nodes.items()
            if not self.children.get(h)
        ]

    def depth(self) -> int:
        """Longest path from root to any leaf."""
        memo: Dict[str, int] = {}

        def _depth(h: str) -> int:
            if h in memo:
                return memo[h]
            kids = self.children.get(h, [])
            if not kids:
                memo[h] = 0
                return 0
            d = 1 + max(_depth(c.content_hash) for c in kids)
            memo[h] = d
            return d

        return _depth(self.root.content_hash)

    # -- validation ----------------------------------------------------

    def validate(self) -> List[str]:
        """Check internal consistency and return a list of problems.

        An empty list means the chain is well-formed.  Possible issues:

        * evidence node with invalid ``is_valid()``
        * child references a parent hash not in the node index
        * cycle detected
        * dangling input hash (evidence.inputs references an unknown hash)
        """
        problems: List[str] = []

        # 1. Well-formedness of individual nodes.
        for h, node in self._nodes.items():
            if not node.is_valid():
                problems.append(
                    f"Node {h[:12]}… ({node.kind.name}) fails is_valid()"
                )

        # 2. Referential integrity of children mapping.
        for parent_hash, kids in self.children.items():
            if parent_hash not in self._nodes:
                problems.append(
                    f"Children list references unknown parent {parent_hash[:12]}…"
                )
            for kid in kids:
                if kid.content_hash not in self._nodes:
                    problems.append(
                        f"Child {kid.content_hash[:12]}… not in node index"
                    )

        # 3. Cycle detection via iterative DFS with colouring.
        WHITE, GREY, BLACK = 0, 1, 2
        colour: Dict[str, int] = {h: WHITE for h in self._nodes}

        def _has_cycle(h: str) -> bool:
            stack = [(h, False)]
            while stack:
                node_h, returning = stack.pop()
                if returning:
                    colour[node_h] = BLACK
                    continue
                if colour.get(node_h) == GREY:
                    return True
                if colour.get(node_h) == BLACK:
                    continue
                colour[node_h] = GREY
                stack.append((node_h, True))
                for kid in self.children.get(node_h, []):
                    kid_h = kid.content_hash
                    if colour.get(kid_h) == GREY:
                        return True
                    if colour.get(kid_h) == WHITE:
                        stack.append((kid_h, False))
            return False

        if _has_cycle(self.root.content_hash):
            problems.append("Cycle detected in evidence chain")

        # 4. Dangling input hashes.
        all_hashes = set(self._nodes.keys())
        for node in self._nodes.values():
            for inp in node.inputs:
                if inp not in all_hashes:
                    problems.append(
                        f"Node {node.content_hash[:12]}… references unknown "
                        f"input hash {inp[:12]}…"
                    )

        return problems

    # -- serialisation -------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        """Serialise the full chain to a JSON-compatible dictionary."""
        return {
            "root_hash": self.root.content_hash,
            "nodes": {h: n.to_dict() for h, n in self._nodes.items()},
            "children": {
                parent: [c.content_hash for c in kids]
                for parent, kids in self.children.items()
            },
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> EvidenceChain:
        """Reconstruct a chain from a dictionary (inverse of :meth:`to_dict`)."""
        nodes: Dict[str, Evidence] = {
            h: Evidence.from_dict(nd) for h, nd in d["nodes"].items()
        }
        root = nodes[d["root_hash"]]
        children: Dict[str, List[Evidence]] = {}
        for parent_hash, kid_hashes in d.get("children", {}).items():
            children[parent_hash] = [nodes[kh] for kh in kid_hashes if kh in nodes]
        chain = cls(root=root, children=children, _nodes=nodes)
        return chain

    def __len__(self) -> int:
        return len(self._nodes)

    def __contains__(self, evidence_hash: str) -> bool:
        return evidence_hash in self._nodes

    def __iter__(self) -> Iterator[Evidence]:
        return iter(self._nodes.values())

    def __repr__(self) -> str:
        return (
            f"EvidenceChain(root={self.root.content_hash[:12]}…, "
            f"nodes={len(self._nodes)}, trust={self.trust_level().name})"
        )


# ═══════════════════════════════════════════════════════════════════
#  §5  Trust Promotion / Demotion dataclasses
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class TrustPromotion:
    """A rule that promotes trust when the required evidence is provided.

    A promotion fires when:
    1. the current trust level is ``from_level``, and
    2. *all* evidence kinds in ``required_evidence`` are present.
    """

    from_level: HybridTrustLevel
    to_level: HybridTrustLevel
    required_evidence: Tuple[EvidenceKind, ...]
    description: str

    def matches(
        self,
        current: HybridTrustLevel,
        available_kinds: Set[EvidenceKind],
    ) -> bool:
        """Return ``True`` when this rule fires for *current* and *available_kinds*."""
        if current != self.from_level:
            return False
        return all(ek in available_kinds for ek in self.required_evidence)

    def to_dict(self) -> Dict[str, Any]:
        """Serialise to a JSON-friendly dictionary."""
        return {
            "from_level": self.from_level.value,
            "to_level": self.to_level.value,
            "required_evidence": [ek.value for ek in self.required_evidence],
            "description": self.description,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> TrustPromotion:
        """Deserialise from a dictionary."""
        return cls(
            from_level=HybridTrustLevel(d["from_level"]),
            to_level=HybridTrustLevel(d["to_level"]),
            required_evidence=tuple(
                EvidenceKind(ek) for ek in d["required_evidence"]
            ),
            description=d["description"],
        )


@dataclass(frozen=True)
class TrustDemotion:
    """A rule that demotes trust when a trigger condition is observed.

    A demotion fires when the current trust level is ``from_level``
    and the trigger string matches.
    """

    trigger: str
    from_level: HybridTrustLevel
    to_level: HybridTrustLevel

    def matches(self, current: HybridTrustLevel, trigger: str) -> bool:
        """Return ``True`` when this rule fires."""
        if self.from_level != current:
            # Special-case: a wildcard from_level matches any level.
            if self.from_level is not None:
                return False
        return trigger == self.trigger

    def to_dict(self) -> Dict[str, Any]:
        """Serialise to a JSON-friendly dictionary."""
        return {
            "trigger": self.trigger,
            "from_level": self.from_level.value,
            "to_level": self.to_level.value,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> TrustDemotion:
        """Deserialise from a dictionary."""
        return cls(
            trigger=d["trigger"],
            from_level=HybridTrustLevel(d["from_level"]),
            to_level=HybridTrustLevel(d["to_level"]),
        )


# ═══════════════════════════════════════════════════════════════════
#  §6  Standard promotion and demotion rule sets
# ═══════════════════════════════════════════════════════════════════

PROMOTION_RULES: List[TrustPromotion] = [
    # ── cross-verifier promotions ──────────────────────────────────
    TrustPromotion(
        from_level=HybridTrustLevel.LLM_JUDGED,
        to_level=HybridTrustLevel.Z3_PROVEN,
        required_evidence=(EvidenceKind.Z3_CERTIFICATE,),
        description=(
            "LLM_JUDGED + Z3_CERTIFICATE → Z3_PROVEN: "
            "LLM hypothesis confirmed by SMT solver"
        ),
    ),
    TrustPromotion(
        from_level=HybridTrustLevel.LLM_JUDGED,
        to_level=HybridTrustLevel.LEAN_VERIFIED,
        required_evidence=(EvidenceKind.LEAN_PROOF,),
        description=(
            "LLM_JUDGED + LEAN_PROOF → LEAN_VERIFIED: "
            "LLM hypothesis confirmed by Lean kernel"
        ),
    ),
    TrustPromotion(
        from_level=HybridTrustLevel.Z3_PROVEN,
        to_level=HybridTrustLevel.LEAN_VERIFIED,
        required_evidence=(EvidenceKind.LEAN_PROOF,),
        description=(
            "Z3_PROVEN + LEAN_PROOF → LEAN_VERIFIED: "
            "SMT result verified by Lean kernel (belt-and-suspenders)"
        ),
    ),
    # ── runtime → formal promotions ────────────────────────────────
    TrustPromotion(
        from_level=HybridTrustLevel.RUNTIME_CHECKED,
        to_level=HybridTrustLevel.Z3_PROVEN,
        required_evidence=(EvidenceKind.Z3_CERTIFICATE,),
        description=(
            "RUNTIME_CHECKED + Z3_CERTIFICATE → Z3_PROVEN: "
            "dynamic observation lifted to a formal proof"
        ),
    ),
    # ── bootstrap promotions ───────────────────────────────────────
    TrustPromotion(
        from_level=HybridTrustLevel.UNTRUSTED,
        to_level=HybridTrustLevel.LLM_JUDGED,
        required_evidence=(EvidenceKind.LLM_JUDGMENT,),
        description=(
            "UNTRUSTED + LLM_JUDGMENT → LLM_JUDGED: "
            "initial LLM triage provides a first trust foothold"
        ),
    ),
    TrustPromotion(
        from_level=HybridTrustLevel.UNTRUSTED,
        to_level=HybridTrustLevel.RUNTIME_CHECKED,
        required_evidence=(EvidenceKind.RUNTIME_TEST,),
        description=(
            "UNTRUSTED + RUNTIME_TEST → RUNTIME_CHECKED: "
            "dynamic test provides empirical evidence"
        ),
    ),
]


# Wildcard sentinel used in demotion rules where any from_level applies.
_WILDCARD_DEMOTIONS_TRIGGER = "counter_evidence_found"

DEMOTION_RULES: List[TrustDemotion] = [
    # ── universal demotion ─────────────────────────────────────────
    TrustDemotion(
        trigger="counter_evidence_found",
        from_level=HybridTrustLevel.LEAN_VERIFIED,
        to_level=HybridTrustLevel.CONTRADICTED,
    ),
    TrustDemotion(
        trigger="counter_evidence_found",
        from_level=HybridTrustLevel.Z3_PROVEN,
        to_level=HybridTrustLevel.CONTRADICTED,
    ),
    TrustDemotion(
        trigger="counter_evidence_found",
        from_level=HybridTrustLevel.LLM_JUDGED,
        to_level=HybridTrustLevel.CONTRADICTED,
    ),
    TrustDemotion(
        trigger="counter_evidence_found",
        from_level=HybridTrustLevel.RUNTIME_CHECKED,
        to_level=HybridTrustLevel.CONTRADICTED,
    ),
    TrustDemotion(
        trigger="counter_evidence_found",
        from_level=HybridTrustLevel.UNTRUSTED,
        to_level=HybridTrustLevel.CONTRADICTED,
    ),
    # ── LLM-specific demotions ─────────────────────────────────────
    TrustDemotion(
        trigger="oracle_model_known_bad",
        from_level=HybridTrustLevel.LLM_JUDGED,
        to_level=HybridTrustLevel.UNTRUSTED,
    ),
    # ── runtime-specific demotions ─────────────────────────────────
    TrustDemotion(
        trigger="test_suite_changed",
        from_level=HybridTrustLevel.RUNTIME_CHECKED,
        to_level=HybridTrustLevel.UNTRUSTED,
    ),
]


# ═══════════════════════════════════════════════════════════════════
#  §7  TrustLattice — the full trust management façade
# ═══════════════════════════════════════════════════════════════════

class TrustLattice:
    """Central trust management system.

    Encapsulates the bounded lattice of :class:`HybridTrustLevel`
    together with the promotion / demotion rule engine.  All operations
    are pure (no mutation of external state) and deterministic.
    """

    def __init__(
        self,
        promotion_rules: Optional[List[TrustPromotion]] = None,
        demotion_rules: Optional[List[TrustDemotion]] = None,
    ) -> None:
        self._promotions = list(promotion_rules or PROMOTION_RULES)
        self._demotions = list(demotion_rules or DEMOTION_RULES)
        # Counters for observability.
        self._promotions_fired: int = 0
        self._demotions_fired: int = 0

    # -- lattice operations --------------------------------------------

    @staticmethod
    def join(a: HybridTrustLevel, b: HybridTrustLevel) -> HybridTrustLevel:
        """Least upper bound (∨) of two trust levels."""
        return a.join(b)

    @staticmethod
    def meet(a: HybridTrustLevel, b: HybridTrustLevel) -> HybridTrustLevel:
        """Greatest lower bound (∧) of two trust levels."""
        return a.meet(b)

    @staticmethod
    def top() -> HybridTrustLevel:
        """Return the top element of the lattice (⊤ = LEAN_VERIFIED)."""
        return HybridTrustLevel.LEAN_VERIFIED

    @staticmethod
    def bottom() -> HybridTrustLevel:
        """Return the bottom element of the lattice (⊥ = CONTRADICTED)."""
        return HybridTrustLevel.CONTRADICTED

    @staticmethod
    def is_sufficient(
        level: HybridTrustLevel,
        required: HybridTrustLevel,
    ) -> bool:
        """Return ``True`` if *level* ≥ *required* in the lattice order."""
        return level >= required

    # -- promotion engine ----------------------------------------------

    def promote(
        self,
        current: HybridTrustLevel,
        evidence: Sequence[Evidence],
    ) -> HybridTrustLevel:
        """Attempt to promote *current* using the supplied *evidence*.

        The promotion engine iterates the rule list in order.  The
        *first* matching rule fires (analogous to a Prolog cut).  If
        no rule matches, the current level is returned unchanged.

        Returns the (possibly promoted) trust level.
        """
        available_kinds: Set[EvidenceKind] = {e.kind for e in evidence}
        best = current
        for rule in self._promotions:
            if rule.matches(current, available_kinds) and rule.to_level > best:
                best = rule.to_level
        if best != current:
            self._promotions_fired += 1
        return best

    def promote_iterative(
        self,
        current: HybridTrustLevel,
        evidence: Sequence[Evidence],
        *,
        max_iterations: int = 10,
    ) -> Tuple[HybridTrustLevel, List[TrustPromotion]]:
        """Promote repeatedly until a fixpoint is reached.

        Returns the final trust level together with the list of
        promotions that fired (in order).
        """
        available_kinds: Set[EvidenceKind] = {e.kind for e in evidence}
        level = current
        fired: List[TrustPromotion] = []
        for _ in range(max_iterations):
            promoted = False
            for rule in self._promotions:
                if rule.matches(level, available_kinds) and rule.to_level > level:
                    fired.append(rule)
                    level = rule.to_level
                    self._promotions_fired += 1
                    promoted = True
                    break  # restart scan at new level
            if not promoted:
                break
        return level, fired

    # -- demotion engine -----------------------------------------------

    def demote(
        self,
        current: HybridTrustLevel,
        trigger: str,
    ) -> HybridTrustLevel:
        """Apply demotion rules for *trigger*.

        The *worst* applicable demotion (lowest ``to_level``) wins.
        """
        worst = current
        for rule in self._demotions:
            if rule.matches(current, trigger) and rule.to_level < worst:
                worst = rule.to_level
        if worst != current:
            self._demotions_fired += 1
        return worst

    # -- chain-level analysis ------------------------------------------

    def weakest_link(self, chain: EvidenceChain) -> HybridTrustLevel:
        """Compute the weakest link in an evidence chain.

        This is the meet (∧) over all nodes in the chain, which
        corresponds to the restriction map of the trust presheaf
        from the global section (conclusion) to each local section
        (premise).
        """
        return chain.trust_level()

    def chain_is_sufficient(
        self,
        chain: EvidenceChain,
        required: HybridTrustLevel,
    ) -> bool:
        """Return ``True`` if the chain meets the required trust floor."""
        return self.is_sufficient(chain.trust_level(), required)

    # -- observability -------------------------------------------------

    def stats(self) -> Dict[str, int]:
        """Return promotion/demotion firing counters."""
        return {
            "promotions_fired": self._promotions_fired,
            "demotions_fired": self._demotions_fired,
            "promotion_rules": len(self._promotions),
            "demotion_rules": len(self._demotions),
        }

    def reset_stats(self) -> None:
        """Reset the internal firing counters."""
        self._promotions_fired = 0
        self._demotions_fired = 0


# ═══════════════════════════════════════════════════════════════════
#  §8  TrustCache — memoisation of trust judgments
# ═══════════════════════════════════════════════════════════════════

@dataclass
class CachedTrust:
    """A single cached trust judgment."""

    predicate_name: str
    content_hash: str
    trust_level: HybridTrustLevel
    evidence_hash: str
    cached_at: float  # time.time() epoch
    hit_count: int = 0

    def age_seconds(self) -> float:
        """Seconds since this entry was cached."""
        return time.time() - self.cached_at

    def to_dict(self) -> Dict[str, Any]:
        """Serialise to a JSON-friendly dictionary."""
        return {
            "predicate_name": self.predicate_name,
            "content_hash": self.content_hash,
            "trust_level": self.trust_level.value,
            "evidence_hash": self.evidence_hash,
            "cached_at": self.cached_at,
            "hit_count": self.hit_count,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> CachedTrust:
        """Deserialise from a dictionary."""
        return cls(
            predicate_name=d["predicate_name"],
            content_hash=d["content_hash"],
            trust_level=HybridTrustLevel(d["trust_level"]),
            evidence_hash=d["evidence_hash"],
            cached_at=d["cached_at"],
            hit_count=d.get("hit_count", 0),
        )


class TrustCache:
    """In-memory cache of trust judgments keyed by (predicate, content_hash).

    The primary purpose is to avoid redundant LLM calls: if the same
    predicate over the same content has already been judged, the cached
    result is returned.  The cache also supports JSON persistence for
    cross-session reuse.
    """

    def __init__(self, *, max_size: int = 4096) -> None:
        self._store: Dict[str, CachedTrust] = {}  # key → entry
        self._max_size = max_size
        self._hits: int = 0
        self._misses: int = 0
        self._evictions: int = 0

    @staticmethod
    def _key(predicate_name: str, content_hash: str) -> str:
        """Compute the cache key."""
        return f"{predicate_name}:{content_hash}"

    # -- read / write --------------------------------------------------

    def get(
        self,
        predicate_name: str,
        content_hash: str,
    ) -> Optional[CachedTrust]:
        """Look up a cached trust judgment.

        Returns ``None`` on a miss; increments the entry's hit count
        on a hit.
        """
        key = self._key(predicate_name, content_hash)
        entry = self._store.get(key)
        if entry is None:
            self._misses += 1
            return None
        entry.hit_count += 1
        self._hits += 1
        return entry

    def put(
        self,
        predicate_name: str,
        content_hash: str,
        trust_level: HybridTrustLevel,
        evidence: Evidence,
    ) -> None:
        """Insert or update a cached trust judgment.

        If the cache is at capacity the least-recently-used entry
        (approximated by lowest hit count) is evicted.
        """
        key = self._key(predicate_name, content_hash)
        if key not in self._store and len(self._store) >= self._max_size:
            self._evict_one()
        self._store[key] = CachedTrust(
            predicate_name=predicate_name,
            content_hash=content_hash,
            trust_level=trust_level,
            evidence_hash=evidence.content_hash,
            cached_at=time.time(),
        )

    def _evict_one(self) -> None:
        """Evict the entry with the lowest hit count (LFU approximation)."""
        if not self._store:
            return
        worst_key = min(self._store, key=lambda k: self._store[k].hit_count)
        del self._store[worst_key]
        self._evictions += 1

    # -- invalidation --------------------------------------------------

    def invalidate(self, content_hash: str) -> int:
        """Invalidate all entries whose *content_hash* matches.

        Returns the number of entries removed.
        """
        to_remove = [
            k for k, v in self._store.items() if v.content_hash == content_hash
        ]
        for k in to_remove:
            del self._store[k]
        return len(to_remove)

    def invalidate_predicate(self, predicate_name: str) -> int:
        """Invalidate all entries for a specific predicate.

        Returns the number of entries removed.
        """
        to_remove = [
            k for k, v in self._store.items() if v.predicate_name == predicate_name
        ]
        for k in to_remove:
            del self._store[k]
        return len(to_remove)

    def invalidate_stale(self, max_age_seconds: float) -> int:
        """Purge entries older than *max_age_seconds*.

        Returns the number of entries removed.
        """
        now = time.time()
        cutoff = now - max_age_seconds
        to_remove = [k for k, v in self._store.items() if v.cached_at < cutoff]
        for k in to_remove:
            del self._store[k]
        return len(to_remove)

    def invalidate_below(self, min_trust: HybridTrustLevel) -> int:
        """Purge entries whose trust level is strictly below *min_trust*.

        Returns the number of entries removed.
        """
        to_remove = [
            k for k, v in self._store.items() if v.trust_level < min_trust
        ]
        for k in to_remove:
            del self._store[k]
        return len(to_remove)

    def clear(self) -> None:
        """Remove all entries."""
        self._store.clear()

    # -- persistence ---------------------------------------------------

    def save(self, path: str) -> None:
        """Persist the cache to a JSON file at *path*."""
        payload = {
            "version": 1,
            "entries": [v.to_dict() for v in self._store.values()],
            "stats": self.stats(),
        }
        with open(path, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2, sort_keys=True)

    def load(self, path: str) -> int:
        """Load entries from a JSON file at *path*.

        Existing entries are *not* cleared; loaded entries are merged.
        Returns the number of entries loaded.
        """
        with open(path, "r", encoding="utf-8") as f:
            payload = json.load(f)
        count = 0
        for entry_d in payload.get("entries", []):
            entry = CachedTrust.from_dict(entry_d)
            key = self._key(entry.predicate_name, entry.content_hash)
            if key not in self._store:
                self._store[key] = entry
                count += 1
        return count

    # -- observability -------------------------------------------------

    def stats(self) -> Dict[str, int]:
        """Return cache hit/miss/eviction statistics."""
        return {
            "size": len(self._store),
            "max_size": self._max_size,
            "hits": self._hits,
            "misses": self._misses,
            "evictions": self._evictions,
            "hit_rate_pct": (
                round(100 * self._hits / (self._hits + self._misses))
                if (self._hits + self._misses) > 0
                else 0
            ),
        }

    def __len__(self) -> int:
        return len(self._store)

    def __repr__(self) -> str:
        s = self.stats()
        return (
            f"TrustCache(size={s['size']}/{s['max_size']}, "
            f"hit_rate={s['hit_rate_pct']}%)"
        )


# ═══════════════════════════════════════════════════════════════════
#  §9  TrustReport — human-readable trust summary
# ═══════════════════════════════════════════════════════════════════

@dataclass
class TrustReport:
    """Summary report of trust status across a set of obligations.

    Designed for both programmatic consumption (``to_dict``) and
    human-readable rendering (``to_markdown``).
    """

    overall_trust: HybridTrustLevel
    per_obligation: Dict[str, HybridTrustLevel]
    evidence_chain: EvidenceChain
    promotions_applied: List[TrustPromotion]
    demotions_applied: List[TrustDemotion]
    cache_stats: Dict[str, int]

    # -- markdown rendering --------------------------------------------

    def to_markdown(self) -> str:
        """Render a human-readable Markdown report."""
        lines: List[str] = []
        lines.append("# Trust Report")
        lines.append("")

        # Overall trust.
        lines.append(f"**Overall trust level:** `{self.overall_trust.name}`")
        lines.append("")

        # Per-obligation table.
        if self.per_obligation:
            lines.append("## Per-Obligation Trust")
            lines.append("")
            lines.append("| Obligation | Trust Level |")
            lines.append("|------------|-------------|")
            for name, level in sorted(self.per_obligation.items()):
                lines.append(f"| `{name}` | `{level.name}` |")
            lines.append("")

        # Evidence chain summary.
        lines.append("## Evidence Chain")
        lines.append("")
        chain_trust = self.evidence_chain.trust_level()
        lines.append(
            f"- **Nodes:** {len(self.evidence_chain)}"
        )
        lines.append(
            f"- **Depth:** {self.evidence_chain.depth()}"
        )
        lines.append(
            f"- **Chain trust:** `{chain_trust.name}`"
        )
        problems = self.evidence_chain.validate()
        if problems:
            lines.append(f"- **Validation issues:** {len(problems)}")
            for p in problems:
                lines.append(f"  - {p}")
        else:
            lines.append("- **Validation:** ✓ consistent")
        lines.append("")

        # Promotions.
        if self.promotions_applied:
            lines.append("## Promotions Applied")
            lines.append("")
            for promo in self.promotions_applied:
                lines.append(
                    f"- `{promo.from_level.name}` → `{promo.to_level.name}`: "
                    f"{promo.description}"
                )
            lines.append("")

        # Demotions.
        if self.demotions_applied:
            lines.append("## Demotions Applied")
            lines.append("")
            for demo in self.demotions_applied:
                lines.append(
                    f"- `{demo.from_level.name}` → `{demo.to_level.name}` "
                    f"(trigger: `{demo.trigger}`)"
                )
            lines.append("")

        # Cache stats.
        if self.cache_stats:
            lines.append("## Cache Statistics")
            lines.append("")
            for k, v in sorted(self.cache_stats.items()):
                lines.append(f"- **{k}:** {v}")
            lines.append("")

        return "\n".join(lines)

    # -- serialisation -------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        """Serialise to a JSON-friendly dictionary."""
        return {
            "overall_trust": self.overall_trust.value,
            "per_obligation": {
                name: level.value
                for name, level in self.per_obligation.items()
            },
            "evidence_chain": self.evidence_chain.to_dict(),
            "promotions_applied": [p.to_dict() for p in self.promotions_applied],
            "demotions_applied": [d.to_dict() for d in self.demotions_applied],
            "cache_stats": self.cache_stats,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> TrustReport:
        """Deserialise from a dictionary."""
        return cls(
            overall_trust=HybridTrustLevel(d["overall_trust"]),
            per_obligation={
                name: HybridTrustLevel(val)
                for name, val in d["per_obligation"].items()
            },
            evidence_chain=EvidenceChain.from_dict(d["evidence_chain"]),
            promotions_applied=[
                TrustPromotion.from_dict(p) for p in d["promotions_applied"]
            ],
            demotions_applied=[
                TrustDemotion.from_dict(dm) for dm in d["demotions_applied"]
            ],
            cache_stats=d.get("cache_stats", {}),
        )

    def __repr__(self) -> str:
        n_oblig = len(self.per_obligation)
        return (
            f"TrustReport(overall={self.overall_trust.name}, "
            f"obligations={n_oblig}, "
            f"promotions={len(self.promotions_applied)}, "
            f"demotions={len(self.demotions_applied)})"
        )


# ═══════════════════════════════════════════════════════════════════
#  §10  Convenience builders
# ═══════════════════════════════════════════════════════════════════

def build_report(
    obligations: Dict[str, Tuple[HybridTrustLevel, List[Evidence]]],
    lattice: Optional[TrustLattice] = None,
    cache: Optional[TrustCache] = None,
) -> TrustReport:
    """Build a :class:`TrustReport` from per-obligation data.

    Parameters
    ----------
    obligations:
        Mapping from obligation name to ``(current_trust, evidence_list)``.
    lattice:
        The trust lattice to use for promotion.  Defaults to a fresh
        instance with the standard rules.
    cache:
        Optional trust cache whose stats will be included in the report.

    Returns
    -------
    TrustReport
        A fully populated report with promotions applied.
    """
    lat = lattice or TrustLattice()

    per_obligation: Dict[str, HybridTrustLevel] = {}
    all_promotions: List[TrustPromotion] = []
    all_demotions: List[TrustDemotion] = []

    # Build the evidence chain rooted at a synthetic "overall" node.
    overall_content = "overall_trust_judgment"
    overall_evidence = Evidence.create(
        kind=EvidenceKind.ASSUMPTION,
        content=overall_content,
        source="trust_report_builder",
        trust_level=HybridTrustLevel.LEAN_VERIFIED,  # start optimistic
    )
    chain = EvidenceChain(root=overall_evidence)

    for name, (current, evidence_list) in obligations.items():
        promoted, fired = lat.promote_iterative(current, evidence_list)
        per_obligation[name] = promoted
        all_promotions.extend(fired)

        # Add each piece of evidence to the chain.
        for ev in evidence_list:
            chain.add_root_support(ev)

    # Overall trust is the meet across all obligations.
    if per_obligation:
        overall = HybridTrustLevel.LEAN_VERIFIED
        for lvl in per_obligation.values():
            overall = overall.meet(lvl)
    else:
        overall = HybridTrustLevel.UNTRUSTED

    cache_stats = cache.stats() if cache is not None else {}

    return TrustReport(
        overall_trust=overall,
        per_obligation=per_obligation,
        evidence_chain=chain,
        promotions_applied=all_promotions,
        demotions_applied=all_demotions,
        cache_stats=cache_stats,
    )


def promote_with_cache(
    predicate_name: str,
    content: str,
    current: HybridTrustLevel,
    evidence: List[Evidence],
    lattice: TrustLattice,
    cache: TrustCache,
) -> Tuple[HybridTrustLevel, bool]:
    """Promote with cache-first lookup.

    Returns ``(trust_level, was_cached)``.  If the cache contains a
    valid entry at or above the level the promotion engine would
    produce, the cached value is returned without re-running the
    engine.
    """
    ch = _content_hash(content)
    cached = cache.get(predicate_name, ch)
    if cached is not None and cached.trust_level >= current:
        return cached.trust_level, True

    promoted = lattice.promote(current, evidence)

    # Store the promoted level if we have evidence to back it.
    if evidence:
        cache.put(predicate_name, ch, promoted, evidence[0])

    return promoted, False


# ═══════════════════════════════════════════════════════════════════
#  §11  Module-level exports
# ═══════════════════════════════════════════════════════════════════

__all__ = [
    # Enums
    "HybridTrustLevel",
    "EvidenceKind",
    # Data classes
    "Evidence",
    "EvidenceChain",
    "TrustPromotion",
    "TrustDemotion",
    "CachedTrust",
    "TrustReport",
    # Rule sets
    "PROMOTION_RULES",
    "DEMOTION_RULES",
    # Classes
    "TrustLattice",
    "TrustCache",
    # Builders
    "build_report",
    "promote_with_cache",
]
