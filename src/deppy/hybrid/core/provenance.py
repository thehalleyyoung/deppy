"""Provenance tracking for the hybrid dependent type system.

Grounded in algebraic geometry: provenance forms a DAG (a category of
derivations), and hallucination detection is finding where a provenance
path exits the "grounded" sub-presheaf.

Extends ``comet_verified.py``'s ``TaintedValue`` and ``ProvenanceRecord``
concepts but makes provenance first-class in the type system.  Every
artifact carries a node in the provenance graph; derivation edges record
how artifacts are composed.  The "grounded" sub-presheaf is the full
sub-DAG whose nodes are all HUMAN_AUTHORED, LEAN_PROVED, or Z3_DERIVED.
A hallucination trace is a witness that a particular node lies *outside*
this sub-presheaf — i.e., its ancestry contains at least one
LLM_GENERATED node that has not been verified.

Drift detection operates on the morphism level: when two layers of a
``HybridType`` diverge, we record a ``DriftEvent`` and quantify its
severity via a normalised Hamming-like distance on content hashes.
"""

from __future__ import annotations

import hashlib
import json
import uuid
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum, auto
from pathlib import Path
from typing import Any


# ═══════════════════════════════════════════════════════════════════
#  ProvenanceKind — taxonomy of derivation origins
# ═══════════════════════════════════════════════════════════════════


# --- Integration with existing deppy codebase ---
try:
    from deppy.core.provenance_tracker import ProvenanceTracker as _CoreProvenanceTracker
    from deppy.core._protocols import TrustLevel as _CoreTrustLevel, SiteId
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

class ProvenanceKind(Enum):
    """How an artifact was produced.

    The ordering roughly tracks trust: HUMAN_AUTHORED and LEAN_PROVED
    are fully grounded; LLM_GENERATED is *not* grounded until verified;
    TRANSPORTED and COMPOSED inherit grounding from their inputs.
    """

    HUMAN_AUTHORED = auto()
    LLM_GENERATED = auto()
    Z3_DERIVED = auto()
    LEAN_PROVED = auto()
    RUNTIME_OBSERVED = auto()
    TRANSPORTED = auto()
    COMPOSED = auto()
    CACHED = auto()


# The set of kinds that are intrinsically grounded (need no parents).
_GROUNDED_KINDS: frozenset[ProvenanceKind] = frozenset({
    ProvenanceKind.HUMAN_AUTHORED,
    ProvenanceKind.LEAN_PROVED,
    ProvenanceKind.Z3_DERIVED,
})


# ═══════════════════════════════════════════════════════════════════
#  ProvenanceNode — a single point in the derivation DAG
# ═══════════════════════════════════════════════════════════════════

def _content_hash(value: Any) -> str:
    """Deterministic SHA-256 prefix for any JSON-serialisable value."""
    raw = json.dumps(value, sort_keys=True, default=str)
    return hashlib.sha256(raw.encode()).hexdigest()[:16]


@dataclass
class ProvenanceNode:
    """A single node in the provenance DAG.

    Each node represents an *artifact* together with metadata about how
    it was produced.  The ``input_hashes`` tuple links this node to its
    immediate parents in the derivation graph.

    Attributes
    ----------
    id : str
        Unique UUID for this node.
    kind : ProvenanceKind
        How the artifact was produced.
    content_hash : str
        SHA-256 prefix of the artifact's serialised form.
    stage : str
        Pipeline stage that produced this artifact (e.g. "synthesis").
    timestamp : str
        ISO-8601 timestamp of creation.
    source_model : str | None
        LLM model identifier when ``kind`` is ``LLM_GENERATED``.
    input_hashes : tuple[str, ...]
        Content hashes of the parent artifacts.
    description : str
        Human-readable description of the derivation step.
    trust_level : str
        Name from the trust lattice (e.g. ``"VERIFIED"``).
    metadata : dict[str, Any]
        Arbitrary extra metadata (temperatures, prompts, …).
    """

    id: str = field(default_factory=lambda: uuid.uuid4().hex[:16])
    kind: ProvenanceKind = ProvenanceKind.HUMAN_AUTHORED
    content_hash: str = ""
    stage: str = ""
    timestamp: str = field(
        default_factory=lambda: datetime.now(timezone.utc).isoformat()
    )
    source_model: str | None = None
    input_hashes: tuple[str, ...] = ()
    description: str = ""
    trust_level: str = "UNKNOWN"
    metadata: dict[str, Any] = field(default_factory=dict)

    # ------------------------------------------------------------------
    # Serialisation
    # ------------------------------------------------------------------

    def to_dict(self) -> dict[str, Any]:
        """Serialise to a plain dictionary."""
        return {
            "id": self.id,
            "kind": self.kind.name,
            "content_hash": self.content_hash,
            "stage": self.stage,
            "timestamp": self.timestamp,
            "source_model": self.source_model,
            "input_hashes": list(self.input_hashes),
            "description": self.description,
            "trust_level": self.trust_level,
            "metadata": self.metadata,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> ProvenanceNode:
        """Reconstruct a node from its dictionary representation."""
        return cls(
            id=data["id"],
            kind=ProvenanceKind[data["kind"]],
            content_hash=data.get("content_hash", ""),
            stage=data.get("stage", ""),
            timestamp=data.get("timestamp", ""),
            source_model=data.get("source_model"),
            input_hashes=tuple(data.get("input_hashes", ())),
            description=data.get("description", ""),
            trust_level=data.get("trust_level", "UNKNOWN"),
            metadata=data.get("metadata", {}),
        )

    # ------------------------------------------------------------------
    # Grounding (local check — does NOT inspect parents)
    # ------------------------------------------------------------------

    def is_grounded(self) -> bool:
        """Return ``True`` if this node is *intrinsically* grounded.

        A node is intrinsically grounded when its kind belongs to the
        set ``{HUMAN_AUTHORED, LEAN_PROVED, Z3_DERIVED}``.  For kinds
        like ``COMPOSED`` or ``TRANSPORTED``, grounding depends on
        ancestors (see ``ProvenanceGraph.is_grounded``).
        """
        return self.kind in _GROUNDED_KINDS

    def __hash__(self) -> int:  # noqa: D105
        return hash(self.id)

    def __eq__(self, other: object) -> bool:  # noqa: D105
        if not isinstance(other, ProvenanceNode):
            return NotImplemented
        return self.id == other.id


# ═══════════════════════════════════════════════════════════════════
#  ProvenanceGraph — the full derivation DAG
# ═══════════════════════════════════════════════════════════════════

class ProvenanceGraph:
    """Directed acyclic graph of provenance derivations.

    Nodes are ``ProvenanceNode`` instances; edges point from a derived
    artifact to each of its inputs.  The graph exposes standard DAG
    operations: root / leaf queries, transitive closure (ancestors /
    descendants), shortest-path search, and sub-graph extraction.

    Serialisation to / from JSON and `Graphviz DOT`_ format is included
    so the graph can be inspected visually.
    """

    def __init__(self) -> None:
        self.nodes: dict[str, ProvenanceNode] = {}
        self.edges: dict[str, list[str]] = {}
        # Reverse adjacency for efficient descendant queries.
        self._reverse_edges: dict[str, list[str]] = {}
        # Index: content_hash → node ids.
        self._hash_index: dict[str, list[str]] = {}

    # ------------------------------------------------------------------
    # Mutation
    # ------------------------------------------------------------------

    def add_node(self, node: ProvenanceNode) -> None:
        """Insert a node, updating all indexes."""
        if node.id in self.nodes:
            return
        self.nodes[node.id] = node
        self.edges.setdefault(node.id, [])
        self._reverse_edges.setdefault(node.id, [])
        self._hash_index.setdefault(node.content_hash, []).append(node.id)

    def add_edge(self, from_id: str, to_id: str) -> None:
        """Add a derivation edge: *from_id* was derived using *to_id*.

        Parameters
        ----------
        from_id : str
            The derived (child) node.
        to_id : str
            The input (parent) node.
        """
        if from_id not in self.nodes or to_id not in self.nodes:
            raise KeyError(
                f"Both endpoints must exist in the graph: "
                f"{from_id!r}, {to_id!r}"
            )
        if to_id not in self.edges[from_id]:
            self.edges[from_id].append(to_id)
        if from_id not in self._reverse_edges[to_id]:
            self._reverse_edges[to_id].append(from_id)

    def nodes_for_hash(self, content_hash: str) -> list[ProvenanceNode]:
        """Return all nodes whose artifact has the given content hash."""
        return [
            self.nodes[nid]
            for nid in self._hash_index.get(content_hash, [])
            if nid in self.nodes
        ]

    # ------------------------------------------------------------------
    # Structural queries
    # ------------------------------------------------------------------

    def roots(self) -> list[ProvenanceNode]:
        """Nodes with no incoming edges (axioms / human-authored)."""
        return [
            node
            for nid, node in self.nodes.items()
            if not self.edges.get(nid)
        ]

    def leaves(self) -> list[ProvenanceNode]:
        """Nodes that no other node depends on."""
        return [
            node
            for nid, node in self.nodes.items()
            if not self._reverse_edges.get(nid)
        ]

    def ancestors(self, node_id: str) -> set[str]:
        """Transitive closure of input edges (all ancestors).

        Uses iterative BFS to avoid stack overflows on deep DAGs.
        """
        visited: set[str] = set()
        queue: deque[str] = deque(self.edges.get(node_id, []))
        while queue:
            nid = queue.popleft()
            if nid in visited:
                continue
            visited.add(nid)
            queue.extend(self.edges.get(nid, []))
        return visited

    def descendants(self, node_id: str) -> set[str]:
        """Transitive closure of reverse edges (all descendants)."""
        visited: set[str] = set()
        queue: deque[str] = deque(self._reverse_edges.get(node_id, []))
        while queue:
            nid = queue.popleft()
            if nid in visited:
                continue
            visited.add(nid)
            queue.extend(self._reverse_edges.get(nid, []))
        return visited

    def path(self, from_id: str, to_id: str) -> list[str] | None:
        """Shortest derivation path from *from_id* back to *to_id*.

        Follows input edges (parent direction).  Returns ``None`` when
        no path exists.  The returned list includes both endpoints.
        """
        if from_id == to_id:
            return [from_id]
        visited: set[str] = set()
        queue: deque[list[str]] = deque([[from_id]])
        while queue:
            current_path = queue.popleft()
            current = current_path[-1]
            if current in visited:
                continue
            visited.add(current)
            for parent_id in self.edges.get(current, []):
                new_path = current_path + [parent_id]
                if parent_id == to_id:
                    return new_path
                queue.append(new_path)
        return None

    # ------------------------------------------------------------------
    # Grounding analysis
    # ------------------------------------------------------------------

    def is_grounded(self, node_id: str) -> bool:
        """Return ``True`` iff the node and ALL its ancestors are grounded.

        A node is grounded when its kind is intrinsically grounded
        (HUMAN_AUTHORED, LEAN_PROVED, Z3_DERIVED) *and* every ancestor
        is also grounded.  This is the characteristic function of the
        "grounded sub-presheaf".
        """
        node = self.nodes.get(node_id)
        if node is None:
            return False
        # Check the node itself.
        if not node.is_grounded():
            return False
        # BFS through ancestors — every one must be intrinsically grounded.
        for ancestor_id in self.ancestors(node_id):
            ancestor = self.nodes.get(ancestor_id)
            if ancestor is None or not ancestor.is_grounded():
                return False
        return True

    def ungrounded_frontier(self, node_id: str) -> set[str]:
        """Identify the *first* ungrounded nodes in the ancestry.

        These are the "hallucination sources": the boundary between the
        grounded sub-presheaf and the rest of the DAG.  Formally, a
        node *n* is on the frontier iff:

        * *n* is NOT intrinsically grounded, AND
        * every input of *n* that is not intrinsically grounded is
          itself on the frontier (i.e., *n* is the earliest
          ungrounded node along each branch).

        The implementation uses BFS from *node_id* upward and stops
        expanding along a branch as soon as it hits an ungrounded node.
        """
        frontier: set[str] = set()
        node = self.nodes.get(node_id)
        if node is None:
            return frontier

        visited: set[str] = set()
        queue: deque[str] = deque([node_id])
        while queue:
            nid = queue.popleft()
            if nid in visited:
                continue
            visited.add(nid)
            current = self.nodes.get(nid)
            if current is None:
                continue
            if not current.is_grounded():
                # This node is ungrounded — it's on the frontier.
                # Do NOT expand further along this branch.
                frontier.add(nid)
            else:
                # Grounded node — keep searching its parents.
                queue.extend(self.edges.get(nid, []))
        return frontier

    # ------------------------------------------------------------------
    # Sub-graph extraction
    # ------------------------------------------------------------------

    def subgraph(self, node_ids: set[str]) -> ProvenanceGraph:
        """Extract an induced subgraph containing only *node_ids*."""
        sg = ProvenanceGraph()
        for nid in node_ids:
            node = self.nodes.get(nid)
            if node is not None:
                sg.add_node(node)
        for nid in node_ids:
            for parent_id in self.edges.get(nid, []):
                if parent_id in node_ids:
                    sg.add_edge(nid, parent_id)
        return sg

    # ------------------------------------------------------------------
    # Serialisation
    # ------------------------------------------------------------------

    def to_dict(self) -> dict[str, Any]:
        """Serialise the entire graph to a JSON-compatible dict."""
        return {
            "nodes": {nid: n.to_dict() for nid, n in self.nodes.items()},
            "edges": {nid: list(parents) for nid, parents in self.edges.items()},
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> ProvenanceGraph:
        """Reconstruct a graph from its dict representation."""
        g = cls()
        for nid, ndata in data.get("nodes", {}).items():
            g.add_node(ProvenanceNode.from_dict(ndata))
        for nid, parents in data.get("edges", {}).items():
            for pid in parents:
                if nid in g.nodes and pid in g.nodes:
                    g.add_edge(nid, pid)
        return g

    # ------------------------------------------------------------------
    # Visualisation (Graphviz DOT)
    # ------------------------------------------------------------------

    _KIND_COLORS: dict[ProvenanceKind, str] = {
        ProvenanceKind.HUMAN_AUTHORED: "green",
        ProvenanceKind.LLM_GENERATED: "red",
        ProvenanceKind.Z3_DERIVED: "blue",
        ProvenanceKind.LEAN_PROVED: "darkgreen",
        ProvenanceKind.RUNTIME_OBSERVED: "orange",
        ProvenanceKind.TRANSPORTED: "purple",
        ProvenanceKind.COMPOSED: "gray",
        ProvenanceKind.CACHED: "lightblue",
    }

    def to_dot(self) -> str:
        """Render the graph in Graphviz DOT format.

        Node colour encodes ``ProvenanceKind``; grounded nodes use a
        double-circle shape.
        """
        lines: list[str] = ["digraph provenance {", "  rankdir=BT;"]
        for nid, node in self.nodes.items():
            color = self._KIND_COLORS.get(node.kind, "black")
            shape = "doublecircle" if self.is_grounded(nid) else "ellipse"
            label = (
                f"{node.kind.name}\\n"
                f"{node.stage}\\n"
                f"{node.content_hash[:8]}"
            )
            lines.append(
                f'  "{nid}" [label="{label}", '
                f'color="{color}", shape="{shape}"];'
            )
        for nid, parents in self.edges.items():
            for pid in parents:
                lines.append(f'  "{nid}" -> "{pid}";')
        lines.append("}")
        return "\n".join(lines)

    def __len__(self) -> int:  # noqa: D105
        return len(self.nodes)

    def __contains__(self, node_id: str) -> bool:  # noqa: D105
        return node_id in self.nodes


# ═══════════════════════════════════════════════════════════════════
#  HallucinationTrace — a witness that an artifact is ungrounded
# ═══════════════════════════════════════════════════════════════════

@dataclass
class HallucinationTrace:
    """Evidence that an artifact's provenance exits the grounded sub-presheaf.

    A trace records:
    * **what** was found (``finding``),
    * **which** artifact is hallucinated (``artifact_hash``),
    * **where** the hallucination originates (``origin_nodes``), and
    * **how** it propagated (``derivation_path``).

    Severity levels follow the standard scale:
    ``CRITICAL > HIGH > MEDIUM > LOW``.
    """

    finding: str
    artifact_hash: str
    origin_nodes: list[ProvenanceNode] = field(default_factory=list)
    derivation_path: list[ProvenanceNode] = field(default_factory=list)
    severity: str = "MEDIUM"

    # ------------------------------------------------------------------
    # Serialisation
    # ------------------------------------------------------------------

    def to_dict(self) -> dict[str, Any]:
        """Serialise to a plain dictionary."""
        return {
            "finding": self.finding,
            "artifact_hash": self.artifact_hash,
            "origin_nodes": [n.to_dict() for n in self.origin_nodes],
            "derivation_path": [n.to_dict() for n in self.derivation_path],
            "severity": self.severity,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> HallucinationTrace:
        """Reconstruct from dict."""
        return cls(
            finding=data["finding"],
            artifact_hash=data["artifact_hash"],
            origin_nodes=[
                ProvenanceNode.from_dict(n) for n in data.get("origin_nodes", [])
            ],
            derivation_path=[
                ProvenanceNode.from_dict(n)
                for n in data.get("derivation_path", [])
            ],
            severity=data.get("severity", "MEDIUM"),
        )

    # ------------------------------------------------------------------
    # Markdown report
    # ------------------------------------------------------------------

    def to_markdown(self) -> str:
        """Render the trace as a Markdown snippet for human review."""
        lines: list[str] = [
            f"### Hallucination Trace — severity **{self.severity}**",
            "",
            f"**Finding:** {self.finding}",
            f"**Artifact hash:** `{self.artifact_hash}`",
            "",
        ]
        if self.origin_nodes:
            lines.append("#### Origin nodes (hallucination sources)")
            lines.append("")
            for node in self.origin_nodes:
                lines.append(
                    f"- `{node.id}` — {node.kind.name} "
                    f"(stage: {node.stage}, model: {node.source_model or 'N/A'})"
                )
            lines.append("")
        if self.derivation_path:
            lines.append("#### Derivation path")
            lines.append("")
            for i, node in enumerate(self.derivation_path):
                prefix = "→" if i > 0 else "⊢"
                lines.append(
                    f"  {prefix} `{node.id}` {node.kind.name} "
                    f"[{node.stage}] {node.description}"
                )
            lines.append("")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
#  DriftEvent / DriftDetector — inter-layer divergence tracking
# ═══════════════════════════════════════════════════════════════════

@dataclass
class DriftEvent:
    """A single divergence between two layers of a HybridType.

    When the intent layer says "sort ascending" but the code layer
    implements descending sort, a ``DriftEvent`` is recorded with
    ``layer_a="intent"`` and ``layer_b="code"``.

    Attributes
    ----------
    layer_a, layer_b : str
        The two layers that diverged (e.g. "intent", "code").
    old_hash_a, new_hash_a : str
        Content hashes of layer A before and after the change.
    old_hash_b, new_hash_b : str
        Content hashes of layer B before and after the change.
    description : str
        Human-readable summary.
    timestamp : str
        ISO-8601 timestamp.
    is_reconciled : bool
        Whether this drift has been resolved.
    """

    layer_a: str
    layer_b: str
    old_hash_a: str
    new_hash_a: str
    old_hash_b: str
    new_hash_b: str
    description: str = ""
    timestamp: str = field(
        default_factory=lambda: datetime.now(timezone.utc).isoformat()
    )
    is_reconciled: bool = False

    # ------------------------------------------------------------------
    # Serialisation
    # ------------------------------------------------------------------

    def to_dict(self) -> dict[str, Any]:
        """Serialise to a plain dictionary."""
        return {
            "layer_a": self.layer_a,
            "layer_b": self.layer_b,
            "old_hash_a": self.old_hash_a,
            "new_hash_a": self.new_hash_a,
            "old_hash_b": self.old_hash_b,
            "new_hash_b": self.new_hash_b,
            "description": self.description,
            "timestamp": self.timestamp,
            "is_reconciled": self.is_reconciled,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> DriftEvent:
        """Reconstruct from dict."""
        return cls(
            layer_a=data["layer_a"],
            layer_b=data["layer_b"],
            old_hash_a=data["old_hash_a"],
            new_hash_a=data["new_hash_a"],
            old_hash_b=data["old_hash_b"],
            new_hash_b=data["new_hash_b"],
            description=data.get("description", ""),
            timestamp=data.get("timestamp", ""),
            is_reconciled=data.get("is_reconciled", False),
        )


class DriftDetector:
    """Detects and records inter-layer drift events.

    A ``HybridType`` (or any layered artifact) has multiple "layers"
    (intent, spec, code, proof, test, …).  When one layer is updated
    without propagating the change to the others, the layers *drift*
    apart.  ``DriftDetector`` compares old and new versions to find
    mismatches, records them, and lets callers mark them reconciled.
    """

    def __init__(self) -> None:
        self.history: list[DriftEvent] = []

    # ------------------------------------------------------------------
    # Detection
    # ------------------------------------------------------------------

    def detect(
        self,
        old_type: dict[str, str],
        new_type: dict[str, str],
    ) -> list[DriftEvent]:
        """Compare two snapshots of a layered artifact and emit drift events.

        Each snapshot is a ``{layer_name: content_hash}`` mapping.
        A drift event is created for every pair of layers ``(a, b)``
        where *a* changed but *b* did not (or vice-versa).

        Parameters
        ----------
        old_type : dict[str, str]
            Previous content hashes keyed by layer name.
        new_type : dict[str, str]
            Current content hashes keyed by layer name.

        Returns
        -------
        list[DriftEvent]
            Newly created drift events (also appended to ``self.history``).
        """
        all_layers = sorted(set(old_type.keys()) | set(new_type.keys()))
        changed_layers: set[str] = set()
        unchanged_layers: set[str] = set()

        for layer in all_layers:
            old_h = old_type.get(layer, "")
            new_h = new_type.get(layer, "")
            if old_h != new_h:
                changed_layers.add(layer)
            else:
                unchanged_layers.add(layer)

        events: list[DriftEvent] = []
        # For every (changed, unchanged) pair we emit a drift event.
        for changed in sorted(changed_layers):
            for unchanged in sorted(unchanged_layers):
                event = DriftEvent(
                    layer_a=changed,
                    layer_b=unchanged,
                    old_hash_a=old_type.get(changed, ""),
                    new_hash_a=new_type.get(changed, ""),
                    old_hash_b=old_type.get(unchanged, ""),
                    new_hash_b=new_type.get(unchanged, ""),
                    description=(
                        f"Layer '{changed}' changed but '{unchanged}' "
                        f"was not updated"
                    ),
                )
                events.append(event)
                self.history.append(event)

        return events

    # ------------------------------------------------------------------
    # Severity quantification
    # ------------------------------------------------------------------

    @staticmethod
    def drift_distance(event: DriftEvent) -> float:
        """Quantify drift severity on a ``[0.0, 1.0]`` scale.

        The metric is a normalised Hamming-like distance between the
        old and new content hashes of both layers.

        * ``0.0`` — no drift (both layers unchanged or both changed
          identically).
        * ``1.0`` — complete divergence (one layer totally replaced
          while the other is unchanged).

        The formula counts how many of the four hashes are "out of
        sync": specifically, how many nibble positions differ across
        the combined hash strings, normalised by total length.
        """
        combined_old = event.old_hash_a + event.old_hash_b
        combined_new = event.new_hash_a + event.new_hash_b
        if not combined_old and not combined_new:
            return 0.0

        max_len = max(len(combined_old), len(combined_new))
        padded_old = combined_old.ljust(max_len, "0")
        padded_new = combined_new.ljust(max_len, "0")

        diffs = sum(a != b for a, b in zip(padded_old, padded_new))
        return diffs / max_len if max_len > 0 else 0.0

    # ------------------------------------------------------------------
    # Lifecycle
    # ------------------------------------------------------------------

    def unreconciled(self) -> list[DriftEvent]:
        """Return all events that have not been reconciled."""
        return [e for e in self.history if not e.is_reconciled]

    def reconcile(self, event_index: int) -> None:
        """Mark the event at *event_index* as reconciled.

        Raises
        ------
        IndexError
            If the index is out of range.
        """
        if event_index < 0 or event_index >= len(self.history):
            raise IndexError(
                f"Event index {event_index} out of range "
                f"[0, {len(self.history)})"
            )
        self.history[event_index].is_reconciled = True

    # ------------------------------------------------------------------
    # Serialisation
    # ------------------------------------------------------------------

    def to_dict(self) -> dict[str, Any]:
        """Serialise full history."""
        return {"history": [e.to_dict() for e in self.history]}

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> DriftDetector:
        """Reconstruct from dict."""
        dd = cls()
        dd.history = [
            DriftEvent.from_dict(e) for e in data.get("history", [])
        ]
        return dd


# ═══════════════════════════════════════════════════════════════════
#  ProvenanceReport — summary of the provenance state
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProvenanceReport:
    """Aggregate report over the current provenance state.

    Collects node counts, hallucination traces, and drift events into
    a single snapshot suitable for CI dashboards or human review.
    """

    total_nodes: int = 0
    grounded_nodes: int = 0
    ungrounded_nodes: int = 0
    hallucination_traces: list[HallucinationTrace] = field(default_factory=list)
    drift_events: list[DriftEvent] = field(default_factory=list)

    # ------------------------------------------------------------------
    # Serialisation
    # ------------------------------------------------------------------

    def to_dict(self) -> dict[str, Any]:
        """Serialise to a plain dictionary."""
        return {
            "total_nodes": self.total_nodes,
            "grounded_nodes": self.grounded_nodes,
            "ungrounded_nodes": self.ungrounded_nodes,
            "hallucination_traces": [
                t.to_dict() for t in self.hallucination_traces
            ],
            "drift_events": [e.to_dict() for e in self.drift_events],
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> ProvenanceReport:
        """Reconstruct from dict."""
        return cls(
            total_nodes=data.get("total_nodes", 0),
            grounded_nodes=data.get("grounded_nodes", 0),
            ungrounded_nodes=data.get("ungrounded_nodes", 0),
            hallucination_traces=[
                HallucinationTrace.from_dict(t)
                for t in data.get("hallucination_traces", [])
            ],
            drift_events=[
                DriftEvent.from_dict(e)
                for e in data.get("drift_events", [])
            ],
        )

    # ------------------------------------------------------------------
    # Markdown
    # ------------------------------------------------------------------

    def to_markdown(self) -> str:
        """Render the full report as Markdown."""
        lines: list[str] = [
            "# Provenance Report",
            "",
            "## Summary",
            "",
            f"| Metric | Count |",
            f"|--------|-------|",
            f"| Total nodes | {self.total_nodes} |",
            f"| Grounded | {self.grounded_nodes} |",
            f"| Ungrounded | {self.ungrounded_nodes} |",
            f"| Hallucination traces | {len(self.hallucination_traces)} |",
            f"| Drift events | {len(self.drift_events)} |",
            "",
        ]

        if self.hallucination_traces:
            lines.append("## Hallucination Traces")
            lines.append("")
            for i, trace in enumerate(self.hallucination_traces, 1):
                lines.append(f"### Trace {i}")
                lines.append("")
                lines.append(trace.to_markdown())

        if self.drift_events:
            lines.append("## Drift Events")
            lines.append("")
            for i, event in enumerate(self.drift_events, 1):
                status = "✅ reconciled" if event.is_reconciled else "⚠️ open"
                lines.append(
                    f"{i}. **{event.layer_a} ↔ {event.layer_b}**: "
                    f"{event.description} ({status})"
                )
            lines.append("")

        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
#  ProvenanceTracker — the main entry-point composing all components
# ═══════════════════════════════════════════════════════════════════

class ProvenanceTracker(_CoreProvenanceTracker if _HAS_DEPPY_CORE else object):
    """High-level provenance tracker composing graph, drift, and reporting.

    Extends the core ``ProvenanceTracker`` when available, adding hybrid-layer
    provenance graph, drift detection, and hallucination tracing.

    This is the primary API surface for callers.  Usage pattern::

        tracker = ProvenanceTracker()

        # Record an artifact authored by a human.
        n1 = tracker.record(
            artifact={"spec": "sort ascending"},
            kind=ProvenanceKind.HUMAN_AUTHORED,
            stage="spec",
        )

        # Derive a new artifact from it via LLM.
        n2 = tracker.derive(
            parent_hashes=[n1.content_hash],
            new_artifact={"code": "xs.sort()"},
            stage="codegen",
            kind=ProvenanceKind.LLM_GENERATED,
            source_model="gpt-4",
        )

        # Check whether n2 is fully grounded.
        assert not tracker.check_grounding(n2.content_hash)

        # Trace the hallucination source.
        trace = tracker.trace_hallucination(n2.content_hash)
        print(trace.to_markdown())
    """

    def __init__(self) -> None:
        self.graph = ProvenanceGraph()
        self.drift_detector = DriftDetector()

    # ------------------------------------------------------------------
    # Recording
    # ------------------------------------------------------------------

    def record(
        self,
        artifact: Any,
        kind: ProvenanceKind,
        stage: str,
        inputs: list[str] | None = None,
        *,
        source_model: str | None = None,
        description: str = "",
        trust_level: str = "UNKNOWN",
        metadata: dict[str, Any] | None = None,
    ) -> ProvenanceNode:
        """Record a new artifact in the provenance graph.

        Parameters
        ----------
        artifact : Any
            The JSON-serialisable artifact value.
        kind : ProvenanceKind
            How the artifact was produced.
        stage : str
            Pipeline stage name.
        inputs : list[str] | None
            Content hashes of parent artifacts (if any).
        source_model : str | None
            LLM model identifier (when ``kind`` is ``LLM_GENERATED``).
        description : str
            Human-readable description of the step.
        trust_level : str
            Trust level name from the lattice.
        metadata : dict[str, Any] | None
            Extra metadata.

        Returns
        -------
        ProvenanceNode
            The newly created provenance node.
        """
        chash = _content_hash(artifact)
        input_hashes = tuple(inputs) if inputs else ()

        node = ProvenanceNode(
            kind=kind,
            content_hash=chash,
            stage=stage,
            source_model=source_model,
            input_hashes=input_hashes,
            description=description,
            trust_level=trust_level,
            metadata=metadata or {},
        )
        self.graph.add_node(node)

        # Wire up edges to parent nodes by matching content hashes.
        for ih in input_hashes:
            parent_nodes = self.graph.nodes_for_hash(ih)
            for parent in parent_nodes:
                if parent.id != node.id:
                    self.graph.add_edge(node.id, parent.id)

        return node

    def derive(
        self,
        parent_hashes: list[str],
        new_artifact: Any,
        stage: str,
        *,
        kind: ProvenanceKind = ProvenanceKind.COMPOSED,
        source_model: str | None = None,
        description: str = "",
        trust_level: str = "UNKNOWN",
        metadata: dict[str, Any] | None = None,
    ) -> ProvenanceNode:
        """Derive a new artifact from one or more existing artifacts.

        This is syntactic sugar around ``record`` that makes the parent
        relationship explicit.

        Parameters
        ----------
        parent_hashes : list[str]
            Content hashes of the parent artifacts.
        new_artifact : Any
            The derived artifact value.
        stage : str
            Pipeline stage.
        kind : ProvenanceKind
            Derivation kind (defaults to COMPOSED).
        source_model : str | None
            LLM model if applicable.
        description : str
            Human-readable description.
        trust_level : str
            Trust level name.
        metadata : dict[str, Any] | None
            Extra metadata.

        Returns
        -------
        ProvenanceNode
            The newly created provenance node.
        """
        return self.record(
            artifact=new_artifact,
            kind=kind,
            stage=stage,
            inputs=parent_hashes,
            source_model=source_model,
            description=description,
            trust_level=trust_level,
            metadata=metadata,
        )

    # ------------------------------------------------------------------
    # Hallucination tracing
    # ------------------------------------------------------------------

    def trace_hallucination(
        self, artifact_hash: str
    ) -> HallucinationTrace | None:
        """Trace a suspected hallucination back to its ungrounded sources.

        If the artifact is fully grounded, returns ``None``.  Otherwise,
        constructs a ``HallucinationTrace`` that identifies the frontier
        of ungrounded nodes and the shortest derivation path from the
        artifact to each origin.

        Parameters
        ----------
        artifact_hash : str
            Content hash of the artifact to investigate.

        Returns
        -------
        HallucinationTrace | None
            The trace, or ``None`` if the artifact is grounded.
        """
        target_nodes = self.graph.nodes_for_hash(artifact_hash)
        if not target_nodes:
            return None

        target = target_nodes[0]

        if self.graph.is_grounded(target.id):
            return None

        # Find the frontier of ungrounded ancestors.
        frontier_ids = self.graph.ungrounded_frontier(target.id)
        origin_nodes = [
            self.graph.nodes[fid]
            for fid in frontier_ids
            if fid in self.graph.nodes
        ]

        # Build the derivation path from the target to the first origin.
        derivation_path: list[ProvenanceNode] = []
        if origin_nodes:
            path_ids = self.graph.path(target.id, origin_nodes[0].id)
            if path_ids:
                derivation_path = [
                    self.graph.nodes[pid]
                    for pid in path_ids
                    if pid in self.graph.nodes
                ]

        # Determine severity based on origin kind and distance.
        severity = self._classify_severity(origin_nodes, derivation_path)

        origin_descriptions = ", ".join(
            f"{n.kind.name}@{n.stage}" for n in origin_nodes
        )
        finding = (
            f"Artifact {artifact_hash[:8]}… is ungrounded.  "
            f"Hallucination sources: {origin_descriptions}"
        )

        return HallucinationTrace(
            finding=finding,
            artifact_hash=artifact_hash,
            origin_nodes=origin_nodes,
            derivation_path=derivation_path,
            severity=severity,
        )

    @staticmethod
    def _classify_severity(
        origins: list[ProvenanceNode],
        path: list[ProvenanceNode],
    ) -> str:
        """Heuristic severity classification.

        * CRITICAL — any origin is LLM_GENERATED with no verification.
        * HIGH — multiple ungrounded origins.
        * MEDIUM — single ungrounded origin, short derivation path.
        * LOW — ungrounded but cached / transported.
        """
        if not origins:
            return "LOW"
        llm_origins = [
            n for n in origins if n.kind == ProvenanceKind.LLM_GENERATED
        ]
        if llm_origins:
            return "CRITICAL"
        if len(origins) > 1:
            return "HIGH"
        cached_or_transported = all(
            n.kind in (ProvenanceKind.CACHED, ProvenanceKind.TRANSPORTED)
            for n in origins
        )
        if cached_or_transported:
            return "LOW"
        return "MEDIUM"

    # ------------------------------------------------------------------
    # Grounding check
    # ------------------------------------------------------------------

    def check_grounding(self, artifact_hash: str) -> bool:
        """Return ``True`` iff the artifact is fully grounded.

        An artifact is fully grounded when every node in its ancestry
        is intrinsically grounded (HUMAN_AUTHORED, LEAN_PROVED, or
        Z3_DERIVED).
        """
        target_nodes = self.graph.nodes_for_hash(artifact_hash)
        if not target_nodes:
            return False
        return all(
            self.graph.is_grounded(n.id) for n in target_nodes
        )

    # ------------------------------------------------------------------
    # Drift detection (delegates to DriftDetector)
    # ------------------------------------------------------------------

    def detect_drift(
        self,
        old_type: dict[str, str],
        new_type: dict[str, str],
    ) -> list[DriftEvent]:
        """Compare two type snapshots and record any drift events.

        Parameters
        ----------
        old_type : dict[str, str]
            Layer-name → content-hash mapping for the previous version.
        new_type : dict[str, str]
            Layer-name → content-hash mapping for the current version.

        Returns
        -------
        list[DriftEvent]
            Newly detected drift events.
        """
        return self.drift_detector.detect(old_type, new_type)

    # ------------------------------------------------------------------
    # Reporting
    # ------------------------------------------------------------------

    def report(self) -> ProvenanceReport:
        """Generate a full provenance report.

        Iterates every node in the graph, classifies grounding, and
        collects all hallucination traces and drift events into a
        single ``ProvenanceReport``.
        """
        total = len(self.graph)
        grounded = 0
        ungrounded_hashes: set[str] = set()

        for nid, node in self.graph.nodes.items():
            if self.graph.is_grounded(nid):
                grounded += 1
            else:
                ungrounded_hashes.add(node.content_hash)

        # Trace each distinct ungrounded artifact.
        traces: list[HallucinationTrace] = []
        seen_hashes: set[str] = set()
        for uhash in ungrounded_hashes:
            if uhash in seen_hashes:
                continue
            seen_hashes.add(uhash)
            trace = self.trace_hallucination(uhash)
            if trace is not None:
                traces.append(trace)

        return ProvenanceReport(
            total_nodes=total,
            grounded_nodes=grounded,
            ungrounded_nodes=total - grounded,
            hallucination_traces=traces,
            drift_events=list(self.drift_detector.history),
        )

    # ------------------------------------------------------------------
    # Persistence
    # ------------------------------------------------------------------

    def save(self, path: str | Path) -> None:
        """Persist the tracker state to a JSON file.

        The file contains the full graph and drift-detector history so
        that the tracker can be restored later with ``load``.

        Parameters
        ----------
        path : str | Path
            Filesystem path to write to.
        """
        dest = Path(path)
        dest.parent.mkdir(parents=True, exist_ok=True)
        payload: dict[str, Any] = {
            "version": 1,
            "graph": self.graph.to_dict(),
            "drift_detector": self.drift_detector.to_dict(),
        }
        dest.write_text(json.dumps(payload, indent=2, default=str))

    @classmethod
    def load(cls, path: str | Path) -> ProvenanceTracker:
        """Restore a tracker from a previously saved JSON file.

        Parameters
        ----------
        path : str | Path
            Filesystem path to read from.

        Returns
        -------
        ProvenanceTracker
            The restored tracker instance.
        """
        raw = Path(path).read_text()
        data = json.loads(raw)
        tracker = cls()
        tracker.graph = ProvenanceGraph.from_dict(data.get("graph", {}))
        tracker.drift_detector = DriftDetector.from_dict(
            data.get("drift_detector", {})
        )
        return tracker

    # ------------------------------------------------------------------
    # Convenience
    # ------------------------------------------------------------------

    def __len__(self) -> int:
        """Number of nodes in the provenance graph."""
        return len(self.graph)

    def __repr__(self) -> str:  # noqa: D105
        grounded = sum(
            1
            for nid in self.graph.nodes
            if self.graph.is_grounded(nid)
        )
        return (
            f"ProvenanceTracker(nodes={len(self.graph)}, "
            f"grounded={grounded}, "
            f"drift_events={len(self.drift_detector.history)})"
        )
