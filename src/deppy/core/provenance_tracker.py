"""Provenance tracking through cover construction.

Records how each site was created, what AST node it maps to, and the full
derivation chain.  This provides audit-trail information for every site in a
Cover, allowing the user (or downstream passes) to trace a site back to its
originating source construct.

Key classes:

- :class:`ProvenanceRecord` -- immutable record for a single site creation event.
- :class:`DerivationStep` -- one step in a multi-hop derivation chain.
- :class:`ProvenanceTracker` -- the mutable accumulator used during cover synthesis.
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import SiteId, SiteKind


# ═══════════════════════════════════════════════════════════════════════════════
# Derivation reason taxonomy
# ═══════════════════════════════════════════════════════════════════════════════


class DerivationReason(Enum):
    """Why a site was created during cover synthesis."""

    ARGUMENT_SCAN = "argument_scan"
    SSA_DEFINITION = "ssa_definition"
    BRANCH_GUARD_EXTRACTION = "branch_guard_extraction"
    CALL_RETURN = "call_return"
    TENSOR_SHAPE_INFERENCE = "tensor_shape_inference"
    TENSOR_ORDER_INFERENCE = "tensor_order_inference"
    TENSOR_INDEXING_EXTRACTION = "tensor_indexing_extraction"
    HEAP_PROTOCOL_DETECTION = "heap_protocol_detection"
    ERROR_PATH_ANALYSIS = "error_path_analysis"
    LOOP_HEADER_EXTRACTION = "loop_header_extraction"
    PROOF_OBLIGATION = "proof_obligation"
    TRACE_INSTRUMENTATION = "trace_instrumentation"
    MODULE_SUMMARY = "module_summary"
    RETURN_SITE_EXTRACTION = "return_site_extraction"
    OVERLAP_INDUCED = "overlap_induced"
    RESTRICTION_MAP = "restriction_map"
    USER_ANNOTATION = "user_annotation"
    BOUNDARY_INFERENCE = "boundary_inference"


# ═══════════════════════════════════════════════════════════════════════════════
# AST node reference
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ASTNodeRef:
    """A lightweight reference to an AST node without holding the node itself.

    Attributes:
        node_type: The AST node class name (e.g. "FunctionDef", "Assign").
        file_path: Source file path, if known.
        line: Starting line number in source, if known.
        col: Starting column offset, if known.
        end_line: Ending line number, if known.
        end_col: Ending column offset, if known.
        node_id: A unique identifier (id of the original AST node).
        snippet: An optional short textual snippet of the source.
    """

    _node_type: str
    _file_path: str = ""
    _line: int = 0
    _col: int = 0
    _end_line: int = 0
    _end_col: int = 0
    _node_id: int = 0
    _snippet: str = ""

    @property
    def node_type(self) -> str:
        return self._node_type

    @property
    def file_path(self) -> str:
        return self._file_path

    @property
    def line(self) -> int:
        return self._line

    @property
    def col(self) -> int:
        return self._col

    @property
    def end_line(self) -> int:
        return self._end_line

    @property
    def end_col(self) -> int:
        return self._end_col

    @property
    def node_id(self) -> int:
        return self._node_id

    @property
    def snippet(self) -> str:
        return self._snippet

    @property
    def location_str(self) -> str:
        """Human-readable location string."""
        if self._file_path:
            return f"{self._file_path}:{self._line}:{self._col}"
        if self._line > 0:
            return f"line {self._line}, col {self._col}"
        return "<unknown>"

    def __repr__(self) -> str:
        return f"ASTNodeRef({self._node_type}, {self.location_str})"

    @staticmethod
    def from_ast_node(node: Any, file_path: str = "") -> ASTNodeRef:
        """Construct from a real ``ast.AST`` node."""
        return ASTNodeRef(
            _node_type=type(node).__name__,
            _file_path=file_path,
            _line=getattr(node, "lineno", 0),
            _col=getattr(node, "col_offset", 0),
            _end_line=getattr(node, "end_lineno", 0) or 0,
            _end_col=getattr(node, "end_col_offset", 0) or 0,
            _node_id=id(node),
        )

    @staticmethod
    def synthetic(label: str) -> ASTNodeRef:
        """Create a synthetic node reference for compiler-generated sites."""
        return ASTNodeRef(_node_type=label, _snippet="<synthetic>")


# ═══════════════════════════════════════════════════════════════════════════════
# Derivation step
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class DerivationStep:
    """One step in a derivation chain explaining how a site came to exist.

    A derivation chain is a sequence of DerivationSteps, oldest first, that
    records the full lineage of a site.

    Attributes:
        reason: Why this step happened.
        description: Free-form human-readable explanation.
        source_site: If this step derived from another site, that site's id.
        timestamp: Monotonic timestamp (ns) for ordering.
    """

    _reason: DerivationReason
    _description: str
    _source_site: Optional[SiteId] = None
    _timestamp: float = 0.0

    @property
    def reason(self) -> DerivationReason:
        return self._reason

    @property
    def description(self) -> str:
        return self._description

    @property
    def source_site(self) -> Optional[SiteId]:
        return self._source_site

    @property
    def timestamp(self) -> float:
        return self._timestamp

    def __repr__(self) -> str:
        src = f" <- {self._source_site}" if self._source_site else ""
        return f"DerivationStep({self._reason.value}: {self._description}{src})"


# ═══════════════════════════════════════════════════════════════════════════════
# Provenance record
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class ProvenanceRecord:
    """Immutable provenance record for a single site.

    Attributes:
        site_id: The site this record describes.
        source_node: Reference to the AST node that produced the site.
        creation_reason: The primary reason the site was created.
        derivation_chain: Full chain of derivation steps (oldest first).
        metadata: Additional key-value metadata attached at creation time.
    """

    _site_id: SiteId
    _source_node: ASTNodeRef
    _creation_reason: DerivationReason
    _derivation_chain: Tuple[DerivationStep, ...] = ()
    _metadata: Tuple[Tuple[str, Any], ...] = ()

    @property
    def site_id(self) -> SiteId:
        return self._site_id

    @property
    def source_node(self) -> ASTNodeRef:
        return self._source_node

    @property
    def creation_reason(self) -> DerivationReason:
        return self._creation_reason

    @property
    def derivation_chain(self) -> Tuple[DerivationStep, ...]:
        return self._derivation_chain

    @property
    def metadata(self) -> Dict[str, Any]:
        return dict(self._metadata)

    @property
    def location_str(self) -> str:
        """Human-readable source location."""
        return self._source_node.location_str

    @property
    def chain_length(self) -> int:
        """Number of derivation steps."""
        return len(self._derivation_chain)

    def with_step(self, step: DerivationStep) -> ProvenanceRecord:
        """Return a new record with an appended derivation step."""
        return ProvenanceRecord(
            _site_id=self._site_id,
            _source_node=self._source_node,
            _creation_reason=self._creation_reason,
            _derivation_chain=self._derivation_chain + (step,),
            _metadata=self._metadata,
        )

    def with_metadata(self, key: str, value: Any) -> ProvenanceRecord:
        """Return a new record with additional metadata."""
        existing = dict(self._metadata)
        existing[key] = value
        return ProvenanceRecord(
            _site_id=self._site_id,
            _source_node=self._source_node,
            _creation_reason=self._creation_reason,
            _derivation_chain=self._derivation_chain,
            _metadata=tuple(sorted(existing.items())),
        )

    def summary(self) -> str:
        """One-line summary for diagnostics."""
        chain_desc = " -> ".join(s.description for s in self._derivation_chain)
        if chain_desc:
            return (
                f"{self._site_id}: {self._creation_reason.value} "
                f"at {self.location_str} [{chain_desc}]"
            )
        return f"{self._site_id}: {self._creation_reason.value} at {self.location_str}"

    def __repr__(self) -> str:
        return (
            f"ProvenanceRecord({self._site_id}, "
            f"reason={self._creation_reason.value}, "
            f"node={self._source_node!r}, "
            f"chain_len={self.chain_length})"
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Provenance tracker
# ═══════════════════════════════════════════════════════════════════════════════


class ProvenanceTracker:
    """Mutable accumulator recording provenance during cover synthesis.

    Records how each site was created, what AST node it maps to, and the
    full derivation chain.  Provides lookup from site-id to provenance and
    reverse lookup from AST node to sites.
    """

    def __init__(self) -> None:
        self._records: Dict[SiteId, ProvenanceRecord] = {}
        # Reverse index: AST node_id -> list of site ids
        self._node_to_sites: Dict[int, List[SiteId]] = {}
        # Reverse index: node_type -> list of site ids
        self._type_to_sites: Dict[str, List[SiteId]] = {}
        # Reverse index: reason -> list of site ids
        self._reason_to_sites: Dict[DerivationReason, List[SiteId]] = {}
        # Reverse index: SiteKind -> list of site ids
        self._kind_to_sites: Dict[SiteKind, List[SiteId]] = {}
        # Derivation edges: site_id -> sites derived from it
        self._derived_from: Dict[SiteId, List[SiteId]] = {}

    # ── Recording ──────────────────────────────────────────────────────────

    def record_site_creation(
        self,
        site_id: SiteId,
        source_node: Any,
        reason: DerivationReason,
        description: str = "",
        file_path: str = "",
        metadata: Optional[Dict[str, Any]] = None,
    ) -> ProvenanceRecord:
        """Record the creation of a site.

        Args:
            site_id: The newly created site.
            source_node: The AST node (or ASTNodeRef) that produced it.
            reason: Why the site was created.
            description: Optional human-readable description.
            file_path: Source file path for AST nodes.
            metadata: Optional key-value metadata.

        Returns:
            The created ProvenanceRecord.
        """
        if isinstance(source_node, ASTNodeRef):
            node_ref = source_node
        else:
            node_ref = ASTNodeRef.from_ast_node(source_node, file_path)

        initial_step = DerivationStep(
            _reason=reason,
            _description=description or reason.value,
            _source_site=None,
            _timestamp=time.monotonic(),
        )

        meta_tuple = tuple(sorted(metadata.items())) if metadata else ()

        record = ProvenanceRecord(
            _site_id=site_id,
            _source_node=node_ref,
            _creation_reason=reason,
            _derivation_chain=(initial_step,),
            _metadata=meta_tuple,
        )

        self._records[site_id] = record

        # Update reverse indices
        if node_ref.node_id != 0:
            self._node_to_sites.setdefault(node_ref.node_id, []).append(site_id)
        self._type_to_sites.setdefault(node_ref.node_type, []).append(site_id)
        self._reason_to_sites.setdefault(reason, []).append(site_id)
        self._kind_to_sites.setdefault(site_id.kind, []).append(site_id)

        return record

    def record_derivation(
        self,
        derived_site: SiteId,
        source_site: SiteId,
        reason: DerivationReason,
        description: str = "",
    ) -> None:
        """Record that *derived_site* was derived from *source_site*.

        Appends a derivation step to the derived site's record and updates
        the derivation edge index.
        """
        step = DerivationStep(
            _reason=reason,
            _description=description or f"derived from {source_site}",
            _source_site=source_site,
            _timestamp=time.monotonic(),
        )

        record = self._records.get(derived_site)
        if record is not None:
            self._records[derived_site] = record.with_step(step)

        self._derived_from.setdefault(source_site, []).append(derived_site)

    def record_metadata(self, site_id: SiteId, key: str, value: Any) -> None:
        """Attach additional metadata to an existing provenance record."""
        record = self._records.get(site_id)
        if record is not None:
            self._records[site_id] = record.with_metadata(key, value)

    # ── Querying ───────────────────────────────────────────────────────────

    def get_provenance(self, site_id: SiteId) -> Optional[ProvenanceRecord]:
        """Look up the provenance record for a site."""
        return self._records.get(site_id)

    def get_sites_from_node(self, ast_node: Any) -> List[SiteId]:
        """Get all sites that were created from a given AST node.

        Accepts either a raw ``ast.AST`` node (lookup by ``id()``) or an
        ``ASTNodeRef``.
        """
        if isinstance(ast_node, ASTNodeRef):
            node_id = ast_node.node_id
        else:
            node_id = id(ast_node)
        return list(self._node_to_sites.get(node_id, []))

    def get_sites_by_reason(self, reason: DerivationReason) -> List[SiteId]:
        """Get all sites created for a given reason."""
        return list(self._reason_to_sites.get(reason, []))

    def get_sites_by_kind(self, kind: SiteKind) -> List[SiteId]:
        """Get all tracked sites of a given SiteKind."""
        return list(self._kind_to_sites.get(kind, []))

    def get_sites_by_node_type(self, node_type: str) -> List[SiteId]:
        """Get all sites created from AST nodes of a given type."""
        return list(self._type_to_sites.get(node_type, []))

    def get_derived_sites(self, source_site: SiteId) -> List[SiteId]:
        """Get all sites that were derived from *source_site*."""
        return list(self._derived_from.get(source_site, []))

    def get_derivation_chain(self, site_id: SiteId) -> List[DerivationStep]:
        """Get the full derivation chain for a site."""
        record = self._records.get(site_id)
        if record is None:
            return []
        return list(record.derivation_chain)

    def get_root_reason(self, site_id: SiteId) -> Optional[DerivationReason]:
        """Get the original creation reason for a site."""
        record = self._records.get(site_id)
        if record is None:
            return None
        return record.creation_reason

    # ── Aggregate queries ──────────────────────────────────────────────────

    @property
    def all_site_ids(self) -> FrozenSet[SiteId]:
        """All tracked site ids."""
        return frozenset(self._records.keys())

    @property
    def site_count(self) -> int:
        """Number of tracked sites."""
        return len(self._records)

    def all_records(self) -> List[ProvenanceRecord]:
        """All provenance records, sorted by site kind then name."""
        return sorted(
            self._records.values(),
            key=lambda r: (r.site_id.kind.value, r.site_id.name),
        )

    def sites_at_location(self, file_path: str, line: int) -> List[SiteId]:
        """Find all sites whose source node is at the given file and line."""
        results: List[SiteId] = []
        for sid, record in self._records.items():
            node = record.source_node
            if node.file_path == file_path and node.line == line:
                results.append(sid)
        return results

    def sites_in_range(
        self, file_path: str, start_line: int, end_line: int
    ) -> List[SiteId]:
        """Find all sites whose source node falls within a line range."""
        results: List[SiteId] = []
        for sid, record in self._records.items():
            node = record.source_node
            if node.file_path == file_path:
                if start_line <= node.line <= end_line:
                    results.append(sid)
        return results

    def reason_histogram(self) -> Dict[DerivationReason, int]:
        """Return a histogram of creation reasons."""
        return {
            reason: len(sites)
            for reason, sites in self._reason_to_sites.items()
        }

    def kind_histogram(self) -> Dict[SiteKind, int]:
        """Return a histogram of site kinds."""
        return {
            kind: len(sites)
            for kind, sites in self._kind_to_sites.items()
        }

    # ── Diagnostics ────────────────────────────────────────────────────────

    def summary_report(self) -> str:
        """Generate a multi-line summary report of all provenance data."""
        lines: List[str] = []
        lines.append(f"Provenance Tracker: {self.site_count} sites tracked")
        lines.append("")

        # By kind
        lines.append("Sites by kind:")
        for kind, count in sorted(
            self.kind_histogram().items(), key=lambda kv: kv[1], reverse=True
        ):
            lines.append(f"  {kind.value}: {count}")

        lines.append("")
        lines.append("Sites by reason:")
        for reason, count in sorted(
            self.reason_histogram().items(), key=lambda kv: kv[1], reverse=True
        ):
            lines.append(f"  {reason.value}: {count}")

        lines.append("")
        lines.append("Derivation edges: "
                      f"{sum(len(v) for v in self._derived_from.values())}")

        return "\n".join(lines)

    def validate(self) -> List[str]:
        """Check internal consistency and return a list of issues."""
        issues: List[str] = []

        # Every site in reverse indices should be in _records
        for node_id, sites in self._node_to_sites.items():
            for sid in sites:
                if sid not in self._records:
                    issues.append(
                        f"Site {sid} in node_to_sites index but missing from records"
                    )

        # Derivation edges should reference known sites
        for source, derived_list in self._derived_from.items():
            if source not in self._records:
                issues.append(
                    f"Derivation source {source} not in records"
                )
            for d in derived_list:
                if d not in self._records:
                    issues.append(
                        f"Derived site {d} not in records"
                    )

        return issues

    def merge(self, other: ProvenanceTracker) -> None:
        """Merge all records from *other* into this tracker.

        On conflict (same site_id in both), the record from *other* wins.
        """
        for sid, record in other._records.items():
            self._records[sid] = record

        for node_id, sites in other._node_to_sites.items():
            existing = self._node_to_sites.setdefault(node_id, [])
            for s in sites:
                if s not in existing:
                    existing.append(s)

        for ntype, sites in other._type_to_sites.items():
            existing = self._type_to_sites.setdefault(ntype, [])
            for s in sites:
                if s not in existing:
                    existing.append(s)

        for reason, sites in other._reason_to_sites.items():
            existing = self._reason_to_sites.setdefault(reason, [])
            for s in sites:
                if s not in existing:
                    existing.append(s)

        for kind, sites in other._kind_to_sites.items():
            existing = self._kind_to_sites.setdefault(kind, [])
            for s in sites:
                if s not in existing:
                    existing.append(s)

        for source, derived_list in other._derived_from.items():
            existing = self._derived_from.setdefault(source, [])
            for d in derived_list:
                if d not in existing:
                    existing.append(d)

    def clear(self) -> None:
        """Reset all tracked data."""
        self._records.clear()
        self._node_to_sites.clear()
        self._type_to_sites.clear()
        self._reason_to_sites.clear()
        self._kind_to_sites.clear()
        self._derived_from.clear()

    def __repr__(self) -> str:
        return f"ProvenanceTracker({self.site_count} sites)"
