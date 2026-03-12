"""Normalize local sections for comparison.

The SectionNormalizer canonicalizes local sections so that semantically
equivalent sections have identical representations.  This is critical
for the sheaf gluing condition: when checking whether sections on
overlapping sites agree, they must be compared in canonical form.

Normalizations applied:
1. Sort refinement keys lexicographically.
2. Canonicalize refinement key names (strip whitespace, lowercase).
3. Deduplicate identical refinement entries.
4. Normalize carrier type representations.
5. Stabilize trust-level provenance strings.
"""

from __future__ import annotations

import hashlib
from collections import OrderedDict
from dataclasses import dataclass, field
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
    Union,
)

from deppy.core._protocols import (
    LocalSection,
    SiteId,
    TrustLevel,
)


# ===================================================================
#  Normalization helpers
# ===================================================================


def _canonical_key(key: str) -> str:
    """Canonicalize a refinement key name.

    - Strip leading/trailing whitespace.
    - Collapse internal whitespace to single spaces.
    - Lowercase.
    """
    normalized = " ".join(key.split())
    return normalized.lower()


def _canonical_value(value: Any) -> Any:
    """Canonicalize a refinement value for comparison.

    - Strings are stripped and lowercased.
    - Numbers are left as-is.
    - Booleans are left as-is.
    - Lists/tuples are sorted if all elements are comparable.
    - Dicts are sorted by key.
    """
    if isinstance(value, str):
        return value.strip()
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return value
    if isinstance(value, (list, tuple)):
        items = list(value)
        try:
            items = sorted(items)
        except TypeError:
            pass
        return tuple(items)
    if isinstance(value, dict):
        return tuple(sorted(value.items()))
    if isinstance(value, set):
        return frozenset(value)
    if isinstance(value, frozenset):
        return value
    return value


def _values_equal(a: Any, b: Any) -> bool:
    """Check if two refinement values are equal after canonicalization."""
    ca = _canonical_value(a)
    cb = _canonical_value(b)
    return ca == cb


def _section_fingerprint(section: LocalSection) -> str:
    """Compute a fingerprint of a section's refinements for fast comparison."""
    parts: List[str] = []
    for key in sorted(section.refinements.keys()):
        value = section.refinements[key]
        canonical = _canonical_value(value)
        parts.append(f"{_canonical_key(key)}={canonical!r}")
    content = "|".join(parts)
    return hashlib.sha256(content.encode("utf-8")).hexdigest()[:12]


# ===================================================================
#  Normalization result
# ===================================================================


@dataclass(frozen=True)
class NormalizationResult:
    """Result of normalizing a section."""

    _normalized: LocalSection
    _changes_made: int
    _keys_renamed: Tuple[Tuple[str, str], ...]
    _keys_removed: Tuple[str, ...]

    @property
    def normalized(self) -> LocalSection:
        return self._normalized

    @property
    def changes_made(self) -> int:
        return self._changes_made

    @property
    def keys_renamed(self) -> Tuple[Tuple[str, str], ...]:
        return self._keys_renamed

    @property
    def keys_removed(self) -> Tuple[str, ...]:
        return self._keys_removed

    @property
    def was_modified(self) -> bool:
        return self._changes_made > 0


# ===================================================================
#  SectionNormalizer
# ===================================================================


class SectionNormalizer:
    """Normalize local sections for canonical comparison.

    Applies a sequence of normalization passes to ensure that
    semantically equivalent sections have identical representations.
    """

    def __init__(
        self,
        canonicalize_keys: bool = True,
        sort_keys: bool = True,
        deduplicate: bool = True,
        normalize_values: bool = True,
    ) -> None:
        self._canonicalize_keys = canonicalize_keys
        self._sort_keys = sort_keys
        self._deduplicate = deduplicate
        self._normalize_values = normalize_values

    def normalize(self, section: LocalSection) -> LocalSection:
        """Normalize a section to canonical form.

        Returns a new LocalSection with normalized refinements.
        """
        refinements = dict(section.refinements)
        changes = 0

        # Pass 1: Canonicalize key names
        if self._canonicalize_keys:
            new_refs: Dict[str, Any] = {}
            for key, value in refinements.items():
                canon_key = _canonical_key(key)
                if canon_key != key:
                    changes += 1
                new_refs[canon_key] = value
            refinements = new_refs

        # Pass 2: Normalize values
        if self._normalize_values:
            for key in list(refinements.keys()):
                old_value = refinements[key]
                new_value = _canonical_value(old_value)
                if new_value != old_value:
                    refinements[key] = new_value
                    changes += 1

        # Pass 3: Deduplicate
        if self._deduplicate:
            seen_values: Dict[Any, str] = {}
            deduped: Dict[str, Any] = {}
            removed_keys: List[str] = []
            for key in sorted(refinements.keys()):
                value = refinements[key]
                canon_val = _canonical_value(value)
                val_repr = repr(canon_val)
                if val_repr in seen_values:
                    # Keep the first occurrence (lexicographically earliest key)
                    removed_keys.append(key)
                    changes += 1
                else:
                    seen_values[val_repr] = key
                    deduped[key] = value
            refinements = deduped

        # Pass 4: Sort keys
        if self._sort_keys:
            sorted_refs = dict(sorted(refinements.items()))
            if list(sorted_refs.keys()) != list(refinements.keys()):
                changes += 1
            refinements = sorted_refs

        return LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=refinements,
            trust=section.trust,
            provenance=section.provenance,
        )

    def normalize_detailed(self, section: LocalSection) -> NormalizationResult:
        """Normalize a section and return detailed information about changes."""
        original_keys = set(section.refinements.keys())
        renamed: List[Tuple[str, str]] = []
        removed: List[str] = []
        changes = 0

        refinements = dict(section.refinements)

        # Track key renames
        if self._canonicalize_keys:
            new_refs: Dict[str, Any] = {}
            for key, value in refinements.items():
                canon_key = _canonical_key(key)
                if canon_key != key:
                    renamed.append((key, canon_key))
                    changes += 1
                new_refs[canon_key] = value
            refinements = new_refs

        # Track value changes
        if self._normalize_values:
            for key in list(refinements.keys()):
                old_value = refinements[key]
                new_value = _canonical_value(old_value)
                if new_value != old_value:
                    refinements[key] = new_value
                    changes += 1

        # Track deduplication
        if self._deduplicate:
            seen_values: Dict[Any, str] = {}
            deduped: Dict[str, Any] = {}
            for key in sorted(refinements.keys()):
                value = refinements[key]
                val_repr = repr(_canonical_value(value))
                if val_repr in seen_values:
                    removed.append(key)
                    changes += 1
                else:
                    seen_values[val_repr] = key
                    deduped[key] = value
            refinements = deduped

        # Sort
        if self._sort_keys:
            refinements = dict(sorted(refinements.items()))

        normalized = LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=refinements,
            trust=section.trust,
            provenance=section.provenance,
        )

        return NormalizationResult(
            _normalized=normalized,
            _changes_made=changes,
            _keys_renamed=tuple(renamed),
            _keys_removed=tuple(removed),
        )

    def sections_equivalent(
        self,
        a: LocalSection,
        b: LocalSection,
    ) -> bool:
        """Check if two sections are semantically equivalent.

        Two sections are equivalent if, after normalization, they have
        the same carrier type and the same refinements (ignoring key
        ordering and provenance).
        """
        norm_a = self.normalize(a)
        norm_b = self.normalize(b)

        # Compare carrier types
        if norm_a.carrier_type != norm_b.carrier_type:
            # Allow None to match anything
            if norm_a.carrier_type is not None and norm_b.carrier_type is not None:
                return False

        # Compare refinements
        if len(norm_a.refinements) != len(norm_b.refinements):
            return False

        for key in norm_a.refinements:
            if key not in norm_b.refinements:
                return False
            if not _values_equal(
                norm_a.refinements[key],
                norm_b.refinements[key],
            ):
                return False

        return True

    def fingerprint(self, section: LocalSection) -> str:
        """Compute a canonical fingerprint for a section.

        Equivalent sections produce the same fingerprint.
        """
        normalized = self.normalize(section)
        return _section_fingerprint(normalized)

    def normalize_all(
        self,
        sections: Mapping[SiteId, LocalSection],
    ) -> Dict[SiteId, LocalSection]:
        """Normalize all sections in a mapping."""
        return {
            site_id: self.normalize(section)
            for site_id, section in sections.items()
        }

    def find_equivalent_groups(
        self,
        sections: Mapping[SiteId, LocalSection],
    ) -> List[List[SiteId]]:
        """Find groups of sections that are semantically equivalent.

        Returns a list of groups, where each group is a list of SiteIds
        that have equivalent sections.
        """
        fingerprints: Dict[str, List[SiteId]] = {}
        for site_id, section in sections.items():
            fp = self.fingerprint(section)
            fingerprints.setdefault(fp, []).append(site_id)

        return [
            group for group in fingerprints.values()
            if len(group) > 1
        ]

    def summary(
        self,
        sections: Mapping[SiteId, LocalSection],
    ) -> str:
        """Produce a summary of normalization effects."""
        lines: List[str] = ["Section normalization summary:"]
        total_changes = 0
        total_renamed = 0
        total_removed = 0

        for site_id, section in sections.items():
            result = self.normalize_detailed(section)
            if result.was_modified:
                total_changes += result.changes_made
                total_renamed += len(result.keys_renamed)
                total_removed += len(result.keys_removed)

        lines.append(f"  Sections: {len(sections)}")
        lines.append(f"  Total changes: {total_changes}")
        lines.append(f"  Keys renamed: {total_renamed}")
        lines.append(f"  Keys removed: {total_removed}")

        groups = self.find_equivalent_groups(sections)
        if groups:
            lines.append(f"  Equivalent groups: {len(groups)}")
            for i, group in enumerate(groups):
                site_names = [str(s) for s in group]
                lines.append(f"    Group {i+1}: {', '.join(site_names)}")

        return "\n".join(lines)
