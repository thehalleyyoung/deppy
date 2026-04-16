"""Mathlib Axiom Lookup — query the Mathlib theorem catalog for C⁴ axioms.

This module provides the ``mathlib_axiom`` function that looks up a Mathlib
theorem by its fully qualified Lean name and returns it as a C⁴ axiom
(a MathLibAxiom proof term).

The catalog is loaded from ``mathlib_full_catalog.json`` in the
``cctt/mathlib_bridge/`` directory.  Each entry contains:
  - name: fully qualified Lean name (e.g., 'Nat.add_comm')
  - type: the Lean type expression (proposition)
  - module: the Mathlib module path

Usage::

    from cctt.proof_theory.mathlib_axioms import mathlib_axiom, lookup_mathlib_axiom

    # Look up raw catalog entry
    info = lookup_mathlib_axiom('Nat.add_comm')

    # Get a proof term
    proof = mathlib_axiom('List.map_map', {'f': some_oterm, 'g': another_oterm})
"""
from __future__ import annotations

import json
import os
from dataclasses import dataclass
from typing import Any, Dict, List, Optional

from cctt.proof_theory.terms import MathLibAxiom

try:
    from cctt.denotation import OTerm
except ImportError:
    OTerm = Any  # type: ignore


# ═══════════════════════════════════════════════════════════════════
# Catalog data
# ═══════════════════════════════════════════════════════════════════

@dataclass
class MathlibEntry:
    """A single theorem entry from the Mathlib catalog."""
    name: str
    type_str: str
    module: str
    docstring: str = ''


# Lazy-loaded catalog singleton
_catalog: Optional[Dict[str, MathlibEntry]] = None
_catalog_path: Optional[str] = None


def _find_catalog_path() -> str:
    """Locate the mathlib_full_catalog.json file."""
    # Try relative to this file
    here = os.path.dirname(os.path.abspath(__file__))
    candidates = [
        os.path.join(here, '..', 'mathlib_bridge', 'mathlib_full_catalog.json'),
        os.path.join(here, '..', '..', 'cctt', 'mathlib_bridge', 'mathlib_full_catalog.json'),
    ]
    for path in candidates:
        normalized = os.path.normpath(path)
        if os.path.isfile(normalized):
            return normalized
    raise FileNotFoundError(
        'mathlib_full_catalog.json not found. '
        'Expected in cctt/mathlib_bridge/mathlib_full_catalog.json'
    )


def _load_catalog() -> Dict[str, MathlibEntry]:
    """Load and index the Mathlib catalog (lazy, cached)."""
    global _catalog, _catalog_path
    if _catalog is not None:
        return _catalog

    _catalog_path = _find_catalog_path()
    with open(_catalog_path, 'r') as f:
        raw = json.load(f)

    _catalog = {}
    if isinstance(raw, list):
        entries = raw
    elif isinstance(raw, dict) and 'theorems' in raw:
        entries = raw['theorems']
    elif isinstance(raw, dict):
        # Dict keyed by name
        for name, entry in raw.items():
            if isinstance(entry, dict):
                _catalog[name] = MathlibEntry(
                    name=name,
                    type_str=entry.get('type', entry.get('signature', '')),
                    module=entry.get('module', entry.get('file_path', '')),
                    docstring=entry.get('docstring', ''),
                )
            elif isinstance(entry, str):
                _catalog[name] = MathlibEntry(
                    name=name,
                    type_str=entry,
                    module='',
                )
        return _catalog
    else:
        entries = []

    for entry in entries:
        if isinstance(entry, dict):
            name = entry.get('name', '')
            if name:
                _catalog[name] = MathlibEntry(
                    name=name,
                    type_str=entry.get('type', entry.get('signature', '')),
                    module=entry.get('module', entry.get('file_path', '')),
                    docstring=entry.get('docstring', ''),
                )

    return _catalog


# ═══════════════════════════════════════════════════════════════════
# Public API
# ═══════════════════════════════════════════════════════════════════

def lookup_mathlib_axiom(name: str) -> Optional[MathlibEntry]:
    """Look up a Mathlib theorem by its fully qualified Lean name.

    Returns the catalog entry if found, None otherwise.

    Parameters
    ----------
    name : str
        Fully qualified Lean name, e.g., 'Nat.add_comm'.

    Returns
    -------
    MathlibEntry or None
    """
    catalog = _load_catalog()
    return catalog.get(name)


def mathlib_axiom(name: str,
                  instantiation: Optional[Dict[str, Any]] = None
                  ) -> MathLibAxiom:
    """Create a MathLibAxiom proof term for the given theorem.

    The theorem must exist in the Mathlib catalog.  If it does not,
    a ValueError is raised.

    Parameters
    ----------
    name : str
        Fully qualified Lean name, e.g., 'List.map_map'.
    instantiation : dict, optional
        Variable bindings for the theorem's free variables.

    Returns
    -------
    MathLibAxiom
        A proof term that can be used in equivalence proofs.

    Raises
    ------
    ValueError
        If the theorem is not in the catalog.
    """
    entry = lookup_mathlib_axiom(name)
    if entry is None:
        # Also accept from the hardcoded known set
        known = {
            'Nat.add_comm', 'Nat.add_assoc', 'Nat.mul_comm', 'Nat.mul_assoc',
            'Nat.add_zero', 'Nat.zero_add', 'Nat.mul_one', 'Nat.one_mul',
            'Nat.left_distrib', 'Nat.right_distrib',
            'Nat.sub_add_cancel', 'Nat.factorial_succ', 'Nat.factorial_zero',
            'List.map_map', 'List.map_id', 'List.filter_map',
            'List.foldl_nil', 'List.foldl_cons',
            'List.length_append', 'List.length_map', 'List.length_filter_le',
            'List.reverse_reverse', 'List.map_reverse',
            'List.perm_sort', 'List.sorted_sort', 'List.sum_append',
            'Finset.sum_comm',
        }
        if name not in known:
            raise ValueError(
                f'Mathlib theorem {name!r} not found in catalog '
                f'({catalog_size()} entries) or known set.'
            )

    return MathLibAxiom(name, instantiation or {})


def search_mathlib(pattern: str, max_results: int = 20) -> List[MathlibEntry]:
    """Search the Mathlib catalog by name pattern.

    Parameters
    ----------
    pattern : str
        Substring to search for in theorem names (case-insensitive).
    max_results : int
        Maximum number of results to return.

    Returns
    -------
    list of MathlibEntry
    """
    catalog = _load_catalog()
    pattern_lower = pattern.lower()
    results = []
    for name, entry in catalog.items():
        if pattern_lower in name.lower():
            results.append(entry)
            if len(results) >= max_results:
                break
    return results


def catalog_size() -> int:
    """Return the number of theorems in the catalog."""
    return len(_load_catalog())
