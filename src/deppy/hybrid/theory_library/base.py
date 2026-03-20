"""Theory Library Base — Per-library type information, axioms, and anti-hallucination checks.

Extensible Theory Packs
───────────────────────
The theory library provides a principled mechanism for encoding library-specific
knowledge into the hybrid verification pipeline.  Each *theory pack* describes:

  1. **API surface** — known functions, their type signatures, and which library
     versions they belong to.
  2. **Type rules** — structural pre/postconditions expressed in a form amenable
     to both Z3 discharge and Lean translation.
  3. **Axioms** — semantic truths about the library (e.g. ``sorted`` is
     idempotent) that the verifier may assume.

Anti-hallucination
──────────────────
A central motivation is *anti-hallucination*: when an LLM generates code that
references ``np.reshpe`` instead of ``np.reshape``, or invokes ``torch.Longtensor``
(wrong capitalisation), the theory pack can detect the mistake and suggest a
correction — *before* the code is ever executed.

Lean Integration
────────────────
Every type rule and axiom carries an optional ``lean_statement`` field so that
the full theory can be exported to a Lean 4 environment for independent
machine-checked verification.

Registry
────────
``TheoryRegistry`` aggregates multiple packs (stdlib, NumPy, PyTorch, …) and
exposes a unified query surface for the rest of the pipeline.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.theory_packs import TheoryPackSpec, register_pack_spec, available_theory_packs
    from deppy.theory_packs.models import AxiomSpec, VerificationCase
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import difflib
import json
import logging
from dataclasses import dataclass, field
from pathlib import Path
from typing import (

    Any,
    Dict,
    List,
    Optional,
    Tuple,
)

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class TheoryPackMeta:
    """Metadata for a theory pack.

    Attributes
    ──────────
    name            Human-readable pack name (e.g. "NumPy Theory Pack").
    version         Semantic version of this pack definition.
    library_name    Canonical name of the target library (e.g. "numpy").
    library_version Minimum library version this pack describes.
    description     One-paragraph summary.
    author          Pack author / maintainer.
    """

    name: str
    version: str
    library_name: str
    library_version: str
    description: str = ""
    author: str = ""

    # -- serialisation -------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "version": self.version,
            "library_name": self.library_name,
            "library_version": self.library_version,
            "description": self.description,
            "author": self.author,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> TheoryPackMeta:
        return cls(
            name=d["name"],
            version=d["version"],
            library_name=d["library_name"],
            library_version=d["library_version"],
            description=d.get("description", ""),
            author=d.get("author", ""),
        )

@dataclass
class APIEntry:
    """A single known API function or class.

    Attributes
    ──────────
    module                  Dotted module path (e.g. "os.path").
    name                    Function / class name (e.g. "join").
    signature               Python-style type annotation string.
    lean_type               Optional Lean 4 type expression.
    description             Short docstring.
    structural_properties   Decidable postconditions (e.g. "len(result) == len(input)").
    semantic_properties     Semantic postconditions (oracle-level).
    deprecated_in           Library version where this API was deprecated, if any.
    added_in                Library version where this API first appeared.
    """

    module: str
    name: str
    signature: str
    lean_type: Optional[str] = None
    description: str = ""
    structural_properties: List[str] = field(default_factory=list)
    semantic_properties: List[str] = field(default_factory=list)
    deprecated_in: Optional[str] = None
    added_in: Optional[str] = None

    # -- helpers -------------------------------------------------------------

    @property
    def qualified_name(self) -> str:
        """Return ``module.name``."""
        if self.module:
            return f"{self.module}.{self.name}"
        return self.name

    # -- serialisation -------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "module": self.module,
            "name": self.name,
            "signature": self.signature,
            "description": self.description,
            "structural_properties": self.structural_properties,
            "semantic_properties": self.semantic_properties,
        }
        if self.lean_type is not None:
            d["lean_type"] = self.lean_type
        if self.deprecated_in is not None:
            d["deprecated_in"] = self.deprecated_in
        if self.added_in is not None:
            d["added_in"] = self.added_in
        return d

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> APIEntry:
        return cls(
            module=d["module"],
            name=d["name"],
            signature=d["signature"],
            lean_type=d.get("lean_type"),
            description=d.get("description", ""),
            structural_properties=d.get("structural_properties", []),
            semantic_properties=d.get("semantic_properties", []),
            deprecated_in=d.get("deprecated_in"),
            added_in=d.get("added_in"),
        )

@dataclass
class TypeRule:
    """A type-level rule about a library operation.

    Attributes
    ──────────
    name            Human-readable identifier (e.g. "sorted_preserves_length").
    pattern         Pattern in Python-ish notation (e.g. "sorted(list[T]) -> list[T]").
    precondition    Precondition expression (may reference argument names).
    postcondition   Postcondition expression (may reference ``result``).
    lean_statement  Lean 4 theorem statement.
    """

    name: str
    pattern: str
    precondition: str = "True"
    postcondition: str = "True"
    lean_statement: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "pattern": self.pattern,
            "precondition": self.precondition,
            "postcondition": self.postcondition,
            "lean_statement": self.lean_statement,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> TypeRule:
        return cls(
            name=d["name"],
            pattern=d["pattern"],
            precondition=d.get("precondition", "True"),
            postcondition=d.get("postcondition", "True"),
            lean_statement=d.get("lean_statement", ""),
        )

@dataclass
class Axiom:
    """A semantic axiom about library behaviour.

    Attributes
    ──────────
    name            Identifier (e.g. "sorted_idempotent").
    statement       Human-readable mathematical statement.
    lean_statement  Lean 4 formalisation.
    trust_level     One of "verified", "tested", "assumed".
    source          Where this axiom comes from (e.g. "CPython docs", "property test").
    """

    name: str
    statement: str
    lean_statement: str = ""
    trust_level: str = "assumed"
    source: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "statement": self.statement,
            "lean_statement": self.lean_statement,
            "trust_level": self.trust_level,
            "source": self.source,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> Axiom:
        return cls(
            name=d["name"],
            statement=d["statement"],
            lean_statement=d.get("lean_statement", ""),
            trust_level=d.get("trust_level", "assumed"),
            source=d.get("source", ""),
        )

# ---------------------------------------------------------------------------
# HybridTheoryPack — the base class
# ---------------------------------------------------------------------------

class HybridTheoryPack:
    """Base class for library-specific theory packs.

    A theory pack bundles:
    * **API entries** — the known public surface of a library.
    * **Type rules** — structural pre-/postconditions for individual APIs.
    * **Axioms** — semantic truths the verifier may assume.

    Subclasses (e.g. ``StdlibTheoryPack``, ``NumPyTheoryPack``) populate these
    tables in ``__init__`` and may override helper methods to provide
    library-specific logic (e.g. NumPy shape algebra).

    Anti-hallucination
    ──────────────────
    ``api_exists`` and ``suggest_correction`` power the anti-hallucination
    layer: before the pipeline trusts an LLM-generated API call, it checks
    that the call actually exists in the theory pack.  If it does not,
    ``suggest_correction`` uses fuzzy matching to propose a fix.
    """

    def __init__(
        self,
        meta: TheoryPackMeta,
        api_entries: Optional[Dict[str, APIEntry]] = None,
        type_rules: Optional[List[TypeRule]] = None,
        axioms: Optional[List[Axiom]] = None,
    ) -> None:
        self.meta = meta
        self.api_entries: Dict[str, APIEntry] = api_entries or {}
        self.type_rules: List[TypeRule] = type_rules or []
        self.axioms: List[Axiom] = axioms or []

        # Indices built lazily
        self._name_index: Dict[str, List[APIEntry]] = {}
        self._module_index: Dict[str, List[APIEntry]] = {}
        self._type_rule_index: Dict[str, TypeRule] = {}
        self._build_indices()

    # -- index construction --------------------------------------------------

    def _build_indices(self) -> None:
        """Rebuild internal look-up indices from the current entries."""
        self._name_index.clear()
        self._module_index.clear()
        self._type_rule_index.clear()

        for entry in self.api_entries.values():
            self._name_index.setdefault(entry.name, []).append(entry)
            self._module_index.setdefault(entry.module, []).append(entry)

        for rule in self.type_rules:
            func = rule.pattern.split("(")[0].strip() if "(" in rule.pattern else rule.name
            self._type_rule_index[func] = rule

    # -- registration helpers ------------------------------------------------

    def register_api(self, entry: APIEntry) -> None:
        """Add or replace an API entry."""
        key = entry.qualified_name
        self.api_entries[key] = entry
        self._name_index.setdefault(entry.name, []).append(entry)
        self._module_index.setdefault(entry.module, []).append(entry)

    def register_type_rule(self, rule: TypeRule) -> None:
        """Add a type rule."""
        self.type_rules.append(rule)
        func = rule.pattern.split("(")[0].strip() if "(" in rule.pattern else rule.name
        self._type_rule_index[func] = rule

    def register_axiom(self, axiom: Axiom) -> None:
        """Add an axiom."""
        self.axioms.append(axiom)

    # -- API queries ---------------------------------------------------------

    def api_exists(self, module: str, name: str) -> bool:
        """Return *True* if ``module.name`` is a known API."""
        key = f"{module}.{name}" if module else name
        return key in self.api_entries

    def get_api(self, module: str, name: str) -> Optional[APIEntry]:
        """Return the ``APIEntry`` for ``module.name``, or *None*."""
        key = f"{module}.{name}" if module else name
        return self.api_entries.get(key)

    def suggest_correction(self, module: str, wrong_name: str) -> Optional[str]:
        """Suggest the closest correct API name via fuzzy matching.

        Returns the best match name (within the same *module*) or *None* if
        nothing is close enough (cutoff 0.6).
        """
        candidates: List[str] = []
        for entry in self.api_entries.values():
            if entry.module == module:
                candidates.append(entry.name)

        if not candidates:
            # Fall back to all known names
            candidates = [e.name for e in self.api_entries.values()]

        matches = difflib.get_close_matches(wrong_name, candidates, n=1, cutoff=0.6)
        return matches[0] if matches else None

    def get_apis_in_module(self, module: str) -> List[APIEntry]:
        """Return all known APIs in *module*."""
        return list(self._module_index.get(module, []))

    def get_apis_by_name(self, name: str) -> List[APIEntry]:
        """Return all entries whose short name is *name* (across modules)."""
        return list(self._name_index.get(name, []))

    # -- type-rule queries ---------------------------------------------------

    def get_type_rule(self, func_name: str) -> Optional[TypeRule]:
        """Return the type rule whose pattern starts with *func_name*."""
        return self._type_rule_index.get(func_name)

    def structural_postcondition(
        self, func_name: str, args: Dict[str, Any]
    ) -> Optional[str]:
        """Return the Z3-amenable postcondition for *func_name*, or *None*.

        The postcondition string may contain references to argument names
        present in *args*; callers are responsible for substituting them.
        """
        rule = self.get_type_rule(func_name)
        if rule is None:
            return None
        postcondition = rule.postcondition
        if postcondition == "True":
            return None
        # Simple template substitution for argument references
        for arg_name, arg_val in args.items():
            postcondition = postcondition.replace(f"{{{arg_name}}}", str(arg_val))
        return postcondition

    def semantic_postcondition(
        self, func_name: str, args: Dict[str, Any]
    ) -> Optional[str]:
        """Return the oracle-level (semantic) postcondition, or *None*.

        Semantic postconditions are not necessarily decidable; they serve as
        documentation and as targets for property-based testing / Lean proofs.
        """
        entry_matches = self._name_index.get(func_name, [])
        for entry in entry_matches:
            if entry.semantic_properties:
                props = "; ".join(entry.semantic_properties)
                for arg_name, arg_val in args.items():
                    props = props.replace(f"{{{arg_name}}}", str(arg_val))
                return props
        return None

    # -- axiom queries -------------------------------------------------------

    def lean_axioms(self) -> List[str]:
        """Return all axioms formatted as Lean 4 declarations."""
        results: List[str] = []
        for ax in self.axioms:
            if ax.lean_statement:
                results.append(ax.lean_statement)
            else:
                # Emit a sorry-based placeholder
                results.append(
                    f"-- {ax.name}: {ax.statement}\n"
                    f"axiom {ax.name} : sorry"
                )
        return results

    def get_axiom(self, name: str) -> Optional[Axiom]:
        """Look up an axiom by name."""
        for ax in self.axioms:
            if ax.name == name:
                return ax
        return None

    def axioms_by_trust(self, trust_level: str) -> List[Axiom]:
        """Return axioms filtered by trust level."""
        return [ax for ax in self.axioms if ax.trust_level == trust_level]

    # -- version queries -----------------------------------------------------

    def apis_added_in(self, version: str) -> List[APIEntry]:
        """Return APIs added in a specific library version."""
        return [e for e in self.api_entries.values() if e.added_in == version]

    def apis_deprecated_in(self, version: str) -> List[APIEntry]:
        """Return APIs deprecated in a specific library version."""
        return [e for e in self.api_entries.values() if e.deprecated_in == version]

    def api_available_in(self, module: str, name: str, version: str) -> bool:
        """Check if an API is available (not deprecated) in *version*."""
        entry = self.get_api(module, name)
        if entry is None:
            return False
        if entry.deprecated_in is not None and version >= entry.deprecated_in:
            return False
        if entry.added_in is not None and version < entry.added_in:
            return False
        return True

    # -- serialisation -------------------------------------------------------

    def to_dict(self) -> Dict[str, Any]:
        """Serialise the entire theory pack to a JSON-compatible dict."""
        return {
            "meta": self.meta.to_dict(),
            "api_entries": {
                k: v.to_dict() for k, v in self.api_entries.items()
            },
            "type_rules": [r.to_dict() for r in self.type_rules],
            "axioms": [a.to_dict() for a in self.axioms],
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> HybridTheoryPack:
        """Deserialise a theory pack from a dict."""
        meta = TheoryPackMeta.from_dict(d["meta"])
        api_entries = {
            k: APIEntry.from_dict(v) for k, v in d.get("api_entries", {}).items()
        }
        type_rules = [TypeRule.from_dict(r) for r in d.get("type_rules", [])]
        axioms = [Axiom.from_dict(a) for a in d.get("axioms", [])]
        return cls(
            meta=meta,
            api_entries=api_entries,
            type_rules=type_rules,
            axioms=axioms,
        )

    def save(self, path: str) -> None:
        """Persist the pack to a JSON file."""
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "w", encoding="utf-8") as fh:
            json.dump(self.to_dict(), fh, indent=2, ensure_ascii=False)
        logger.info("Saved theory pack %s to %s", self.meta.name, path)

    @classmethod
    def load(cls, path: str) -> HybridTheoryPack:
        """Load a theory pack from a JSON file."""
        with open(path, encoding="utf-8") as fh:
            d = json.load(fh)
        pack = cls.from_dict(d)
        logger.info("Loaded theory pack %s from %s", pack.meta.name, path)
        return pack

    # -- summary / repr ------------------------------------------------------

    def summary(self) -> str:
        """One-line human-readable summary."""
        return (
            f"{self.meta.name} v{self.meta.version}: "
            f"{len(self.api_entries)} APIs, "
            f"{len(self.type_rules)} type rules, "
            f"{len(self.axioms)} axioms"
        )

    def __repr__(self) -> str:  # pragma: no cover
        return f"<{type(self).__name__} {self.summary()}>"

# ---------------------------------------------------------------------------
# TheoryRegistry
# ---------------------------------------------------------------------------

class TheoryRegistry:
    """Aggregate registry for multiple theory packs.

    The pipeline creates a single ``TheoryRegistry`` at startup and registers
    all available packs.  Every anti-hallucination check and type-rule look-up
    then goes through the registry rather than querying packs individually.
    """

    def __init__(self) -> None:
        self._packs: Dict[str, HybridTheoryPack] = {}

    # -- registration --------------------------------------------------------

    def register(self, pack: HybridTheoryPack) -> None:
        """Register a theory pack (keyed by ``meta.library_name``)."""
        key = pack.meta.library_name
        if key in self._packs:
            logger.warning(
                "Replacing existing theory pack for %s (old v%s -> new v%s)",
                key,
                self._packs[key].meta.version,
                pack.meta.version,
            )
        self._packs[key] = pack
        logger.info("Registered theory pack: %s", pack.summary())

    def unregister(self, library_name: str) -> bool:
        """Remove a pack; return *True* if it existed."""
        return self._packs.pop(library_name, None) is not None

    # -- look-ups ------------------------------------------------------------

    def get(self, library_name: str) -> Optional[HybridTheoryPack]:
        """Get the pack for *library_name*, or *None*."""
        return self._packs.get(library_name)

    def all_packs(self) -> List[HybridTheoryPack]:
        """Return every registered pack."""
        return list(self._packs.values())

    def api_exists(self, module: str, name: str) -> bool:
        """Check whether ``module.name`` exists in *any* registered pack."""
        for pack in self._packs.values():
            if pack.api_exists(module, name):
                return True
        return False

    def get_api(self, module: str, name: str) -> Optional[Tuple[str, APIEntry]]:
        """Return ``(library_name, entry)`` for the first pack that knows ``module.name``."""
        for lib, pack in self._packs.items():
            entry = pack.get_api(module, name)
            if entry is not None:
                return lib, entry
        return None

    def suggest_correction(
        self, module: str, name: str
    ) -> Optional[Tuple[str, str]]:
        """Suggest a correction across all packs.

        Returns ``(library_name, suggested_name)`` or *None*.
        """
        best: Optional[Tuple[str, str]] = None
        best_ratio = 0.0

        for lib, pack in self._packs.items():
            suggestion = pack.suggest_correction(module, name)
            if suggestion is not None:
                ratio = difflib.SequenceMatcher(None, name, suggestion).ratio()
                if ratio > best_ratio:
                    best_ratio = ratio
                    best = (lib, suggestion)

        return best

    def get_type_rule(self, func_name: str) -> Optional[Tuple[str, TypeRule]]:
        """Return ``(library_name, rule)`` from the first pack that has a rule."""
        for lib, pack in self._packs.items():
            rule = pack.get_type_rule(func_name)
            if rule is not None:
                return lib, rule
        return None

    def structural_postcondition(
        self, func_name: str, args: Dict[str, Any]
    ) -> Optional[str]:
        """Query all packs for a structural postcondition."""
        for pack in self._packs.values():
            pc = pack.structural_postcondition(func_name, args)
            if pc is not None:
                return pc
        return None

    def semantic_postcondition(
        self, func_name: str, args: Dict[str, Any]
    ) -> Optional[str]:
        """Query all packs for a semantic postcondition."""
        for pack in self._packs.values():
            pc = pack.semantic_postcondition(func_name, args)
            if pc is not None:
                return pc
        return None

    # -- axiom aggregation ---------------------------------------------------

    def combined_lean_axioms(self) -> str:
        """Return all axioms from every pack as a single Lean 4 block."""
        sections: List[str] = []
        for pack in self._packs.values():
            axioms = pack.lean_axioms()
            if axioms:
                header = (
                    f"-- ═══════════════════════════════════════\n"
                    f"-- Theory pack: {pack.meta.name}\n"
                    f"-- Library:     {pack.meta.library_name} "
                    f"v{pack.meta.library_version}\n"
                    f"-- ═══════════════════════════════════════"
                )
                sections.append(header + "\n\n" + "\n\n".join(axioms))
        return "\n\n".join(sections)

    # -- introspection -------------------------------------------------------

    def summary(self) -> str:
        """Human-readable summary of all registered packs."""
        lines = [f"TheoryRegistry ({len(self._packs)} packs):"]
        for pack in self._packs.values():
            lines.append(f"  • {pack.summary()}")
        return "\n".join(lines)

    def __len__(self) -> int:
        return len(self._packs)

    def __contains__(self, library_name: str) -> bool:
        return library_name in self._packs

    def __repr__(self) -> str:  # pragma: no cover
        return f"<TheoryRegistry packs={list(self._packs.keys())}>"
