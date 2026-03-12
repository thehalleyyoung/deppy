"""Ghost variable declarations for specification-only state.

Ghost variables are specification-level entities that do not exist in
the executable program but are used in contracts and proofs to express
properties.  They are the sheaf-descent analog of auxiliary variables
in Hoare logic: they enrich local sections with additional refinement
dimensions that are erased before code generation.

GhostVariable: A single ghost variable declaration.
GhostState: A collection of ghost variables tracking specification state
            through execution.
GhostUpdate: A single state transition for a ghost variable.
"""

from __future__ import annotations

import copy
import uuid
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterator,
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
    SiteKind,
    TrustLevel,
)
from deppy.contracts.base import (
    Contract,
    ContractSet,
    Predicate,
    PredicateKind,
    SourceLocation,
    Term,
    TermKind,
)


# ===================================================================
#  Ghost variable types
# ===================================================================


@dataclass(frozen=True)
class GhostTypeInfo:
    """Type information for a ghost variable."""

    _type_name: str
    _is_collection: bool = False
    _element_type: Optional[str] = None
    _is_numeric: bool = False
    _is_boolean: bool = False

    @property
    def type_name(self) -> str:
        return self._type_name

    @property
    def is_collection(self) -> bool:
        return self._is_collection

    @property
    def element_type(self) -> Optional[str]:
        return self._element_type

    @property
    def is_numeric(self) -> bool:
        return self._is_numeric

    @property
    def is_boolean(self) -> bool:
        return self._is_boolean

    def pretty(self) -> str:
        if self._is_collection and self._element_type:
            return f"{self._type_name}[{self._element_type}]"
        return self._type_name

    @classmethod
    def from_string(cls, type_str: str) -> GhostTypeInfo:
        """Parse a type string into GhostTypeInfo."""
        type_str = type_str.strip()
        is_numeric = type_str.lower() in ("int", "float", "complex", "number")
        is_boolean = type_str.lower() in ("bool", "boolean")

        # Check for collection types
        collection_types = ("list", "set", "frozenset", "tuple", "sequence", "multiset")
        is_collection = False
        element_type = None
        for ct in collection_types:
            if type_str.lower().startswith(ct):
                is_collection = True
                # Extract element type from brackets
                if "[" in type_str and "]" in type_str:
                    start = type_str.index("[") + 1
                    end = type_str.rindex("]")
                    element_type = type_str[start:end].strip()
                break

        return cls(
            _type_name=type_str,
            _is_collection=is_collection,
            _element_type=element_type,
            _is_numeric=is_numeric,
            _is_boolean=is_boolean,
        )


# ===================================================================
#  Ghost variable
# ===================================================================


@dataclass(frozen=True)
class GhostVariable:
    """A specification-only variable that enriches type analysis.

    Ghost variables exist only in the logical layer -- they are used
    in contracts and proofs but erased from generated code.
    """

    _name: str
    _type_info: GhostTypeInfo
    _initial_value: Any = None
    _description: str = ""
    _scope: str = ""
    _uid: str = field(default_factory=lambda: uuid.uuid4().hex[:12])

    @property
    def name(self) -> str:
        return self._name

    @property
    def type_info(self) -> GhostTypeInfo:
        return self._type_info

    @property
    def initial_value(self) -> Any:
        return self._initial_value

    @property
    def description(self) -> str:
        return self._description

    @property
    def scope(self) -> str:
        return self._scope

    @property
    def uid(self) -> str:
        return self._uid

    def to_term(self) -> Term:
        """Convert to a Term for use in predicates."""
        return Term.var(f"ghost${self._name}")

    def to_refinement_key(self) -> str:
        """Produce the refinement key under which this ghost is stored."""
        return f"ghost:{self._name}"

    def pretty(self) -> str:
        parts = [f"ghost {self._name}: {self._type_info.pretty()}"]
        if self._initial_value is not None:
            parts.append(f" = {self._initial_value!r}")
        if self._description:
            parts.append(f"  // {self._description}")
        return "".join(parts)


# ===================================================================
#  Ghost update
# ===================================================================


@dataclass(frozen=True)
class GhostUpdate:
    """A state transition for a ghost variable.

    Records what value the ghost takes after a specific program point.
    """

    _ghost_name: str
    _new_value: Any
    _site_id: Optional[SiteId] = None
    _condition: Optional[str] = None
    _provenance: str = "update"

    @property
    def ghost_name(self) -> str:
        return self._ghost_name

    @property
    def new_value(self) -> Any:
        return self._new_value

    @property
    def site_id(self) -> Optional[SiteId]:
        return self._site_id

    @property
    def condition(self) -> Optional[str]:
        return self._condition

    @property
    def provenance(self) -> str:
        return self._provenance

    def pretty(self) -> str:
        cond = f" when {self._condition}" if self._condition else ""
        return f"ghost${self._ghost_name} := {self._new_value!r}{cond}"


# ===================================================================
#  Ghost state
# ===================================================================


class GhostState:
    """Track ghost variable state through execution.

    Maintains a mapping from ghost variable names to their current values,
    updated as the analysis progresses through program points.  Supports
    snapshots for branching and joins for merging.
    """

    def __init__(self) -> None:
        self._variables: Dict[str, GhostVariable] = {}
        self._values: Dict[str, Any] = {}
        self._history: List[GhostUpdate] = []
        self._snapshots: List[Dict[str, Any]] = []

    # -- Declaration -------------------------------------------------------

    def declare(
        self,
        name: str,
        type_str: str,
        initial_value: Any = None,
        description: str = "",
        scope: str = "",
    ) -> GhostVariable:
        """Declare a new ghost variable.

        Parameters
        ----------
        name : str
            The ghost variable name.
        type_str : str
            Type annotation as a string.
        initial_value : Any
            Initial value (default None).
        description : str
            Human-readable description.
        scope : str
            Scope qualifier (e.g., function name).

        Returns
        -------
        GhostVariable
            The declared ghost variable.
        """
        if name in self._variables:
            raise ValueError(f"Ghost variable '{name}' already declared")

        type_info = GhostTypeInfo.from_string(type_str)
        ghost = GhostVariable(
            _name=name,
            _type_info=type_info,
            _initial_value=initial_value,
            _description=description,
            _scope=scope,
        )
        self._variables[name] = ghost
        self._values[name] = initial_value
        return ghost

    # -- Access ------------------------------------------------------------

    def get(self, name: str) -> Any:
        """Get the current value of a ghost variable.

        Raises KeyError if the variable is not declared.
        """
        if name not in self._variables:
            raise KeyError(f"Ghost variable '{name}' not declared")
        return self._values.get(name)

    def get_variable(self, name: str) -> Optional[GhostVariable]:
        """Get the GhostVariable metadata for a ghost variable."""
        return self._variables.get(name)

    def has(self, name: str) -> bool:
        """Check if a ghost variable is declared."""
        return name in self._variables

    # -- Update ------------------------------------------------------------

    def update(
        self,
        name: str,
        new_value: Any,
        site_id: Optional[SiteId] = None,
        condition: Optional[str] = None,
    ) -> GhostUpdate:
        """Update a ghost variable's value.

        Records the update in history for audit purposes.
        """
        if name not in self._variables:
            raise KeyError(f"Ghost variable '{name}' not declared")

        self._values[name] = new_value

        update_record = GhostUpdate(
            _ghost_name=name,
            _new_value=new_value,
            _site_id=site_id,
            _condition=condition,
        )
        self._history.append(update_record)
        return update_record

    def increment(
        self,
        name: str,
        amount: Any = 1,
        site_id: Optional[SiteId] = None,
    ) -> GhostUpdate:
        """Increment a numeric ghost variable."""
        current = self.get(name)
        if current is None:
            current = 0
        new_value = current + amount
        return self.update(name, new_value, site_id=site_id)

    def append_to(
        self,
        name: str,
        element: Any,
        site_id: Optional[SiteId] = None,
    ) -> GhostUpdate:
        """Append an element to a collection ghost variable."""
        current = self.get(name)
        if current is None:
            current = []
        if isinstance(current, (list, tuple)):
            new_value = list(current) + [element]
        elif isinstance(current, set):
            new_value = current | {element}
        else:
            new_value = [current, element]
        return self.update(name, new_value, site_id=site_id)

    def union_with(
        self,
        name: str,
        elements: Any,
        site_id: Optional[SiteId] = None,
    ) -> GhostUpdate:
        """Union a set ghost variable with new elements."""
        current = self.get(name)
        if current is None:
            current = set()
        if isinstance(current, (set, frozenset)):
            new_value = set(current) | set(elements)
        else:
            new_value = set(elements)
        return self.update(name, new_value, site_id=site_id)

    # -- Snapshot and branching -------------------------------------------

    def snapshot(self) -> Dict[str, Any]:
        """Take a snapshot of the current ghost state.

        Returns a copy of the current values that can be restored later.
        """
        snap = dict(self._values)
        self._snapshots.append(snap)
        return snap

    def restore(self, snapshot: Dict[str, Any]) -> None:
        """Restore ghost state from a snapshot."""
        self._values = dict(snapshot)

    def fork(self) -> GhostState:
        """Create an independent copy of this ghost state.

        Used when analysis branches (e.g., if/else).
        """
        new_state = GhostState()
        new_state._variables = dict(self._variables)
        new_state._values = dict(self._values)
        new_state._history = list(self._history)
        return new_state

    def join(self, other: GhostState) -> GhostState:
        """Join two ghost states (merge after branching).

        For numeric values, takes the upper bound.
        For collections, takes the union.
        For booleans, takes disjunction.
        For incompatible types, uses None (unknown).
        """
        result = GhostState()
        all_names = set(self._variables.keys()) | set(other._variables.keys())

        for name in all_names:
            # Declare in result
            var = self._variables.get(name) or other._variables.get(name)
            if var is None:
                continue
            result._variables[name] = var

            val_a = self._values.get(name)
            val_b = other._values.get(name)

            if val_a is None and val_b is None:
                result._values[name] = None
            elif val_a is None:
                result._values[name] = val_b
            elif val_b is None:
                result._values[name] = val_a
            elif isinstance(val_a, (int, float)) and isinstance(val_b, (int, float)):
                result._values[name] = max(val_a, val_b)
            elif isinstance(val_a, bool) and isinstance(val_b, bool):
                result._values[name] = val_a or val_b
            elif isinstance(val_a, (set, frozenset)) and isinstance(val_b, (set, frozenset)):
                result._values[name] = set(val_a) | set(val_b)
            elif isinstance(val_a, (list, tuple)) and isinstance(val_b, (list, tuple)):
                # Union of elements preserving order
                seen: Set[Any] = set()
                merged: List[Any] = []
                for item in list(val_a) + list(val_b):
                    key = id(item) if not isinstance(item, (int, float, str, bool)) else item
                    if key not in seen:
                        seen.add(key)
                        merged.append(item)
                result._values[name] = merged
            elif val_a == val_b:
                result._values[name] = val_a
            else:
                result._values[name] = None  # cannot merge

        result._history = self._history + other._history
        return result

    # -- Section integration -----------------------------------------------

    def to_refinements(self) -> Dict[str, Any]:
        """Export ghost state as refinement key/value pairs.

        Each ghost variable produces a refinement entry with a
        ``ghost:`` prefixed key.
        """
        result: Dict[str, Any] = {}
        for name, value in self._values.items():
            result[f"ghost:{name}"] = value
        return result

    def enrich_section(self, section: LocalSection) -> LocalSection:
        """Add ghost state refinements to a local section."""
        ghost_refs = self.to_refinements()
        if not ghost_refs:
            return section

        merged = dict(section.refinements)
        merged.update(ghost_refs)

        return LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=merged,
            trust=section.trust,
            provenance=f"{section.provenance or ''}:ghost_enriched",
        )

    @staticmethod
    def strip_ghost_refinements(section: LocalSection) -> LocalSection:
        """Remove all ghost refinements from a section.

        Used before code generation to erase specification-only state.
        """
        cleaned = {
            k: v for k, v in section.refinements.items()
            if not k.startswith("ghost:")
        }
        return LocalSection(
            site_id=section.site_id,
            carrier_type=section.carrier_type,
            refinements=cleaned,
            trust=section.trust,
            provenance=section.provenance,
        )

    # -- Inspection --------------------------------------------------------

    @property
    def variables(self) -> Dict[str, GhostVariable]:
        return dict(self._variables)

    @property
    def values(self) -> Dict[str, Any]:
        return dict(self._values)

    @property
    def history(self) -> List[GhostUpdate]:
        return list(self._history)

    @property
    def variable_names(self) -> FrozenSet[str]:
        return frozenset(self._variables.keys())

    def __len__(self) -> int:
        return len(self._variables)

    def __contains__(self, name: str) -> bool:
        return name in self._variables

    def __iter__(self) -> Iterator[str]:
        return iter(self._variables)

    def pretty(self) -> str:
        lines: List[str] = ["GhostState:"]
        for name, var in sorted(self._variables.items()):
            value = self._values.get(name)
            lines.append(f"  {var.pretty()} [current: {value!r}]")
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"GhostState({len(self._variables)} vars, {len(self._history)} updates)"


# ===================================================================
#  Ghost contract (decorator)
# ===================================================================


class GhostContract(Contract):
    """Contract that declares ghost variables for a scope.

    Ghost contracts seed the analysis with specification-level state
    that enriches the local sections with auxiliary refinements.
    """

    def __init__(
        self,
        declarations: Sequence[Tuple[str, str, Any]],
        *,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
        provenance: str = "ghost_declaration",
    ) -> None:
        super().__init__(
            source_location=source_location,
            trust=trust,
            provenance=provenance,
        )
        self._declarations = tuple(declarations)
        self._ghost_state = GhostState()
        for name, type_str, initial in self._declarations:
            self._ghost_state.declare(name, type_str, initial)

    @property
    def declarations(self) -> Tuple[Tuple[str, str, Any], ...]:
        return self._declarations

    @property
    def ghost_state(self) -> GhostState:
        return self._ghost_state

    def to_predicate(self) -> Predicate:
        """Ghost declarations are logically true (they add structure, not constraints)."""
        return Predicate.true_()

    def to_boundary_seed(self) -> Any:
        """Project to a boundary seed."""
        return {
            "kind": "ghost",
            "variables": {
                name: {"type": type_str, "initial": initial}
                for name, type_str, initial in self._declarations
            },
        }

    def pretty(self) -> str:
        vars_str = ", ".join(
            f"{name}: {type_str}" for name, type_str, _ in self._declarations
        )
        return f"@ghost({vars_str})"


def ghost(
    *declarations: Tuple[str, str, Any],
    **named_declarations: Any,
) -> Callable[[Any], Any]:
    """Decorator to declare ghost variables for a function.

    Usage::

        @ghost(("counter", "int", 0), ("seen", "Set[str]", set()))
        def process(items: List[str]) -> None: ...

        @ghost(counter=("int", 0), seen=("Set[str]", set()))
        def process(items: List[str]) -> None: ...
    """
    all_decls: List[Tuple[str, str, Any]] = list(declarations)
    for name, (type_str, initial) in named_declarations.items():
        all_decls.append((name, type_str, initial))

    contract = GhostContract(all_decls)

    def decorator(fn: Any) -> Any:
        if not hasattr(fn, "_deppy_contracts"):
            fn._deppy_contracts = ContractSet()
        fn._deppy_contracts.theorems.append(contract)
        # Attach ghost state for runtime access
        fn._deppy_ghost_state = contract.ghost_state
        return fn

    return decorator
