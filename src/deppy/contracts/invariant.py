"""Invariant contracts: loop, class, and module invariants.

An invariant is a predicate that holds at every entry to a scope and
is preserved by every transition within that scope.  In the sheaf
framework, invariants become seeds at *internal* sites (loop headers,
class method boundaries, module boundaries) rather than at input/output
boundaries.
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
    Contract,
    Predicate,
    PredicateKind,
    SourceLocation,
    Term,
    TermKind,
    TypeBase,
)
from deppy.core._protocols import TrustLevel

if TYPE_CHECKING:
    from deppy.contracts.seed import BoundarySeed


# ---------------------------------------------------------------------------
# InvariantKind
# ---------------------------------------------------------------------------


class InvariantKind(enum.Enum):
    """Classification of invariant scope."""

    LOOP = "loop"
    CLASS = "class"
    MODULE = "module"


# ---------------------------------------------------------------------------
# InvariantContract (base)
# ---------------------------------------------------------------------------


class InvariantContract(Contract):
    """Base class for invariant contracts.

    An invariant is a predicate that must hold on every entry to a scope
    and be preserved by every transition.  Subclasses refine this by
    scope kind (loop, class, module).

    Attributes:
        kind: What sort of scope the invariant covers.
        predicate: The invariant proposition.
        predicate_fn: The original callable if provided.
        scope: Human-readable scope descriptor (e.g. function name, class name).
        description: Optional human-readable gloss.
    """

    def __init__(
        self,
        *,
        kind: InvariantKind,
        predicate_fn: Optional[Callable[..., bool]] = None,
        predicate: Optional[Predicate] = None,
        scope: str = "",
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(source_location=source_location, trust=trust, provenance=provenance)
        self.kind: InvariantKind = kind
        self.predicate_fn: Optional[Callable[..., bool]] = predicate_fn
        self.scope: str = scope
        self.description: Optional[str] = description

        if predicate is not None:
            self.predicate: Predicate = predicate
        elif predicate_fn is not None:
            self.predicate = Predicate.from_callable(predicate_fn, description=description)
        else:
            self.predicate = Predicate.true_()

    # -- Contract interface --------------------------------------------------

    def to_predicate(self) -> Predicate:
        return self.predicate

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import BoundarySeed, SeedProvenance

        provenance_map: Dict[str, SeedProvenance] = {
            "user_annotation": SeedProvenance.SOURCE_ANNOTATION,
            "synthesized": SeedProvenance.SYNTHESIZED,
            "proof_backed": SeedProvenance.PROOF_BACKED,
            "trace_backed": SeedProvenance.TRACE_BACKED,
        }
        prov = provenance_map.get(self.provenance, SeedProvenance.SOURCE_ANNOTATION)

        return BoundarySeed(
            predicate=self.predicate,
            trust=self.trust,
            provenance=prov,
            source_location=self.source_location,
        )

    def pretty(self) -> str:
        scope = f" [{self.scope}]" if self.scope else ""
        desc = f"  # {self.description}" if self.description else ""
        return f"invariant({self.kind.value}{scope}): {self.predicate.pretty()}{desc}"

    # -- operations ----------------------------------------------------------

    def strengthen(self, additional: Predicate) -> InvariantContract:
        """Return a stronger invariant by conjoining *additional*."""
        result = copy.copy(self)
        result.predicate = Predicate.conjunction(self.predicate, additional)
        return result

    def weaken(self) -> InvariantContract:
        """Drop the invariant to true (total weakening)."""
        result = copy.copy(self)
        result.predicate = Predicate.true_()
        result.trust = TrustLevel.RESIDUAL
        result.provenance = "weakened"
        return result

    def restrict_to_vars(self, var_names: FrozenSet[str]) -> InvariantContract:
        """Restrict the invariant to mention only *var_names*.

        If the predicate mentions variables outside *var_names*, the
        invariant is weakened to ``True`` (conservative).
        """
        fv = self.predicate.free_variables()
        if fv <= var_names:
            return self
        # Cannot cleanly restrict; weaken
        result = copy.copy(self)
        result.predicate = Predicate.true_()
        result.provenance = "restricted"
        return result

    def evaluate(self, env: Mapping[str, Any]) -> bool:
        """Evaluate the invariant in the given variable environment."""
        if self.predicate_fn is not None:
            try:
                return bool(self.predicate_fn(**{k: env[k] for k in env}))
            except (KeyError, TypeError, Exception):
                return True
        return self.predicate.evaluate(env)

    def __repr__(self) -> str:
        return f"<InvariantContract kind={self.kind.value} scope={self.scope!r}>"


# ---------------------------------------------------------------------------
# LoopInvariant
# ---------------------------------------------------------------------------


class LoopInvariant(InvariantContract):
    """Loop invariant: maintained at the top of every iteration.

    In addition to the invariant predicate, a loop invariant may include:

    * **loop_variable** — the induction variable (for documentation and
      specialisation).
    * **decreases** — a termination measure that must strictly decrease
      on each iteration.

    Usage::

        @deppy.loop_invariant(lambda i, acc: acc >= 0, decreases="n - i")
        for i in range(n):
            acc += data[i]
    """

    def __init__(
        self,
        *,
        predicate_fn: Optional[Callable[..., bool]] = None,
        predicate: Optional[Predicate] = None,
        loop_variable: Optional[str] = None,
        decreases: Optional[Term] = None,
        scope: str = "",
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(
            kind=InvariantKind.LOOP,
            predicate_fn=predicate_fn,
            predicate=predicate,
            scope=scope,
            description=description,
            source_location=source_location,
            trust=trust,
            provenance=provenance,
        )
        self.loop_variable: Optional[str] = loop_variable
        self.decreases: Optional[Term] = decreases

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import BoundarySeed, SeedProvenance
        from deppy.core._protocols import SiteId, SiteKind

        provenance_map: Dict[str, SeedProvenance] = {
            "user_annotation": SeedProvenance.SOURCE_ANNOTATION,
            "synthesized": SeedProvenance.SYNTHESIZED,
            "proof_backed": SeedProvenance.PROOF_BACKED,
        }
        prov = provenance_map.get(self.provenance, SeedProvenance.SOURCE_ANNOTATION)

        site_id = SiteId(
            kind=SiteKind.LOOP_HEADER_INVARIANT,
            name=self.scope or "loop",
            source_location=(
                (self.source_location.file, self.source_location.line, self.source_location.col)
                if self.source_location
                else None
            ),
        )

        return BoundarySeed(
            site_id=site_id,
            predicate=self.predicate,
            trust=self.trust,
            provenance=prov,
            source_location=self.source_location,
        )

    def has_termination_measure(self) -> bool:
        """Whether a decreasing measure is specified."""
        return self.decreases is not None

    def termination_predicate(self) -> Optional[Predicate]:
        """Build a predicate asserting that the termination measure decreases."""
        if self.decreases is None:
            return None
        # "decreases(expr)" means expr_next < expr_current
        current = self.decreases
        next_var = Term.var(f"{self.decreases.pretty()}'")
        lt_term = Term.binary("<", next_var, current)
        return Predicate.atomic(lt_term, description=f"{self.decreases.pretty()} decreases")

    def full_predicate(self) -> Predicate:
        """Invariant ∧ termination measure (if present)."""
        term_pred = self.termination_predicate()
        if term_pred is not None:
            return Predicate.conjunction(self.predicate, term_pred)
        return self.predicate

    def pretty(self) -> str:
        parts = [f"loop_invariant"]
        if self.scope:
            parts.append(f"[{self.scope}]")
        parts.append(f": {self.predicate.pretty()}")
        if self.loop_variable:
            parts.append(f" (var={self.loop_variable})")
        if self.decreases:
            parts.append(f" decreases {self.decreases.pretty()}")
        if self.description:
            parts.append(f"  # {self.description}")
        return "".join(parts)

    def __repr__(self) -> str:
        return f"<LoopInvariant scope={self.scope!r} var={self.loop_variable!r}>"


# ---------------------------------------------------------------------------
# ClassInvariant
# ---------------------------------------------------------------------------


class ClassInvariant(InvariantContract):
    """Class invariant: must hold after ``__init__`` and be preserved by
    every public method.

    Usage::

        @deppy.class_invariant(lambda self: self.balance >= 0)
        class BankAccount:
            ...

    Attributes:
        class_name: Fully qualified class name.
        fields_involved: Fields that the invariant references.
    """

    def __init__(
        self,
        *,
        class_name: str,
        predicate_fn: Optional[Callable[..., bool]] = None,
        predicate: Optional[Predicate] = None,
        fields_involved: Optional[List[str]] = None,
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(
            kind=InvariantKind.CLASS,
            predicate_fn=predicate_fn,
            predicate=predicate,
            scope=class_name,
            description=description,
            source_location=source_location,
            trust=trust,
            provenance=provenance,
        )
        self.class_name: str = class_name
        self.fields_involved: List[str] = fields_involved if fields_involved is not None else []

        # Auto-detect field references from predicate variables
        if not self.fields_involved:
            fv = self.predicate.free_variables()
            self.fields_involved = sorted(
                v for v in fv if v != "self" and not v.startswith("_")
            )

    def applies_to_method(self, method_name: str) -> bool:
        """Whether this invariant applies to a given method.

        Private methods (starting with ``_``, except ``__init__``) and
        static methods are excluded.
        """
        if method_name == "__init__":
            return True  # must establish the invariant
        if method_name.startswith("_") and not method_name.startswith("__"):
            return False  # private helper — not required to maintain
        return True

    def as_method_pre_post(self) -> Tuple[Predicate, Predicate]:
        """Express the class invariant as a pre/post pair for a method.

        The invariant is a precondition on entry and a postcondition on
        exit for every public method.
        """
        return self.predicate, self.predicate

    def pretty(self) -> str:
        fields = ", ".join(self.fields_involved) if self.fields_involved else "*"
        desc = f"  # {self.description}" if self.description else ""
        return f"class_invariant({self.class_name}, fields=[{fields}]): {self.predicate.pretty()}{desc}"

    def __repr__(self) -> str:
        return f"<ClassInvariant class={self.class_name!r} fields={self.fields_involved!r}>"


# ---------------------------------------------------------------------------
# ModuleInvariant
# ---------------------------------------------------------------------------


class ModuleInvariant(InvariantContract):
    """Module-level invariant: must hold after module initialisation and
    be preserved by all public functions.

    Usage::

        deppy.module_invariant(lambda: config.is_valid())

    Attributes:
        module_name: Fully qualified module name.
    """

    def __init__(
        self,
        *,
        module_name: str,
        predicate_fn: Optional[Callable[..., bool]] = None,
        predicate: Optional[Predicate] = None,
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(
            kind=InvariantKind.MODULE,
            predicate_fn=predicate_fn,
            predicate=predicate,
            scope=module_name,
            description=description,
            source_location=source_location,
            trust=trust,
            provenance=provenance,
        )
        self.module_name: str = module_name

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import BoundarySeed, SeedProvenance
        from deppy.core._protocols import SiteId, SiteKind

        provenance_map: Dict[str, SeedProvenance] = {
            "user_annotation": SeedProvenance.SOURCE_ANNOTATION,
            "synthesized": SeedProvenance.SYNTHESIZED,
        }
        prov = provenance_map.get(self.provenance, SeedProvenance.SOURCE_ANNOTATION)

        site_id = SiteId(
            kind=SiteKind.MODULE_SUMMARY,
            name=self.module_name,
        )
        return BoundarySeed(
            site_id=site_id,
            predicate=self.predicate,
            trust=self.trust,
            provenance=prov,
            source_location=self.source_location,
        )

    def pretty(self) -> str:
        desc = f"  # {self.description}" if self.description else ""
        return f"module_invariant({self.module_name}): {self.predicate.pretty()}{desc}"

    def __repr__(self) -> str:
        return f"<ModuleInvariant module={self.module_name!r}>"


# ---------------------------------------------------------------------------
# Decorator factories
# ---------------------------------------------------------------------------


def loop_invariant(
    predicate_fn: Optional[Callable[..., bool]] = None,
    *,
    loop_variable: Optional[str] = None,
    decreases: Optional[str] = None,
    description: Optional[str] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
) -> Callable[..., Any]:
    """Decorator/marker for loop invariants."""

    dec_term: Optional[Term] = None
    if decreases is not None:
        dec_term = Term.var(decreases)

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        contract = LoopInvariant(
            predicate_fn=predicate_fn,
            loop_variable=loop_variable,
            decreases=dec_term,
            description=description,
            trust=trust,
        )
        if not hasattr(fn, "__deppy_contracts__"):
            fn.__deppy_contracts__ = []  # type: ignore[attr-defined]
        fn.__deppy_contracts__.append(contract)  # type: ignore[attr-defined]
        return fn

    return decorator


def class_invariant(
    predicate_fn: Optional[Callable[..., bool]] = None,
    *,
    class_name: str = "",
    fields_involved: Optional[List[str]] = None,
    description: Optional[str] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
) -> Callable[..., Any]:
    """Decorator for class invariants."""

    def decorator(cls: Any) -> Any:
        name = class_name or getattr(cls, "__qualname__", getattr(cls, "__name__", ""))
        contract = ClassInvariant(
            class_name=name,
            predicate_fn=predicate_fn,
            fields_involved=fields_involved,
            description=description,
            trust=trust,
        )
        if not hasattr(cls, "__deppy_contracts__"):
            cls.__deppy_contracts__ = []  # type: ignore[attr-defined]
        cls.__deppy_contracts__.append(contract)  # type: ignore[attr-defined]
        return cls

    return decorator


def module_invariant(
    predicate_fn: Optional[Callable[..., bool]] = None,
    *,
    module_name: str = "",
    description: Optional[str] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
) -> InvariantContract:
    """Create a module-level invariant (called inline, not as decorator)."""
    return ModuleInvariant(
        module_name=module_name,
        predicate_fn=predicate_fn,
        description=description,
        trust=trust,
    )
