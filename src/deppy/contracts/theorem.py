"""Theorem, lemma, transport, and assumption contracts.

These contracts represent *logical declarations* rather than runtime
checks.  A ``TheoremContract`` declares that a proposition is provably
true; a ``LemmaContract`` is an intermediate step; a
``TransportContract`` declares that a fact can be carried between types;
an ``AssumptionContract`` is an unproven hypothesis.
"""

from __future__ import annotations

import copy
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
# TheoremContract
# ---------------------------------------------------------------------------


class TheoremContract(Contract):
    """Theorem declaration: ``@deppy.theorem``.

    A theorem is a named proposition together with a proof body.  The
    proof body is the function itself — DepPy treats it as a constructive
    proof that produces a witness for the statement.

    Attributes:
        name: Theorem identifier (typically the function name).
        statement: The proposition being proved.
        proof_body: The proof code (retained as the raw AST or callable).
        dependencies: Other theorems/lemmas used in the proof.
        description: Optional human-readable gloss.
    """

    def __init__(
        self,
        *,
        name: str,
        statement: Optional[Predicate] = None,
        statement_fn: Optional[Callable[..., bool]] = None,
        proof_body: Optional[Any] = None,
        dependencies: Optional[List[str]] = None,
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.PROOF_BACKED,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(source_location=source_location, trust=trust, provenance=provenance)
        self.name: str = name
        self.proof_body: Optional[Any] = proof_body
        self.dependencies: List[str] = dependencies if dependencies is not None else []
        self.description: Optional[str] = description

        if statement is not None:
            self.statement: Predicate = statement
        elif statement_fn is not None:
            self.statement = Predicate.from_callable(statement_fn, description=description)
        else:
            self.statement = Predicate.true_()

    # -- Contract interface --------------------------------------------------

    def to_predicate(self) -> Predicate:
        return self.statement

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import OutputBoundarySeed, SeedProvenance
        from deppy.core._protocols import SiteId, SiteKind

        site_id = SiteId(
            kind=SiteKind.PROOF,
            name=self.name,
            source_location=(
                (self.source_location.file, self.source_location.line, self.source_location.col)
                if self.source_location
                else None
            ),
        )
        return OutputBoundarySeed(
            site_id=site_id,
            predicate=self.statement,
            trust=self.trust,
            provenance=SeedProvenance.PROOF_BACKED,
            source_location=self.source_location,
            result_component=f"theorem:{self.name}",
            guarantee=self.statement,
        )

    def pretty(self) -> str:
        deps = ""
        if self.dependencies:
            deps = f" using [{', '.join(self.dependencies)}]"
        desc = f"  # {self.description}" if self.description else ""
        return f"theorem {self.name}: {self.statement.pretty()}{deps}{desc}"

    # -- operations ----------------------------------------------------------

    def has_proof(self) -> bool:
        """Whether a proof body is attached."""
        return self.proof_body is not None

    def add_dependency(self, dep_name: str) -> TheoremContract:
        """Return a copy with an additional dependency."""
        result = copy.copy(self)
        result.dependencies = list(self.dependencies) + [dep_name]
        return result

    def specialize(self, bindings: Dict[str, Term]) -> TheoremContract:
        """Specialise the theorem statement by substituting variables."""
        result = copy.copy(self)
        result.statement = self.statement.substitute(bindings)
        return result

    def dependency_graph_entry(self) -> Tuple[str, List[str]]:
        """Return ``(name, dependencies)`` for dependency graph construction."""
        return self.name, list(self.dependencies)

    def __repr__(self) -> str:
        has_proof = "✓" if self.has_proof() else "✗"
        return f"<TheoremContract {self.name!r} proof={has_proof}>"


# ---------------------------------------------------------------------------
# LemmaContract
# ---------------------------------------------------------------------------


class LemmaContract(Contract):
    """Intermediate lemma used in proofs.

    A lemma is structurally identical to a theorem but is not part of
    the public API — it is used internally by other proofs.

    Attributes:
        name: Lemma identifier.
        statement: The proposition.
        used_by: Theorems that use this lemma.
        description: Optional gloss.
    """

    def __init__(
        self,
        *,
        name: str,
        statement: Optional[Predicate] = None,
        statement_fn: Optional[Callable[..., bool]] = None,
        used_by: Optional[List[str]] = None,
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.PROOF_BACKED,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(source_location=source_location, trust=trust, provenance=provenance)
        self.name: str = name
        self.used_by: List[str] = used_by if used_by is not None else []
        self.description: Optional[str] = description

        if statement is not None:
            self.statement: Predicate = statement
        elif statement_fn is not None:
            self.statement = Predicate.from_callable(statement_fn, description=description)
        else:
            self.statement = Predicate.true_()

    def to_predicate(self) -> Predicate:
        return self.statement

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import OutputBoundarySeed, SeedProvenance

        return OutputBoundarySeed(
            predicate=self.statement,
            trust=self.trust,
            provenance=SeedProvenance.PROOF_BACKED,
            source_location=self.source_location,
            result_component=f"lemma:{self.name}",
            guarantee=self.statement,
        )

    def pretty(self) -> str:
        used = ""
        if self.used_by:
            used = f" (used by {', '.join(self.used_by)})"
        desc = f"  # {self.description}" if self.description else ""
        return f"lemma {self.name}: {self.statement.pretty()}{used}{desc}"

    def as_theorem(self) -> TheoremContract:
        """Promote this lemma to a full theorem."""
        return TheoremContract(
            name=self.name,
            statement=self.statement,
            description=self.description,
            source_location=self.source_location,
            trust=self.trust,
            provenance=self.provenance,
        )

    def specialize(self, bindings: Dict[str, Term]) -> LemmaContract:
        result = copy.copy(self)
        result.statement = self.statement.substitute(bindings)
        return result

    def __repr__(self) -> str:
        return f"<LemmaContract {self.name!r}>"


# ---------------------------------------------------------------------------
# TransportContract
# ---------------------------------------------------------------------------


class TransportContract(Contract):
    """Transport declaration: ``deppy.transport(source=..., target=...)``.

    A transport declares that a proposition can be carried from one type
    context to another.  In the sheaf framework this corresponds to a
    morphism between sites that preserves a specific section property.

    Attributes:
        source_prop: Proposition in the source context.
        target_prop: Proposition in the target context.
        transport_fn: Optional callable that performs the transport.
        description: Optional human-readable gloss.
    """

    def __init__(
        self,
        *,
        source_prop: Optional[Predicate] = None,
        target_prop: Optional[Predicate] = None,
        source_fn: Optional[Callable[..., bool]] = None,
        target_fn: Optional[Callable[..., bool]] = None,
        transport_fn: Optional[Callable[..., Any]] = None,
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.PROOF_BACKED,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(source_location=source_location, trust=trust, provenance=provenance)
        self.transport_fn: Optional[Callable[..., Any]] = transport_fn
        self.description: Optional[str] = description

        if source_prop is not None:
            self.source_prop: Predicate = source_prop
        elif source_fn is not None:
            self.source_prop = Predicate.from_callable(source_fn)
        else:
            self.source_prop = Predicate.true_()

        if target_prop is not None:
            self.target_prop: Predicate = target_prop
        elif target_fn is not None:
            self.target_prop = Predicate.from_callable(target_fn)
        else:
            self.target_prop = Predicate.true_()

    def to_predicate(self) -> Predicate:
        """The transport as an implication: source_prop → target_prop."""
        return Predicate.implication(self.source_prop, self.target_prop)

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import OutputBoundarySeed, SeedProvenance

        return OutputBoundarySeed(
            predicate=self.to_predicate(),
            trust=self.trust,
            provenance=SeedProvenance.PROOF_BACKED,
            source_location=self.source_location,
            result_component="transport",
            guarantee=self.to_predicate(),
        )

    def pretty(self) -> str:
        desc = f"  # {self.description}" if self.description else ""
        return f"transport: {self.source_prop.pretty()} → {self.target_prop.pretty()}{desc}"

    def to_transport_seed(self) -> Any:
        """Convert to a TransportSeed for the transport_seed module."""
        from deppy.contracts.transport_seed import TransportJustification, TransportSeed

        justification_map: Dict[str, TransportJustification] = {
            "user_annotation": TransportJustification.PROOF,
            "proof_backed": TransportJustification.PROOF,
            "theorem": TransportJustification.THEOREM,
            "library_pack": TransportJustification.LIBRARY,
            "observation": TransportJustification.OBSERVATION,
            "assumed": TransportJustification.ASSUMPTION,
        }
        just = justification_map.get(self.provenance, TransportJustification.PROOF)

        return TransportSeed(
            source_prop=self.source_prop,
            target_prop=self.target_prop,
            justification=just,
        )

    def reversed(self) -> TransportContract:
        """Return the reverse transport (swap source and target)."""
        return TransportContract(
            source_prop=self.target_prop,
            target_prop=self.source_prop,
            transport_fn=None,
            description=f"reverse of: {self.description}" if self.description else None,
            source_location=self.source_location,
            trust=self.trust,
            provenance=self.provenance,
        )

    def chain(self, other: TransportContract) -> TransportContract:
        """Chain two transports: self ; other.

        Requires ``self.target_prop`` to be compatible with ``other.source_prop``.
        """
        return TransportContract(
            source_prop=self.source_prop,
            target_prop=other.target_prop,
            description=f"chain({self.pretty()}, {other.pretty()})",
            source_location=self.source_location,
            trust=min(self.trust, other.trust, key=lambda t: _TRUST_ORD.get(t, 0)),
            provenance=self.provenance,
        )

    def __repr__(self) -> str:
        return f"<TransportContract {self.source_prop.pretty()!r} → {self.target_prop.pretty()!r}>"


# ---------------------------------------------------------------------------
# AssumptionContract
# ---------------------------------------------------------------------------


class AssumptionContract(Contract):
    """Explicit assumption: ``deppy.assume(...)``.

    An assumption is an unproven proposition that the programmer asserts
    to be true.  Assumptions carry the weakest trust level and create
    proof debt that should eventually be discharged.

    Attributes:
        proposition: The assumed proposition.
        justification: Why the programmer believes it's true.
        discharged: Whether the assumption has been proved elsewhere.
        discharged_by: Name of the theorem that discharged it.
    """

    def __init__(
        self,
        *,
        proposition: Optional[Predicate] = None,
        proposition_fn: Optional[Callable[..., bool]] = None,
        justification: Optional[str] = None,
        discharged: bool = False,
        discharged_by: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.ASSUMED,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(source_location=source_location, trust=trust, provenance=provenance)
        self.justification: Optional[str] = justification
        self.discharged: bool = discharged
        self.discharged_by: Optional[str] = discharged_by

        if proposition is not None:
            self.proposition: Predicate = proposition
        elif proposition_fn is not None:
            self.proposition = Predicate.from_callable(
                proposition_fn, description=justification,
            )
        else:
            self.proposition = Predicate.true_()

    def to_predicate(self) -> Predicate:
        return self.proposition

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import BoundarySeed, SeedProvenance

        return BoundarySeed(
            predicate=self.proposition,
            trust=self.trust,
            provenance=SeedProvenance.SOURCE_ANNOTATION,
            source_location=self.source_location,
        )

    def pretty(self) -> str:
        just = f"  // {self.justification}" if self.justification else ""
        status = ""
        if self.discharged:
            status = f" [discharged by {self.discharged_by}]"
        return f"assume: {self.proposition.pretty()}{just}{status}"

    def discharge(self, theorem_name: str) -> AssumptionContract:
        """Mark this assumption as discharged by a theorem."""
        result = copy.copy(self)
        result.discharged = True
        result.discharged_by = theorem_name
        result.trust = TrustLevel.PROOF_BACKED
        result.provenance = "discharged"
        return result

    def is_discharged(self) -> bool:
        return self.discharged

    def creates_proof_debt(self) -> bool:
        """Whether this assumption represents outstanding proof debt."""
        return not self.discharged

    def __repr__(self) -> str:
        status = "discharged" if self.discharged else "open"
        return f"<AssumptionContract [{status}] {self.proposition.pretty()!r}>"


# ---------------------------------------------------------------------------
# Decorator factories
# ---------------------------------------------------------------------------


def theorem(
    name: Optional[str] = None,
    *,
    statement: Optional[Callable[..., bool]] = None,
    dependencies: Optional[List[str]] = None,
    description: Optional[str] = None,
) -> Callable[..., Any]:
    """Decorator factory for ``@deppy.theorem``.

    Usage::

        @theorem("triangle_inequality")
        def tri_ineq(a, b, c):
            ...  # proof body
    """

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        thm_name = name or fn.__name__
        contract = TheoremContract(
            name=thm_name,
            statement_fn=statement,
            proof_body=fn,
            dependencies=dependencies,
            description=description,
        )
        if not hasattr(fn, "__deppy_contracts__"):
            fn.__deppy_contracts__ = []  # type: ignore[attr-defined]
        fn.__deppy_contracts__.append(contract)  # type: ignore[attr-defined]
        return fn

    return decorator


def lemma(
    name: Optional[str] = None,
    *,
    statement: Optional[Callable[..., bool]] = None,
    description: Optional[str] = None,
) -> Callable[..., Any]:
    """Decorator factory for ``@deppy.lemma``."""

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        lem_name = name or fn.__name__
        contract = LemmaContract(
            name=lem_name,
            statement_fn=statement,
            description=description,
        )
        if not hasattr(fn, "__deppy_contracts__"):
            fn.__deppy_contracts__ = []  # type: ignore[attr-defined]
        fn.__deppy_contracts__.append(contract)  # type: ignore[attr-defined]
        return fn

    return decorator


def assume(
    proposition_fn: Optional[Callable[..., bool]] = None,
    *,
    justification: Optional[str] = None,
) -> AssumptionContract:
    """Create an assumption (called inline, not as a decorator).

    Usage::

        deppy.assume(lambda n: n > 0, justification="validated at input boundary")
    """
    return AssumptionContract(
        proposition_fn=proposition_fn,
        justification=justification,
    )


def transport(
    *,
    source: Optional[Callable[..., bool]] = None,
    target: Optional[Callable[..., bool]] = None,
    transport_fn: Optional[Callable[..., Any]] = None,
    description: Optional[str] = None,
) -> TransportContract:
    """Create a transport declaration (called inline).

    Usage::

        deppy.transport(
            source=lambda x: isinstance(x, int),
            target=lambda x: isinstance(x, float),
            description="int embeds into float",
        )
    """
    return TransportContract(
        source_fn=source,
        target_fn=target,
        transport_fn=transport_fn,
        description=description,
    )


# Trust ordering for internal comparisons
_TRUST_ORD: Dict[TrustLevel, int] = {
    TrustLevel.RESIDUAL: 0,
    TrustLevel.ASSUMED: 1,
    TrustLevel.TRACE_BACKED: 2,
    TrustLevel.BOUNDED_AUTO: 3,
    TrustLevel.TRUSTED_AUTO: 4,
    TrustLevel.PROOF_BACKED: 5,
}
