"""Postcondition contracts: ``@deppy.ensures(lambda result, x: result > x)``.

An *ensures* contract is an output-boundary seed.  It constrains the
values that a function may return (or the exceptions it may raise).
Multiple ensures combine with conjunction — every postcondition must hold.
"""

from __future__ import annotations

import copy
import inspect
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
    from deppy.contracts.seed import OutputBoundarySeed


# ---------------------------------------------------------------------------
# EnsuresContract
# ---------------------------------------------------------------------------


class EnsuresContract(Contract):
    """Output postcondition contract.

    Usage::

        @deppy.ensures(lambda result: result >= 0)
        @deppy.ensures(lambda result, x: result > x, description="grows")

    A postcondition may relate the return value (named *result* by
    convention) to the input parameters.

    Attributes:
        result_name: Name used for the return value (default ``"result"``).
        parameters: Input param names that may appear in the predicate.
        predicate_fn: The original callable, if provided.
        predicate: Parsed :class:`Predicate` representation.
        description: Optional human-readable gloss.
        is_exceptional: Whether this contract governs an exception path.
        exception_type: If exceptional, the exception class name.
    """

    def __init__(
        self,
        *,
        result_name: str = "result",
        parameters: Optional[List[str]] = None,
        predicate_fn: Optional[Callable[..., bool]] = None,
        predicate: Optional[Predicate] = None,
        description: Optional[str] = None,
        is_exceptional: bool = False,
        exception_type: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(source_location=source_location, trust=trust, provenance=provenance)
        self.result_name: str = result_name
        self.parameters: List[str] = parameters if parameters is not None else []
        self.predicate_fn: Optional[Callable[..., bool]] = predicate_fn
        self.description: Optional[str] = description
        self.is_exceptional: bool = is_exceptional
        self.exception_type: Optional[str] = exception_type

        # Build or accept predicate
        if predicate is not None:
            self.predicate: Predicate = predicate
        elif predicate_fn is not None:
            all_names = [self.result_name] + self.parameters
            self.predicate = Predicate.from_callable(
                predicate_fn, param_names=all_names, description=description,
            )
        else:
            self.predicate = Predicate.true_()

        # Auto-discover param names from callable signature
        if predicate_fn is not None and not self.parameters:
            try:
                sig = inspect.signature(predicate_fn)
                names = list(sig.parameters.keys())
                if names:
                    self.result_name = names[0]
                    self.parameters = names[1:]
            except (ValueError, TypeError):
                pass

    # -- Contract interface --------------------------------------------------

    def to_predicate(self) -> Predicate:
        return self.predicate

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import OutputBoundarySeed, SeedProvenance

        provenance_map: Dict[str, SeedProvenance] = {
            "user_annotation": SeedProvenance.SOURCE_ANNOTATION,
            "synthesized": SeedProvenance.SYNTHESIZED,
            "proof_backed": SeedProvenance.PROOF_BACKED,
            "trace_backed": SeedProvenance.TRACE_BACKED,
            "library_pack": SeedProvenance.LIBRARY_PACK,
            "inferred": SeedProvenance.INFERRED,
        }
        prov = provenance_map.get(self.provenance, SeedProvenance.SOURCE_ANNOTATION)

        component = self.result_name
        if self.is_exceptional:
            component = f"raises:{self.exception_type or 'Exception'}"

        return OutputBoundarySeed(
            predicate=self.predicate,
            trust=self.trust,
            provenance=prov,
            source_location=self.source_location,
            result_component=component,
            guarantee=self.predicate,
        )

    def pretty(self) -> str:
        pred_str = self.predicate.pretty()
        params = [self.result_name] + self.parameters
        params_str = ", ".join(params)
        tag = "ensures"
        if self.is_exceptional:
            exc = self.exception_type or "Exception"
            tag = f"ensures_raises({exc})"
        desc = f"  # {self.description}" if self.description else ""
        return f"{tag}({params_str}): {pred_str}{desc}"

    # -- Binding and specialisation -----------------------------------------

    def bind_to_result(self, result_name: str) -> EnsuresContract:
        """Rename the result variable."""
        if result_name == self.result_name:
            return self
        bindings = {self.result_name: Term.var(result_name)}
        new_pred = self.predicate.substitute(bindings)
        result = copy.copy(self)
        result.result_name = result_name
        result.predicate = new_pred
        return result

    def bind_to_params(self, param_names: List[str]) -> EnsuresContract:
        """Bind input parameter names to concrete names."""
        if len(param_names) < len(self.parameters):
            param_names = param_names + self.parameters[len(param_names):]

        bindings: Dict[str, Term] = {}
        for old, new in zip(self.parameters, param_names):
            if old != new:
                bindings[old] = Term.var(new)

        new_pred = self.predicate.substitute(bindings) if bindings else self.predicate
        result = copy.copy(self)
        result.parameters = list(param_names[: len(self.parameters)])
        result.predicate = new_pred
        return result

    def specialize(self, bindings: Dict[str, Any]) -> EnsuresContract:
        """Specialise by substituting known input values."""
        term_bindings = {k: Term.const(v) for k, v in bindings.items()}
        new_pred = self.predicate.substitute(term_bindings)
        remaining = [p for p in self.parameters if p not in bindings]

        result = copy.copy(self)
        result.parameters = remaining
        result.predicate = new_pred
        return result

    def strengthen(self, additional: Predicate) -> EnsuresContract:
        """Return a strengthened postcondition by conjoining *additional*."""
        result = copy.copy(self)
        result.predicate = Predicate.conjunction(self.predicate, additional)
        return result

    def weaken(self) -> EnsuresContract:
        """Drop the predicate, keeping metadata."""
        result = copy.copy(self)
        result.predicate = Predicate.true_()
        result.trust = TrustLevel.RESIDUAL
        result.provenance = "weakened"
        return result

    def for_exceptional_path(
        self, exception_type: str, predicate: Optional[Predicate] = None,
    ) -> EnsuresContract:
        """Create a variant for an exceptional code path."""
        result = copy.copy(self)
        result.is_exceptional = True
        result.exception_type = exception_type
        if predicate is not None:
            result.predicate = predicate
        return result

    def evaluate(self, result_value: Any, env: Mapping[str, Any]) -> bool:
        """Evaluate the postcondition against a concrete result and environment."""
        full_env = dict(env)
        full_env[self.result_name] = result_value
        if self.predicate_fn is not None:
            try:
                args = [full_env[self.result_name]]
                args.extend(full_env[p] for p in self.parameters)
                return bool(self.predicate_fn(*args))
            except (KeyError, TypeError, Exception):
                return True
        return self.predicate.evaluate(full_env)

    def covers_result(self) -> bool:
        """Whether this contract constrains the return value."""
        fv = self.predicate.free_variables()
        return self.result_name in fv or not fv

    def relates_inputs(self) -> bool:
        """Whether this contract mentions input parameters (relational postcondition)."""
        fv = self.predicate.free_variables()
        return bool(fv & frozenset(self.parameters))

    def __repr__(self) -> str:
        tag = "EnsuresContract"
        if self.is_exceptional:
            tag = f"EnsuresContract[raises:{self.exception_type}]"
        return f"<{tag} result={self.result_name!r} pred={self.predicate.pretty()!r}>"


# ---------------------------------------------------------------------------
# ExceptionalEnsures
# ---------------------------------------------------------------------------


class ExceptionalEnsures(Contract):
    """Contract specifically for exception paths.

    This is a specialised variant of ensures that explicitly models
    whether an exception is guaranteed to be raised, guaranteed *not* to
    be raised, or what properties hold on the exception value.

    Usage::

        @deppy.ensures_raises(ValueError, lambda e: "negative" in str(e))
        def sqrt(x: float) -> float: ...
    """

    def __init__(
        self,
        *,
        exception_type: str,
        predicate_fn: Optional[Callable[..., bool]] = None,
        predicate: Optional[Predicate] = None,
        guarantees_raised: bool = False,
        guarantees_not_raised: bool = False,
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(source_location=source_location, trust=trust, provenance=provenance)
        self.exception_type: str = exception_type
        self.predicate_fn: Optional[Callable[..., bool]] = predicate_fn
        self.guarantees_raised: bool = guarantees_raised
        self.guarantees_not_raised: bool = guarantees_not_raised
        self.description: Optional[str] = description

        if predicate is not None:
            self.predicate: Optional[Predicate] = predicate
        elif predicate_fn is not None:
            self.predicate = Predicate.from_callable(
                predicate_fn, param_names=["exception"], description=description,
            )
        else:
            self.predicate = None

        # Validate mutual exclusivity
        if guarantees_raised and guarantees_not_raised:
            raise ValueError("Cannot both guarantee raised and not raised")

    def to_predicate(self) -> Predicate:
        if self.guarantees_raised:
            desc = f"raises {self.exception_type}"
            base = Predicate.from_callable(
                lambda: True, param_names=[], description=desc,
            )
            if self.predicate is not None:
                return Predicate.conjunction(base, self.predicate)
            return base

        if self.guarantees_not_raised:
            return Predicate.from_callable(
                lambda: True,
                param_names=[],
                description=f"does not raise {self.exception_type}",
            )

        if self.predicate is not None:
            return self.predicate

        return Predicate.true_()

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import OutputBoundarySeed, SeedProvenance

        provenance_map: Dict[str, SeedProvenance] = {
            "user_annotation": SeedProvenance.SOURCE_ANNOTATION,
            "synthesized": SeedProvenance.SYNTHESIZED,
            "proof_backed": SeedProvenance.PROOF_BACKED,
        }
        prov = provenance_map.get(self.provenance, SeedProvenance.SOURCE_ANNOTATION)

        return OutputBoundarySeed(
            predicate=self.to_predicate(),
            trust=self.trust,
            provenance=prov,
            source_location=self.source_location,
            result_component=f"raises:{self.exception_type}",
            guarantee=self.to_predicate(),
        )

    def pretty(self) -> str:
        if self.guarantees_raised:
            suffix = ""
            if self.predicate is not None:
                suffix = f" where {self.predicate.pretty()}"
            return f"raises({self.exception_type}){suffix}"
        if self.guarantees_not_raised:
            return f"never_raises({self.exception_type})"
        pred_str = self.predicate.pretty() if self.predicate else "⊤"
        return f"exceptional({self.exception_type}): {pred_str}"

    def as_ensures(self) -> EnsuresContract:
        """Convert to a standard EnsuresContract for uniform processing."""
        return EnsuresContract(
            result_name="exception",
            predicate=self.to_predicate(),
            is_exceptional=True,
            exception_type=self.exception_type,
            description=self.description,
            source_location=self.source_location,
            trust=self.trust,
            provenance=self.provenance,
        )

    def __repr__(self) -> str:
        mode = "raises" if self.guarantees_raised else ("never" if self.guarantees_not_raised else "exc")
        return f"<ExceptionalEnsures {mode}:{self.exception_type}>"


# ---------------------------------------------------------------------------
# CompositeEnsures
# ---------------------------------------------------------------------------


class CompositeEnsures:
    """Multiple ensures combined with conjunction.

    Analogous to :class:`~deppy.contracts.requires.CompositeRequires`
    for postconditions.
    """

    def __init__(self, guarantees: Optional[List[EnsuresContract]] = None) -> None:
        self.guarantees: List[EnsuresContract] = guarantees if guarantees is not None else []

    def add(self, contract: EnsuresContract) -> None:
        self.guarantees.append(contract)

    def to_single(self) -> EnsuresContract:
        """Combine all ensures into a single conjunctive contract."""
        if not self.guarantees:
            return EnsuresContract(predicate=Predicate.true_(), provenance="synthesized")
        if len(self.guarantees) == 1:
            return self.guarantees[0]

        predicates = [g.predicate for g in self.guarantees]
        combined = Predicate.conjunction(*predicates)

        all_params: List[str] = []
        seen: Set[str] = set()
        for g in self.guarantees:
            for p in g.parameters:
                if p not in seen:
                    all_params.append(p)
                    seen.add(p)

        return EnsuresContract(
            result_name=self.guarantees[0].result_name,
            parameters=all_params,
            predicate=combined,
            trust=self.guarantees[0].trust,
            provenance=self.guarantees[0].provenance,
        )

    def split_normal_exceptional(
        self,
    ) -> Tuple[List[EnsuresContract], List[EnsuresContract]]:
        """Separate normal-path and exceptional-path ensures."""
        normal = [g for g in self.guarantees if not g.is_exceptional]
        exceptional = [g for g in self.guarantees if g.is_exceptional]
        return normal, exceptional

    def is_empty(self) -> bool:
        return len(self.guarantees) == 0

    def pretty(self) -> str:
        if not self.guarantees:
            return "ensures: ⊤"
        return " ∧ ".join(g.pretty() for g in self.guarantees)

    def __len__(self) -> int:
        return len(self.guarantees)

    def __repr__(self) -> str:
        return f"<CompositeEnsures n={len(self.guarantees)}>"


# ---------------------------------------------------------------------------
# Decorator factory
# ---------------------------------------------------------------------------


def ensures(
    predicate_fn: Optional[Callable[..., bool]] = None,
    *,
    result_name: str = "result",
    parameters: Optional[List[str]] = None,
    description: Optional[str] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
) -> Callable[..., Any]:
    """Decorator factory for ``@deppy.ensures``.

    Usage::

        @ensures(lambda result: result >= 0)
        def abs_val(x: float) -> float: ...

        @ensures(lambda result, x: result > x, description="strictly greater")
        def increment(x: int) -> int: ...
    """

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        contract = EnsuresContract(
            result_name=result_name,
            parameters=parameters,
            predicate_fn=predicate_fn,
            description=description,
            trust=trust,
        )

        if not hasattr(fn, "__deppy_contracts__"):
            fn.__deppy_contracts__ = []  # type: ignore[attr-defined]
        fn.__deppy_contracts__.append(contract)  # type: ignore[attr-defined]
        return fn

    return decorator


def ensures_raises(
    exception_type: str,
    predicate_fn: Optional[Callable[..., bool]] = None,
    *,
    description: Optional[str] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
) -> Callable[..., Any]:
    """Decorator factory for ``@deppy.ensures_raises``."""

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        contract = ExceptionalEnsures(
            exception_type=exception_type,
            predicate_fn=predicate_fn,
            guarantees_raised=True,
            description=description,
            trust=trust,
        )

        if not hasattr(fn, "__deppy_contracts__"):
            fn.__deppy_contracts__ = []  # type: ignore[attr-defined]
        fn.__deppy_contracts__.append(contract)  # type: ignore[attr-defined]
        return fn

    return decorator
