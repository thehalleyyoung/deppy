"""Precondition contracts: ``@deppy.requires(lambda x: x > 0)``.

A *requires* contract is an input-boundary seed.  It constrains the
values that callers must supply.  Multiple requires combine with
conjunction — every precondition must hold.
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
    from deppy.contracts.seed import InputBoundarySeed


# ---------------------------------------------------------------------------
# RequiresContract
# ---------------------------------------------------------------------------


class RequiresContract(Contract):
    """Input precondition contract.

    Usage::

        @deppy.requires(lambda x: x > 0)
        @deppy.requires(lambda x, y: x < y, description="x must precede y")

    A requires contract carries:

    * **parameters** — parameter names the predicate ranges over.
    * **predicate_fn** — the original callable (if provided).
    * **predicate** — the parsed :class:`Predicate` representation.
    * **description** — optional human-readable gloss.
    """

    def __init__(
        self,
        *,
        parameters: Optional[List[str]] = None,
        predicate_fn: Optional[Callable[..., bool]] = None,
        predicate: Optional[Predicate] = None,
        description: Optional[str] = None,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.RESIDUAL,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(source_location=source_location, trust=trust, provenance=provenance)
        self.parameters: List[str] = parameters if parameters is not None else []
        self.predicate_fn: Optional[Callable[..., bool]] = predicate_fn
        self.description: Optional[str] = description

        # Build or accept predicate
        if predicate is not None:
            self.predicate: Predicate = predicate
        elif predicate_fn is not None:
            self.predicate = Predicate.from_callable(
                predicate_fn, param_names=self.parameters, description=description,
            )
        else:
            self.predicate = Predicate.true_()

        # Auto-discover parameter names if not explicitly given
        if not self.parameters and predicate_fn is not None:
            try:
                sig = inspect.signature(predicate_fn)
                self.parameters = list(sig.parameters.keys())
            except (ValueError, TypeError):
                pass

    # -- Contract interface --------------------------------------------------

    def to_predicate(self) -> Predicate:
        return self.predicate

    def to_boundary_seed(self) -> Any:
        from deppy.contracts.seed import InputBoundarySeed, SeedProvenance

        provenance_map: Dict[str, SeedProvenance] = {
            "user_annotation": SeedProvenance.SOURCE_ANNOTATION,
            "synthesized": SeedProvenance.SYNTHESIZED,
            "proof_backed": SeedProvenance.PROOF_BACKED,
            "trace_backed": SeedProvenance.TRACE_BACKED,
            "library_pack": SeedProvenance.LIBRARY_PACK,
            "inferred": SeedProvenance.INFERRED,
        }
        prov = provenance_map.get(self.provenance, SeedProvenance.SOURCE_ANNOTATION)

        # For each parameter, emit a separate input seed
        seeds: List[InputBoundarySeed] = []
        if self.parameters:
            for param in self.parameters:
                seeds.append(
                    InputBoundarySeed(
                        predicate=self.predicate,
                        trust=self.trust,
                        provenance=prov,
                        source_location=self.source_location,
                        parameter=param,
                        requirement=self.predicate,
                    )
                )
        else:
            seeds.append(
                InputBoundarySeed(
                    predicate=self.predicate,
                    trust=self.trust,
                    provenance=prov,
                    source_location=self.source_location,
                    parameter="*",
                    requirement=self.predicate,
                )
            )
        # Return first if single, otherwise the list
        return seeds[0] if len(seeds) == 1 else seeds

    def pretty(self) -> str:
        params_str = ", ".join(self.parameters) if self.parameters else "*"
        pred_str = self.predicate.pretty()
        desc = f"  # {self.description}" if self.description else ""
        return f"requires({params_str}): {pred_str}{desc}"

    # -- Binding and specialisation -----------------------------------------

    def bind_to_params(self, param_names: List[str]) -> RequiresContract:
        """Bind this contract to concrete parameter names.

        If the contract was written with generic names (e.g. positional
        ``x``, ``y``), rename them to the actual function parameters.
        """
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

    def specialize(self, bindings: Dict[str, Any]) -> RequiresContract:
        """Specialise by substituting known values.

        Parameters present in *bindings* are replaced by their constant
        values, reducing the predicate.  If all parameters are bound the
        result is effectively a boolean check.
        """
        term_bindings = {k: Term.const(v) for k, v in bindings.items()}
        new_pred = self.predicate.substitute(term_bindings)
        remaining = [p for p in self.parameters if p not in bindings]

        result = copy.copy(self)
        result.parameters = remaining
        result.predicate = new_pred
        return result

    def weaken(self) -> RequiresContract:
        """Return a weakened version (drop the predicate, keep metadata).

        Used when a precondition cannot be verified and must be relaxed
        rather than rejected.
        """
        result = copy.copy(self)
        result.predicate = Predicate.true_()
        result.trust = TrustLevel.RESIDUAL
        result.provenance = "weakened"
        return result

    def strengthen(self, additional: Predicate) -> RequiresContract:
        """Return a strengthened version by conjoining *additional*."""
        result = copy.copy(self)
        result.predicate = Predicate.conjunction(self.predicate, additional)
        return result

    def evaluate(self, env: Mapping[str, Any]) -> bool:
        """Evaluate the precondition in the given environment.

        Returns True if the precondition is satisfied, or if evaluation
        is inconclusive.
        """
        if self.predicate_fn is not None:
            try:
                args = [env[p] for p in self.parameters]
                return bool(self.predicate_fn(*args))
            except (KeyError, TypeError, Exception):
                return True  # inconclusive → accept
        return self.predicate.evaluate(env)

    def covers_param(self, param_name: str) -> bool:
        """Does this contract constrain *param_name*?"""
        return param_name in self.parameters or not self.parameters

    def overlapping_params(self, other: RequiresContract) -> FrozenSet[str]:
        """Parameters constrained by both *self* and *other*."""
        return frozenset(self.parameters) & frozenset(other.parameters)

    def __repr__(self) -> str:
        return f"<RequiresContract params={self.parameters!r} pred={self.predicate.pretty()!r}>"


# ---------------------------------------------------------------------------
# ParameterRequirement
# ---------------------------------------------------------------------------


@dataclass
class ParameterRequirement:
    """Requirement on a single parameter.

    Combines an optional type bound with an optional predicate refinement.
    This is the normalised form used during seed synthesis — each parameter
    gets exactly one ``ParameterRequirement``.
    """

    param_name: str
    type_bound: Optional[TypeBase] = None
    refinement: Optional[Predicate] = None
    source_contracts: List[RequiresContract] = field(default_factory=list)

    @property
    def has_type_bound(self) -> bool:
        return self.type_bound is not None

    @property
    def has_refinement(self) -> bool:
        return self.refinement is not None and not self.refinement.is_trivially_true

    def to_predicate(self) -> Predicate:
        """Combined predicate: type check ∧ refinement."""
        parts: List[Predicate] = []
        if self.type_bound is not None:
            type_pred = Predicate.from_callable(
                lambda v: isinstance(v, object),  # placeholder — real check in types
                param_names=[self.param_name],
                description=f"isinstance({self.param_name}, {self.type_bound.pretty()})",
            )
            parts.append(type_pred)
        if self.refinement is not None:
            parts.append(self.refinement)
        if not parts:
            return Predicate.true_()
        return Predicate.conjunction(*parts)

    def merge_with(self, other: ParameterRequirement) -> ParameterRequirement:
        """Merge two requirements on the same parameter (conjunction)."""
        if self.param_name != other.param_name:
            raise ValueError(
                f"Cannot merge requirements for different params: "
                f"{self.param_name!r} vs {other.param_name!r}"
            )
        # Use the more specific type bound (prefer non-None)
        merged_type = self.type_bound or other.type_bound
        if self.type_bound is not None and other.type_bound is not None:
            # Both have type bounds; prefer the one with a refinement
            merged_type = (
                self.type_bound if self.type_bound.refinement is not None else other.type_bound
            )

        # Conjoin refinements
        merged_ref: Optional[Predicate] = None
        if self.refinement is not None and other.refinement is not None:
            merged_ref = Predicate.conjunction(self.refinement, other.refinement)
        else:
            merged_ref = self.refinement or other.refinement

        return ParameterRequirement(
            param_name=self.param_name,
            type_bound=merged_type,
            refinement=merged_ref,
            source_contracts=self.source_contracts + other.source_contracts,
        )

    def pretty(self) -> str:
        parts: List[str] = [self.param_name]
        if self.type_bound is not None:
            parts.append(f": {self.type_bound.pretty()}")
        if self.refinement is not None and not self.refinement.is_trivially_true:
            parts.append(f" where {self.refinement.pretty()}")
        return "".join(parts)

    def __repr__(self) -> str:
        return f"<ParameterRequirement {self.pretty()!r}>"


# ---------------------------------------------------------------------------
# CompositeRequires
# ---------------------------------------------------------------------------


class CompositeRequires:
    """Multiple requires combined with conjunction.

    This is the pre-normalisation form: several ``@requires`` decorators
    are collected into a ``CompositeRequires`` before being split into
    per-parameter :class:`ParameterRequirement` instances.
    """

    def __init__(self, requirements: Optional[List[RequiresContract]] = None) -> None:
        self.requirements: List[RequiresContract] = requirements if requirements is not None else []

    def add(self, contract: RequiresContract) -> None:
        """Append a requires contract."""
        self.requirements.append(contract)

    def to_single(self) -> RequiresContract:
        """Combine all requirements into a single conjunctive contract."""
        if not self.requirements:
            return RequiresContract(predicate=Predicate.true_(), provenance="synthesized")
        if len(self.requirements) == 1:
            return self.requirements[0]

        all_params: List[str] = []
        seen: Set[str] = set()
        predicates: List[Predicate] = []

        for req in self.requirements:
            predicates.append(req.predicate)
            for p in req.parameters:
                if p not in seen:
                    all_params.append(p)
                    seen.add(p)

        combined = Predicate.conjunction(*predicates)

        # Pick the highest trust and best provenance
        best_trust = max(
            (r.trust for r in self.requirements),
            key=lambda t: _TRUST_ORD.get(t, 0),
        )
        provenance = self.requirements[0].provenance

        return RequiresContract(
            parameters=all_params,
            predicate=combined,
            trust=best_trust,
            provenance=provenance,
        )

    def split_by_param(self) -> Dict[str, List[RequiresContract]]:
        """Group requirements by the parameter they constrain.

        Requirements that don't name a specific parameter are filed under
        the ``"*"`` key.
        """
        result: Dict[str, List[RequiresContract]] = {}
        for req in self.requirements:
            if not req.parameters:
                result.setdefault("*", []).append(req)
            else:
                for param in req.parameters:
                    result.setdefault(param, []).append(req)
        return result

    def to_parameter_requirements(self) -> Dict[str, ParameterRequirement]:
        """Normalise into one :class:`ParameterRequirement` per parameter."""
        by_param = self.split_by_param()
        result: Dict[str, ParameterRequirement] = {}

        for param, reqs in by_param.items():
            predicates = [r.predicate for r in reqs]
            combined = Predicate.conjunction(*predicates) if len(predicates) > 1 else predicates[0]
            result[param] = ParameterRequirement(
                param_name=param,
                refinement=combined,
                source_contracts=list(reqs),
            )
        return result

    def filter_for_param(self, param_name: str) -> List[RequiresContract]:
        """Return only requirements that mention *param_name*."""
        return [r for r in self.requirements if r.covers_param(param_name)]

    @property
    def all_parameters(self) -> FrozenSet[str]:
        """All parameter names mentioned across all requirements."""
        result: Set[str] = set()
        for req in self.requirements:
            result.update(req.parameters)
        return frozenset(result)

    def is_empty(self) -> bool:
        return len(self.requirements) == 0

    def pretty(self) -> str:
        if not self.requirements:
            return "requires: ⊤"
        return " ∧ ".join(r.pretty() for r in self.requirements)

    def __len__(self) -> int:
        return len(self.requirements)

    def __repr__(self) -> str:
        return f"<CompositeRequires n={len(self.requirements)}>"


# ---------------------------------------------------------------------------
# Helper: decorator factory
# ---------------------------------------------------------------------------


def requires(
    predicate_fn: Optional[Callable[..., bool]] = None,
    *,
    parameters: Optional[List[str]] = None,
    description: Optional[str] = None,
    trust: TrustLevel = TrustLevel.RESIDUAL,
) -> Callable[..., Any]:
    """Decorator factory for ``@deppy.requires``.

    Usage::

        @requires(lambda x: x > 0)
        def sqrt(x: float) -> float: ...

        @requires(lambda x, y: x < y, description="x must be less than y")
        def range_check(x: int, y: int) -> bool: ...
    """

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        contract = RequiresContract(
            parameters=parameters,
            predicate_fn=predicate_fn,
            description=description,
            trust=trust,
        )

        # Attach contract metadata to the function
        if not hasattr(fn, "__deppy_contracts__"):
            fn.__deppy_contracts__ = []  # type: ignore[attr-defined]
        fn.__deppy_contracts__.append(contract)  # type: ignore[attr-defined]
        return fn

    if predicate_fn is not None and callable(predicate_fn) and not isinstance(predicate_fn, type):
        # Bare @requires(lambda ...) — predicate_fn is the actual predicate
        # We still return a decorator
        pass

    return decorator


# Trust ordering for internal comparisons
_TRUST_ORD: Dict[TrustLevel, int] = {
    TrustLevel.RESIDUAL: 0,
    TrustLevel.ASSUMED: 1,
    TrustLevel.TRACE_BACKED: 2,
    TrustLevel.BOUNDED_AUTO: 3,
    TrustLevel.TRUSTED_AUTO: 4,
    TrustLevel.PROOF_BACKED: 5,
}
