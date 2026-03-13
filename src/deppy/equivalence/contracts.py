"""Contract-based equivalence specifications.

Provides decorators for annotating Python functions with equivalence
contracts, which are lowered to equivalence predicates using the
existing ``RefinementType`` and ``Predicate`` infrastructure.

Decorators
----------
@equiv(other_fn)
    Assert that the decorated function is equivalent to *other_fn*.
    Generates a full sheaf-theoretic equivalence check.

@refines(other_fn)
    Assert that the decorated function refines *other_fn*
    (one-directional: every behavior of ``self`` is a behavior of ``other_fn``).

@equiv_predicate(pred)
    Attach an explicit equivalence predicate to the decorated function.

@behavioral_equiv(other_fn, *, inputs=...)
    Assert behavioral equivalence on a specific set of inputs.

These decorators store metadata on the function via ``__deppy_equiv__``
and ``__deppy_refines__`` attributes.  The equivalence pipeline reads
these attributes during the harvest stage.
"""

from __future__ import annotations

import functools
import inspect
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Tuple,
    TypeVar,
    Union,
)

from deppy.types.refinement import (
    ComparisonOp,
    ComparisonPred,
    ConjunctionPred,
    DisjunctionPred,
    ImplicationPred,
    Predicate,
    RefinementType,
    TruePred,
    VarPred,
)
from deppy.types.dependent import (
    ForallType,
    IdentityType,
    PiType,
)
from deppy.types.witnesses import (
    ProofTerm,
    ReflProof,
    RefinementWitness,
)

from deppy.equivalence._protocols import (
    EquivalenceStrength,
    ProgramId,
)
from deppy.equivalence.predicates import (
    BiimplicationPred,
    BehavioralEquivalencePred,
    EquivalencePred,
    RefinementEquivalencePred,
    build_equivalence_predicate,
    predicate_biimplication,
)

F = TypeVar("F", bound=Callable[..., Any])


# ═══════════════════════════════════════════════════════════════════════════════
# Contract metadata
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass(frozen=True)
class EquivalenceContract:
    """Metadata stored on a function annotated with @equiv."""
    other: Union[Callable[..., Any], str]
    strength: EquivalenceStrength = EquivalenceStrength.DENOTATIONAL
    predicate: Optional[Predicate] = None
    inputs: Optional[Sequence[Any]] = None
    description: Optional[str] = None


@dataclass(frozen=True)
class RefinementContract:
    """Metadata stored on a function annotated with @refines."""
    other: Union[Callable[..., Any], str]
    direction: str = "forward"  # "forward" = self ⊑ other, "backward" = other ⊑ self
    predicate: Optional[Predicate] = None
    description: Optional[str] = None


# ═══════════════════════════════════════════════════════════════════════════════
# Decorator: @equiv
# ═══════════════════════════════════════════════════════════════════════════════


def equiv(
    other: Union[Callable[..., Any], str],
    *,
    strength: EquivalenceStrength = EquivalenceStrength.DENOTATIONAL,
    description: Optional[str] = None,
) -> Callable[[F], F]:
    """Declare that the decorated function is equivalent to *other*.

    Example::

        def original(x: int) -> int:
            return x + 1

        @equiv(original)
        def optimized(x: int) -> int:
            return 1 + x

    The decorator stores an ``EquivalenceContract`` on the function
    which is read by the equivalence pipeline during analysis.
    """

    def decorator(fn: F) -> F:
        contract = EquivalenceContract(
            other=other,
            strength=strength,
            description=description or f"{_fn_name(fn)} ≡ {_fn_name(other)}",
        )
        _attach_equiv(fn, contract)
        return fn

    return decorator


# ═══════════════════════════════════════════════════════════════════════════════
# Decorator: @refines
# ═══════════════════════════════════════════════════════════════════════════════


def refines(
    other: Union[Callable[..., Any], str],
    *,
    direction: str = "forward",
    description: Optional[str] = None,
) -> Callable[[F], F]:
    """Declare that the decorated function refines *other*.

    Refinement is one-directional: every behavior of the decorated
    function is also a behavior of *other*, but not necessarily vice
    versa.

    Example::

        def general(x: int) -> int:
            return x + 1

        @refines(general)
        def specialised(x: int) -> int:
            if x < 0:
                raise ValueError("positive only")
            return x + 1

    Parameters:
        other: The function being refined (or its qualified name)
        direction: "forward" means self ⊑ other, "backward" means other ⊑ self
    """

    def decorator(fn: F) -> F:
        contract = RefinementContract(
            other=other,
            direction=direction,
            description=description or f"{_fn_name(fn)} ⊑ {_fn_name(other)}",
        )
        _attach_refines(fn, contract)
        return fn

    return decorator


# ═══════════════════════════════════════════════════════════════════════════════
# Decorator: @equiv_predicate
# ═══════════════════════════════════════════════════════════════════════════════


def equiv_predicate(
    other: Union[Callable[..., Any], str],
    predicate: Predicate,
    *,
    strength: EquivalenceStrength = EquivalenceStrength.DENOTATIONAL,
) -> Callable[[F], F]:
    """Declare equivalence with an explicit predicate.

    Example::

        from deppy.types.refinement import ComparisonPred, ComparisonOp

        @equiv_predicate(
            other_fn,
            ComparisonPred(lhs="f_result", op=ComparisonOp.EQ, rhs="g_result"),
        )
        def my_fn(x: int) -> int:
            ...
    """

    def decorator(fn: F) -> F:
        contract = EquivalenceContract(
            other=other,
            strength=strength,
            predicate=predicate,
        )
        _attach_equiv(fn, contract)
        return fn

    return decorator


# ═══════════════════════════════════════════════════════════════════════════════
# Decorator: @behavioral_equiv
# ═══════════════════════════════════════════════════════════════════════════════


def behavioral_equiv(
    other: Union[Callable[..., Any], str],
    *,
    inputs: Optional[Sequence[Any]] = None,
    strength: EquivalenceStrength = EquivalenceStrength.OBSERVATIONAL,
) -> Callable[[F], F]:
    """Declare behavioral equivalence (possibly on specific inputs).

    Example::

        @behavioral_equiv(original, inputs=[(0,), (1,), (-1,)])
        def optimized(x: int) -> int:
            return x + 1
    """

    def decorator(fn: F) -> F:
        contract = EquivalenceContract(
            other=other,
            strength=strength,
            inputs=inputs,
            description=f"{_fn_name(fn)} ≡_obs {_fn_name(other)}",
        )
        _attach_equiv(fn, contract)
        return fn

    return decorator


# ═══════════════════════════════════════════════════════════════════════════════
# Contract lowering: contract → equivalence predicates
# ═══════════════════════════════════════════════════════════════════════════════


def lower_equiv_contract(
    fn: Callable[..., Any],
    other: Callable[..., Any],
    contract: EquivalenceContract,
) -> Predicate:
    """Lower an equivalence contract to an equivalence predicate.

    Extracts the type annotations from both functions and constructs
    the appropriate BiimplicationPred, RefinementEquivalencePred, or
    BehavioralEquivalencePred.
    """
    # If the contract already has an explicit predicate, use it
    if contract.predicate is not None:
        return contract.predicate

    # Extract parameter names from both functions
    fn_params = _extract_params(fn)
    other_params = _extract_params(other)

    # Build equivalence predicate based on strength
    if contract.strength == EquivalenceStrength.OBSERVATIONAL:
        return _build_observational_predicate(fn, other, fn_params, other_params)
    elif contract.strength == EquivalenceStrength.BISIMULATION:
        return _build_bisimulation_predicate(fn, other, fn_params, other_params)
    else:
        # Denotational: full semantic equivalence
        return _build_denotational_predicate(fn, other, fn_params, other_params)


def lower_refines_contract(
    fn: Callable[..., Any],
    other: Callable[..., Any],
    contract: RefinementContract,
) -> Predicate:
    """Lower a refinement contract to an implication predicate.

    One-directional: fn ⊑ other means ∀x. φ_fn(x) ⟹ φ_other(x).
    """
    if contract.predicate is not None:
        return contract.predicate

    fn_params = _extract_params(fn)
    other_params = _extract_params(other)

    # Build the forward implication
    fn_pred = VarPred(var_name=f"{_fn_name(fn)}_holds")
    other_pred = VarPred(var_name=f"{_fn_name(other)}_holds")

    if contract.direction == "forward":
        return ImplicationPred(antecedent=fn_pred, consequent=other_pred)
    else:
        return ImplicationPred(antecedent=other_pred, consequent=fn_pred)


# ═══════════════════════════════════════════════════════════════════════════════
# Contract harvesting
# ═══════════════════════════════════════════════════════════════════════════════


def get_equiv_contracts(fn: Callable[..., Any]) -> List[EquivalenceContract]:
    """Get all equivalence contracts attached to a function."""
    return list(getattr(fn, "__deppy_equiv__", []))


def get_refines_contracts(fn: Callable[..., Any]) -> List[RefinementContract]:
    """Get all refinement contracts attached to a function."""
    return list(getattr(fn, "__deppy_refines__", []))


def has_equiv_contract(fn: Callable[..., Any]) -> bool:
    """Check if a function has any equivalence contracts."""
    return bool(getattr(fn, "__deppy_equiv__", []))


def has_refines_contract(fn: Callable[..., Any]) -> bool:
    """Check if a function has any refinement contracts."""
    return bool(getattr(fn, "__deppy_refines__", []))


def collect_all_contracts(
    module: Any,
) -> Tuple[
    List[Tuple[Callable[..., Any], EquivalenceContract]],
    List[Tuple[Callable[..., Any], RefinementContract]],
]:
    """Collect all equivalence and refinement contracts from a module.

    Scans all callable attributes of the module for ``__deppy_equiv__``
    and ``__deppy_refines__`` annotations.
    """
    equiv_contracts: List[Tuple[Callable[..., Any], EquivalenceContract]] = []
    refines_contracts: List[Tuple[Callable[..., Any], RefinementContract]] = []

    for name in dir(module):
        try:
            obj = getattr(module, name)
        except (AttributeError, Exception):
            continue

        if not callable(obj):
            continue

        for contract in get_equiv_contracts(obj):
            equiv_contracts.append((obj, contract))

        for contract in get_refines_contracts(obj):
            refines_contracts.append((obj, contract))

    return equiv_contracts, refines_contracts


# ═══════════════════════════════════════════════════════════════════════════════
# Contract-to-RefinementType lowering
# ═══════════════════════════════════════════════════════════════════════════════


def contract_to_refinement_type(
    fn: Callable[..., Any],
    other: Callable[..., Any],
    contract: EquivalenceContract,
) -> RefinementType:
    """Lower an equivalence contract to a RefinementType.

    The RefinementType encodes the equivalence obligation:
    {result : τ | f(x) = g(x)} where the predicate captures the
    denotational equivalence.

    Returns:
        RefinementType whose predicate is the equivalence obligation.
    """
    predicate = lower_equiv_contract(fn, other, contract)

    # Build the return type as the base
    fn_return = _get_return_annotation(fn)
    base_type = fn_return  # could be None

    return RefinementType(
        base=base_type,
        binder="equiv_result",
        predicate=predicate,
    )


def contract_to_identity_type(
    fn: Callable[..., Any],
    other: Callable[..., Any],
    contract: EquivalenceContract,
) -> IdentityType:
    """Lower an equivalence contract to an IdentityType.

    IdentityType(carrier=τ, lhs=f, rhs=g) represents the proposition
    that f = g as elements of type τ.

    Returns:
        IdentityType representing the equivalence.
    """
    fn_return = _get_return_annotation(fn)

    return IdentityType(
        carrier=fn_return,
        lhs=_fn_name(fn),
        rhs=_fn_name(other),
    )


def contract_to_forall_type(
    fn: Callable[..., Any],
    other: Callable[..., Any],
    contract: EquivalenceContract,
) -> ForallType:
    """Lower an equivalence contract to a ForallType.

    ForallType(var_name="x", bound=τ_input, body=f(x) = g(x))
    represents ∀x:τ. f(x) = g(x).

    Returns:
        ForallType encoding the universal equivalence.
    """
    params = _extract_params(fn)
    predicate = lower_equiv_contract(fn, other, contract)

    if params:
        first_param = params[0]
        param_type = _get_param_annotation(fn, first_param)
        return ForallType(
            var_name=first_param,
            bound=param_type,
            body=RefinementType(
                base=_get_return_annotation(fn),
                binder="result",
                predicate=predicate,
            ),
        )
    else:
        return ForallType(
            var_name="_",
            bound=None,
            body=RefinementType(
                base=_get_return_annotation(fn),
                binder="result",
                predicate=predicate,
            ),
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Internal helpers
# ═══════════════════════════════════════════════════════════════════════════════


def _fn_name(fn: Union[Callable[..., Any], str]) -> str:
    """Get the qualified name of a function."""
    if isinstance(fn, str):
        return fn
    return getattr(fn, "__qualname__", getattr(fn, "__name__", repr(fn)))


def _extract_params(fn: Callable[..., Any]) -> List[str]:
    """Extract parameter names from a function."""
    try:
        sig = inspect.signature(fn)
        return [
            p.name
            for p in sig.parameters.values()
            if p.kind not in (
                inspect.Parameter.VAR_POSITIONAL,
                inspect.Parameter.VAR_KEYWORD,
            )
        ]
    except (ValueError, TypeError):
        return []


def _get_return_annotation(fn: Callable[..., Any]) -> Any:
    """Get the return type annotation (or None)."""
    try:
        sig = inspect.signature(fn)
        if sig.return_annotation is not inspect.Parameter.empty:
            return sig.return_annotation
    except (ValueError, TypeError):
        pass
    return None


def _get_param_annotation(fn: Callable[..., Any], param_name: str) -> Any:
    """Get a parameter type annotation (or None)."""
    try:
        sig = inspect.signature(fn)
        param = sig.parameters.get(param_name)
        if param is not None and param.annotation is not inspect.Parameter.empty:
            return param.annotation
    except (ValueError, TypeError):
        pass
    return None


def _attach_equiv(fn: Callable[..., Any], contract: EquivalenceContract) -> None:
    """Attach an equivalence contract to a function."""
    if not hasattr(fn, "__deppy_equiv__"):
        fn.__deppy_equiv__ = []  # type: ignore[attr-defined]
    fn.__deppy_equiv__.append(contract)  # type: ignore[attr-defined]


def _attach_refines(fn: Callable[..., Any], contract: RefinementContract) -> None:
    """Attach a refinement contract to a function."""
    if not hasattr(fn, "__deppy_refines__"):
        fn.__deppy_refines__ = []  # type: ignore[attr-defined]
    fn.__deppy_refines__.append(contract)  # type: ignore[attr-defined]


def _build_denotational_predicate(
    fn: Callable[..., Any],
    other: Callable[..., Any],
    fn_params: List[str],
    other_params: List[str],
) -> Predicate:
    """Build a denotational equivalence predicate.

    ∀x. f(x) = g(x) encoded as a BiimplicationPred of the
    output refinements.
    """
    fn_name = _fn_name(fn)
    other_name = _fn_name(other)

    # Build the core equality: f(x) = g(x)
    lhs = VarPred(var_name=f"{fn_name}_result")
    rhs = VarPred(var_name=f"{other_name}_result")

    return BiimplicationPred(
        forward=ImplicationPred(antecedent=lhs, consequent=rhs),
        backward=ImplicationPred(antecedent=rhs, consequent=lhs),
    )


def _build_observational_predicate(
    fn: Callable[..., Any],
    other: Callable[..., Any],
    fn_params: List[str],
    other_params: List[str],
) -> Predicate:
    """Build an observational equivalence predicate.

    Observable behaviors agree on all contexts.
    """
    fn_name = _fn_name(fn)
    other_name = _fn_name(other)

    return BehavioralEquivalencePred(
        fn_name=fn_name,
        gn_name=other_name,
        input_vars=frozenset(fn_params),
        output_var="result",
    )


def _build_bisimulation_predicate(
    fn: Callable[..., Any],
    other: Callable[..., Any],
    fn_params: List[str],
    other_params: List[str],
) -> Predicate:
    """Build a bisimulation predicate.

    Bisimulation: step-by-step correspondence of transitions.
    Encoded as a conjunction of forward and backward simulation.
    """
    fn_name = _fn_name(fn)
    other_name = _fn_name(other)

    # Forward simulation: f steps can be matched by g
    forward = EquivalencePred(
        fn_name=fn_name,
        gn_name=other_name,
        domain_var="state",
    )

    # Backward simulation: g steps can be matched by f
    backward = EquivalencePred(
        fn_name=other_name,
        gn_name=fn_name,
        domain_var="state",
    )

    return ConjunctionPred(conjuncts=(forward, backward))
