"""@decreases contract implementation for termination arguments.

The DecreasesContract specifies a ranking function that must strictly
decrease on each loop iteration or recursive call, ensuring termination.
This is the sheaf-descent analog of a well-founded relation proof:
the ranking function defines a local section at each loop-header site,
and the sheaf gluing condition ensures the ranking is consistent across
the entire cover.

Ranking functions map program states to elements of a well-ordered set.
The default well-ordering is the natural numbers, but lexicographic
tuples and custom orderings are also supported.
"""

from __future__ import annotations

import copy
import enum
import uuid
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import (
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
#  Well-founded orderings
# ===================================================================


class WellFoundedOrdering(enum.Enum):
    """Built-in well-founded orderings for ranking functions."""

    NATURAL = "natural"  # Natural numbers (non-negative integers)
    INTEGER = "integer"  # Integers with lower bound
    LEXICOGRAPHIC = "lexicographic"  # Lexicographic tuple ordering
    MULTISET = "multiset"  # Multiset (Dershowitz-Manna) ordering
    CUSTOM = "custom"  # User-provided ordering


@dataclass(frozen=True)
class RankingMeasure:
    """A single component of a ranking function.

    For lexicographic orderings, multiple measures are combined.
    Each measure maps program state to a well-ordered value.
    """

    _name: str
    _expression: str
    _bound_term: Optional[Term] = None
    _lower_bound: int = 0
    _callable_fn: Optional[Callable[..., Any]] = field(default=None, hash=False, compare=False)

    @property
    def name(self) -> str:
        return self._name

    @property
    def expression(self) -> str:
        return self._expression

    @property
    def bound_term(self) -> Optional[Term]:
        return self._bound_term

    @property
    def lower_bound(self) -> int:
        return self._lower_bound

    @property
    def callable_fn(self) -> Optional[Callable[..., Any]]:
        return self._callable_fn

    def evaluate(self, env: Mapping[str, Any]) -> Any:
        """Evaluate this measure in the given variable environment."""
        if self._callable_fn is not None:
            try:
                return self._callable_fn(**{k: v for k, v in env.items()})
            except (TypeError, KeyError):
                try:
                    return self._callable_fn(*env.values())
                except (TypeError, IndexError):
                    return None
        return None

    def pretty(self) -> str:
        return f"{self._name}: {self._expression}"


@dataclass(frozen=True)
class RankingFunction:
    """A complete ranking function mapping states to a well-ordered set.

    The ranking function may be:
    - A single measure (natural number valued).
    - A lexicographic tuple of measures.
    - A custom function with a provided well-founded proof.
    """

    _measures: Tuple[RankingMeasure, ...]
    _ordering: WellFoundedOrdering = WellFoundedOrdering.NATURAL
    _strict: bool = True  # Must strictly decrease

    @property
    def measures(self) -> Tuple[RankingMeasure, ...]:
        return self._measures

    @property
    def ordering(self) -> WellFoundedOrdering:
        return self._ordering

    @property
    def strict(self) -> bool:
        return self._strict

    @property
    def arity(self) -> int:
        return len(self._measures)

    def evaluate(self, env: Mapping[str, Any]) -> Tuple[Any, ...]:
        """Evaluate all measures in the given environment."""
        return tuple(m.evaluate(env) for m in self._measures)

    def decreases(
        self,
        pre_state: Mapping[str, Any],
        post_state: Mapping[str, Any],
    ) -> bool:
        """Check if the ranking function decreases from pre to post state.

        For lexicographic ordering: the first differing component must decrease.
        For natural ordering: the value must strictly decrease.
        """
        pre_values = self.evaluate(pre_state)
        post_values = self.evaluate(post_state)

        if any(v is None for v in pre_values) or any(v is None for v in post_values):
            return False  # Cannot evaluate

        if self._ordering == WellFoundedOrdering.LEXICOGRAPHIC:
            return self._lex_less(post_values, pre_values)
        else:
            # Simple natural/integer ordering
            for pre_v, post_v in zip(pre_values, post_values):
                if self._strict:
                    if not (post_v < pre_v):
                        return False
                else:
                    if not (post_v <= pre_v):
                        return False
            return True

    def bounded(self, env: Mapping[str, Any]) -> bool:
        """Check if the ranking function is bounded from below."""
        values = self.evaluate(env)
        for measure, value in zip(self._measures, values):
            if value is None:
                return False
            try:
                if value < measure.lower_bound:
                    return False
            except TypeError:
                return False
        return True

    @staticmethod
    def _lex_less(a: Tuple[Any, ...], b: Tuple[Any, ...]) -> bool:
        """Lexicographic less-than comparison."""
        for x, y in zip(a, b):
            if x < y:
                return True
            if x > y:
                return False
        return False

    def pretty(self) -> str:
        if self.arity == 1:
            return self._measures[0].pretty()
        measures_str = ", ".join(m.pretty() for m in self._measures)
        return f"({measures_str}) [{self._ordering.value}]"

    @classmethod
    def simple(cls, name: str, expression: str, lower_bound: int = 0) -> RankingFunction:
        """Create a simple single-measure ranking function."""
        measure = RankingMeasure(
            _name=name,
            _expression=expression,
            _lower_bound=lower_bound,
        )
        return cls(_measures=(measure,))

    @classmethod
    def lexicographic(cls, *measures: RankingMeasure) -> RankingFunction:
        """Create a lexicographic ranking function from multiple measures."""
        return cls(
            _measures=tuple(measures),
            _ordering=WellFoundedOrdering.LEXICOGRAPHIC,
        )

    @classmethod
    def from_callable(
        cls,
        fn: Callable[..., Any],
        name: str = "rank",
    ) -> RankingFunction:
        """Create a ranking function from a Python callable."""
        measure = RankingMeasure(
            _name=name,
            _expression=f"<callable:{name}>",
            _callable_fn=fn,
        )
        return cls(_measures=(measure,))


# ===================================================================
#  Well-founded proof
# ===================================================================


@dataclass(frozen=True)
class WellFoundedProof:
    """A proof that the ranking function's ordering is well-founded.

    For built-in orderings (natural, lexicographic), the proof is
    automatic.  For custom orderings, the user must supply evidence.
    """

    _ordering: WellFoundedOrdering
    _proof_text: str = ""
    _verified: bool = False
    _evidence: Optional[Dict[str, Any]] = None

    @property
    def ordering(self) -> WellFoundedOrdering:
        return self._ordering

    @property
    def proof_text(self) -> str:
        return self._proof_text

    @property
    def verified(self) -> bool:
        return self._verified

    @property
    def evidence(self) -> Optional[Dict[str, Any]]:
        return self._evidence

    @classmethod
    def automatic(cls, ordering: WellFoundedOrdering) -> WellFoundedProof:
        """Create an automatic well-foundedness proof for built-in orderings."""
        if ordering == WellFoundedOrdering.NATURAL:
            return cls(
                _ordering=ordering,
                _proof_text="Natural numbers are well-ordered by <",
                _verified=True,
            )
        if ordering == WellFoundedOrdering.INTEGER:
            return cls(
                _ordering=ordering,
                _proof_text="Integers bounded below are well-ordered by <",
                _verified=True,
            )
        if ordering == WellFoundedOrdering.LEXICOGRAPHIC:
            return cls(
                _ordering=ordering,
                _proof_text=(
                    "Lexicographic product of well-orderings is well-ordered "
                    "(by transfinite induction on the length)"
                ),
                _verified=True,
            )
        return cls(
            _ordering=ordering,
            _proof_text="Well-foundedness not automatically verified",
            _verified=False,
        )


# ===================================================================
#  Verification obligations
# ===================================================================


@dataclass(frozen=True)
class DecreasesObligation:
    """A verification obligation generated from a @decreases contract.

    The obligation states that on each loop iteration or recursive call,
    the ranking function must strictly decrease while remaining bounded.
    """

    _description: str
    _ranking_function: RankingFunction
    _loop_site: Optional[SiteId] = None
    _call_site: Optional[SiteId] = None
    _discharged: bool = False
    _discharge_method: Optional[str] = None

    @property
    def description(self) -> str:
        return self._description

    @property
    def ranking_function(self) -> RankingFunction:
        return self._ranking_function

    @property
    def loop_site(self) -> Optional[SiteId]:
        return self._loop_site

    @property
    def call_site(self) -> Optional[SiteId]:
        return self._call_site

    @property
    def discharged(self) -> bool:
        return self._discharged

    def pretty(self) -> str:
        status = "PROVED" if self._discharged else "PENDING"
        return f"[{status}] {self._description}"


# ===================================================================
#  DecreasesContract
# ===================================================================


class DecreasesContract(Contract):
    """@decreases contract for termination arguments.

    Attaches to a loop or recursive function to specify the ranking
    function that must decrease on each iteration/call.

    Usage::

        @decreases(lambda n: n, bound=0)
        def factorial(n: int) -> int: ...

        @decreases(lambda x, y: (x, y), ordering="lexicographic")
        def ackermann(x: int, y: int) -> int: ...
    """

    def __init__(
        self,
        ranking_function: RankingFunction,
        well_founded_proof: Optional[WellFoundedProof] = None,
        *,
        source_location: Optional[SourceLocation] = None,
        trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
        provenance: str = "user_annotation",
    ) -> None:
        super().__init__(
            source_location=source_location,
            trust=trust,
            provenance=provenance,
        )
        self._ranking_function = ranking_function
        self._well_founded_proof = (
            well_founded_proof
            or WellFoundedProof.automatic(ranking_function.ordering)
        )
        self._obligations: List[DecreasesObligation] = []

    @property
    def ranking_function(self) -> RankingFunction:
        return self._ranking_function

    @property
    def well_founded_proof(self) -> WellFoundedProof:
        return self._well_founded_proof

    @property
    def measure(self) -> RankingFunction:
        """Alias for ranking_function."""
        return self._ranking_function

    @property
    def obligations(self) -> List[DecreasesObligation]:
        return list(self._obligations)

    def check(
        self,
        pre_state: Mapping[str, Any],
        post_state: Mapping[str, Any],
    ) -> bool:
        """Check that the ranking function decreases from pre to post state.

        Also verifies that the ranking is bounded from below in both states.
        """
        # Check boundedness
        if not self._ranking_function.bounded(pre_state):
            return False
        if not self._ranking_function.bounded(post_state):
            return False

        # Check decrease
        return self._ranking_function.decreases(pre_state, post_state)

    def generate_obligation(
        self,
        loop_site: Optional[SiteId] = None,
        call_site: Optional[SiteId] = None,
    ) -> DecreasesObligation:
        """Generate a verification obligation for this contract.

        Returns a DecreasesObligation describing what must be proved.
        """
        if loop_site:
            desc = (
                f"Loop at {loop_site.name}: ranking function "
                f"{self._ranking_function.pretty()} must strictly decrease "
                f"and remain bounded from below"
            )
        elif call_site:
            desc = (
                f"Recursive call at {call_site.name}: ranking function "
                f"{self._ranking_function.pretty()} must strictly decrease"
            )
        else:
            desc = (
                f"Ranking function {self._ranking_function.pretty()} "
                f"must strictly decrease and remain bounded"
            )

        obligation = DecreasesObligation(
            _description=desc,
            _ranking_function=self._ranking_function,
            _loop_site=loop_site,
            _call_site=call_site,
        )
        self._obligations.append(obligation)
        return obligation

    def to_predicate(self) -> Predicate:
        """Project to a predicate expressing the decrease condition."""
        measures = self._ranking_function.measures
        if not measures:
            return Predicate.true_()

        terms: List[Term] = []
        for m in measures:
            terms.append(Term.var(m.name))

        if len(terms) == 1:
            # Single measure: rank(post) < rank(pre)
            desc = f"{measures[0].expression}' < {measures[0].expression}"
        else:
            # Lexicographic: (r1', r2', ...) <_lex (r1, r2, ...)
            pre_str = ", ".join(m.expression for m in measures)
            post_str = ", ".join(f"{m.expression}'" for m in measures)
            desc = f"({post_str}) <_lex ({pre_str})"

        return Predicate(
            kind=PredicateKind.COMPARISON,
            terms=tuple(terms),
            description=desc,
        )

    def to_boundary_seed(self) -> Any:
        """Project to a boundary seed for cover synthesis.

        The decrease contract seeds loop-header sites with the ranking
        function as a local section refinement.
        """
        return {
            "kind": "decreases",
            "ranking": self._ranking_function.pretty(),
            "ordering": self._ranking_function.ordering.value,
            "trust": self.trust.value,
        }

    def to_local_section(self, site_id: SiteId) -> LocalSection:
        """Create a local section encoding this contract at a site."""
        refinements: Dict[str, Any] = {
            "decreases": True,
            "ranking_function": self._ranking_function.pretty(),
            "ordering": self._ranking_function.ordering.value,
            "well_founded": self._well_founded_proof.verified,
        }
        for measure in self._ranking_function.measures:
            refinements[f"measure_{measure.name}"] = measure.expression
            refinements[f"bound_{measure.name}"] = measure.lower_bound

        return LocalSection(
            site_id=site_id,
            carrier_type=None,
            refinements=refinements,
            trust=self.trust,
            provenance=f"decreases_contract:{self.uid}",
        )

    def pretty(self) -> str:
        return f"@decreases({self._ranking_function.pretty()})"


# ===================================================================
#  Decorator function
# ===================================================================


def decreases(
    ranking_fn: Union[Callable[..., Any], str],
    *,
    bound: int = 0,
    ordering: str = "natural",
    measures: Optional[Sequence[Tuple[str, str]]] = None,
) -> Callable[[Any], Any]:
    """Decorator to attach a @decreases contract to a function.

    Usage::

        @decreases(lambda n: n, bound=0)
        def factorial(n: int) -> int: ...

        @decreases("n", bound=0)
        def countdown(n: int) -> None: ...

        @decreases(lambda x, y: (x, y), ordering="lexicographic")
        def ackermann(x: int, y: int) -> int: ...
    """
    # Build ranking function
    ordering_enum = WellFoundedOrdering(ordering)

    if measures is not None:
        # Multiple measures (lexicographic)
        measure_objs = tuple(
            RankingMeasure(_name=name, _expression=expr, _lower_bound=bound)
            for name, expr in measures
        )
        rf = RankingFunction(
            _measures=measure_objs,
            _ordering=ordering_enum,
        )
    elif callable(ranking_fn):
        rf = RankingFunction.from_callable(ranking_fn, name="rank")
    elif isinstance(ranking_fn, str):
        rf = RankingFunction.simple(ranking_fn, ranking_fn, lower_bound=bound)
    else:
        rf = RankingFunction.simple("rank", str(ranking_fn), lower_bound=bound)

    contract = DecreasesContract(ranking_function=rf)

    def decorator(fn: Any) -> Any:
        if not hasattr(fn, "_deppy_contracts"):
            fn._deppy_contracts = ContractSet()
        fn._deppy_contracts.theorems.append(contract)
        return fn

    return decorator
