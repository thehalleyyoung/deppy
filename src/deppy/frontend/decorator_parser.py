"""Parse @deppy decorators to contract seeds, proof seeds, and invariant seeds.

In the sheaf-descent framework, decorators on functions serve as
*boundary section contributions*: they declare facts about the input
boundary (preconditions), output boundary (postconditions), proof
obligations, termination measures, and transport declarations.

These seed dataclasses are consumed by the cover synthesis stage to:
1. Create proof observation sites for theorem/lemma decorators
2. Add refinement constraints to argument-boundary sites (requires)
3. Add refinement constraints to return-boundary sites (ensures)
4. Create loop-invariant site data from invariant decorators
5. Declare transport morphisms between sites (transport)

Recognized decorators:
- ``@deppy.requires(predicate_str, *, over=..., trust=...)``
- ``@deppy.ensures(predicate_str, *, over=..., trust=...)``
- ``@deppy.theorem(name, *, proof_method=..., dependencies=...)``
- ``@deppy.decreases(expression_str, *, bound=...)``
- ``@deppy.invariant(predicate_str, *, variables=...)``
- ``@deppy.transport(source, target, *, via=..., preserves=...)``
- ``@deppy.ghost(...)`` -- ghost parameters
- ``@deppy.witness(name, *, type=...)`` -- witness exports
- ``@deppy.axiom(name, ...)`` -- axiom declarations

All other decorators are preserved as-is in the IR for downstream handling.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from enum import Enum, auto
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

from deppy.core._protocols import SiteKind, TrustLevel
from deppy.static_analysis.observation_sites import SourceSpan


# ═══════════════════════════════════════════════════════════════════════════════
# Seed dataclasses
# ═══════════════════════════════════════════════════════════════════════════════


class SeedKind(Enum):
    """Classification of decorator seeds."""
    REQUIRES = "requires"
    ENSURES = "ensures"
    THEOREM = "theorem"
    DECREASES = "decreases"
    INVARIANT = "invariant"
    TRANSPORT = "transport"
    GHOST = "ghost"
    WITNESS = "witness"
    AXIOM = "axiom"


@dataclass(frozen=True)
class ContractSeed:
    """A precondition or postcondition seed from @deppy.requires / @deppy.ensures.

    In the sheaf view, a contract seed contributes refinement data to
    the boundary sections:
    - ``requires`` seeds add constraints to argument-boundary site carriers
    - ``ensures`` seeds add constraints to return-boundary site carriers

    The ``predicate`` is a string expression that will be parsed by the
    predicate evaluator during local solving.

    Attributes:
        kind: Whether this is a REQUIRES or ENSURES contract.
        predicate: The predicate expression string.
        over: Optional list of variable names the predicate ranges over.
        trust: Trust level for this contract's contribution.
        quantifier: Optional quantifier scope (forall/exists).
        label: Optional human-readable label for error messages.
        span: Source location of the decorator.
    """
    kind: SeedKind
    predicate: str
    over: Tuple[str, ...] = ()
    trust: TrustLevel = TrustLevel.ASSUMED
    quantifier: Optional[str] = None
    label: Optional[str] = None
    span: SourceSpan = field(default_factory=lambda: SourceSpan("<unknown>", 0, 0))

    @property
    def is_precondition(self) -> bool:
        return self.kind == SeedKind.REQUIRES

    @property
    def is_postcondition(self) -> bool:
        return self.kind == SeedKind.ENSURES

    @property
    def boundary_kind(self) -> SiteKind:
        """Which boundary this seed contributes to."""
        if self.kind == SeedKind.REQUIRES:
            return SiteKind.ARGUMENT_BOUNDARY
        return SiteKind.RETURN_OUTPUT_BOUNDARY


@dataclass(frozen=True)
class ProofSeed:
    """A proof obligation seed from @deppy.theorem / @deppy.axiom.

    Proof seeds create proof observation sites in the cover.  During
    local solving, these sites carry proof-backed trust levels and
    export witnesses to downstream consumer sites.

    Attributes:
        kind: THEOREM or AXIOM.
        name: The theorem/axiom name.
        proof_method: Suggested proof strategy (e.g., "induction", "smt").
        dependencies: Names of other theorems this depends on.
        is_lemma: Whether this is a lemma (local scope) vs theorem (exported).
        statement: Optional formal statement string.
        span: Source location of the decorator.
    """
    kind: SeedKind
    name: str
    proof_method: Optional[str] = None
    dependencies: Tuple[str, ...] = ()
    is_lemma: bool = False
    statement: Optional[str] = None
    span: SourceSpan = field(default_factory=lambda: SourceSpan("<unknown>", 0, 0))

    @property
    def boundary_kind(self) -> SiteKind:
        return SiteKind.PROOF


@dataclass(frozen=True)
class DecreaseSeed:
    """A termination measure seed from @deppy.decreases.

    Decrease seeds contribute to loop-invariant sites by specifying
    the ranking function used for well-founded recursion arguments.

    Attributes:
        expression: The decreases expression string.
        bound: Optional lower bound for the measure.
        over: Variables involved in the measure.
        span: Source location.
    """
    expression: str
    bound: Optional[str] = None
    over: Tuple[str, ...] = ()
    span: SourceSpan = field(default_factory=lambda: SourceSpan("<unknown>", 0, 0))

    @property
    def kind(self) -> SeedKind:
        return SeedKind.DECREASES

    @property
    def boundary_kind(self) -> SiteKind:
        return SiteKind.LOOP_HEADER_INVARIANT


@dataclass(frozen=True)
class InvariantSeed:
    """A loop invariant seed from @deppy.invariant.

    Invariant seeds contribute to loop-header/invariant sites by
    specifying candidate invariants that must hold at each iteration.

    Attributes:
        predicate: The invariant predicate string.
        variables: Variables involved in the invariant.
        label: Optional label for diagnostics.
        span: Source location.
    """
    predicate: str
    variables: Tuple[str, ...] = ()
    label: Optional[str] = None
    span: SourceSpan = field(default_factory=lambda: SourceSpan("<unknown>", 0, 0))

    @property
    def kind(self) -> SeedKind:
        return SeedKind.INVARIANT

    @property
    def boundary_kind(self) -> SiteKind:
        return SiteKind.LOOP_HEADER_INVARIANT


@dataclass(frozen=True)
class TransportSeed:
    """A transport declaration seed from @deppy.transport.

    Transport seeds create morphisms between observation sites.  They
    declare that facts at one site restrict/transport to facts at
    another site, optionally specifying which refinement keys are
    preserved and the theory pack that justifies the transport.

    Attributes:
        source: Source site descriptor (variable name or site label).
        target: Target site descriptor.
        via: The transport mechanism or theory pack.
        preserves: Refinement keys preserved by the transport.
        span: Source location.
    """
    source: str
    target: str
    via: Optional[str] = None
    preserves: Tuple[str, ...] = ()
    span: SourceSpan = field(default_factory=lambda: SourceSpan("<unknown>", 0, 0))

    @property
    def kind(self) -> SeedKind:
        return SeedKind.TRANSPORT

    @property
    def boundary_kind(self) -> SiteKind:
        return SiteKind.PROOF


@dataclass(frozen=True)
class GhostSeed:
    """A ghost parameter seed from @deppy.ghost.

    Ghost seeds declare ghost parameters that exist only for
    specification purposes and are erased at runtime.

    Attributes:
        name: The ghost parameter name.
        type_str: Optional type annotation string.
        span: Source location.
    """
    name: str
    type_str: Optional[str] = None
    span: SourceSpan = field(default_factory=lambda: SourceSpan("<unknown>", 0, 0))

    @property
    def kind(self) -> SeedKind:
        return SeedKind.GHOST


@dataclass(frozen=True)
class WitnessSeed:
    """A witness export seed from @deppy.witness.

    Witness seeds declare that a function exports a proof witness
    that can be consumed by downstream proof sites.

    Attributes:
        name: The witness name.
        type_str: Optional type annotation string.
        span: Source location.
    """
    name: str
    type_str: Optional[str] = None
    span: SourceSpan = field(default_factory=lambda: SourceSpan("<unknown>", 0, 0))

    @property
    def kind(self) -> SeedKind:
        return SeedKind.WITNESS


# Union of all seed types
DecoratorSeed = Union[
    ContractSeed,
    ProofSeed,
    DecreaseSeed,
    InvariantSeed,
    TransportSeed,
    GhostSeed,
    WitnessSeed,
]


# ═══════════════════════════════════════════════════════════════════════════════
# Decorator parser
# ═══════════════════════════════════════════════════════════════════════════════


class DecoratorParser:
    """Parses @deppy.* decorators from function AST nodes.

    The parser recognizes deppy-specific decorator patterns and produces
    seed dataclasses that the cover builder consumes to create proof sites,
    boundary constraints, and transport morphisms.

    Usage::

        parser = DecoratorParser(filename="my_module.py")
        for decorator_node in func_def.decorator_list:
            seed = parser.parse(decorator_node)
            if seed is not None:
                # Process the seed
    """

    def __init__(self, filename: str = "<unknown>") -> None:
        self._filename = filename
        # Map from decorator name to parser method
        self._parsers: Dict[str, Any] = {
            "requires": self._parse_requires,
            "ensures": self._parse_ensures,
            "theorem": self._parse_theorem,
            "decreases": self._parse_decreases,
            "invariant": self._parse_invariant,
            "transport": self._parse_transport,
            "ghost": self._parse_ghost,
            "witness": self._parse_witness,
            "axiom": self._parse_axiom,
        }

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._filename)

    def parse(self, node: ast.expr) -> Optional[DecoratorSeed]:
        """Parse a single decorator AST node.

        Returns a seed dataclass if the decorator is recognized as a
        deppy decorator, or None if it is not.
        """
        # Pattern 1: @deppy.requires("predicate")
        if isinstance(node, ast.Call):
            name = self._extract_deppy_name(node.func)
            if name is not None and name in self._parsers:
                return self._parsers[name](node)

        # Pattern 2: @deppy.theorem (without call, unusual but possible)
        if isinstance(node, (ast.Attribute, ast.Name)):
            name = self._extract_deppy_name(node)
            if name is not None and name in self._parsers:
                # Create a synthetic call node with no args
                return self._parsers[name](None, span=self._span(node))

        return None

    def parse_all(
        self, decorator_list: Sequence[ast.expr]
    ) -> Tuple[List[DecoratorSeed], List[ast.expr]]:
        """Parse all decorators, separating deppy seeds from others.

        Returns:
            - List of recognized deppy decorator seeds
            - List of unrecognized decorator AST nodes (preserved as-is)
        """
        seeds: List[DecoratorSeed] = []
        other_decorators: List[ast.expr] = []

        for dec in decorator_list:
            seed = self.parse(dec)
            if seed is not None:
                seeds.append(seed)
            else:
                other_decorators.append(dec)

        return seeds, other_decorators

    def _extract_deppy_name(self, node: ast.expr) -> Optional[str]:
        """Extract the deppy decorator name from a node.

        Recognizes patterns:
        - ``deppy.requires`` -> "requires"
        - ``deppy.theorem`` -> "theorem"
        - ``dp.requires`` -> "requires" (alias)
        """
        if isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Name):
                if node.value.id in ("deppy", "dp"):
                    return node.attr
        return None

    # ── Individual decorator parsers ──────────────────────────────────────

    def _parse_requires(
        self,
        node: Optional[ast.Call],
        *,
        span: Optional[SourceSpan] = None,
    ) -> ContractSeed:
        """Parse @deppy.requires(predicate, *, over=..., trust=...)."""
        if node is None:
            return ContractSeed(
                kind=SeedKind.REQUIRES,
                predicate="True",
                span=span or SourceSpan("<unknown>", 0, 0),
            )

        predicate = self._extract_string_arg(node, 0, "True")
        over = self._extract_tuple_kwarg(node, "over")
        trust = self._extract_trust_kwarg(node)
        label = self._extract_string_kwarg(node, "label")
        quantifier = self._extract_string_kwarg(node, "quantifier")

        return ContractSeed(
            kind=SeedKind.REQUIRES,
            predicate=predicate,
            over=over,
            trust=trust,
            quantifier=quantifier,
            label=label,
            span=self._span(node),
        )

    def _parse_ensures(
        self,
        node: Optional[ast.Call],
        *,
        span: Optional[SourceSpan] = None,
    ) -> ContractSeed:
        """Parse @deppy.ensures(predicate, *, over=..., trust=...)."""
        if node is None:
            return ContractSeed(
                kind=SeedKind.ENSURES,
                predicate="True",
                span=span or SourceSpan("<unknown>", 0, 0),
            )

        predicate = self._extract_string_arg(node, 0, "True")
        over = self._extract_tuple_kwarg(node, "over")
        trust = self._extract_trust_kwarg(node)
        label = self._extract_string_kwarg(node, "label")
        quantifier = self._extract_string_kwarg(node, "quantifier")

        return ContractSeed(
            kind=SeedKind.ENSURES,
            predicate=predicate,
            over=over,
            trust=trust,
            quantifier=quantifier,
            label=label,
            span=self._span(node),
        )

    def _parse_theorem(
        self,
        node: Optional[ast.Call],
        *,
        span: Optional[SourceSpan] = None,
    ) -> ProofSeed:
        """Parse @deppy.theorem(name, *, proof_method=..., dependencies=...)."""
        if node is None:
            return ProofSeed(
                kind=SeedKind.THEOREM,
                name="<unnamed>",
                span=span or SourceSpan("<unknown>", 0, 0),
            )

        name = self._extract_string_arg(node, 0, "<unnamed>")
        proof_method = self._extract_string_kwarg(node, "proof_method")
        deps = self._extract_tuple_kwarg(node, "dependencies")
        is_lemma = self._extract_bool_kwarg(node, "lemma", False)
        statement = self._extract_string_kwarg(node, "statement")

        return ProofSeed(
            kind=SeedKind.THEOREM,
            name=name,
            proof_method=proof_method,
            dependencies=deps,
            is_lemma=is_lemma,
            statement=statement,
            span=self._span(node),
        )

    def _parse_axiom(
        self,
        node: Optional[ast.Call],
        *,
        span: Optional[SourceSpan] = None,
    ) -> ProofSeed:
        """Parse @deppy.axiom(name, ...)."""
        if node is None:
            return ProofSeed(
                kind=SeedKind.AXIOM,
                name="<unnamed>",
                span=span or SourceSpan("<unknown>", 0, 0),
            )

        name = self._extract_string_arg(node, 0, "<unnamed>")
        statement = self._extract_string_kwarg(node, "statement")

        return ProofSeed(
            kind=SeedKind.AXIOM,
            name=name,
            statement=statement,
            span=self._span(node),
        )

    def _parse_decreases(
        self,
        node: Optional[ast.Call],
        *,
        span: Optional[SourceSpan] = None,
    ) -> DecreaseSeed:
        """Parse @deppy.decreases(expression, *, bound=...)."""
        if node is None:
            return DecreaseSeed(
                expression="0",
                span=span or SourceSpan("<unknown>", 0, 0),
            )

        expression = self._extract_string_arg(node, 0, "0")
        bound = self._extract_string_kwarg(node, "bound")
        over = self._extract_tuple_kwarg(node, "over")

        return DecreaseSeed(
            expression=expression,
            bound=bound,
            over=over,
            span=self._span(node),
        )

    def _parse_invariant(
        self,
        node: Optional[ast.Call],
        *,
        span: Optional[SourceSpan] = None,
    ) -> InvariantSeed:
        """Parse @deppy.invariant(predicate, *, variables=...)."""
        if node is None:
            return InvariantSeed(
                predicate="True",
                span=span or SourceSpan("<unknown>", 0, 0),
            )

        predicate = self._extract_string_arg(node, 0, "True")
        variables = self._extract_tuple_kwarg(node, "variables")
        label = self._extract_string_kwarg(node, "label")

        return InvariantSeed(
            predicate=predicate,
            variables=variables,
            label=label,
            span=self._span(node),
        )

    def _parse_transport(
        self,
        node: Optional[ast.Call],
        *,
        span: Optional[SourceSpan] = None,
    ) -> TransportSeed:
        """Parse @deppy.transport(source, target, *, via=..., preserves=...)."""
        if node is None:
            return TransportSeed(
                source="<unknown>",
                target="<unknown>",
                span=span or SourceSpan("<unknown>", 0, 0),
            )

        source = self._extract_string_arg(node, 0, "<unknown>")
        target = self._extract_string_arg(node, 1, "<unknown>")
        via = self._extract_string_kwarg(node, "via")
        preserves = self._extract_tuple_kwarg(node, "preserves")

        return TransportSeed(
            source=source,
            target=target,
            via=via,
            preserves=preserves,
            span=self._span(node),
        )

    def _parse_ghost(
        self,
        node: Optional[ast.Call],
        *,
        span: Optional[SourceSpan] = None,
    ) -> GhostSeed:
        """Parse @deppy.ghost(name, *, type=...)."""
        if node is None:
            return GhostSeed(
                name="<unnamed>",
                span=span or SourceSpan("<unknown>", 0, 0),
            )

        name = self._extract_string_arg(node, 0, "<unnamed>")
        type_str = self._extract_string_kwarg(node, "type")

        return GhostSeed(
            name=name,
            type_str=type_str,
            span=self._span(node),
        )

    def _parse_witness(
        self,
        node: Optional[ast.Call],
        *,
        span: Optional[SourceSpan] = None,
    ) -> WitnessSeed:
        """Parse @deppy.witness(name, *, type=...)."""
        if node is None:
            return WitnessSeed(
                name="<unnamed>",
                span=span or SourceSpan("<unknown>", 0, 0),
            )

        name = self._extract_string_arg(node, 0, "<unnamed>")
        type_str = self._extract_string_kwarg(node, "type")

        return WitnessSeed(
            name=name,
            type_str=type_str,
            span=self._span(node),
        )

    # ── Argument extraction helpers ───────────────────────────────────────

    def _extract_string_arg(
        self, node: ast.Call, index: int, default: str
    ) -> str:
        """Extract a string positional argument from a call node."""
        if index < len(node.args):
            arg = node.args[index]
            if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                return arg.value
            # Try to unparse the expression as a string
            try:
                return ast.unparse(arg)
            except Exception:
                return default
        return default

    def _extract_string_kwarg(
        self, node: ast.Call, name: str
    ) -> Optional[str]:
        """Extract a string keyword argument from a call node."""
        for kw in node.keywords:
            if kw.arg == name:
                if isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, str):
                    return kw.value.value
                try:
                    return ast.unparse(kw.value)
                except Exception:
                    return None
        return None

    def _extract_tuple_kwarg(
        self, node: ast.Call, name: str
    ) -> Tuple[str, ...]:
        """Extract a tuple-of-strings keyword argument."""
        for kw in node.keywords:
            if kw.arg == name:
                return self._ast_to_string_tuple(kw.value)
        return ()

    def _extract_bool_kwarg(
        self, node: ast.Call, name: str, default: bool
    ) -> bool:
        """Extract a boolean keyword argument."""
        for kw in node.keywords:
            if kw.arg == name:
                if isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, bool):
                    return kw.value.value
        return default

    def _extract_trust_kwarg(self, node: ast.Call) -> TrustLevel:
        """Extract a trust level keyword argument."""
        trust_str = self._extract_string_kwarg(node, "trust")
        if trust_str is not None:
            trust_str_lower = trust_str.lower().strip()
            for level in TrustLevel:
                if level.value == trust_str_lower or level.name.lower() == trust_str_lower:
                    return level
        return TrustLevel.ASSUMED

    def _ast_to_string_tuple(self, node: ast.expr) -> Tuple[str, ...]:
        """Convert an AST node to a tuple of strings."""
        if isinstance(node, ast.Tuple) or isinstance(node, ast.List):
            result: List[str] = []
            for elt in node.elts:
                if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
                    result.append(elt.value)
                elif isinstance(elt, ast.Name):
                    result.append(elt.id)
                else:
                    try:
                        result.append(ast.unparse(elt))
                    except Exception:
                        pass
            return tuple(result)
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return (node.value,)
        return ()


# ═══════════════════════════════════════════════════════════════════════════════
# Convenience functions
# ═══════════════════════════════════════════════════════════════════════════════


def parse_decorators(
    decorator_list: Sequence[ast.expr],
    *,
    filename: str = "<unknown>",
) -> Tuple[List[DecoratorSeed], List[ast.expr]]:
    """Parse a list of decorator AST nodes.

    Returns a tuple of (deppy_seeds, other_decorators).
    """
    parser = DecoratorParser(filename=filename)
    return parser.parse_all(decorator_list)


def extract_contracts(
    seeds: Sequence[DecoratorSeed],
) -> Tuple[List[ContractSeed], List[ContractSeed]]:
    """Separate contract seeds into preconditions and postconditions."""
    requires: List[ContractSeed] = []
    ensures: List[ContractSeed] = []
    for seed in seeds:
        if isinstance(seed, ContractSeed):
            if seed.is_precondition:
                requires.append(seed)
            else:
                ensures.append(seed)
    return requires, ensures


def extract_proof_seeds(
    seeds: Sequence[DecoratorSeed],
) -> List[ProofSeed]:
    """Extract all proof seeds (theorem + axiom) from a list of seeds."""
    return [s for s in seeds if isinstance(s, ProofSeed)]


def extract_invariant_seeds(
    seeds: Sequence[DecoratorSeed],
) -> List[InvariantSeed]:
    """Extract all invariant seeds from a list of seeds."""
    return [s for s in seeds if isinstance(s, InvariantSeed)]


def extract_transport_seeds(
    seeds: Sequence[DecoratorSeed],
) -> List[TransportSeed]:
    """Extract all transport seeds from a list of seeds."""
    return [s for s in seeds if isinstance(s, TransportSeed)]
