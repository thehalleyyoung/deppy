"""Proof elaborator: elaborate theorem decorators into proof sites and obligations.

Processes function ASTs with theorem-related decorators (@requires, @ensures,
@invariant, @theorem, @lemma, @transport) and produces:
- Proof sites in the observation site category
- Proof obligations that must be discharged
- Transport maps (morphisms) between sites
"""

from __future__ import annotations

import ast
import enum
import logging
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
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteSite, ConcreteMorphism
from deppy.types.base import TypeBase, AnyType, ANY_TYPE
from deppy.types.refinement import (
    RefinementType,
    Predicate as RefinementPredicate,
    TruePred,
    ComparisonPred,
    ComparisonOp,
    ConjunctionPred,
    ImplicationPred,
)
from deppy.types.witnesses import ProofTerm, ReflProof, AssumptionProof
from deppy.proof._protocols import (
    ProofTermKind,
    ProofObligation,
    ObligationStatus,
    ProofContext,
    AnnotationLevel,
)

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Decorator kinds
# ---------------------------------------------------------------------------


class DecoratorKind(enum.Enum):
    """Kinds of decorators recognized by the elaborator."""

    REQUIRES = "requires"
    ENSURES = "ensures"
    INVARIANT = "invariant"
    THEOREM = "theorem"
    LEMMA = "lemma"
    TRANSPORT = "transport"
    DECREASES = "decreases"
    PURE = "pure"
    TOTAL = "total"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class ParsedDecorator:
    """A decorator parsed from an AST node.

    Attributes:
        _kind: The kind of decorator.
        _name: The decorator name as it appears in source.
        _args: Positional arguments to the decorator.
        _kwargs: Keyword arguments to the decorator.
        _source_line: Line number in source.
        _raw_node: The raw AST node (if available).
    """

    _kind: DecoratorKind
    _name: str = ""
    _args: Tuple[Any, ...] = ()
    _kwargs: Dict[str, Any] = field(default_factory=dict)
    _source_line: int = 0
    _raw_node: Any = None

    @property
    def kind(self) -> DecoratorKind:
        return self._kind

    @property
    def name(self) -> str:
        return self._name

    @property
    def args(self) -> Tuple[Any, ...]:
        return self._args

    @property
    def kwargs(self) -> Dict[str, Any]:
        return dict(self._kwargs)

    @property
    def source_line(self) -> int:
        return self._source_line

    def __repr__(self) -> str:
        return f"ParsedDecorator({self._kind.value}, {self._name!r})"


# ---------------------------------------------------------------------------
# Elaboration result
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ElaborationResult:
    """Result of elaborating a decorated function.

    Attributes:
        _proof_sites: Sites created for proof obligations.
        _obligations: Proof obligations to discharge.
        _transport_maps: Transport morphisms derived from @transport declarations.
        _annotation_level: Detected annotation level.
        _context: Proof context with assumptions derived from decorators.
        _function_name: Name of the elaborated function.
        _warnings: Non-fatal warnings encountered during elaboration.
    """

    _proof_sites: Tuple[SiteId, ...]
    _obligations: Tuple[ProofObligation, ...]
    _transport_maps: Tuple[ConcreteMorphism, ...]
    _annotation_level: AnnotationLevel = AnnotationLevel.ZERO
    _context: Optional[ProofContext] = None
    _function_name: str = ""
    _warnings: Tuple[str, ...] = ()

    @property
    def proof_sites(self) -> List[SiteId]:
        return list(self._proof_sites)

    @property
    def obligations(self) -> List[ProofObligation]:
        return list(self._obligations)

    @property
    def transport_maps(self) -> List[ConcreteMorphism]:
        return list(self._transport_maps)

    @property
    def annotation_level(self) -> AnnotationLevel:
        return self._annotation_level

    @property
    def context(self) -> Optional[ProofContext]:
        return self._context

    @property
    def function_name(self) -> str:
        return self._function_name

    @property
    def warnings(self) -> List[str]:
        return list(self._warnings)

    @property
    def total_obligations(self) -> int:
        return len(self._obligations)

    @property
    def has_transport(self) -> bool:
        return len(self._transport_maps) > 0

    def __repr__(self) -> str:
        return (
            f"ElaborationResult(sites={len(self._proof_sites)}, "
            f"obligations={len(self._obligations)}, "
            f"transports={len(self._transport_maps)})"
        )


# ---------------------------------------------------------------------------
# AST helpers
# ---------------------------------------------------------------------------


def _extract_decorator_name(node: ast.expr) -> str:
    """Extract the name of a decorator from its AST node."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Call):
        return _extract_decorator_name(node.func)
    return ""


def _classify_decorator(name: str) -> DecoratorKind:
    """Classify a decorator name into a DecoratorKind."""
    _mapping: Dict[str, DecoratorKind] = {
        "requires": DecoratorKind.REQUIRES,
        "pre": DecoratorKind.REQUIRES,
        "precondition": DecoratorKind.REQUIRES,
        "ensures": DecoratorKind.ENSURES,
        "post": DecoratorKind.ENSURES,
        "postcondition": DecoratorKind.ENSURES,
        "invariant": DecoratorKind.INVARIANT,
        "inv": DecoratorKind.INVARIANT,
        "theorem": DecoratorKind.THEOREM,
        "thm": DecoratorKind.THEOREM,
        "lemma": DecoratorKind.LEMMA,
        "transport": DecoratorKind.TRANSPORT,
        "decreases": DecoratorKind.DECREASES,
        "pure": DecoratorKind.PURE,
        "total": DecoratorKind.TOTAL,
    }
    return _mapping.get(name.lower(), DecoratorKind.UNKNOWN)


def _extract_string_arg(node: ast.expr) -> Optional[str]:
    """Extract a string from a Constant AST node."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _extract_name_or_string(node: ast.expr) -> Optional[str]:
    """Extract a name or string from an AST node."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _parse_decorator_node(node: ast.expr) -> ParsedDecorator:
    """Parse an AST decorator node into a ParsedDecorator."""
    if isinstance(node, ast.Call):
        name = _extract_decorator_name(node.func)
        kind = _classify_decorator(name)
        args = tuple(
            _extract_name_or_string(a) or ast.dump(a) for a in node.args
        )
        kwargs: Dict[str, Any] = {}
        for kw in node.keywords:
            if kw.arg is not None:
                kwargs[kw.arg] = _extract_name_or_string(kw.value) or ast.dump(
                    kw.value
                )
        return ParsedDecorator(
            _kind=kind,
            _name=name,
            _args=args,
            _kwargs=kwargs,
            _source_line=getattr(node, "lineno", 0),
            _raw_node=node,
        )
    name = _extract_decorator_name(node)
    kind = _classify_decorator(name)
    return ParsedDecorator(
        _kind=kind,
        _name=name,
        _source_line=getattr(node, "lineno", 0),
        _raw_node=node,
    )


def _extract_function_params(func_node: ast.FunctionDef) -> List[Tuple[str, Optional[str]]]:
    """Extract parameter names and optional type annotation strings."""
    params: List[Tuple[str, Optional[str]]] = []
    for arg in func_node.args.args:
        ann = None
        if arg.annotation is not None:
            if isinstance(arg.annotation, ast.Name):
                ann = arg.annotation.id
            elif isinstance(arg.annotation, ast.Constant):
                ann = str(arg.annotation.value)
            else:
                ann = ast.dump(arg.annotation)
        params.append((arg.arg, ann))
    return params


def _extract_return_annotation(func_node: ast.FunctionDef) -> Optional[str]:
    """Extract the return type annotation as a string."""
    ret = func_node.returns
    if ret is None:
        return None
    if isinstance(ret, ast.Name):
        return ret.id
    if isinstance(ret, ast.Constant):
        return str(ret.value)
    return ast.dump(ret)


# ---------------------------------------------------------------------------
# Proof site factory
# ---------------------------------------------------------------------------


def _make_proof_site_id(func_name: str, decorator_kind: DecoratorKind,
                        index: int) -> SiteId:
    """Create a SiteId for a proof obligation site."""
    site_name = f"{func_name}.{decorator_kind.value}_{index}"
    return SiteId(
        kind=SiteKind.PROOF,
        name=site_name,
    )


def _make_argument_site_id(func_name: str, param_name: str) -> SiteId:
    """Create a SiteId for a function argument boundary."""
    return SiteId(
        kind=SiteKind.ARGUMENT_BOUNDARY,
        name=f"{func_name}.{param_name}",
    )


def _make_return_site_id(func_name: str) -> SiteId:
    """Create a SiteId for the function return boundary."""
    return SiteId(
        kind=SiteKind.RETURN_OUTPUT_BOUNDARY,
        name=f"{func_name}.return",
    )


# ---------------------------------------------------------------------------
# Obligation builders
# ---------------------------------------------------------------------------


def _build_requires_obligation(
    func_name: str,
    decorator: ParsedDecorator,
    site_id: SiteId,
    params: List[Tuple[str, Optional[str]]],
) -> ProofObligation:
    """Build a proof obligation from a @requires decorator."""
    pred_text = decorator.args[0] if decorator.args else "True"
    context: Dict[str, Any] = {
        "kind": "precondition",
        "function": func_name,
        "predicate_text": pred_text,
        "parameters": {name: ann for name, ann in params},
    }
    return ProofObligation(
        prop=("requires", pred_text, func_name),
        site_id=site_id,
        context=context,
        status=ObligationStatus.GENERATED,
        source_location=f"line {decorator.source_line}",
    )


def _build_ensures_obligation(
    func_name: str,
    decorator: ParsedDecorator,
    site_id: SiteId,
    params: List[Tuple[str, Optional[str]]],
    return_ann: Optional[str],
) -> ProofObligation:
    """Build a proof obligation from an @ensures decorator."""
    pred_text = decorator.args[0] if decorator.args else "True"
    context: Dict[str, Any] = {
        "kind": "postcondition",
        "function": func_name,
        "predicate_text": pred_text,
        "parameters": {name: ann for name, ann in params},
        "return_type": return_ann,
    }
    return ProofObligation(
        prop=("ensures", pred_text, func_name),
        site_id=site_id,
        context=context,
        status=ObligationStatus.GENERATED,
        source_location=f"line {decorator.source_line}",
    )


def _build_invariant_obligation(
    func_name: str,
    decorator: ParsedDecorator,
    site_id: SiteId,
) -> ProofObligation:
    """Build a proof obligation from an @invariant decorator."""
    pred_text = decorator.args[0] if decorator.args else "True"
    context: Dict[str, Any] = {
        "kind": "invariant",
        "function": func_name,
        "predicate_text": pred_text,
    }
    return ProofObligation(
        prop=("invariant", pred_text, func_name),
        site_id=site_id,
        context=context,
        status=ObligationStatus.GENERATED,
        source_location=f"line {decorator.source_line}",
    )


def _build_theorem_obligation(
    func_name: str,
    decorator: ParsedDecorator,
    site_id: SiteId,
) -> ProofObligation:
    """Build a proof obligation from a @theorem decorator."""
    statement = decorator.args[0] if decorator.args else func_name
    context: Dict[str, Any] = {
        "kind": "theorem",
        "function": func_name,
        "statement": statement,
    }
    return ProofObligation(
        prop=("theorem", statement, func_name),
        site_id=site_id,
        context=context,
        status=ObligationStatus.GENERATED,
        source_location=f"line {decorator.source_line}",
    )


def _build_lemma_obligation(
    func_name: str,
    decorator: ParsedDecorator,
    site_id: SiteId,
) -> ProofObligation:
    """Build a proof obligation from a @lemma decorator."""
    statement = decorator.args[0] if decorator.args else func_name
    context: Dict[str, Any] = {
        "kind": "lemma",
        "function": func_name,
        "statement": statement,
    }
    return ProofObligation(
        prop=("lemma", statement, func_name),
        site_id=site_id,
        context=context,
        status=ObligationStatus.GENERATED,
        source_location=f"line {decorator.source_line}",
    )


def _build_decreases_obligation(
    func_name: str,
    decorator: ParsedDecorator,
    site_id: SiteId,
) -> ProofObligation:
    """Build a proof obligation from a @decreases decorator."""
    ranking = decorator.args[0] if decorator.args else "unknown"
    context: Dict[str, Any] = {
        "kind": "decreases",
        "function": func_name,
        "ranking_function": ranking,
    }
    return ProofObligation(
        prop=("decreases", ranking, func_name),
        site_id=site_id,
        context=context,
        status=ObligationStatus.GENERATED,
        source_location=f"line {decorator.source_line}",
    )


# ---------------------------------------------------------------------------
# Transport morphism builder
# ---------------------------------------------------------------------------


def _build_transport_morphism(
    func_name: str,
    decorator: ParsedDecorator,
    source_site: SiteId,
    target_site: SiteId,
) -> ConcreteMorphism:
    """Build a transport morphism from a @transport decorator."""
    eq_proof_name = decorator.args[0] if len(decorator.args) > 0 else "eq"
    target_func = decorator.args[1] if len(decorator.args) > 1 else func_name
    metadata: Dict[str, Any] = {
        "transport_kind": "equality",
        "eq_proof": eq_proof_name,
        "target_func": target_func,
        "source_line": decorator.source_line,
    }
    return ConcreteMorphism(
        _source=source_site,
        _target=target_site,
        projection=None,
        _metadata=metadata,
    )


# ---------------------------------------------------------------------------
# Annotation level inference
# ---------------------------------------------------------------------------


def _infer_annotation_level(
    decorators: List[ParsedDecorator],
    has_assertions: bool = False,
    has_loop_invariants: bool = False,
) -> AnnotationLevel:
    """Infer the annotation level from the decorators present."""
    kinds = {d.kind for d in decorators}
    if DecoratorKind.THEOREM in kinds or DecoratorKind.LEMMA in kinds:
        if any(d.kind == DecoratorKind.DECREASES for d in decorators):
            return AnnotationLevel.FULL
        return AnnotationLevel.LEMMAS
    if DecoratorKind.INVARIANT in kinds or has_loop_invariants:
        return AnnotationLevel.INVARIANTS
    if DecoratorKind.REQUIRES in kinds or DecoratorKind.ENSURES in kinds:
        return AnnotationLevel.CONTRACTS
    if has_assertions:
        return AnnotationLevel.CONTRACTS
    return AnnotationLevel.ZERO


# ---------------------------------------------------------------------------
# AST analysis helpers
# ---------------------------------------------------------------------------


def _find_assert_statements(body: List[ast.stmt]) -> List[ast.Assert]:
    """Find all assert statements in a function body (non-recursive)."""
    asserts: List[ast.Assert] = []
    for stmt in body:
        if isinstance(stmt, ast.Assert):
            asserts.append(stmt)
        if isinstance(stmt, (ast.For, ast.While)):
            for sub in stmt.body:
                if isinstance(sub, ast.Assert):
                    asserts.append(sub)
        if isinstance(stmt, ast.If):
            for sub in stmt.body + stmt.orelse:
                if isinstance(sub, ast.Assert):
                    asserts.append(sub)
        if isinstance(stmt, ast.With):
            for sub in stmt.body:
                if isinstance(sub, ast.Assert):
                    asserts.append(sub)
    return asserts


def _find_loops(body: List[ast.stmt]) -> List[Union[ast.For, ast.While]]:
    """Find all loop statements in a function body."""
    loops: List[Union[ast.For, ast.While]] = []
    for stmt in body:
        if isinstance(stmt, (ast.For, ast.While)):
            loops.append(stmt)
    return loops


def _has_recursive_calls(func_node: ast.FunctionDef) -> bool:
    """Check if a function contains recursive calls to itself."""
    func_name = func_node.name

    class RecursionVisitor(ast.NodeVisitor):
        def __init__(self) -> None:
            self.found = False

        def visit_Call(self, node: ast.Call) -> None:
            if isinstance(node.func, ast.Name) and node.func.id == func_name:
                self.found = True
            self.generic_visit(node)

    visitor = RecursionVisitor()
    visitor.visit(func_node)
    return visitor.found


# ---------------------------------------------------------------------------
# Proof elaborator
# ---------------------------------------------------------------------------


class ProofElaborator:
    """Elaborate theorem decorators into proof sites and obligations.

    Takes a function AST along with its decorators and produces an
    ElaborationResult containing proof sites, proof obligations, and
    transport maps.

    Attributes:
        _site_counter: Counter for generating unique site identifiers.
        _default_trust: Default trust level for generated obligations.
        _strict_mode: If True, unknown decorators produce warnings.
    """

    def __init__(
        self,
        default_trust: TrustLevel = TrustLevel.RESIDUAL,
        strict_mode: bool = False,
    ) -> None:
        self._site_counter: int = 0
        self._default_trust: TrustLevel = default_trust
        self._strict_mode: bool = strict_mode

    def _next_site_index(self) -> int:
        """Generate the next unique site index."""
        idx = self._site_counter
        self._site_counter += 1
        return idx

    def elaborate(
        self,
        func_ast: ast.FunctionDef,
        decorators: Optional[List[Any]] = None,
    ) -> ElaborationResult:
        """Elaborate a function AST with decorators into proof artifacts.

        Args:
            func_ast: The AST node for the function definition.
            decorators: Optional list of decorators. If None, uses
                        func_ast.decorator_list.

        Returns:
            An ElaborationResult with proof sites, obligations, and transports.
        """
        func_name = func_ast.name
        raw_decorators = decorators if decorators is not None else func_ast.decorator_list

        # Parse decorators
        parsed: List[ParsedDecorator] = []
        for dec_node in raw_decorators:
            if isinstance(dec_node, ast.expr):
                parsed.append(_parse_decorator_node(dec_node))
            elif isinstance(dec_node, ParsedDecorator):
                parsed.append(dec_node)
            elif isinstance(dec_node, str):
                kind = _classify_decorator(dec_node)
                parsed.append(ParsedDecorator(_kind=kind, _name=dec_node))

        # Extract function metadata
        params = _extract_function_params(func_ast)
        return_ann = _extract_return_annotation(func_ast)
        asserts = _find_assert_statements(func_ast.body)
        loops = _find_loops(func_ast.body)
        is_recursive = _has_recursive_calls(func_ast)

        # Build proof sites, obligations, transport maps
        proof_sites: List[SiteId] = []
        obligations: List[ProofObligation] = []
        transport_maps: List[ConcreteMorphism] = []
        warnings: List[str] = []

        # Create argument boundary sites
        for param_name, param_ann in params:
            if param_name == "self":
                continue
            arg_site = _make_argument_site_id(func_name, param_name)
            proof_sites.append(arg_site)

        # Create return boundary site
        ret_site = _make_return_site_id(func_name)
        proof_sites.append(ret_site)

        # Process each decorator
        for dec in parsed:
            site_idx = self._next_site_index()
            site_id = _make_proof_site_id(func_name, dec.kind, site_idx)
            proof_sites.append(site_id)

            if dec.kind == DecoratorKind.REQUIRES:
                obl = _build_requires_obligation(
                    func_name, dec, site_id, params
                )
                obligations.append(obl)

            elif dec.kind == DecoratorKind.ENSURES:
                obl = _build_ensures_obligation(
                    func_name, dec, site_id, params, return_ann
                )
                obligations.append(obl)

            elif dec.kind == DecoratorKind.INVARIANT:
                obl = _build_invariant_obligation(func_name, dec, site_id)
                obligations.append(obl)

            elif dec.kind == DecoratorKind.THEOREM:
                obl = _build_theorem_obligation(func_name, dec, site_id)
                obligations.append(obl)

            elif dec.kind == DecoratorKind.LEMMA:
                obl = _build_lemma_obligation(func_name, dec, site_id)
                obligations.append(obl)

            elif dec.kind == DecoratorKind.DECREASES:
                obl = _build_decreases_obligation(func_name, dec, site_id)
                obligations.append(obl)

            elif dec.kind == DecoratorKind.TRANSPORT:
                # Transport produces morphisms, not simple obligations
                src_site = proof_sites[0] if proof_sites else site_id
                tgt_site = ret_site
                morphism = _build_transport_morphism(
                    func_name, dec, src_site, tgt_site
                )
                transport_maps.append(morphism)

            elif dec.kind == DecoratorKind.PURE:
                obl = ProofObligation(
                    prop=("pure", func_name),
                    site_id=site_id,
                    context={"kind": "purity", "function": func_name},
                    status=ObligationStatus.GENERATED,
                    source_location=f"line {dec.source_line}",
                )
                obligations.append(obl)

            elif dec.kind == DecoratorKind.TOTAL:
                obl = ProofObligation(
                    prop=("total", func_name),
                    site_id=site_id,
                    context={"kind": "totality", "function": func_name},
                    status=ObligationStatus.GENERATED,
                    source_location=f"line {dec.source_line}",
                )
                obligations.append(obl)

            elif dec.kind == DecoratorKind.UNKNOWN:
                if self._strict_mode:
                    warnings.append(
                        f"Unknown decorator @{dec.name} at line {dec.source_line}"
                    )

        # Generate obligations from assert statements
        for i, assert_node in enumerate(asserts):
            assert_site = SiteId(
                kind=SiteKind.PROOF,
                name=f"{func_name}.assert_{i}",
            )
            proof_sites.append(assert_site)
            obl = ProofObligation(
                prop=("assert", ast.dump(assert_node.test), func_name),
                site_id=assert_site,
                context={
                    "kind": "assertion",
                    "function": func_name,
                    "line": getattr(assert_node, "lineno", 0),
                },
                status=ObligationStatus.GENERATED,
                source_location=f"line {getattr(assert_node, 'lineno', 0)}",
            )
            obligations.append(obl)

        # Generate loop invariant obligations
        for i, loop_node in enumerate(loops):
            loop_site = SiteId(
                kind=SiteKind.LOOP_HEADER_INVARIANT,
                name=f"{func_name}.loop_{i}",
            )
            proof_sites.append(loop_site)
            if is_recursive:
                obl = ProofObligation(
                    prop=("loop_variant", f"loop_{i}", func_name),
                    site_id=loop_site,
                    context={
                        "kind": "loop_variant",
                        "function": func_name,
                        "loop_index": i,
                    },
                    status=ObligationStatus.GENERATED,
                )
                obligations.append(obl)

        # Build proof context with assumptions from @requires
        context = ProofContext()
        context.push_scope()
        for dec in parsed:
            if dec.kind == DecoratorKind.REQUIRES and dec.args:
                context.push_scope({"precondition": dec.args[0]})

        # Infer annotation level
        ann_level = _infer_annotation_level(
            parsed,
            has_assertions=len(asserts) > 0,
            has_loop_invariants=len(loops) > 0,
        )

        return ElaborationResult(
            _proof_sites=tuple(proof_sites),
            _obligations=tuple(obligations),
            _transport_maps=tuple(transport_maps),
            _annotation_level=ann_level,
            _context=context,
            _function_name=func_name,
            _warnings=tuple(warnings),
        )

    def elaborate_source(self, source: str) -> List[ElaborationResult]:
        """Elaborate all functions in a source string.

        Args:
            source: Python source code string.

        Returns:
            A list of ElaborationResult, one per function definition.
        """
        try:
            tree = ast.parse(source)
        except SyntaxError as exc:
            logger.warning("Failed to parse source: %s", exc)
            return []
        results: List[ElaborationResult] = []
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                result = self.elaborate(node)
                results.append(result)
        return results

    def elaborate_module(self, module_ast: ast.Module) -> List[ElaborationResult]:
        """Elaborate all function definitions in a module AST.

        Args:
            module_ast: The module AST.

        Returns:
            A list of ElaborationResult, one per function definition.
        """
        results: List[ElaborationResult] = []
        for node in ast.iter_child_nodes(module_ast):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                results.append(self.elaborate(node))
            elif isinstance(node, ast.ClassDef):
                for child in ast.iter_child_nodes(node):
                    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        results.append(self.elaborate(child))
        return results

    def create_concrete_sites(
        self, result: ElaborationResult
    ) -> List[ConcreteSite]:
        """Create ConcreteSite objects from elaboration proof sites."""
        sites: List[ConcreteSite] = []
        for site_id in result.proof_sites:
            site = ConcreteSite(
                _site_id=site_id,
                _carrier_schema=None,
                _metadata={"function": result.function_name},
            )
            sites.append(site)
        return sites

    def build_cover(self, result: ElaborationResult) -> Cover:
        """Build a Cover from an elaboration result.

        Creates sites and morphisms connecting argument boundaries
        to proof obligation sites and the return boundary.
        """
        sites_dict: Dict[SiteId, ConcreteSite] = {}
        morphisms: List[ConcreteMorphism] = []
        overlaps: List[Tuple[SiteId, SiteId]] = []

        # Create all sites
        for site_id in result.proof_sites:
            sites_dict[site_id] = ConcreteSite(
                _site_id=site_id,
                _metadata={"function": result.function_name},
            )

        # Create morphisms: each obligation site connects to relevant boundaries
        arg_sites = [
            sid for sid in result.proof_sites
            if sid.kind == SiteKind.ARGUMENT_BOUNDARY
        ]
        ret_sites = [
            sid for sid in result.proof_sites
            if sid.kind == SiteKind.RETURN_OUTPUT_BOUNDARY
        ]
        proof_site_ids = [
            sid for sid in result.proof_sites if sid.kind == SiteKind.PROOF
        ]

        for proof_sid in proof_site_ids:
            for arg_sid in arg_sites:
                morphisms.append(ConcreteMorphism(
                    _source=arg_sid, _target=proof_sid
                ))
            for ret_sid in ret_sites:
                morphisms.append(ConcreteMorphism(
                    _source=proof_sid, _target=ret_sid
                ))

        # Add transport morphisms
        morphisms.extend(result.transport_maps)

        # Overlaps between proof sites
        for i in range(len(proof_site_ids)):
            for j in range(i + 1, len(proof_site_ids)):
                overlaps.append((proof_site_ids[i], proof_site_ids[j]))

        input_boundary = {sid for sid in arg_sites}
        output_boundary = {sid for sid in ret_sites}

        return Cover(
            sites=sites_dict,  # type: ignore
            morphisms=morphisms,
            overlaps=overlaps,
            input_boundary=input_boundary,
            output_boundary=output_boundary,
        )

    def statistics(self) -> Dict[str, int]:
        """Return elaboration statistics."""
        return {"sites_created": self._site_counter}
