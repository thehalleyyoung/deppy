"""Transport compiler: compile @transport declarations into transport maps.

When a user writes @transport(eq_proof, f), this module compiles it into
a ConcreteMorphism that transports refinements along an equality proof.
Transport is the type-theoretic operation that moves values and proofs
along equality paths: given a proof of A = B, any value of type A can
be transported to type B.
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
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteSite, ConcreteMorphism
from deppy.types.base import TypeBase, AnyType, ANY_TYPE
from deppy.types.refinement import RefinementType
from deppy.types.witnesses import (
    ProofTerm,
    ReflProof,
    TransitivityProof,
    SymmetryProof,
    CongruenceProof,
    TransportWitness,
    WitnessCarrier,
)

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Transport kind
# ---------------------------------------------------------------------------


class TransportKind(enum.Enum):
    """The kind of transport being compiled."""

    EQUALITY = "equality"
    SUBTYPE = "subtype"
    COERCION = "coercion"
    REFINEMENT = "refinement"
    FUNCTORIAL = "functorial"
    IDENTITY = "identity"


# ---------------------------------------------------------------------------
# Transport declaration
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TransportDeclaration:
    """A parsed @transport declaration.

    Attributes:
        _eq_proof_name: Name of the equality proof to transport along.
        _target_func: Name of the target function.
        _source_type: The source type (if known).
        _target_type: The target type (if known).
        _transport_kind: The kind of transport.
        _source_line: Source line number.
        _context: Additional context from the declaration.
    """

    _eq_proof_name: str
    _target_func: str = ""
    _source_type: Optional[TypeBase] = None
    _target_type: Optional[TypeBase] = None
    _transport_kind: TransportKind = TransportKind.EQUALITY
    _source_line: int = 0
    _context: Dict[str, Any] = field(default_factory=dict)

    @property
    def eq_proof_name(self) -> str:
        return self._eq_proof_name

    @property
    def target_func(self) -> str:
        return self._target_func

    @property
    def source_type(self) -> Optional[TypeBase]:
        return self._source_type

    @property
    def target_type(self) -> Optional[TypeBase]:
        return self._target_type

    @property
    def transport_kind(self) -> TransportKind:
        return self._transport_kind

    @property
    def source_line(self) -> int:
        return self._source_line

    def __repr__(self) -> str:
        return (
            f"TransportDeclaration({self._eq_proof_name!r} -> "
            f"{self._target_func!r}, kind={self._transport_kind.value})"
        )


# ---------------------------------------------------------------------------
# Compilation result
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TransportCompilationResult:
    """Result of compiling a transport declaration.

    Attributes:
        _morphisms: The generated concrete morphisms.
        _witnesses: Transport witnesses created during compilation.
        _sites_created: Any new sites created for intermediate steps.
        _warnings: Non-fatal warnings.
        _transport_kind: The kind of transport compiled.
    """

    _morphisms: Tuple[ConcreteMorphism, ...]
    _witnesses: Tuple[TransportWitness, ...] = ()
    _sites_created: Tuple[SiteId, ...] = ()
    _warnings: Tuple[str, ...] = ()
    _transport_kind: TransportKind = TransportKind.EQUALITY

    @property
    def morphisms(self) -> List[ConcreteMorphism]:
        return list(self._morphisms)

    @property
    def witnesses(self) -> List[TransportWitness]:
        return list(self._witnesses)

    @property
    def sites_created(self) -> List[SiteId]:
        return list(self._sites_created)

    @property
    def warnings(self) -> List[str]:
        return list(self._warnings)

    @property
    def is_identity(self) -> bool:
        return self._transport_kind == TransportKind.IDENTITY

    def __repr__(self) -> str:
        return (
            f"TransportCompilationResult(morphisms={len(self._morphisms)}, "
            f"kind={self._transport_kind.value})"
        )


# ---------------------------------------------------------------------------
# Refinement projection builder
# ---------------------------------------------------------------------------


def _build_refinement_projection(
    source_refinements: Dict[str, Any],
    target_refinements: Dict[str, Any],
    eq_proof_name: str,
) -> Dict[str, str]:
    """Build a projection mapping for refinement transport.

    Maps target refinement keys to source refinement keys, accounting
    for the equality proof that justifies the transport.
    """
    projection: Dict[str, str] = {}
    for tgt_key in target_refinements:
        if tgt_key in source_refinements:
            projection[tgt_key] = tgt_key
        else:
            # Try to find a matching key via the equality proof
            for src_key in source_refinements:
                if _refinements_compatible(
                    source_refinements[src_key],
                    target_refinements[tgt_key],
                    eq_proof_name,
                ):
                    projection[tgt_key] = src_key
                    break
    return projection


def _refinements_compatible(
    source_ref: Any, target_ref: Any, eq_proof_name: str
) -> bool:
    """Check if two refinement values are compatible under transport.

    Two refinements are compatible if they are equal, or if the equality
    proof establishes a relationship between them.
    """
    if source_ref == target_ref:
        return True
    if isinstance(source_ref, TypeBase) and isinstance(target_ref, TypeBase):
        if source_ref == target_ref:
            return True
    # If the refinements are strings (predicate descriptions), check
    # if they differ only by the transported variable
    if isinstance(source_ref, str) and isinstance(target_ref, str):
        if source_ref.replace("source", "target") == target_ref:
            return True
        if source_ref.replace("target", "source") == target_ref:
            return True
    return False


# ---------------------------------------------------------------------------
# Transport morphism factory
# ---------------------------------------------------------------------------


def _make_transport_site(
    func_name: str, proof_name: str, direction: str, index: int
) -> SiteId:
    """Create a site ID for a transport intermediate."""
    return SiteId(
        kind=SiteKind.PROOF,
        name=f"{func_name}.transport_{proof_name}_{direction}_{index}",
    )


def _build_identity_morphism(site_id: SiteId) -> ConcreteMorphism:
    """Build an identity morphism (transport along refl)."""
    return ConcreteMorphism(
        _source=site_id,
        _target=site_id,
        projection=None,
        _metadata={"transport_kind": "identity"},
    )


def _build_equality_transport_morphism(
    source_site: SiteId,
    target_site: SiteId,
    eq_proof_name: str,
    target_func: str,
    projection: Optional[Dict[str, str]] = None,
) -> ConcreteMorphism:
    """Build a morphism that transports refinements along an equality proof."""
    metadata: Dict[str, Any] = {
        "transport_kind": "equality",
        "eq_proof": eq_proof_name,
        "target_func": target_func,
    }
    return ConcreteMorphism(
        _source=source_site,
        _target=target_site,
        projection=projection,
        _metadata=metadata,
    )


def _build_subtype_transport_morphism(
    source_site: SiteId,
    target_site: SiteId,
    source_type: TypeBase,
    target_type: TypeBase,
) -> ConcreteMorphism:
    """Build a morphism for subtype transport (coercion)."""
    metadata: Dict[str, Any] = {
        "transport_kind": "subtype",
        "source_type": repr(source_type),
        "target_type": repr(target_type),
    }
    return ConcreteMorphism(
        _source=source_site,
        _target=target_site,
        projection=None,
        _metadata=metadata,
    )


def _build_functorial_transport_morphism(
    source_site: SiteId,
    target_site: SiteId,
    functor_name: str,
    inner_proof: str,
) -> ConcreteMorphism:
    """Build a morphism for functorial transport (map under a type constructor)."""
    metadata: Dict[str, Any] = {
        "transport_kind": "functorial",
        "functor": functor_name,
        "inner_proof": inner_proof,
    }
    return ConcreteMorphism(
        _source=source_site,
        _target=target_site,
        projection=None,
        _metadata=metadata,
    )


def _build_refinement_transport_morphism(
    source_site: SiteId,
    target_site: SiteId,
    eq_proof_name: str,
    source_refs: Dict[str, Any],
    target_refs: Dict[str, Any],
) -> ConcreteMorphism:
    """Build a morphism that transports refinement predicates."""
    projection = _build_refinement_projection(
        source_refs, target_refs, eq_proof_name
    )
    metadata: Dict[str, Any] = {
        "transport_kind": "refinement",
        "eq_proof": eq_proof_name,
    }
    return ConcreteMorphism(
        _source=source_site,
        _target=target_site,
        projection=projection,
        _metadata=metadata,
    )


# ---------------------------------------------------------------------------
# Transport witness factory
# ---------------------------------------------------------------------------


def _build_transport_witness(
    source_type: TypeBase,
    target_type: TypeBase,
    eq_proof: ProofTerm,
) -> TransportWitness:
    """Build a TransportWitness from an equality proof."""
    return TransportWitness(
        source_type=source_type,
        target_type=target_type,
        path=eq_proof,
    )


def _build_composed_transport_witness(
    witnesses: List[TransportWitness],
) -> TransportWitness:
    """Compose multiple transport witnesses in sequence."""
    if not witnesses:
        return TransportWitness(
            source_type=ANY_TYPE, target_type=ANY_TYPE, path=ReflProof()
        )
    result = witnesses[0]
    for w in witnesses[1:]:
        result = result.compose(w)
    return result


def _build_reverse_transport_witness(
    witness: TransportWitness,
) -> TransportWitness:
    """Build the reverse of a transport witness."""
    return witness.reverse()


# ---------------------------------------------------------------------------
# Transport compiler
# ---------------------------------------------------------------------------


class TransportCompiler:
    """Compile @transport declarations into transport maps (morphisms).

    When a user writes @transport(eq_proof, f), this compiler:
    1. Resolves the equality proof reference
    2. Determines source and target types
    3. Builds morphisms that transport refinements
    4. Creates transport witnesses for proof tracking

    Attributes:
        _site_counter: Counter for unique site generation.
        _known_proofs: Registry of known equality proofs.
        _known_types: Registry of known type bindings.
        _compiled_transports: Cache of previously compiled transports.
    """

    def __init__(self) -> None:
        self._site_counter: int = 0
        self._known_proofs: Dict[str, ProofTerm] = {}
        self._known_types: Dict[str, TypeBase] = {}
        self._compiled_transports: Dict[str, TransportCompilationResult] = {}

    def _next_site_index(self) -> int:
        idx = self._site_counter
        self._site_counter += 1
        return idx

    def register_proof(self, name: str, proof: ProofTerm) -> None:
        """Register a known equality proof by name."""
        self._known_proofs[name] = proof

    def register_type(self, name: str, type_base: TypeBase) -> None:
        """Register a known type binding by name."""
        self._known_types[name] = type_base

    # -- Main entry point --------------------------------------------------

    def compile(
        self, transport_decl: TransportDeclaration
    ) -> TransportCompilationResult:
        """Compile a transport declaration into morphisms and witnesses.

        Args:
            transport_decl: The parsed transport declaration.

        Returns:
            A TransportCompilationResult with morphisms and witnesses.
        """
        cache_key = f"{transport_decl.eq_proof_name}:{transport_decl.target_func}"
        if cache_key in self._compiled_transports:
            return self._compiled_transports[cache_key]

        kind = transport_decl.transport_kind

        if kind == TransportKind.IDENTITY:
            result = self._compile_identity(transport_decl)
        elif kind == TransportKind.EQUALITY:
            result = self._compile_equality(transport_decl)
        elif kind == TransportKind.SUBTYPE:
            result = self._compile_subtype(transport_decl)
        elif kind == TransportKind.COERCION:
            result = self._compile_coercion(transport_decl)
        elif kind == TransportKind.REFINEMENT:
            result = self._compile_refinement(transport_decl)
        elif kind == TransportKind.FUNCTORIAL:
            result = self._compile_functorial(transport_decl)
        else:
            result = self._compile_equality(transport_decl)

        self._compiled_transports[cache_key] = result
        return result

    def compile_from_ast(
        self,
        decorator_node: ast.expr,
        func_name: str,
    ) -> TransportCompilationResult:
        """Compile a transport from an AST decorator node.

        Parses the @transport(eq_proof, f) decorator and compiles it.
        """
        decl = self._parse_transport_ast(decorator_node, func_name)
        return self.compile(decl)

    def compile_batch(
        self, declarations: List[TransportDeclaration]
    ) -> List[TransportCompilationResult]:
        """Compile multiple transport declarations."""
        return [self.compile(decl) for decl in declarations]

    # -- Compilation strategies --------------------------------------------

    def _compile_identity(
        self, decl: TransportDeclaration
    ) -> TransportCompilationResult:
        """Compile an identity transport (trivial, source = target)."""
        idx = self._next_site_index()
        site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.identity_{idx}",
        )
        morphism = _build_identity_morphism(site)
        witness: Optional[TransportWitness] = None
        if decl.source_type is not None:
            witness = TransportWitness(
                source_type=decl.source_type,
                target_type=decl.source_type,
                path=ReflProof(decl.source_type),
            )
        witnesses = (witness,) if witness is not None else ()
        return TransportCompilationResult(
            _morphisms=(morphism,),
            _witnesses=witnesses,
            _sites_created=(site,),
            _transport_kind=TransportKind.IDENTITY,
        )

    def _compile_equality(
        self, decl: TransportDeclaration
    ) -> TransportCompilationResult:
        """Compile an equality transport along an equality proof."""
        idx = self._next_site_index()
        source_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.eq_source_{decl.eq_proof_name}_{idx}",
        )
        target_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.eq_target_{decl.eq_proof_name}_{idx}",
        )

        # Resolve the equality proof
        eq_proof = self._known_proofs.get(decl.eq_proof_name)
        if eq_proof is None:
            eq_proof = ReflProof(decl.eq_proof_name)

        morphism = _build_equality_transport_morphism(
            source_site, target_site, decl.eq_proof_name, decl.target_func
        )

        witnesses: List[TransportWitness] = []
        if decl.source_type is not None and decl.target_type is not None:
            witnesses.append(
                _build_transport_witness(
                    decl.source_type, decl.target_type, eq_proof
                )
            )

        # Build reverse morphism for bidirectional transport
        reverse_morphism = _build_equality_transport_morphism(
            target_site, source_site, decl.eq_proof_name, decl.target_func
        )

        return TransportCompilationResult(
            _morphisms=(morphism, reverse_morphism),
            _witnesses=tuple(witnesses),
            _sites_created=(source_site, target_site),
            _transport_kind=TransportKind.EQUALITY,
        )

    def _compile_subtype(
        self, decl: TransportDeclaration
    ) -> TransportCompilationResult:
        """Compile a subtype transport (widening coercion)."""
        idx = self._next_site_index()
        source_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.sub_source_{idx}",
        )
        target_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.sub_target_{idx}",
        )

        source_type = decl.source_type or ANY_TYPE
        target_type = decl.target_type or ANY_TYPE

        morphism = _build_subtype_transport_morphism(
            source_site, target_site, source_type, target_type
        )

        witnesses: List[TransportWitness] = []
        if decl.source_type is not None and decl.target_type is not None:
            witnesses.append(TransportWitness(
                source_type=decl.source_type,
                target_type=decl.target_type,
                path=("subtype", repr(decl.source_type), repr(decl.target_type)),
            ))

        return TransportCompilationResult(
            _morphisms=(morphism,),
            _witnesses=tuple(witnesses),
            _sites_created=(source_site, target_site),
            _transport_kind=TransportKind.SUBTYPE,
        )

    def _compile_coercion(
        self, decl: TransportDeclaration
    ) -> TransportCompilationResult:
        """Compile a coercion transport (explicit type cast)."""
        idx = self._next_site_index()
        source_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.coerce_source_{idx}",
        )
        target_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.coerce_target_{idx}",
        )

        source_type = decl.source_type or ANY_TYPE
        target_type = decl.target_type or ANY_TYPE

        morphism = ConcreteMorphism(
            _source=source_site,
            _target=target_site,
            projection=None,
            _metadata={
                "transport_kind": "coercion",
                "source_type": repr(source_type),
                "target_type": repr(target_type),
            },
        )

        return TransportCompilationResult(
            _morphisms=(morphism,),
            _sites_created=(source_site, target_site),
            _transport_kind=TransportKind.COERCION,
        )

    def _compile_refinement(
        self, decl: TransportDeclaration
    ) -> TransportCompilationResult:
        """Compile a refinement transport (transport predicates)."""
        idx = self._next_site_index()
        source_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.ref_source_{idx}",
        )
        target_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.ref_target_{idx}",
        )

        source_refs: Dict[str, Any] = decl._context.get("source_refinements", {})
        target_refs: Dict[str, Any] = decl._context.get("target_refinements", {})

        morphism = _build_refinement_transport_morphism(
            source_site, target_site,
            decl.eq_proof_name, source_refs, target_refs
        )

        eq_proof = self._known_proofs.get(decl.eq_proof_name, ReflProof())
        witnesses: List[TransportWitness] = []
        if decl.source_type is not None and decl.target_type is not None:
            witnesses.append(
                _build_transport_witness(
                    decl.source_type, decl.target_type, eq_proof
                )
            )

        return TransportCompilationResult(
            _morphisms=(morphism,),
            _witnesses=tuple(witnesses),
            _sites_created=(source_site, target_site),
            _transport_kind=TransportKind.REFINEMENT,
        )

    def _compile_functorial(
        self, decl: TransportDeclaration
    ) -> TransportCompilationResult:
        """Compile a functorial transport (map under a type constructor).

        If we have a proof that A = B and a functor F, we can derive
        F(A) = F(B). This is compiled into a morphism that transports
        refinements within the functor.
        """
        idx = self._next_site_index()
        source_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.func_source_{idx}",
        )
        target_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.func_target_{idx}",
        )

        functor_name = decl._context.get("functor", "F")
        inner_proof = decl.eq_proof_name

        morphism = _build_functorial_transport_morphism(
            source_site, target_site, functor_name, inner_proof
        )

        eq_proof = self._known_proofs.get(inner_proof, ReflProof())
        witnesses: List[TransportWitness] = []
        if decl.source_type is not None and decl.target_type is not None:
            cong_proof = CongruenceProof(inner=eq_proof, function_name=functor_name)
            witnesses.append(
                _build_transport_witness(
                    decl.source_type, decl.target_type, cong_proof
                )
            )

        return TransportCompilationResult(
            _morphisms=(morphism,),
            _witnesses=tuple(witnesses),
            _sites_created=(source_site, target_site),
            _transport_kind=TransportKind.FUNCTORIAL,
        )

    # -- AST parsing -------------------------------------------------------

    def _parse_transport_ast(
        self, node: ast.expr, func_name: str
    ) -> TransportDeclaration:
        """Parse a @transport(...) AST node into a TransportDeclaration."""
        eq_proof_name = "eq"
        target_func = func_name
        transport_kind = TransportKind.EQUALITY
        context: Dict[str, Any] = {}

        if isinstance(node, ast.Call):
            if node.args:
                first = node.args[0]
                if isinstance(first, ast.Name):
                    eq_proof_name = first.id
                elif isinstance(first, ast.Constant) and isinstance(first.value, str):
                    eq_proof_name = first.value
            if len(node.args) > 1:
                second = node.args[1]
                if isinstance(second, ast.Name):
                    target_func = second.id
                elif isinstance(second, ast.Constant) and isinstance(second.value, str):
                    target_func = second.value
            for kw in node.keywords:
                if kw.arg == "kind":
                    if isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, str):
                        try:
                            transport_kind = TransportKind(kw.value.value)
                        except ValueError:
                            pass
                elif kw.arg == "functor":
                    if isinstance(kw.value, ast.Constant) and isinstance(kw.value.value, str):
                        context["functor"] = kw.value.value

        return TransportDeclaration(
            _eq_proof_name=eq_proof_name,
            _target_func=target_func,
            _transport_kind=transport_kind,
            _source_line=getattr(node, "lineno", 0),
            _context=context,
        )

    # -- High-level API ----------------------------------------------------

    def _build_transport_morphism(
        self,
        eq_proof: ProofTerm,
        target_func: str,
    ) -> ConcreteMorphism:
        """Build a single transport morphism from an equality proof and target.

        This is the core compilation step: given a proof that A = B and
        a function f, produce a morphism transporting refinements of A
        to refinements of B through f.
        """
        idx = self._next_site_index()
        source_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.direct_source_{idx}",
        )
        target_site = SiteId(
            kind=SiteKind.PROOF,
            name=f"transport.direct_target_{target_func}_{idx}",
        )

        proof_name = eq_proof.description() if hasattr(eq_proof, "description") else str(eq_proof)

        return _build_equality_transport_morphism(
            source_site, target_site, proof_name, target_func
        )

    def compile_chain(
        self, declarations: List[TransportDeclaration]
    ) -> TransportCompilationResult:
        """Compile a chain of transports into a single composed transport.

        Given transports A->B and B->C, produces A->C by composing
        the underlying morphisms and witnesses.
        """
        if not declarations:
            return TransportCompilationResult(
                _morphisms=(),
                _transport_kind=TransportKind.IDENTITY,
            )
        if len(declarations) == 1:
            return self.compile(declarations[0])

        all_morphisms: List[ConcreteMorphism] = []
        all_witnesses: List[TransportWitness] = []
        all_sites: List[SiteId] = []
        all_warnings: List[str] = []

        for decl in declarations:
            result = self.compile(decl)
            all_morphisms.extend(result.morphisms)
            all_witnesses.extend(result.witnesses)
            all_sites.extend(result.sites_created)
            all_warnings.extend(result.warnings)

        # Compose adjacent witnesses
        composed_witnesses: List[TransportWitness] = []
        if len(all_witnesses) >= 2:
            composed = _build_composed_transport_witness(all_witnesses)
            composed_witnesses.append(composed)
        else:
            composed_witnesses = all_witnesses

        return TransportCompilationResult(
            _morphisms=tuple(all_morphisms),
            _witnesses=tuple(composed_witnesses),
            _sites_created=tuple(all_sites),
            _warnings=tuple(all_warnings),
            _transport_kind=TransportKind.EQUALITY,
        )

    def statistics(self) -> Dict[str, int]:
        """Return compilation statistics."""
        return {
            "sites_created": self._site_counter,
            "known_proofs": len(self._known_proofs),
            "known_types": len(self._known_types),
            "cached_compilations": len(self._compiled_transports),
        }

    def clear_cache(self) -> None:
        """Clear the compilation cache."""
        self._compiled_transports.clear()
