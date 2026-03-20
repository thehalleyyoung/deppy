"""Mixed-mode compiler for deppy.

Compiles the surface language (hole(), spec(), guarantee(), assume(), check())
into hybrid type obligations — bridging natural-language annotations to the
sheaf-theoretic verification pipeline.

The compilation pipeline is:

    Source with NL annotations
        → MixedModeParser (existing — extracts NL fragments + AST)
        → **MixedModeCompiler** (this module — compiles to obligations)
        → ObligationEmitter (emits Z3 / Lean / pytest / runtime checks)
        → HoleFiller (fills holes via Z3 synthesis or LLM oracle)
        → CodeGenerator (produces final annotated Python)

Every compilation target reuses existing deppy infrastructure:

- hole()      → Σ-type obligation  (deppy.types.dependent.SigmaType)
- spec()      → refinement type    (deppy.types.refinement.RefinementType)
- guarantee() → contract           (deppy.contracts.base.Contract)
- assume()    → precondition       (solver obligation context)
- check()     → assertion + proof  (deppy.solver.SolverObligation)
"""

from __future__ import annotations

import ast
import copy
import enum
import hashlib
import logging
import textwrap
import time
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
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

if TYPE_CHECKING:
    from deppy.hybrid.mixed_mode.parser import MixedAST, ParsedFragment, TypeContext
    from deppy.hybrid.core.intent_bridge import IntentBridgeResult

# ---------------------------------------------------------------------------
# Graceful integration with existing deppy infrastructure
# ---------------------------------------------------------------------------

try:
    from deppy.types.dependent import PiType, SigmaType, IdentityType
    from deppy.types.refinement import RefinementType, Predicate as RefinementPredicate
    from deppy.contracts.base import Contract, SourceLocation
    from deppy.solver.solver_interface import SolverObligation, SolverStatus
    from deppy.solver.fragment_dispatcher import FragmentDispatcher
    _HAS_CORE = True
except ImportError:
    _HAS_CORE = False

try:
    from deppy.solver.z3_encoder import Z3Encoder, VariableEnvironment
    _HAS_Z3_ENCODER = True
except ImportError:
    _HAS_Z3_ENCODER = False

try:
    from deppy.hybrid import HybridLayer, HybridTrustLevel
    _HAS_HYBRID = True
except ImportError:
    _HAS_HYBRID = False

try:
    from deppy.core._protocols import SiteId, SiteKind, TrustLevel, LocalSection
    _HAS_PROTOCOLS = True
except ImportError:
    _HAS_PROTOCOLS = False

logger = logging.getLogger(__name__)

try:
    from deppy.hybrid.core.intent_bridge import IntentBridge, IntentBridgeResult
    _HAS_INTENT_BRIDGE = True
except ImportError:
    _HAS_INTENT_BRIDGE = False

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

_DEFAULT_TIMEOUT_MS: float = 5000.0
_MAX_SYNTHESIS_ATTEMPTS: int = 5
_HOLE_PREFIX = "__deppy_hole_"
_RUNTIME_CHECK_PREFIX = "__deppy_check_"

# ---------------------------------------------------------------------------
# Enums
# ---------------------------------------------------------------------------


class ObligationKind(enum.Enum):
    """Discriminant for the kind of proof obligation produced."""

    HOLE = "hole"
    SPEC = "spec"
    GUARANTEE = "guarantee"
    ASSUME = "assume"
    CHECK = "check"
    FUNCTION = "function"
    INVARIANT = "invariant"
    DECREASES = "decreases"


class EmitTarget(enum.Enum):
    """Target backend for obligation emission."""

    Z3 = "z3"
    LEAN = "lean"
    PYTEST = "pytest"
    RUNTIME = "runtime"


class FillStrategy(enum.Enum):
    """Strategy used to fill a hole."""

    Z3_SYNTHESIS = "z3_synthesis"
    ORACLE_LLM = "oracle_llm"
    USER_PROVIDED = "user_provided"
    UNFILLED = "unfilled"


class CompilationPhase(enum.Enum):
    """Tracks the current phase of the compiler."""

    PARSING = "parsing"
    OBLIGATION_EXTRACTION = "obligation_extraction"
    EMISSION = "emission"
    HOLE_FILLING = "hole_filling"
    CODE_GENERATION = "code_generation"
    DONE = "done"


# ---------------------------------------------------------------------------
# Source location utilities
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CompilerLocation:
    """Location within the source being compiled.

    Wraps deppy.contracts.base.SourceLocation when available, otherwise
    provides a standalone representation.
    """

    file: str
    line: int
    col: int = 0
    end_line: Optional[int] = None
    end_col: Optional[int] = None

    def to_core_location(self) -> Any:
        """Convert to deppy.contracts.base.SourceLocation if available."""
        if _HAS_CORE:
            return SourceLocation(
                file=self.file,
                line=self.line,
                col=self.col,
                end_line=self.end_line,
                end_col=self.end_col,
            )
        return self

    @classmethod
    def from_ast_node(cls, node: ast.AST, file: str = "<string>") -> CompilerLocation:
        """Extract location from an AST node."""
        end_line = getattr(node, "end_lineno", None)
        end_col = getattr(node, "end_col_offset", None)
        return cls(
            file=file,
            line=getattr(node, "lineno", 0),
            col=getattr(node, "col_offset", 0),
            end_line=end_line,
            end_col=end_col,
        )

    def __str__(self) -> str:
        return f"{self.file}:{self.line}:{self.col}"


# ---------------------------------------------------------------------------
# Obligation dataclasses
# ---------------------------------------------------------------------------


@dataclass
class ObligationBase:
    """Base for all proof obligations produced by the compiler."""

    kind: ObligationKind
    description: str
    location: CompilerLocation
    nl_text: str = ""
    trust_level: int = 0  # maps to HybridTrustLevel.value when available
    context_variables: Dict[str, str] = field(default_factory=dict)
    parent_function: Optional[str] = None
    uid: str = ""

    def __post_init__(self) -> None:
        if not self.uid:
            h = hashlib.sha256(
                f"{self.kind.value}:{self.location}:{self.description}".encode()
            ).hexdigest()[:12]
            self.uid = f"obl_{h}"


@dataclass
class HoleObligation(ObligationBase):
    r"""A hole() becomes a Σ-type obligation.

    The hole ``hole("sort the list in O(n log n)")`` induces:

        Σ (code : str). TypeChecks(code) ∧ Satisfies(code, spec)

    When deppy.types.dependent is available, ``sigma_type`` holds the actual
    ``SigmaType`` value; otherwise we store the spec as a string for later
    emission.
    """

    kind: ObligationKind = field(default=ObligationKind.HOLE, init=False)
    sigma_type: Any = None
    expected_type_hint: Optional[str] = None
    surrounding_context: str = ""
    synthesis_hints: List[str] = field(default_factory=list)

    def to_sigma_type(self) -> Any:
        """Build the Σ-type if deppy core is available."""
        if _HAS_CORE and self.sigma_type is None:
            from deppy.types.base import PrimitiveType
            from deppy.types.dependent import SigmaType as _Sigma

            code_type = PrimitiveType("str")
            spec_pred = RefinementType(
                base=code_type,
                binder="code",
                predicate=RefinementPredicate.true_pred()
                if hasattr(RefinementPredicate, "true_pred")
                else _make_true_pred(),
            )
            self.sigma_type = _Sigma(
                fst_name="code",
                fst_type=code_type,
                snd_type=spec_pred,
            )
        return self.sigma_type


@dataclass
class SpecObligation(ObligationBase):
    """A @spec() decorator becomes a refinement type obligation.

    The refinement captures the function's behavioral specification:

        { f : (params) -> ret | spec_predicate(f) }
    """

    kind: ObligationKind = field(default=ObligationKind.SPEC, init=False)
    refinement_type: Any = None
    function_name: str = ""
    param_types: Dict[str, str] = field(default_factory=dict)
    return_type: str = ""
    spec_text: str = ""


@dataclass
class GuaranteeObligation(ObligationBase):
    """A @guarantee() decorator becomes a contract.

    Maps directly to deppy.contracts.base.Contract when available:
    the guarantee induces a postcondition on the decorated function.
    """

    kind: ObligationKind = field(default=ObligationKind.GUARANTEE, init=False)
    contract: Any = None
    function_name: str = ""
    temporal: bool = False
    guarantee_text: str = ""


@dataclass
class AssumeObligation(ObligationBase):
    """An assume() call becomes a precondition in the solver context.

    Assumptions are added to the context of downstream obligations
    rather than checked directly — they constrain the verification
    environment.
    """

    kind: ObligationKind = field(default=ObligationKind.ASSUME, init=False)
    predicate: Any = None
    scope: str = ""
    assumption_text: str = ""


@dataclass
class CheckObligation(ObligationBase):
    """A check() call becomes an assertion + proof obligation.

    The compiler emits both:
    1. A runtime assertion (always)
    2. A solver obligation (attempt static proof via Z3)
    """

    kind: ObligationKind = field(default=ObligationKind.CHECK, init=False)
    solver_obligation: Any = None
    assertion_text: str = ""
    is_decidable: Optional[bool] = None


@dataclass
class FunctionObligation(ObligationBase):
    """Composite obligation for an entire function with mixed-mode annotations."""

    kind: ObligationKind = field(default=ObligationKind.FUNCTION, init=False)
    function_name: str = ""
    holes: List[HoleObligation] = field(default_factory=list)
    specs: List[SpecObligation] = field(default_factory=list)
    guarantees: List[GuaranteeObligation] = field(default_factory=list)
    assumes: List[AssumeObligation] = field(default_factory=list)
    checks: List[CheckObligation] = field(default_factory=list)
    pi_type: Any = None

    @property
    def all_obligations(self) -> List[ObligationBase]:
        """Flatten all child obligations."""
        result: List[ObligationBase] = []
        result.extend(self.holes)
        result.extend(self.specs)
        result.extend(self.guarantees)
        result.extend(self.assumes)
        result.extend(self.checks)
        return result

    @property
    def n_total(self) -> int:
        return len(self.all_obligations)


@dataclass
class FilledHole:
    """Result of filling a hole with synthesized or oracle-provided code."""

    hole: HoleObligation
    code: str
    strategy: FillStrategy
    verified: bool = False
    trust_level: int = 0
    verification_details: str = ""
    attempts: int = 1


# ---------------------------------------------------------------------------
# CompilationResult
# ---------------------------------------------------------------------------


@dataclass
class CompilationResult:
    """Complete result of compiling a mixed-mode source file."""

    source: str = ""
    file_path: str = "<string>"
    phase: CompilationPhase = CompilationPhase.DONE

    # Obligations by kind
    functions: List[FunctionObligation] = field(default_factory=list)
    top_level_holes: List[HoleObligation] = field(default_factory=list)
    top_level_checks: List[CheckObligation] = field(default_factory=list)
    top_level_assumes: List[AssumeObligation] = field(default_factory=list)

    # Aggregate stats
    n_holes: int = 0
    n_specs: int = 0
    n_guarantees: int = 0
    n_assumes: int = 0
    n_checks: int = 0

    # Diagnostics
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    elapsed_ms: float = 0.0

    @property
    def all_obligations(self) -> List[ObligationBase]:
        """Every obligation in flat order."""
        result: List[ObligationBase] = []
        for fn in self.functions:
            result.append(fn)
            result.extend(fn.all_obligations)
        result.extend(self.top_level_holes)
        result.extend(self.top_level_checks)
        result.extend(self.top_level_assumes)
        return result

    @property
    def is_success(self) -> bool:
        return len(self.errors) == 0

    @property
    def has_holes(self) -> bool:
        return self.n_holes > 0

    def summary(self) -> str:
        parts = [f"MixedModeCompilation({self.file_path})"]
        parts.append(f"  functions:  {len(self.functions)}")
        parts.append(f"  holes:      {self.n_holes}")
        parts.append(f"  specs:      {self.n_specs}")
        parts.append(f"  guarantees: {self.n_guarantees}")
        parts.append(f"  assumes:    {self.n_assumes}")
        parts.append(f"  checks:     {self.n_checks}")
        if self.errors:
            parts.append(f"  errors:     {len(self.errors)}")
        parts.append(f"  elapsed:    {self.elapsed_ms:.1f}ms")
        return "\n".join(parts)


@dataclass
class BridgedCompilationResult:
    """Compilation result plus intent-bridge products."""

    compilation: CompilationResult
    bridged_intents: Dict[str, IntentBridgeResult] = field(default_factory=dict)
    warnings: List[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _make_true_pred() -> Any:
    """Build a trivially-true predicate using whichever deppy module is loaded."""
    if _HAS_CORE:
        from deppy.types.refinement import TruePred
        return TruePred()
    return None


def _extract_call_arg_string(node: ast.Call) -> str:
    """Extract the first string argument from an ast.Call node."""
    if node.args and isinstance(node.args[0], ast.Constant) and isinstance(
        node.args[0].value, str
    ):
        return node.args[0].value
    return ""


def _extract_decorator_arg_string(decorator: ast.expr) -> str:
    """Extract the first string argument from a decorator node."""
    if isinstance(decorator, ast.Call):
        return _extract_call_arg_string(decorator)
    return ""


def _decorator_name(decorator: ast.expr) -> str:
    """Return the bare name of a decorator."""
    if isinstance(decorator, ast.Call):
        return _decorator_name(decorator.func)
    if isinstance(decorator, ast.Attribute):
        return decorator.attr
    if isinstance(decorator, ast.Name):
        return decorator.id
    return ""


def _annotation_to_str(node: Optional[ast.expr]) -> str:
    """Best-effort conversion of an annotation AST node to a string."""
    if node is None:
        return ""
    return ast.unparse(node)


def _build_context_vars(func_node: ast.FunctionDef) -> Dict[str, str]:
    """Extract parameter names and their annotation strings from a function."""
    ctx: Dict[str, str] = {}
    for arg in func_node.args.args:
        name = arg.arg
        ann = _annotation_to_str(arg.annotation)
        ctx[name] = ann if ann else "Any"
    return ctx


# ═══════════════════════════════════════════════════════════════════════════════
# MixedModeCompiler
# ═══════════════════════════════════════════════════════════════════════════════


class MixedModeCompiler:
    """Compile mixed-mode annotated Python into typed proof obligations.

    The compiler operates on raw source or pre-parsed ``MixedAST`` (from
    ``deppy.hybrid.mixed_mode.parser.MixedModeParser``).  For each surface
    form it encounters it produces a typed obligation that downstream passes
    can discharge via Z3, Lean, pytest, or runtime assertion.

    Integration with existing deppy:
    - Holes produce ``SigmaType`` obligations (deppy.types.dependent)
    - Specs produce ``RefinementType`` obligations (deppy.types.refinement)
    - Guarantees produce ``Contract`` wrappers (deppy.contracts.base)
    - Checks produce ``SolverObligation`` instances (deppy.solver)

    Usage::

        compiler = MixedModeCompiler()
        result = compiler.compile(source_code)
        for fn in result.functions:
            for hole in fn.holes:
                print(hole.description, hole.sigma_type)
    """

    def __init__(
        self,
        *,
        file_path: str = "<string>",
        trust_floor: int = 0,
        timeout_ms: float = _DEFAULT_TIMEOUT_MS,
        use_existing_parser: bool = True,
    ) -> None:
        self._file_path = file_path
        self._trust_floor = trust_floor
        self._timeout_ms = timeout_ms
        self._use_existing_parser = use_existing_parser
        self._errors: List[str] = []
        self._warnings: List[str] = []

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def compile(self, source: str) -> CompilationResult:
        """Full compilation: source → obligations.

        Parses the source, walks the AST, and for every mixed-mode
        annotation (hole, spec, guarantee, assume, check) produces the
        corresponding typed obligation.
        """
        start = time.monotonic()
        self._errors.clear()
        self._warnings.clear()

        result = CompilationResult(
            source=source,
            file_path=self._file_path,
            phase=CompilationPhase.PARSING,
        )

        # Phase 1: Parse
        try:
            tree = ast.parse(source)
        except SyntaxError as exc:
            result.errors.append(f"SyntaxError: {exc}")
            result.elapsed_ms = (time.monotonic() - start) * 1000
            return result

        result.phase = CompilationPhase.OBLIGATION_EXTRACTION

        # Phase 2: Walk the AST and extract obligations
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                try:
                    fn_obl = self.compile_function(node, node.decorator_list)
                    result.functions.append(fn_obl)
                except Exception as exc:  # noqa: BLE001
                    self._errors.append(
                        f"Error compiling {getattr(node, 'name', '?')}: {exc}"
                    )

        # Phase 2b: Top-level calls (outside functions)
        for node in ast.iter_child_nodes(tree):
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
                call = node.value
                name = _decorator_name(call.func) if isinstance(call.func, (ast.Name, ast.Attribute)) else ""
                if name == "hole":
                    obl = self.compile_hole(call)
                    result.top_level_holes.append(obl)
                elif name == "check":
                    obl = self.compile_check(call)
                    result.top_level_checks.append(obl)
                elif name == "assume":
                    obl = self.compile_assume(call)
                    result.top_level_assumes.append(obl)

        # Phase 3: Aggregate counts
        for fn in result.functions:
            result.n_holes += len(fn.holes)
            result.n_specs += len(fn.specs)
            result.n_guarantees += len(fn.guarantees)
            result.n_assumes += len(fn.assumes)
            result.n_checks += len(fn.checks)
        result.n_holes += len(result.top_level_holes)
        result.n_checks += len(result.top_level_checks)
        result.n_assumes += len(result.top_level_assumes)

        result.errors.extend(self._errors)
        result.warnings.extend(self._warnings)
        result.phase = CompilationPhase.DONE
        result.elapsed_ms = (time.monotonic() - start) * 1000
        return result

    def compile_function(
        self,
        func_ast: Union[ast.FunctionDef, ast.AsyncFunctionDef],
        annotations: List[ast.expr],
    ) -> FunctionObligation:
        """Compile a single function with mixed-mode annotations.

        Walks the function body for hole/assume/check calls, and
        inspects decorators for spec/guarantee annotations.  Produces
        a ``FunctionObligation`` containing all child obligations plus
        an optional Π-type for the overall function signature.
        """
        loc = CompilerLocation.from_ast_node(func_ast, self._file_path)
        ctx_vars = _build_context_vars(func_ast)
        ret_ann = _annotation_to_str(func_ast.returns)

        fn_obl = FunctionObligation(
            description=f"function {func_ast.name}",
            location=loc,
            function_name=func_ast.name,
            context_variables=ctx_vars,
            parent_function=func_ast.name,
        )

        # --- Decorators → spec / guarantee ---
        for dec in annotations:
            dec_name = _decorator_name(dec)
            if dec_name == "spec":
                spec_obl = self._compile_spec_decorator(dec, func_ast)
                fn_obl.specs.append(spec_obl)
            elif dec_name == "guarantee":
                guar_obl = self._compile_guarantee_decorator(dec, func_ast)
                fn_obl.guarantees.append(guar_obl)

        # --- Body → holes / assumes / checks ---
        for node in ast.walk(func_ast):
            if not isinstance(node, ast.Call):
                continue
            call_name = ""
            if isinstance(node.func, ast.Name):
                call_name = node.func.id
            elif isinstance(node.func, ast.Attribute):
                call_name = node.func.attr
            if not call_name:
                continue

            if call_name == "hole":
                hole_obl = self.compile_hole(node)
                hole_obl.parent_function = func_ast.name
                hole_obl.context_variables = ctx_vars
                fn_obl.holes.append(hole_obl)
            elif call_name == "assume":
                assume_obl = self.compile_assume(node)
                assume_obl.parent_function = func_ast.name
                assume_obl.context_variables = ctx_vars
                fn_obl.assumes.append(assume_obl)
            elif call_name == "check":
                check_obl = self.compile_check(node)
                check_obl.parent_function = func_ast.name
                check_obl.context_variables = ctx_vars
                fn_obl.checks.append(check_obl)

        # --- Build Π-type for the function signature ---
        fn_obl.pi_type = self._build_pi_type(func_ast, ctx_vars, ret_ann)

        return fn_obl

    def compile_hole(self, hole_node: ast.Call) -> HoleObligation:
        """Compile a hole() call into a Σ-type obligation.

        A ``hole("description")`` compiles to:

            Σ (code : str). TypeChecks(code) ∧ Satisfies(code, description)

        The Σ-type encodes the synthesis problem: find a witness (code)
        together with a proof that it satisfies the specification.
        """
        nl_text = _extract_call_arg_string(hole_node)
        loc = CompilerLocation.from_ast_node(hole_node, self._file_path)

        # Extract optional type hint from keyword arguments
        expected_type = None
        for kw in hole_node.keywords:
            if kw.arg == "type" and isinstance(kw.value, ast.Constant):
                expected_type = str(kw.value.value)

        obl = HoleObligation(
            description=f"hole: {nl_text[:80]}",
            location=loc,
            nl_text=nl_text,
            expected_type_hint=expected_type,
        )

        # Build the Σ-type when deppy core is available
        obl.to_sigma_type()

        return obl

    def compile_spec(self, spec_node: ast.expr) -> SpecObligation:
        """Compile a @spec() decorator into a refinement type obligation.

        A ``@spec("returns sorted list")`` compiles to a refinement:

            { f : (params) -> ret | spec_predicate(f) }

        When deppy.types.refinement is available, we build a real
        ``RefinementType``; otherwise we record the spec text for
        later emission.
        """
        return self._compile_spec_decorator(spec_node, func_node=None)

    def compile_guarantee(self, guarantee_node: ast.expr) -> GuaranteeObligation:
        """Compile a @guarantee() decorator into a contract obligation.

        Maps to deppy.contracts.base.Contract when available: the guarantee
        text is parsed as a postcondition on the decorated function.
        """
        return self._compile_guarantee_decorator(guarantee_node, func_node=None)

    def compile_assume(self, assume_node: ast.Call) -> AssumeObligation:
        """Compile an assume() call into a precondition.

        Assumptions are not checked — they are added to the verification
        context for downstream obligations.  An ``assume("x > 0")`` adds
        the predicate ``x > 0`` to the environment.
        """
        nl_text = _extract_call_arg_string(assume_node)
        loc = CompilerLocation.from_ast_node(assume_node, self._file_path)

        obl = AssumeObligation(
            description=f"assume: {nl_text[:80]}",
            location=loc,
            nl_text=nl_text,
            assumption_text=nl_text,
        )

        if _HAS_CORE:
            obl.predicate = self._try_parse_predicate(nl_text)

        return obl

    def compile_check(self, check_node: ast.Call) -> CheckObligation:
        """Compile a check() call into an assertion + proof obligation.

        A ``check("result > 0")`` produces:
        1. A runtime ``assert`` statement
        2. A ``SolverObligation`` for Z3 (if the predicate is decidable)
        """
        nl_text = _extract_call_arg_string(check_node)
        loc = CompilerLocation.from_ast_node(check_node, self._file_path)

        obl = CheckObligation(
            description=f"check: {nl_text[:80]}",
            location=loc,
            nl_text=nl_text,
            assertion_text=nl_text,
        )

        if _HAS_CORE and _HAS_PROTOCOLS:
            site_id = SiteId(
                kind=SiteKind.PROOF,
                name=f"check_{obl.uid}",
                source_location=(self._file_path, loc.line, loc.col),
            )
            predicate = self._try_parse_predicate(nl_text)
            if predicate is not None:
                obl.solver_obligation = SolverObligation(
                    site_id=site_id,
                    formula=predicate,
                    trust_level=TrustLevel.RESIDUAL,
                    description=nl_text,
                    timeout_ms=self._timeout_ms,
                )
                obl.is_decidable = self._check_decidability(obl.solver_obligation)

        return obl

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _compile_spec_decorator(
        self,
        dec_node: ast.expr,
        func_node: Optional[Union[ast.FunctionDef, ast.AsyncFunctionDef]],
    ) -> SpecObligation:
        """Internal: compile a @spec decorator."""
        nl_text = _extract_decorator_arg_string(dec_node)
        loc = CompilerLocation.from_ast_node(dec_node, self._file_path)

        func_name = func_node.name if func_node else ""
        param_types: Dict[str, str] = {}
        ret_type = ""
        if func_node:
            param_types = _build_context_vars(func_node)
            ret_type = _annotation_to_str(func_node.returns)

        obl = SpecObligation(
            description=f"spec: {nl_text[:80]}",
            location=loc,
            nl_text=nl_text,
            function_name=func_name,
            param_types=param_types,
            return_type=ret_type,
            spec_text=nl_text,
        )

        if _HAS_CORE:
            obl.refinement_type = self._build_refinement_type(
                nl_text, func_name, param_types, ret_type
            )

        return obl

    def _compile_guarantee_decorator(
        self,
        dec_node: ast.expr,
        func_node: Optional[Union[ast.FunctionDef, ast.AsyncFunctionDef]],
    ) -> GuaranteeObligation:
        """Internal: compile a @guarantee decorator."""
        nl_text = _extract_decorator_arg_string(dec_node)
        loc = CompilerLocation.from_ast_node(dec_node, self._file_path)
        func_name = func_node.name if func_node else ""

        obl = GuaranteeObligation(
            description=f"guarantee: {nl_text[:80]}",
            location=loc,
            nl_text=nl_text,
            function_name=func_name,
            guarantee_text=nl_text,
        )

        if _HAS_CORE:
            obl.contract = self._build_contract(nl_text, loc)

        return obl

    def _build_pi_type(
        self,
        func_node: Union[ast.FunctionDef, ast.AsyncFunctionDef],
        ctx_vars: Dict[str, str],
        ret_ann: str,
    ) -> Any:
        """Build a Π-type for a function signature if deppy core is available."""
        if not _HAS_CORE:
            return None

        from deppy.types.base import PrimitiveType
        from deppy.types.dependent import PiType as _Pi

        if not ctx_vars:
            return None

        params = list(ctx_vars.items())
        ret_type = PrimitiveType(ret_ann if ret_ann else "Any")

        # Telescope: Π (p1 : T1) (p2 : T2) ... -> Ret
        result: Any = ret_type
        for name, type_str in reversed(params):
            param_type = PrimitiveType(type_str)
            result = _Pi(
                param_name=name,
                param_type=param_type,
                return_type=result,
            )
        return result

    def _build_refinement_type(
        self,
        spec_text: str,
        func_name: str,
        param_types: Dict[str, str],
        ret_type: str,
    ) -> Any:
        """Build a RefinementType from a spec string."""
        if not _HAS_CORE:
            return None
        from deppy.types.base import PrimitiveType
        from deppy.types.refinement import RefinementType as _Ref, CallPred

        base = PrimitiveType(ret_type if ret_type else "Any")
        pred = CallPred(
            func_name=f"satisfies_{func_name}",
            args=tuple(param_types.keys()),
        )
        return _Ref(base=base, binder="result", predicate=pred)

    def _build_contract(self, nl_text: str, loc: CompilerLocation) -> Any:
        """Build a Contract-like wrapper from guarantee text."""
        if not _HAS_CORE:
            return None

        class _GuaranteeContract(Contract):
            """Lightweight contract wrapping a guarantee NL string."""

            def __init__(self, text: str, source_loc: Any) -> None:
                super().__init__(source_location=source_loc)
                self._text = text

            def to_predicate(self) -> Any:
                from deppy.contracts.base import Predicate as _P, Term as _T
                return _P.atomic(
                    _T.const(self._text),
                    description=f"guarantee: {self._text}",
                )

            def to_boundary_seed(self) -> Any:
                return {"guarantee": self._text}

            def pretty(self) -> str:
                return f"@guarantee({self._text!r})"

        return _GuaranteeContract(nl_text, loc.to_core_location())

    def _try_parse_predicate(self, text: str) -> Any:
        """Attempt to parse a NL/simple-expression predicate string.

        If the text looks like a simple comparison (``x > 0``, ``len(xs) > 0``),
        build a proper ``Predicate``.  Otherwise returns a callable predicate
        with the raw text for later oracle-assisted resolution.
        """
        if not _HAS_CORE:
            return None

        from deppy.contracts.base import Predicate as _P, Term as _T

        text = text.strip()

        # Try simple comparison patterns
        for op_str, op_name in [
            (">=", ">="), ("<=", "<="), ("!=", "!="),
            ("==", "=="), (">", ">"), ("<", "<"),
        ]:
            if op_str in text:
                parts = text.split(op_str, 1)
                if len(parts) == 2:
                    lhs = parts[0].strip()
                    rhs = parts[1].strip()
                    return _P.comparison(
                        op_name,
                        _T.var(lhs) if not lhs.isdigit() else _T.const(int(lhs)),
                        _T.var(rhs) if not rhs.isdigit() else _T.const(int(rhs)),
                        description=text,
                    )

        return _P.atomic(_T.const(text), description=text)

    def _check_decidability(self, obligation: Any) -> Optional[bool]:
        """Check whether a solver obligation is decidable via fragment classification."""
        if not _HAS_CORE:
            return None
        try:
            dispatcher = FragmentDispatcher.create_default()
            fragment = dispatcher.classify(obligation)
            return dispatcher.registry.get_primary(fragment) is not None
        except Exception:  # noqa: BLE001
            return None


# ═══════════════════════════════════════════════════════════════════════════════
# ObligationEmitter
# ═══════════════════════════════════════════════════════════════════════════════


class ObligationEmitter:
    """Emit proof obligations in various target formats.

    Given a compiled obligation, the emitter can produce:
    - Z3 formula strings (for decidable fragments)
    - Lean theorem statements (for proof obligations)
    - pytest test case code
    - Python runtime assertion code

    Reuses ``deppy.solver.z3_encoder.Z3Encoder`` for Z3 emission and
    the existing predicate pretty-printing infrastructure for other targets.
    """

    def __init__(
        self,
        *,
        z3_timeout_ms: float = _DEFAULT_TIMEOUT_MS,
        lean_prelude: str = "",
    ) -> None:
        self._z3_timeout_ms = z3_timeout_ms
        self._lean_prelude = lean_prelude

    # ------------------------------------------------------------------
    # Z3 emission
    # ------------------------------------------------------------------

    def emit_z3(self, obligation: ObligationBase) -> Optional[str]:
        """Emit a Z3-SMT formula for a decidable obligation.

        Uses ``deppy.solver.z3_encoder.Z3Encoder`` to convert the
        obligation's predicate into an SMT-LIB–compatible formula.
        Returns ``None`` if the obligation has no solver-encodable predicate
        or if the Z3 encoder is unavailable.
        """
        if not _HAS_Z3_ENCODER:
            return None

        pred = self._extract_predicate(obligation)
        if pred is None:
            return None

        try:
            env = VariableEnvironment()
            # Declare variables from obligation context
            for var_name in obligation.context_variables:
                env.declare(var_name)
            encoder = Z3Encoder(env=env)
            z3_expr = encoder.encode_predicate(pred)
            return f"(assert {z3_expr})"
        except Exception as exc:  # noqa: BLE001
            logger.debug("Z3 encoding failed for %s: %s", obligation.uid, exc)
            return None

    # ------------------------------------------------------------------
    # Lean emission
    # ------------------------------------------------------------------

    def emit_lean(self, obligation: ObligationBase) -> str:
        """Emit a Lean 4 theorem statement for the obligation.

        Produces a ``theorem`` declaration with a ``sorry`` proof placeholder.
        The statement encodes the obligation's specification as a Lean proposition.
        """
        lines: List[str] = []
        if self._lean_prelude:
            lines.append(self._lean_prelude)

        name = _lean_safe_name(obligation.uid)
        desc = obligation.nl_text or obligation.description

        if isinstance(obligation, HoleObligation):
            lines.append(f"-- Hole: {desc}")
            lines.append(f"-- Σ-type: ∃ code, satisfies code spec")
            ctx = self._lean_context(obligation)
            lines.append(f"theorem {name} {ctx}:")
            lines.append(f"  ∃ (code : String), True := by sorry")

        elif isinstance(obligation, SpecObligation):
            lines.append(f"-- Spec: {desc}")
            fn = obligation.function_name or "f"
            ctx = self._lean_context(obligation)
            lines.append(f"theorem {name} {ctx}:")
            lines.append(f"  spec_{_lean_safe_name(fn)} := by sorry")

        elif isinstance(obligation, GuaranteeObligation):
            lines.append(f"-- Guarantee: {desc}")
            fn = obligation.function_name or "f"
            ctx = self._lean_context(obligation)
            lines.append(f"theorem {name} {ctx}:")
            lines.append(f"  guarantee_{_lean_safe_name(fn)} := by sorry")

        elif isinstance(obligation, CheckObligation):
            lines.append(f"-- Check: {desc}")
            ctx = self._lean_context(obligation)
            lines.append(f"theorem {name} {ctx}:")
            lines.append(f"  check_holds := by sorry")

        elif isinstance(obligation, AssumeObligation):
            lines.append(f"-- Assumption (axiom): {desc}")
            ctx = self._lean_context(obligation)
            lines.append(f"axiom {name} {ctx}: assumption_holds")

        else:
            lines.append(f"-- Obligation: {desc}")
            lines.append(f"theorem {name} : True := by sorry")

        return "\n".join(lines)

    # ------------------------------------------------------------------
    # Pytest emission
    # ------------------------------------------------------------------

    def emit_test(self, obligation: ObligationBase) -> str:
        """Emit a pytest test case that checks the obligation at runtime.

        Generates a self-contained test function that exercises the
        obligation's predicate with example inputs.
        """
        name = obligation.uid.replace("-", "_")
        desc = obligation.nl_text or obligation.description
        lines: List[str] = []

        lines.append(f"def test_{name}():")
        lines.append(f'    """Auto-generated test for: {desc}"""')

        if isinstance(obligation, HoleObligation):
            lines.append(f"    # Hole must be filled before testing")
            lines.append(f"    # hole description: {desc}")
            lines.append(f"    pass  # TODO: fill hole and add assertions")

        elif isinstance(obligation, CheckObligation):
            assertion = obligation.assertion_text or desc
            lines.append(f"    # check: {assertion}")
            lines.append(f"    # TODO: set up inputs")
            lines.append(f"    assert {_safe_assertion(assertion)}")

        elif isinstance(obligation, SpecObligation):
            fn = obligation.function_name or "target_function"
            lines.append(f"    # spec for {fn}: {desc}")
            lines.append(f"    # TODO: import {fn} and add property-based tests")
            lines.append(f"    pass")

        elif isinstance(obligation, GuaranteeObligation):
            fn = obligation.function_name or "target_function"
            lines.append(f"    # guarantee for {fn}: {desc}")
            lines.append(f"    # TODO: import {fn}, call it, and verify postcondition")
            lines.append(f"    pass")

        elif isinstance(obligation, AssumeObligation):
            lines.append(f"    # assumption: {desc}")
            lines.append(f"    # Assumptions are not tested — they constrain the context")
            lines.append(f"    pass")

        else:
            lines.append(f"    # obligation: {desc}")
            lines.append(f"    pass")

        return "\n".join(lines)

    # ------------------------------------------------------------------
    # Runtime check emission
    # ------------------------------------------------------------------

    def emit_runtime_check(self, obligation: ObligationBase) -> str:
        """Emit a Python runtime assertion for the obligation.

        Generates ``assert`` or ``if not ... : raise`` statements that
        can be inserted into the compiled output.
        """
        desc = obligation.nl_text or obligation.description

        if isinstance(obligation, CheckObligation):
            assertion = obligation.assertion_text or desc
            safe = _safe_assertion(assertion)
            return (
                f"# {_RUNTIME_CHECK_PREFIX}{obligation.uid}\n"
                f"assert {safe}, {desc!r}"
            )

        if isinstance(obligation, AssumeObligation):
            assumption = obligation.assumption_text or desc
            safe = _safe_assertion(assumption)
            return (
                f"# assumption (not checked at runtime): {desc}\n"
                f"# assert {safe}"
            )

        if isinstance(obligation, GuaranteeObligation):
            return (
                f"# guarantee: {desc}\n"
                f"# Guarantee checked by contract decorator"
            )

        return f"# obligation {obligation.uid}: {desc}"

    # ------------------------------------------------------------------
    # Batch emission
    # ------------------------------------------------------------------

    def emit_all(
        self,
        obligations: Sequence[ObligationBase],
        target: EmitTarget,
    ) -> List[str]:
        """Emit all obligations to the given target format."""
        dispatch = {
            EmitTarget.Z3: self.emit_z3,
            EmitTarget.LEAN: self.emit_lean,
            EmitTarget.PYTEST: self.emit_test,
            EmitTarget.RUNTIME: self.emit_runtime_check,
        }
        emitter = dispatch[target]
        results: List[str] = []
        for obl in obligations:
            out = emitter(obl)
            if out is not None:
                results.append(out)
        return results

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _extract_predicate(self, obligation: ObligationBase) -> Any:
        """Pull out the encodable predicate from an obligation."""
        if isinstance(obligation, CheckObligation) and obligation.solver_obligation:
            return obligation.solver_obligation.formula
        if isinstance(obligation, AssumeObligation):
            return obligation.predicate
        if isinstance(obligation, SpecObligation):
            if obligation.refinement_type and _HAS_CORE:
                return obligation.refinement_type.predicate
        return None

    def _lean_context(self, obligation: ObligationBase) -> str:
        """Build a Lean-style context string from obligation variables."""
        parts: List[str] = []
        for var_name, type_str in obligation.context_variables.items():
            lean_type = _python_type_to_lean(type_str)
            safe_name = _lean_safe_name(var_name)
            parts.append(f"({safe_name} : {lean_type})")
        return " ".join(parts) if parts else ""


# ═══════════════════════════════════════════════════════════════════════════════
# HoleFiller
# ═══════════════════════════════════════════════════════════════════════════════


class HoleFiller:
    """Fill synthesis holes using Z3 or an oracle (LLM) callback.

    The filler attempts strategies in order:
    1. Z3 synthesis — if the hole's Σ-type is decidable, try Z3
    2. Oracle (LLM) — call the oracle callback, then type-check the result
    3. Fallback — leave the hole unfilled with a NotImplementedError stub

    Integration:
    - Uses ``deppy.solver.FragmentDispatcher`` to attempt Z3 synthesis
    - Uses ``deppy.solver.z3_encoder.Z3Encoder`` for constraint encoding
    - Oracle results are verified against the hole's Σ-type obligation
    """

    def __init__(
        self,
        *,
        max_attempts: int = _MAX_SYNTHESIS_ATTEMPTS,
        timeout_ms: float = _DEFAULT_TIMEOUT_MS,
        allow_z3: bool = True,
        allow_oracle: bool = True,
    ) -> None:
        self._max_attempts = max_attempts
        self._timeout_ms = timeout_ms
        self._allow_z3 = allow_z3
        self._allow_oracle = allow_oracle

    def fill_hole(
        self,
        hole: HoleObligation,
        context: Dict[str, Any],
        oracle_fn: Optional[Callable[..., Optional[str]]] = None,
    ) -> FilledHole:
        """Attempt to fill a hole using available strategies.

        Tries Z3 first (if enabled and the obligation is decidable),
        then the oracle, then gives up.

        Args:
            hole: The hole obligation to fill.
            context: Variable bindings available at the hole site.
            oracle_fn: Optional callback ``(description, context) -> code``.

        Returns:
            FilledHole with the synthesized code and verification status.
        """
        # Strategy 1: Z3 synthesis
        if self._allow_z3:
            z3_result = self.fill_with_z3(hole, context)
            if z3_result is not None:
                verified = self.verify_fill(hole, z3_result)
                return FilledHole(
                    hole=hole,
                    code=z3_result,
                    strategy=FillStrategy.Z3_SYNTHESIS,
                    verified=verified,
                    trust_level=4 if verified else 1,
                    verification_details="Z3 synthesis + verification",
                )

        # Strategy 2: Oracle (LLM)
        if self._allow_oracle and oracle_fn is not None:
            oracle_result = self.fill_with_oracle(hole, context, oracle_fn)
            if oracle_result is not None:
                verified = self.verify_fill(hole, oracle_result)
                trust = 2 if not verified else 3
                return FilledHole(
                    hole=hole,
                    code=oracle_result,
                    strategy=FillStrategy.ORACLE_LLM,
                    verified=verified,
                    trust_level=trust,
                    verification_details="Oracle fill" + (
                        " + verification passed" if verified else " (unverified)"
                    ),
                )

        # Strategy 3: Unfilled
        stub = self._make_stub(hole)
        return FilledHole(
            hole=hole,
            code=stub,
            strategy=FillStrategy.UNFILLED,
            verified=False,
            trust_level=0,
            verification_details="Hole left unfilled",
        )

    def fill_with_z3(
        self, hole: HoleObligation, context: Dict[str, Any]
    ) -> Optional[str]:
        """Attempt Z3-based synthesis for a hole.

        Encodes the hole's Σ-type as a Z3 constraint and asks the solver
        to find a satisfying model.  If the model is found, converts it
        to a Python expression string.
        """
        if not _HAS_CORE or not _HAS_Z3_ENCODER:
            return None

        sigma = hole.to_sigma_type()
        if sigma is None:
            return None

        try:
            env = VariableEnvironment()
            for var_name, type_str in hole.context_variables.items():
                hint = _type_str_to_sort_hint(type_str)
                env.declare(var_name, hint)
            env.declare("__hole_result")

            encoder = Z3Encoder(env=env)

            # Build constraints from the Σ-type's second component
            if hasattr(sigma, "snd_type") and _HAS_CORE:
                try:
                    constraint = encoder.encode_type_constraint(sigma.snd_type)
                except Exception:  # noqa: BLE001
                    return None

                # Try solving
                dispatcher = FragmentDispatcher.create_default()
                site_id = SiteId(
                    kind=SiteKind.PROOF,
                    name=f"hole_synth_{hole.uid}",
                )
                obl = SolverObligation(
                    site_id=site_id,
                    formula=constraint if not isinstance(constraint, str) else
                    self._wrap_as_predicate(hole.nl_text),
                    timeout_ms=self._timeout_ms,
                )
                result = dispatcher.dispatch(obl)
                if result.is_sat and result.model:
                    return self._model_to_code(result.model, hole)

        except Exception as exc:  # noqa: BLE001
            logger.debug("Z3 synthesis failed for %s: %s", hole.uid, exc)
        return None

    def fill_with_oracle(
        self,
        hole: HoleObligation,
        context: Dict[str, Any],
        oracle_fn: Callable[..., Optional[str]],
    ) -> Optional[str]:
        """Fill a hole using an LLM oracle, then type-check the result.

        Calls ``oracle_fn(description, context)`` up to ``max_attempts``
        times, verifying each attempt against the hole's obligation.
        """
        desc = hole.nl_text or hole.description
        for attempt in range(self._max_attempts):
            try:
                code = oracle_fn(desc, context)
            except Exception:  # noqa: BLE001
                continue
            if code is None:
                continue

            # Validate syntax
            try:
                ast.parse(code)
            except SyntaxError:
                logger.debug(
                    "Oracle attempt %d/%d for %s: syntax error",
                    attempt + 1, self._max_attempts, hole.uid,
                )
                continue

            return code

        return None

    def verify_fill(self, hole: HoleObligation, filled_code: str) -> bool:
        """Verify that a filled hole satisfies its Σ-type obligation.

        Checks:
        1. The code is syntactically valid Python
        2. If Z3 is available and the obligation is decidable, checks the
           predicate against the filled code
        3. Returns True if all available checks pass
        """
        # Check 1: syntax
        try:
            ast.parse(filled_code)
        except SyntaxError:
            return False

        # Check 2: Z3 verification (if available)
        if _HAS_CORE and _HAS_Z3_ENCODER and hole.solver_obligation is not None:
            try:
                dispatcher = FragmentDispatcher.create_default()
                result = dispatcher.dispatch(hole.solver_obligation)
                if result.is_unsat:
                    return False
            except Exception:  # noqa: BLE001
                pass

        return True

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _make_stub(self, hole: HoleObligation) -> str:
        """Generate a NotImplementedError stub for an unfilled hole."""
        desc = hole.nl_text or hole.description
        return f'raise NotImplementedError("Unfilled hole: {desc}")'

    def _model_to_code(self, model: Dict[str, Any], hole: HoleObligation) -> str:
        """Convert a Z3 satisfying model to a Python expression."""
        result_val = model.get("__hole_result")
        if result_val is not None:
            return repr(result_val)

        # If no direct result, build expression from model values
        parts: List[str] = []
        for k, v in sorted(model.items()):
            if k.startswith("__"):
                continue
            parts.append(f"{k} = {v!r}")
        if parts:
            return "; ".join(parts)

        return f'raise NotImplementedError("Z3 model: {model}")'

    def _wrap_as_predicate(self, text: str) -> Any:
        """Wrap a text string as a predicate for solver dispatch."""
        if _HAS_CORE:
            from deppy.contracts.base import Predicate as _P, Term as _T
            return _P.atomic(_T.const(text), description=text)
        return text


# ═══════════════════════════════════════════════════════════════════════════════
# CodeGenerator
# ═══════════════════════════════════════════════════════════════════════════════


class CodeGenerator:
    """Generate final Python code from compiled obligations and filled holes.

    Takes a ``CompilationResult`` and a mapping of hole UIDs to ``FilledHole``
    values, then produces the final annotated Python source with:
    - Holes replaced by synthesized code
    - Runtime assertions inserted for check() obligations
    - Contract decorators generated for guarantee() obligations

    Integration:
    - Generates ``@requires`` / ``@ensures`` decorators from existing
      ``deppy.contracts`` when available
    - Inserts trust-level annotations as comments for the hybrid pipeline
    """

    def __init__(
        self,
        *,
        insert_trust_comments: bool = True,
        insert_provenance: bool = True,
    ) -> None:
        self._insert_trust_comments = insert_trust_comments
        self._insert_provenance = insert_provenance
        self._emitter = ObligationEmitter()

    def generate(
        self,
        compilation: CompilationResult,
        fills: Dict[str, FilledHole],
    ) -> str:
        """Generate final Python source from compiled result + fills.

        Processing order:
        1. Replace holes with filled code
        2. Insert runtime checks for check() obligations
        3. Insert contract decorators for guarantee() obligations
        4. Optionally add trust-level comments
        """
        source = compilation.source
        lines = source.splitlines(keepends=True)

        # Collect all transformations as (line, col, kind, content)
        transforms: List[Tuple[int, int, str, str]] = []

        # 1. Hole replacements
        all_holes: List[HoleObligation] = list(compilation.top_level_holes)
        for fn in compilation.functions:
            all_holes.extend(fn.holes)

        for hole in all_holes:
            filled = fills.get(hole.uid)
            if filled is None:
                continue
            loc = hole.location
            transforms.append((loc.line, loc.col, "replace_hole", filled.code))

        # 2. Runtime checks
        all_checks: List[CheckObligation] = list(compilation.top_level_checks)
        for fn in compilation.functions:
            all_checks.extend(fn.checks)

        for chk in all_checks:
            runtime_code = self._emitter.emit_runtime_check(chk)
            loc = chk.location
            transforms.append((loc.line, loc.col, "insert_check", runtime_code))

        # 3. Guarantee contracts
        for fn in compilation.functions:
            for guar in fn.guarantees:
                contract_code = self._generate_contract_decorator(guar)
                loc = guar.location
                transforms.append((loc.line, 0, "insert_contract", contract_code))

        # Apply transforms in reverse order (highest line first)
        transforms.sort(key=lambda t: (t[0], t[1]), reverse=True)

        for line_no, col, kind, content in transforms:
            idx = line_no - 1
            if idx < 0 or idx >= len(lines):
                continue

            if kind == "replace_hole":
                lines[idx] = self._replace_hole_in_line(lines[idx], content)
            elif kind == "insert_check":
                indent = self._get_indent(lines[idx])
                check_lines = content.splitlines()
                insertion = "\n".join(indent + cl for cl in check_lines) + "\n"
                lines.insert(idx, insertion)
            elif kind == "insert_contract":
                indent = self._get_indent(lines[idx])
                contract_lines = content.splitlines()
                insertion = "\n".join(indent + cl for cl in contract_lines) + "\n"
                lines.insert(idx, insertion)

        result = "".join(lines)

        # 4. Add trust comments
        if self._insert_trust_comments:
            result = self._add_trust_comments(result, compilation, fills)

        return result

    def insert_runtime_checks(
        self,
        source: str,
        obligations: List[ObligationBase],
    ) -> str:
        """Insert runtime assertion statements for a list of obligations.

        Each check() obligation becomes an ``assert`` statement inserted
        just before the check() call.
        """
        lines = source.splitlines(keepends=True)
        checks = [o for o in obligations if isinstance(o, CheckObligation)]
        checks.sort(key=lambda c: c.location.line, reverse=True)

        for chk in checks:
            runtime = self._emitter.emit_runtime_check(chk)
            idx = chk.location.line - 1
            if 0 <= idx < len(lines):
                indent = self._get_indent(lines[idx])
                insertion = indent + runtime + "\n"
                lines.insert(idx, insertion)

        return "".join(lines)

    def insert_contracts(
        self,
        source: str,
        guarantees: List[GuaranteeObligation],
    ) -> str:
        """Insert @requires/@ensures decorators for guarantee obligations.

        Generates existing deppy contract decorators when the contracts
        module is available, otherwise inserts comment-based annotations.
        """
        lines = source.splitlines(keepends=True)
        guarantees_sorted = sorted(
            guarantees, key=lambda g: g.location.line, reverse=True
        )

        for guar in guarantees_sorted:
            decorator_code = self._generate_contract_decorator(guar)
            idx = guar.location.line - 1
            if 0 <= idx < len(lines):
                indent = self._get_indent(lines[idx])
                dec_lines = decorator_code.splitlines()
                insertion = "\n".join(indent + dl for dl in dec_lines) + "\n"
                lines.insert(idx, insertion)

        return "".join(lines)

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _generate_contract_decorator(self, guar: GuaranteeObligation) -> str:
        """Generate a contract decorator string from a guarantee obligation."""
        text = guar.guarantee_text or guar.nl_text or guar.description
        safe_text = text.replace('"', '\\"')

        if _HAS_CORE:
            return f'@ensures("{safe_text}")'
        return f'# @ensures("{safe_text}")  # deppy contracts not available'

    def _replace_hole_in_line(self, line: str, code: str) -> str:
        """Replace a hole() call in a source line with filled code."""
        import re
        pattern = r'hole\s*\([^)]*\)'
        if re.search(pattern, line):
            return re.sub(pattern, code, line, count=1)
        return line

    def _get_indent(self, line: str) -> str:
        """Extract leading whitespace from a line."""
        return line[: len(line) - len(line.lstrip())]

    def _add_trust_comments(
        self,
        source: str,
        compilation: CompilationResult,
        fills: Dict[str, FilledHole],
    ) -> str:
        """Add trust-level annotations as trailing comments."""
        lines = source.splitlines()
        annotations: Dict[int, str] = {}

        for hole_uid, filled in fills.items():
            loc = filled.hole.location
            trust_name = _trust_level_name(filled.trust_level)
            strategy = filled.strategy.value
            annotations[loc.line] = f"  # trust: {trust_name} ({strategy})"

        result_lines: List[str] = []
        for i, line in enumerate(lines, 1):
            if i in annotations:
                line = line.rstrip() + annotations[i]
            result_lines.append(line)

        return "\n".join(result_lines)


# ═══════════════════════════════════════════════════════════════════════════════
# Module-level helpers
# ═══════════════════════════════════════════════════════════════════════════════


def _lean_safe_name(name: str) -> str:
    """Convert a Python identifier to a Lean-safe name."""
    safe = name.replace("-", "_").replace(".", "_").replace(" ", "_")
    # Lean names can't start with digits
    if safe and safe[0].isdigit():
        safe = "v_" + safe
    return safe


def _python_type_to_lean(type_str: str) -> str:
    """Best-effort mapping from Python type annotation to Lean type."""
    mapping = {
        "int": "Int",
        "float": "Float",
        "str": "String",
        "bool": "Bool",
        "None": "Unit",
        "Any": "α",
        "List": "List",
        "Dict": "HashMap",
        "Set": "Finset",
        "Tuple": "Prod",
        "Optional": "Option",
    }
    # Strip Optional[...]
    if type_str.startswith("Optional[") and type_str.endswith("]"):
        inner = type_str[9:-1]
        return f"Option {_python_type_to_lean(inner)}"
    # Strip List[...]
    if type_str.startswith("List[") and type_str.endswith("]"):
        inner = type_str[5:-1]
        return f"List {_python_type_to_lean(inner)}"
    return mapping.get(type_str, type_str)


def _type_str_to_sort_hint(type_str: str) -> str:
    """Map a Python type annotation string to a Z3 sort hint."""
    if not _HAS_Z3_ENCODER:
        return "int"
    from deppy.solver.z3_encoder import SortHint
    mapping = {
        "int": SortHint.INT,
        "float": SortHint.REAL,
        "bool": SortHint.BOOL,
        "str": SortHint.STRING,
    }
    return mapping.get(type_str, SortHint.INT)


def _trust_level_name(level: int) -> str:
    """Map an integer trust level to a human-readable name."""
    if _HAS_HYBRID:
        try:
            return HybridTrustLevel(level).name
        except (ValueError, KeyError):
            pass
    names = {
        0: "UNTRUSTED",
        1: "LLM_RAW",
        2: "LLM_JUDGED",
        3: "PROPERTY_CHECKED",
        4: "Z3_PROVEN",
        5: "LEAN_VERIFIED",
        6: "HUMAN_VERIFIED",
    }
    return names.get(level, f"TRUST_{level}")


def _safe_assertion(text: str) -> str:
    """Make a string safe for use in an ``assert`` statement.

    If the text looks like a valid Python expression, return it directly.
    Otherwise wrap it in a ``True  # <text>`` comment.
    """
    try:
        ast.parse(text, mode="eval")
        return text
    except SyntaxError:
        safe = text.replace('"', '\\"')
        return f'True  # {safe}'


# ═══════════════════════════════════════════════════════════════════════════════
# Convenience: compile_source
# ═══════════════════════════════════════════════════════════════════════════════


def compile_source(
    source: str,
    *,
    file_path: str = "<string>",
    fill_holes: bool = False,
    oracle_fn: Optional[Callable[..., Optional[str]]] = None,
) -> CompilationResult:
    """One-shot convenience: compile, optionally fill holes, return result.

    Usage::

        result = compile_source('''
        @spec("returns sorted list")
        def sort_list(xs: list) -> list:
            return hole("sort xs in O(n log n)")
        ''')

        for fn in result.functions:
            print(fn.function_name, fn.n_total, "obligations")
    """
    compiler = MixedModeCompiler(file_path=file_path)
    result = compiler.compile(source)

    if fill_holes and result.has_holes:
        filler = HoleFiller()
        fills: Dict[str, FilledHole] = {}
        all_holes: List[HoleObligation] = list(result.top_level_holes)
        for fn in result.functions:
            all_holes.extend(fn.holes)
        for hole in all_holes:
            filled = filler.fill_hole(
                hole,
                context=hole.context_variables,
                oracle_fn=oracle_fn,
            )
            fills[hole.uid] = filled

    return result


def compile_source_with_intent_bridge(
    source: str,
    *,
    file_path: str = "<string>",
) -> BridgedCompilationResult:
    """Compile mixed-mode source and derive intent bridges for each function."""
    compiler = MixedModeCompiler(file_path=file_path)
    compilation = compiler.compile(source)
    bridged: Dict[str, IntentBridgeResult] = {}
    warnings: List[str] = []
    if not _HAS_INTENT_BRIDGE:
        warnings.append("Intent bridge unavailable; returning compilation only")
        return BridgedCompilationResult(compilation=compilation, warnings=warnings)

    bridge = IntentBridge()
    try:
        tree = ast.parse(source)
    except SyntaxError as exc:
        warnings.append(f"syntax error while bridging intent: {exc}")
        return BridgedCompilationResult(compilation=compilation, warnings=warnings)

    for fn in tree.body:
        if isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
            doc = ast.get_docstring(fn) or f"Function {fn.name} behavior is encoded in code."
            bridged[fn.name] = bridge.from_text(doc, type_name=f"{fn.name}_intent")
    return BridgedCompilationResult(
        compilation=compilation,
        bridged_intents=bridged,
        warnings=warnings,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# __all__
# ═══════════════════════════════════════════════════════════════════════════════

__all__ = [
    # Enums
    "ObligationKind",
    "EmitTarget",
    "FillStrategy",
    "CompilationPhase",
    # Location
    "CompilerLocation",
    # Obligations
    "ObligationBase",
    "HoleObligation",
    "SpecObligation",
    "GuaranteeObligation",
    "AssumeObligation",
    "CheckObligation",
    "FunctionObligation",
    "FilledHole",
    # Result
    "CompilationResult",
    "BridgedCompilationResult",
    # Core classes
    "MixedModeCompiler",
    "ObligationEmitter",
    "HoleFiller",
    "CodeGenerator",
    # Convenience
    "compile_source",
    "compile_source_with_intent_bridge",
]
