"""
Surface syntax for mixed-mode programming in deppy.

All surface forms are valid Python (decorators and function calls), so the
program parses and runs *before* compilation.  This enables incremental
development:

    - hole("description")       → raises NotImplementedError before compilation,
                                   returns synthesized code after
    - assume("condition")       → returns True before compilation,
                                   emits proof obligation after
    - check("condition")        → returns True before compilation,
                                   emits assertion after
    - @spec("description")      → passes through before compilation,
                                   verifies after
    - @guarantee("description") → passes through before compilation,
                                   verifies after

Design invariant: every surface form degrades gracefully to standard Python
semantics so that tests, type checkers, and IDEs work without a compilation
step.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.contracts.requires import RequiresContract
    from deppy.contracts.ensures import EnsuresContract
    from deppy.types.refinement import RefinementType as _CoreRefinementType
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import ast
import enum
import functools
import hashlib
import inspect
import logging
import textwrap
import threading
import warnings
from dataclasses import dataclass, field
from typing import (

    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Tuple,
    TypeVar,
    Union,
    overload,
)

__all__ = [
    "FragmentKind",
    "NLFragment",
    "CompilationStatus",
    "HoleResult",
    "hole",
    "spec",
    "guarantee",
    "assume",
    "check",
    "given",
    "sketch",
    "invariant_nl",
    "decreases_nl",
    "enable_compilation_mode",
    "disable_compilation_mode",
    "get_registry",
    "MixedModeExample",
]

logger = logging.getLogger(__name__)

F = TypeVar("F", bound=Callable[..., Any])

# ---------------------------------------------------------------------------
# Module-level compilation state
# ---------------------------------------------------------------------------

_COMPILATION_MODE: bool = False
"""When *False* (the default) every surface form behaves as a no-op or raises
``NotImplementedError``.  When *True*, the compiled code paths are active."""

_COMPILED_HOLES: Dict[int, Callable[..., Any]] = {}
"""Mapping from fragment index → compiled callable that produces the value."""

_compilation_lock = threading.Lock()
"""Guards mutation of the two globals above."""

# ---- public helpers to flip compilation mode -----------------------------

def enable_compilation_mode(
    compiled_holes: Dict[int, Callable[..., Any]],
) -> None:
    """Switch the runtime into *compiled* mode.

    Parameters
    ----------
    compiled_holes:
        A mapping from fragment index (as returned by
        ``_FragmentRegistry.register``) to a callable that, when invoked with
        the same keyword context the original ``hole()`` received, returns the
        synthesized value.
    """
    global _COMPILATION_MODE, _COMPILED_HOLES  # noqa: PLW0603
    with _compilation_lock:
        _COMPILED_HOLES = dict(compiled_holes)
        _COMPILATION_MODE = True
    logger.info(
        "Compilation mode ENABLED with %d compiled holes", len(compiled_holes)
    )

def disable_compilation_mode() -> None:
    """Revert to *uncompiled* mode (the safe default)."""
    global _COMPILATION_MODE, _COMPILED_HOLES  # noqa: PLW0603
    with _compilation_lock:
        _COMPILATION_MODE = False
        _COMPILED_HOLES = {}
    logger.info("Compilation mode DISABLED")

# ---------------------------------------------------------------------------
# FragmentKind
# ---------------------------------------------------------------------------

class FragmentKind(enum.Enum):
    """Classifies the role each NL fragment plays in the mixed-mode program."""

    HOLE = "hole"
    """A missing expression to be synthesized."""

    SPEC = "spec"
    """A full function specification given in NL."""

    GUARANTEE = "guarantee"
    """A postcondition / refinement on a concrete function body."""

    ASSUME = "assume"
    """An optimistic assumption that becomes a proof obligation."""

    CHECK = "check"
    """A runtime assertion that also generates a proof obligation."""

    GIVEN = "given"
    """An imported lemma or axiom expressed in NL."""

    SKETCH = "sketch"
    """A proof sketch that guides the proof search strategy."""

    INVARIANT_NL = "invariant_nl"
    """A loop invariant expressed in NL."""

    DECREASES_NL = "decreases_nl"
    """A termination measure expressed in NL."""

# ---------------------------------------------------------------------------
# CompilationStatus
# ---------------------------------------------------------------------------

class CompilationStatus(enum.Enum):
    """Lifecycle of a single NL fragment."""

    UNCOMPILED = "uncompiled"
    """Fragment has been registered but not yet compiled."""

    COMPILING = "compiling"
    """Compilation is in progress (e.g. LLM call in flight)."""

    COMPILED = "compiled"
    """Compilation succeeded; code is available but not yet verified."""

    VERIFIED = "verified"
    """Compiled code has been formally verified in Lean."""

    FAILED = "failed"
    """Compilation or verification failed."""

# ---------------------------------------------------------------------------
# NLFragment
# ---------------------------------------------------------------------------

@dataclass
class NLFragment:
    """A single natural-language fragment embedded in a mixed-mode program.

    Instances are created by the surface-syntax helpers (``hole``, ``spec``,
    …) and accumulated in the module-level ``_FragmentRegistry``.
    """

    kind: FragmentKind
    """What role this fragment plays."""

    text: str
    """The NL description supplied by the programmer."""

    context: Dict[str, Any] = field(default_factory=dict)
    """Surrounding code context — available variables, expected types, etc."""

    source_location: Optional[Tuple[str, int, int]] = None
    """(file, line, column) where the fragment appears."""

    parent_function: Optional[str] = None
    """Name of the immediately enclosing function, if any."""

    expected_type: Optional[str] = None
    """Type expected from the surrounding context (e.g. ``'list'``)."""

    content_hash: str = ""
    """SHA-256 of ``kind.value + text + sorted(context keys)``; used for
    caching so that re-compilation can be skipped when the fragment has not
    changed."""

    compiled_code: Optional[str] = None
    """Source code produced by the compiler.  ``None`` before compilation."""

    proof_obligation: Optional[str] = None
    """Lean theorem statement that must be discharged for this fragment."""

    trust_level: Optional[str] = None
    """After verification: ``'verified'``, ``'trusted'``, or ``'unverified'``."""

    status: CompilationStatus = CompilationStatus.UNCOMPILED
    """Current lifecycle stage."""

    # index assigned by the registry — not part of the logical identity
    _registry_index: int = field(default=-1, repr=False, compare=False)

    def __post_init__(self) -> None:
        if not self.content_hash:
            self.content_hash = self._compute_hash()

    # -- helpers -----------------------------------------------------------

    def _compute_hash(self) -> str:
        """Deterministic hash of the fragment's logical content."""
        parts = [
            self.kind.value,
            self.text,
            ",".join(sorted(self.context.keys())),
        ]
        if self.parent_function is not None:
            parts.append(self.parent_function)
        if self.expected_type is not None:
            parts.append(self.expected_type)
        return hashlib.sha256("|".join(parts).encode()).hexdigest()

    @property
    def is_compiled(self) -> bool:
        return self.status in (
            CompilationStatus.COMPILED,
            CompilationStatus.VERIFIED,
        )

    @property
    def is_verified(self) -> bool:
        return self.status is CompilationStatus.VERIFIED

    @property
    def needs_proof(self) -> bool:
        """True when this fragment creates a proof obligation."""
        return self.kind in (
            FragmentKind.GUARANTEE,
            FragmentKind.ASSUME,
            FragmentKind.CHECK,
            FragmentKind.INVARIANT_NL,
            FragmentKind.DECREASES_NL,
        )

    def pretty(self) -> str:
        """Human-readable one-liner for diagnostics."""
        loc = ""
        if self.source_location is not None:
            f, ln, col = self.source_location
            loc = f" @ {f}:{ln}:{col}"
        fn = f" in {self.parent_function}()" if self.parent_function else ""
        return (
            f"[{self.kind.value.upper()}]{fn}{loc}  "
            f"{self.text!r}  ({self.status.value})"
        )

    def to_lean_comment(self) -> str:
        """Render the fragment as a Lean comment for embedding in proofs."""
        wrapped = textwrap.fill(self.text, width=76, initial_indent="-- ",
                                subsequent_indent="-- ")
        header = f"-- Fragment [{self.kind.value}]"
        if self.parent_function:
            header += f" in `{self.parent_function}`"
        return f"{header}\n{wrapped}"

    def mark_compiling(self) -> None:
        self.status = CompilationStatus.COMPILING

    def mark_compiled(self, code: str) -> None:
        self.compiled_code = code
        self.status = CompilationStatus.COMPILED

    def mark_verified(self, trust: str = "verified") -> None:
        self.trust_level = trust
        self.status = CompilationStatus.VERIFIED

    def mark_failed(self) -> None:
        self.status = CompilationStatus.FAILED

# ---------------------------------------------------------------------------
# HoleResult — returned by hole() in compiled mode
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class HoleResult:
    """Value wrapper returned when a compiled hole is evaluated.

    Carries the synthesized *value* together with provenance metadata so that
    downstream code can inspect the origin and verification status.
    """

    value: Any
    """The synthesized result."""

    fragment: NLFragment
    """The NL fragment that produced this value."""

    status: CompilationStatus
    """Compilation / verification status at the time the hole was evaluated."""

    def __repr__(self) -> str:  # noqa: D105
        return (
            f"HoleResult(value={self.value!r}, "
            f"status={self.status.value!r})"
        )

    # Allow transparent use as the underlying value in boolean contexts.
    def __bool__(self) -> bool:
        return bool(self.value)

# ---------------------------------------------------------------------------
# _FragmentRegistry
# ---------------------------------------------------------------------------

class _FragmentRegistry:
    """Module-level registry of all NL fragments in the current program.

    Thread-safe: every mutation acquires ``_lock``.
    """

    def __init__(self) -> None:
        self._fragments: List[NLFragment] = []
        self._lock = threading.Lock()

    # -- mutators ----------------------------------------------------------

    def register(self, fragment: NLFragment) -> int:
        """Append *fragment* and return its index."""
        with self._lock:
            idx = len(self._fragments)
            fragment._registry_index = idx
            self._fragments.append(fragment)
        logger.debug("Registered fragment %d: %s", idx, fragment.pretty())
        return idx

    def clear(self) -> None:
        """Reset the registry (typically between compilation rounds)."""
        with self._lock:
            self._fragments.clear()
        logger.debug("Fragment registry cleared")

    # -- queries -----------------------------------------------------------

    def get(self, index: int) -> NLFragment:
        """Retrieve the fragment at *index*.

        Raises ``IndexError`` when *index* is out of range.
        """
        with self._lock:
            return self._fragments[index]

    def all(self) -> List[NLFragment]:
        """Return a shallow copy of every registered fragment."""
        with self._lock:
            return list(self._fragments)

    def by_function(self, func_name: str) -> List[NLFragment]:
        """Return fragments whose ``parent_function`` matches *func_name*."""
        with self._lock:
            return [
                f for f in self._fragments if f.parent_function == func_name
            ]

    def by_kind(self, kind: FragmentKind) -> List[NLFragment]:
        """Return fragments of the given *kind*."""
        with self._lock:
            return [f for f in self._fragments if f.kind is kind]

    def uncompiled(self) -> List[NLFragment]:
        """Return fragments that have not yet been compiled."""
        with self._lock:
            return [
                f
                for f in self._fragments
                if f.status is CompilationStatus.UNCOMPILED
            ]

    def __len__(self) -> int:
        with self._lock:
            return len(self._fragments)

    def __repr__(self) -> str:
        return f"_FragmentRegistry({len(self)} fragments)"

    def summary(self) -> str:
        """Multi-line summary grouped by kind."""
        lines: List[str] = [f"Fragment registry ({len(self)} total):"]
        for kind in FragmentKind:
            frags = self.by_kind(kind)
            if frags:
                lines.append(f"  {kind.value}: {len(frags)}")
                for frag in frags:
                    lines.append(f"    - {frag.pretty()}")
        return "\n".join(lines)

# Singleton registry used by all surface forms in this module.
_registry = _FragmentRegistry()

def get_registry() -> _FragmentRegistry:
    """Return the module-level fragment registry."""
    return _registry

# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _caller_location(stack_depth: int = 2) -> Tuple[Optional[Tuple[str, int, int]], Optional[str]]:
    """Inspect the call stack to capture source location and enclosing function.

    Parameters
    ----------
    stack_depth:
        How many frames to skip.  ``2`` is correct when called from a
        surface-syntax helper that is itself called by user code.

    Returns
    -------
    (source_location, parent_function)
    """
    frame = inspect.currentframe()
    try:
        for _ in range(stack_depth):
            if frame is not None:
                frame = frame.f_back
        if frame is None:
            return None, None
        info = inspect.getframeinfo(frame)
        source_location = (info.filename, info.lineno, 0)
        parent_function = info.function if info.function != "<module>" else None
        return source_location, parent_function
    finally:
        del frame

def _infer_expected_type(context: Dict[str, Any]) -> Optional[str]:
    """Try to pull an expected return type from keyword context.

    The user may write ``hole("sort this", returns=list)`` — in that case
    we extract ``'list'`` as the expected type.
    """
    hint = context.get("returns") or context.get("return_type")
    if hint is None:
        return None
    if isinstance(hint, type):
        return hint.__name__
    return str(hint)

def _function_signature_context(fn: Callable[..., Any]) -> Dict[str, Any]:
    """Build a context dict from a function's signature and source."""
    ctx: Dict[str, Any] = {}
    try:
        sig = inspect.signature(fn)
        params: Dict[str, str] = {}
        for name, param in sig.parameters.items():
            annotation = param.annotation
            if annotation is inspect.Parameter.empty:
                params[name] = "Any"
            else:
                params[name] = (
                    annotation.__name__
                    if isinstance(annotation, type)
                    else str(annotation)
                )
        ctx["parameters"] = params
        ret = sig.return_annotation
        if ret is not inspect.Signature.empty:
            ctx["return_type"] = (
                ret.__name__ if isinstance(ret, type) else str(ret)
            )
    except (ValueError, TypeError):
        pass
    try:
        ctx["source"] = textwrap.dedent(inspect.getsource(fn))
    except OSError:
        pass
    if fn.__doc__:
        ctx["docstring"] = fn.__doc__
    return ctx

def _is_stub_body(fn: Callable[..., Any]) -> bool:
    """Return *True* if *fn* has a body that is ``...``, ``pass``, or
    docstring-only — i.e. the user intends the body to be synthesized.
    """
    try:
        source = textwrap.dedent(inspect.getsource(fn))
    except OSError:
        return False

    try:
        tree = ast.parse(source)
    except SyntaxError:
        return False

    if not tree.body:
        return False

    func_def = tree.body[0]
    if not isinstance(func_def, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False

    body = func_def.body
    # Strip leading docstring
    stmts = body
    _str_node_types: tuple[type, ...] = (ast.Constant,)
    if hasattr(ast, "Str"):
        _str_node_types = (ast.Constant, ast.Str)  # type: ignore[attr-defined]
    if (
        stmts
        and isinstance(stmts[0], ast.Expr)
        and isinstance(stmts[0].value, _str_node_types)
    ):
        stmts = stmts[1:]

    if not stmts:
        # docstring-only
        return True

    if len(stmts) == 1:
        stmt = stmts[0]
        # `pass`
        if isinstance(stmt, ast.Pass):
            return True
        # `...` (Ellipsis)
        if (
            isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and stmt.value.value is ...
        ):
            return True

    return False

# ---------------------------------------------------------------------------
# Surface-syntax: hole()
# ---------------------------------------------------------------------------

def hole(description: str, **context: Any) -> Any:
    """Declare a *hole* — an expression to be synthesized from NL.

    Before compilation
    ~~~~~~~~~~~~~~~~~~
    Registers the fragment and raises ``NotImplementedError`` so that tests
    fail fast and the programmer knows which holes remain.

    After compilation
    ~~~~~~~~~~~~~~~~~
    Looks up the compiled callable for this hole's fragment index and
    evaluates it, returning a ``HoleResult`` wrapping the synthesized value.

    Parameters
    ----------
    description:
        Natural-language description of what the hole should compute.
    **context:
        Optional keyword arguments that supply type hints and available
        variables.  Special keys:

        - ``returns`` / ``return_type``: expected result type.
        - Any other key is treated as a named value available for synthesis.

    Examples
    --------
    >>> unique = hole("remove duplicates preserving order", input=lst, returns=list)
    """
    source_location, parent_function = _caller_location()
    expected_type = _infer_expected_type(context)

    fragment = NLFragment(
        kind=FragmentKind.HOLE,
        text=description,
        context=context,
        source_location=source_location,
        parent_function=parent_function,
        expected_type=expected_type,
    )
    idx = _registry.register(fragment)

    if not _COMPILATION_MODE:
        raise NotImplementedError(f"Uncompiled hole: {description}")

    compiled_fn = _COMPILED_HOLES.get(idx)
    if compiled_fn is None:
        raise NotImplementedError(
            f"Hole {idx} ({description!r}) has no compiled implementation"
        )

    value = compiled_fn(**context)
    return HoleResult(
        value=value,
        fragment=fragment,
        status=fragment.status,
    )

# ---------------------------------------------------------------------------
# Surface-syntax: spec()
# ---------------------------------------------------------------------------

def spec(description: str) -> Callable[[F], F]:
    """Decorator — specify a function entirely in NL.

    The decorated function should have a *stub* body (``...``, ``pass``, or
    a docstring only).  Before compilation the wrapper raises
    ``NotImplementedError``; after compilation the synthesized body runs
    instead.

    Parameters
    ----------
    description:
        Natural-language specification of the function's behaviour.

    Example
    -------
    ::

        @spec("Return the convex hull of a set of 2D points as a list of "
              "vertices in counter-clockwise order.")
        def convex_hull(points: List[Tuple[float, float]]) -> List[Tuple[float, float]]:
            ...
    """

    def decorator(fn: F) -> F:
        source_location, _ = _caller_location()
        ctx = _function_signature_context(fn)
        is_stub = _is_stub_body(fn)

        fragment = NLFragment(
            kind=FragmentKind.SPEC,
            text=description,
            context=ctx,
            source_location=source_location,
            parent_function=fn.__name__,
            expected_type=ctx.get("return_type"),
        )
        idx = _registry.register(fragment)

        @functools.wraps(fn)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            if not _COMPILATION_MODE:
                if is_stub:
                    raise NotImplementedError(
                        f"Uncompiled spec for {fn.__name__}: {description}"
                    )
                # Non-stub body: run it but warn that the spec is unchecked.
                warnings.warn(
                    f"Spec for {fn.__name__} is not yet compiled — "
                    f"running original body without verification",
                    stacklevel=2,
                )
                return fn(*args, **kwargs)

            compiled_fn = _COMPILED_HOLES.get(idx)
            if compiled_fn is not None:
                return compiled_fn(*args, **kwargs)

            # Compilation mode is on but this spec wasn't in compiled_holes;
            # the original body may have been kept.
            if not is_stub:
                return fn(*args, **kwargs)

            raise NotImplementedError(
                f"Spec {idx} for {fn.__name__} has no compiled body"
            )

        # Attach metadata so that the compiler can inspect the wrapper.
        wrapper._deppy_fragment_index = idx  # type: ignore[attr-defined]
        wrapper._deppy_fragment = fragment  # type: ignore[attr-defined]
        wrapper._deppy_original = fn  # type: ignore[attr-defined]
        return wrapper  # type: ignore[return-value]

    return decorator

# ---------------------------------------------------------------------------
# Surface-syntax: guarantee()
# ---------------------------------------------------------------------------

def guarantee(description: str) -> Callable[[F], F]:
    """Decorator — attach a *guarantee* (postcondition) to a concrete function.

    The function body executes as-is; the guarantee is checked post-hoc by
    the compiler / verifier.  In dependent-type notation the guarantee
    becomes:

        Π(inputs). { output | guarantee(inputs, output) }

    Before compilation the function runs normally with a logged warning.
    After compilation, postcondition checks are inserted around the call.

    Parameters
    ----------
    description:
        NL postcondition.  May reference parameter names and ``result``.

    Example
    -------
    ::

        @guarantee("The returned list is sorted and contains no duplicates")
        def unique_sorted(items: List[int]) -> List[int]:
            return sorted(set(items))
    """

    def decorator(fn: F) -> F:
        source_location, _ = _caller_location()
        ctx = _function_signature_context(fn)

        fragment = NLFragment(
            kind=FragmentKind.GUARANTEE,
            text=description,
            context=ctx,
            source_location=source_location,
            parent_function=fn.__name__,
            expected_type=ctx.get("return_type"),
        )
        idx = _registry.register(fragment)

        @functools.wraps(fn)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            if not _COMPILATION_MODE:
                warnings.warn(
                    f"Guarantee for {fn.__name__} is not yet compiled — "
                    f"postcondition unchecked: {description}",
                    stacklevel=2,
                )
                return fn(*args, **kwargs)

            # Compiled mode: run the body then invoke the compiled
            # postcondition checker if available.
            result = fn(*args, **kwargs)

            checker = _COMPILED_HOLES.get(idx)
            if checker is not None:
                # The checker receives (result, *args, **kwargs) and either
                # returns True or raises AssertionError.
                ok = checker(result, *args, **kwargs)
                if not ok:
                    raise AssertionError(
                        f"Guarantee violated for {fn.__name__}: {description}"
                    )

            return result

        wrapper._deppy_fragment_index = idx  # type: ignore[attr-defined]
        wrapper._deppy_fragment = fragment  # type: ignore[attr-defined]
        wrapper._deppy_original = fn  # type: ignore[attr-defined]
        return wrapper  # type: ignore[return-value]

    return decorator

# ---------------------------------------------------------------------------
# Surface-syntax: assume()
# ---------------------------------------------------------------------------

def assume(description: str, **context: Any) -> bool:
    """Declare an *assumption*.

    Before compilation
    ~~~~~~~~~~~~~~~~~~
    Returns ``True`` (the optimistic path) and logs a warning so the
    programmer is aware that the assumption is not yet discharged.

    After compilation
    ~~~~~~~~~~~~~~~~~
    Emits a proof obligation — the assumption must either be proven, or
    explicitly marked as ``TrustAssumption`` in the Lean context.  The
    returned boolean is ``True`` if the obligation has been discharged,
    ``False`` otherwise (and the caller should treat this as an unchecked
    hypothesis).

    The assumption is available as a named hypothesis in the enclosing
    function's proof context so that downstream ``check()`` and
    ``guarantee()`` calls can cite it.

    Parameters
    ----------
    description:
        NL statement of the assumption.
    **context:
        Variables in scope that the assumption refers to.
    """
    source_location, parent_function = _caller_location()

    fragment = NLFragment(
        kind=FragmentKind.ASSUME,
        text=description,
        context=context,
        source_location=source_location,
        parent_function=parent_function,
    )
    idx = _registry.register(fragment)

    if not _COMPILATION_MODE:
        warnings.warn(
            f"Uncompiled assumption in "
            f"{parent_function or '<module>'}: {description}",
            stacklevel=2,
        )
        return True

    # Compiled mode: the obligation may have been discharged.
    checker = _COMPILED_HOLES.get(idx)
    if checker is not None:
        result = checker(**context)
        if not result:
            warnings.warn(
                f"Assumption not discharged in "
                f"{parent_function or '<module>'}: {description}",
                stacklevel=2,
            )
        return bool(result)

    # No compiled checker — treat as trusted.
    fragment.trust_level = "trusted"
    return True

# ---------------------------------------------------------------------------
# Surface-syntax: check()
# ---------------------------------------------------------------------------

def check(description: str, **context: Any) -> bool:
    """Declare a *check* — a runtime assertion with an associated proof
    obligation.

    Before compilation
    ~~~~~~~~~~~~~~~~~~
    Returns ``True`` with a warning.  The check is not enforced.

    After compilation
    ~~~~~~~~~~~~~~~~~
    Emits both:

    1. A **runtime assertion** (if the compiled checker returns ``False`` an
       ``AssertionError`` is raised).
    2. A **proof obligation** in Lean that the condition always holds.

    Parameters
    ----------
    description:
        NL condition to be checked.
    **context:
        Variables in scope that the condition refers to.
    """
    source_location, parent_function = _caller_location()

    fragment = NLFragment(
        kind=FragmentKind.CHECK,
        text=description,
        context=context,
        source_location=source_location,
        parent_function=parent_function,
    )
    idx = _registry.register(fragment)

    if not _COMPILATION_MODE:
        warnings.warn(
            f"Uncompiled check in "
            f"{parent_function or '<module>'}: {description}",
            stacklevel=2,
        )
        return True

    checker = _COMPILED_HOLES.get(idx)
    if checker is not None:
        ok = checker(**context)
        if not ok:
            raise AssertionError(
                f"Check failed in "
                f"{parent_function or '<module>'}: {description}"
            )
        return True

    # No compiled checker — structural pass only.
    warnings.warn(
        f"Check has no compiled verifier in "
        f"{parent_function or '<module>'}: {description}",
        stacklevel=2,
    )
    return True

# ---------------------------------------------------------------------------
# Surface-syntax: given()
# ---------------------------------------------------------------------------

def given(description: str, **context: Any) -> Callable[[F], F]:
    """Import a lemma or axiom from NL.

    Can be used as a decorator (attaching the lemma to a function) **or**
    called standalone to introduce a module-level axiom.

    Before compilation
    ~~~~~~~~~~~~~~~~~~
    No-op — the decorator passes the function through unchanged.

    After compilation
    ~~~~~~~~~~~~~~~~~
    The NL description is translated into a Lean axiom wrapped in
    ``TrustAssumption`` so that it can be cited in proofs without a
    machine-checked derivation.

    Parameters
    ----------
    description:
        NL statement of the lemma / axiom.
    **context:
        Variables or types that the axiom references.
    """
    source_location, parent_function = _caller_location()

    fragment = NLFragment(
        kind=FragmentKind.GIVEN,
        text=description,
        context=context,
        source_location=source_location,
        parent_function=parent_function,
    )
    _registry.register(fragment)

    def decorator(fn: F) -> F:
        fn._deppy_given_fragment = fragment  # type: ignore[attr-defined]
        return fn

    return decorator

# ---------------------------------------------------------------------------
# Surface-syntax: sketch()
# ---------------------------------------------------------------------------

def sketch(description: str, **context: Any) -> None:
    """Provide a proof sketch in NL.

    Before compilation
    ~~~~~~~~~~~~~~~~~~
    No-op.

    After compilation
    ~~~~~~~~~~~~~~~~~
    The sketch guides the proof search strategy — for example "induct on
    the length of the list then apply the IH" tells the tactic engine to
    prefer structural induction.

    Parameters
    ----------
    description:
        Free-form proof sketch.
    **context:
        Variables the sketch references.
    """
    source_location, parent_function = _caller_location()

    fragment = NLFragment(
        kind=FragmentKind.SKETCH,
        text=description,
        context=context,
        source_location=source_location,
        parent_function=parent_function,
    )
    _registry.register(fragment)

    # sketch() is purely advisory — it never raises and has no return value.
    if not _COMPILATION_MODE:
        logger.debug(
            "Proof sketch recorded (uncompiled) in %s: %s",
            parent_function or "<module>",
            description,
        )

# ---------------------------------------------------------------------------
# Surface-syntax: invariant_nl()
# ---------------------------------------------------------------------------

def invariant_nl(description: str, **context: Any) -> Callable[[F], F]:
    """Decorator — attach an NL loop invariant to a function.

    Before compilation
    ~~~~~~~~~~~~~~~~~~
    No-op; the decorated function runs unchanged.

    After compilation
    ~~~~~~~~~~~~~~~~~
    The invariant is formalised and checked inductively:

    1. *Init*  — the invariant holds on loop entry.
    2. *Pres*  — if the invariant holds before an iteration it holds after.
    3. *Post*  — the invariant plus the loop guard's negation imply the
       postcondition.

    Parameters
    ----------
    description:
        NL loop invariant.
    **context:
        Variables the invariant references.
    """
    source_location, parent_function = _caller_location()

    fragment = NLFragment(
        kind=FragmentKind.INVARIANT_NL,
        text=description,
        context=context,
        source_location=source_location,
        parent_function=parent_function,
    )
    idx = _registry.register(fragment)

    def decorator(fn: F) -> F:
        @functools.wraps(fn)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            if not _COMPILATION_MODE:
                logger.debug(
                    "Invariant unchecked for %s: %s", fn.__name__, description
                )
                return fn(*args, **kwargs)

            # Compiled mode: optionally run the invariant checker on each
            # iteration via a tracing hook.
            checker = _COMPILED_HOLES.get(idx)
            if checker is not None:
                # The compiled checker is expected to instrument the function
                # and return a wrapped version.
                instrumented = checker(fn)
                return instrumented(*args, **kwargs)

            return fn(*args, **kwargs)

        wrapper._deppy_fragment_index = idx  # type: ignore[attr-defined]
        wrapper._deppy_fragment = fragment  # type: ignore[attr-defined]
        wrapper._deppy_original = fn  # type: ignore[attr-defined]
        return wrapper  # type: ignore[return-value]

    return decorator

# ---------------------------------------------------------------------------
# Surface-syntax: decreases_nl()
# ---------------------------------------------------------------------------

def decreases_nl(description: str, **context: Any) -> Callable[[F], F]:
    """Decorator — attach an NL termination measure to a recursive function.

    Before compilation
    ~~~~~~~~~~~~~~~~~~
    No-op; the decorated function runs unchanged.

    After compilation
    ~~~~~~~~~~~~~~~~~
    The termination measure is formalised as a well-founded relation and
    every recursive call must be shown to decrease the measure.

    Parameters
    ----------
    description:
        NL termination measure, e.g. "the length of the list decreases
        on every recursive call".
    **context:
        Variables the measure references.
    """
    source_location, parent_function = _caller_location()

    fragment = NLFragment(
        kind=FragmentKind.DECREASES_NL,
        text=description,
        context=context,
        source_location=source_location,
        parent_function=parent_function,
    )
    idx = _registry.register(fragment)

    def decorator(fn: F) -> F:
        @functools.wraps(fn)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            if not _COMPILATION_MODE:
                logger.debug(
                    "Termination measure unchecked for %s: %s",
                    fn.__name__,
                    description,
                )
                return fn(*args, **kwargs)

            checker = _COMPILED_HOLES.get(idx)
            if checker is not None:
                instrumented = checker(fn)
                return instrumented(*args, **kwargs)

            return fn(*args, **kwargs)

        wrapper._deppy_fragment_index = idx  # type: ignore[attr-defined]
        wrapper._deppy_fragment = fragment  # type: ignore[attr-defined]
        wrapper._deppy_original = fn  # type: ignore[attr-defined]
        return wrapper  # type: ignore[return-value]

    return decorator

# ---------------------------------------------------------------------------
# MixedModeExample — demonstrates the surface syntax
# ---------------------------------------------------------------------------

class MixedModeExample:
    """Demonstrates mixed-mode programming with the deppy surface syntax.

    Each method shows a different pattern — run them *before* compilation to
    see the fail-safe behaviour, then again *after* ``enable_compilation_mode``
    to see synthesized + verified results.

    Example 1 — ``unique_sorted``
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    Uses ``hole()`` for the deduplication logic and ``@guarantee()`` for the
    sorted-and-unique postcondition.

    Before compilation::

        >>> ex = MixedModeExample()
        >>> ex.unique_sorted([3, 1, 2, 1])
        NotImplementedError: Uncompiled hole: remove duplicates …

    After compilation (once a provider maps the hole to an implementation)::

        >>> ex.unique_sorted([3, 1, 2, 1])
        [1, 2, 3]

    Example 2 — ``binary_search``
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    A concrete algorithm annotated with ``assume("arr is sorted")`` and
    ``@guarantee("runs in O(log n) time")``.

    Before compilation the function runs but prints warnings about unchecked
    assumptions and guarantees.  After compilation the assumption is
    discharged and the guarantee is verified.

    Example 3 — ``convex_hull``
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~
    Purely NL specification — the body is ``...``.  Before compilation the
    function raises ``NotImplementedError``; after compilation the body is
    fully synthesized from the spec.
    """

    # ------------------------------------------------------------------
    # Example 1: unique_sorted
    # ------------------------------------------------------------------

    @guarantee("The returned list is sorted in ascending order and contains "
               "no duplicate elements")
    def unique_sorted(self, items: List[int]) -> List[int]:
        """Remove duplicates and sort.

        Before compilation
        ~~~~~~~~~~~~~~~~~~
        The ``hole()`` call raises ``NotImplementedError`` because no
        compiled implementation exists yet.

        After compilation
        ~~~~~~~~~~~~~~~~~
        The hole is filled with synthesized code (e.g.
        ``sorted(set(items))``) and the guarantee decorator verifies that
        the result is indeed sorted and unique.

        Dependent type
        ~~~~~~~~~~~~~~
        unique_sorted : List Int →
            { r : List Int | Sorted r ∧ Unique r ∧ Permutation.toSet r = toSet items }
        """
        # The hole synthesizes the deduplication + sort logic.
        result = hole(
            "remove duplicates from items and return a sorted list",
            input=items,
            returns=list,
        )
        # In compiled mode, result is a HoleResult; unwrap it.
        if isinstance(result, HoleResult):
            return result.value
        return result

    # ------------------------------------------------------------------
    # Example 2: binary_search
    # ------------------------------------------------------------------

    @guarantee("returns the index of target in arr if present, else -1; "
               "runs in O(log n) comparisons")
    def binary_search(self, arr: List[int], target: int) -> int:
        """Classic binary search with mixed-mode annotations.

        Before compilation
        ~~~~~~~~~~~~~~~~~~
        ``assume()`` returns ``True`` and logs a warning.
        ``check()`` returns ``True`` and logs a warning.
        The function body runs normally — it *works*, but its properties
        are not formally verified.

        After compilation
        ~~~~~~~~~~~~~~~~~
        * The assumption ``arr is sorted`` emits a Lean proof obligation::

              theorem arr_sorted_obligation (arr : List Int) :
                  Sorted arr → …

        * The guarantee becomes a verified postcondition.
        * The ``check()`` becomes both a runtime assertion and a proof goal.

        Dependent type
        ~~~~~~~~~~~~~~
        binary_search : (arr : List Int) → (target : Int) →
            { Sorted arr } →
            { r : Int | (r ≠ -1 → arr[r] = target) ∧ (r = -1 → target ∉ arr) }
        """
        assume("arr is sorted in ascending order", arr=arr)

        lo, hi = 0, len(arr) - 1
        while lo <= hi:
            mid = lo + (hi - lo) // 2

            check("lo >= 0 and hi < len(arr) and lo <= hi + 1",
                  lo=lo, hi=hi, arr=arr)

            sketch(
                "The loop maintains the invariant that if target is in arr "
                "then arr[lo] <= target <= arr[hi].  Each iteration halves "
                "the search space, so termination follows from "
                "hi - lo decreasing."
            )

            if arr[mid] == target:
                return mid
            elif arr[mid] < target:
                lo = mid + 1
            else:
                hi = mid - 1

        return -1

    # ------------------------------------------------------------------
    # Example 3: convex_hull — fully NL-specified
    # ------------------------------------------------------------------

    @spec("Compute the convex hull of a set of 2D points.  Return the hull "
          "vertices as a list of (x, y) tuples in counter-clockwise order.  "
          "Use the Graham scan algorithm.  Handle collinear points by "
          "keeping only the extreme points.  If fewer than 3 points are "
          "given, return them all.")
    def convex_hull(
        self,
        points: List[Tuple[float, float]],
    ) -> List[Tuple[float, float]]:
        """Convex hull — synthesized entirely from the NL spec.

        Before compilation
        ~~~~~~~~~~~~~~~~~~
        The body is ``...`` so the ``@spec`` decorator raises
        ``NotImplementedError``.

        After compilation
        ~~~~~~~~~~~~~~~~~
        The body is replaced by a synthesized Graham scan implementation
        and the spec is checked against it.

        Dependent type
        ~~~~~~~~~~~~~~
        convex_hull : (pts : List (Float × Float)) →
            { r : List (Float × Float) |
              IsConvexHull r pts ∧ CounterClockwise r }
        """
        ...

    # ------------------------------------------------------------------
    # Example 4 (bonus): gcd with termination measure
    # ------------------------------------------------------------------

    @decreases_nl("b decreases towards 0 on every recursive call")
    @guarantee("result divides both a and b, and is the largest such divisor")
    def gcd(self, a: int, b: int) -> int:
        """Euclidean GCD with termination annotation.

        Before compilation
        ~~~~~~~~~~~~~~~~~~
        Runs normally; the ``@decreases_nl`` and ``@guarantee`` decorators
        are no-ops (with warnings).

        After compilation
        ~~~~~~~~~~~~~~~~~
        * The termination measure ``b`` is formalised as a well-founded
          relation on ℕ and each recursive call must provably decrease it.
        * The guarantee becomes a verified postcondition:
          ``gcd(a,b) | a  ∧  gcd(a,b) | b  ∧  ∀ d, d|a → d|b → d ≤ gcd(a,b)``
        """
        if b == 0:
            return abs(a)
        return self.gcd(b, a % b)

    # ------------------------------------------------------------------
    # Example 5 (bonus): invariant_nl on an iterative function
    # ------------------------------------------------------------------

    @invariant_nl(
        "After each iteration, partial_sum equals the sum of arr[0..i] "
        "and 0 <= i <= len(arr)"
    )
    def prefix_sum(self, arr: List[int]) -> List[int]:
        """Running prefix sum with an NL loop invariant.

        Before compilation
        ~~~~~~~~~~~~~~~~~~
        Runs normally.

        After compilation
        ~~~~~~~~~~~~~~~~~
        The invariant is formalised and three proof obligations are emitted:

        1. *Init*:  ``partial_sum = 0 ∧ i = 0  →  Inv(partial_sum, i)``
        2. *Pres*:  ``Inv(s, i) ∧ i < len(arr)  →  Inv(s + arr[i], i+1)``
        3. *Post*:  ``Inv(s, len(arr))  →  result = prefix_sums(arr)``
        """
        result: List[int] = []
        partial_sum = 0
        for val in arr:
            partial_sum += val
            result.append(partial_sum)
        return result

    # ------------------------------------------------------------------
    # Example 6 (bonus): given() for importing a lemma
    # ------------------------------------------------------------------

    @given("For any list xs, sorting xs then removing adjacent duplicates "
           "yields the same set as xs")
    @guarantee("returns True when items has no duplicates, False otherwise")
    def has_duplicates(self, items: List[int]) -> bool:
        """Check for duplicates, using a *given* lemma.

        Before compilation
        ~~~~~~~~~~~~~~~~~~
        Runs normally; the ``@given`` is a no-op.

        After compilation
        ~~~~~~~~~~~~~~~~~
        The lemma is available as a Lean axiom::

            axiom sort_dedup_set_eq (xs : List Int) :
                toSet (dedup (sort xs)) = toSet xs

        and the guarantee can cite it in its proof.
        """
        return len(items) != len(set(items))

    # ------------------------------------------------------------------
    # Demonstration runner
    # ------------------------------------------------------------------

    @staticmethod
    def run_demo() -> None:
        """Run all examples in uncompiled mode, printing results or errors.

        This shows the *safe default* behaviour — every surface form either
        works (assume/check return True, given/sketch are no-ops) or fails
        fast (hole/spec raise NotImplementedError).
        """
        ex = MixedModeExample()
        registry = get_registry()
        registry.clear()

        print("=" * 60)
        print("Mixed-mode surface syntax demo (UNCOMPILED)")
        print("=" * 60)
        print()

        # -- unique_sorted (should fail at hole) -------------------------
        print("1. unique_sorted([3, 1, 2, 1])")
        try:
            ex.unique_sorted([3, 1, 2, 1])
        except NotImplementedError as exc:
            print(f"   → NotImplementedError: {exc}")
        print()

        # -- binary_search (should run with warnings) ---------------------
        import io
        import contextlib

        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            result = ex.binary_search([1, 2, 3, 4, 5], 3)
            print(f"2. binary_search([1,2,3,4,5], 3) → {result}")
            for w in caught:
                print(f"   ⚠ {w.message}")
        print()

        # -- convex_hull (should fail — stub body) -----------------------
        print("3. convex_hull([(0,0), (1,0), (0,1)])")
        try:
            ex.convex_hull([(0, 0), (1, 0), (0, 1)])
        except NotImplementedError as exc:
            print(f"   → NotImplementedError: {exc}")
        print()

        # -- gcd (should run with warnings) ------------------------------
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            result = ex.gcd(12, 8)
            print(f"4. gcd(12, 8) → {result}")
            for w in caught:
                print(f"   ⚠ {w.message}")
        print()

        # -- prefix_sum (should run) ------------------------------------
        result = ex.prefix_sum([1, 2, 3, 4])
        print(f"5. prefix_sum([1, 2, 3, 4]) → {result}")
        print()

        # -- has_duplicates (should run with warnings) -------------------
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            result = ex.has_duplicates([1, 2, 2, 3])
            print(f"6. has_duplicates([1, 2, 2, 3]) → {result}")
            for w in caught:
                print(f"   ⚠ {w.message}")
        print()

        # -- registry summary -------------------------------------------
        print("-" * 60)
        print(registry.summary())
        print("-" * 60)

# ---------------------------------------------------------------------------
# Module self-test
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    MixedModeExample.run_demo()
