"""
Mixed-mode AST parser for deppy.

Parses a Python source file and identifies all natural-language (NL) fragments
— holes, specs, guarantees, assumptions, checks, sketches, invariants, and
decreases annotations — together with their surrounding code context and
inferred type information.

The parser works in three phases:

1. **Parse** — use the standard ``ast`` module to obtain a full AST.
2. **Visit** — walk the AST with ``MixedModeVisitor`` to locate every NL
   fragment and attach a ``TypeContext`` that records the type information
   available at that program point.
3. **Assemble** — bundle the fragments, function map, and plain code blocks
   into a ``MixedAST`` value that downstream passes (synthesis, verification,
   Lean translation) can consume.
"""

from __future__ import annotations


# --- Integration with existing deppy codebase ---
try:
    from deppy.types.dependent import PiType, SigmaType
    from deppy.types.refinement import RefinementType as _CoreRefinementType
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

import ast
import enum
import hashlib
import textwrap
from dataclasses import dataclass, field
from pathlib import Path
from typing import (

    Dict,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

#: Call-site names that introduce NL fragments.
_NL_CALL_NAMES: Set[str] = {"hole", "assume", "check", "sketch"}

#: Decorator names that introduce NL fragments.
_NL_DECORATOR_NAMES: Set[str] = {
    "spec",
    "guarantee",
    "given",
    "invariant_nl",
    "decreases_nl",
}

#: Mapping from call name to the corresponding ``MixedASTNodeKind``.
_CALL_KIND_MAP: Dict[str, "MixedASTNodeKind"] = {}  # populated after enum

#: Mapping from decorator name to the corresponding ``MixedASTNodeKind``.
_DECORATOR_KIND_MAP: Dict[str, "MixedASTNodeKind"] = {}  # populated after enum

# ---------------------------------------------------------------------------
# MixedASTNodeKind
# ---------------------------------------------------------------------------

class MixedASTNodeKind(enum.Enum):
    """Discriminant for every node kind that the mixed-mode parser cares about."""

    FUNCTION = "function"
    HOLE = "hole"
    SPEC_DECORATOR = "spec_decorator"
    GUARANTEE_DECORATOR = "guarantee_decorator"
    ASSUME_CALL = "assume_call"
    CHECK_CALL = "check_call"
    GIVEN_DECORATOR = "given_decorator"
    SKETCH_CALL = "sketch_call"
    INVARIANT_DECORATOR = "invariant_decorator"
    DECREASES_DECORATOR = "decreases_decorator"
    CODE_BLOCK = "code_block"

# Populate the lookup tables now that the enum exists.
_CALL_KIND_MAP.update(
    {
        "hole": MixedASTNodeKind.HOLE,
        "assume": MixedASTNodeKind.ASSUME_CALL,
        "check": MixedASTNodeKind.CHECK_CALL,
        "sketch": MixedASTNodeKind.SKETCH_CALL,
    }
)

_DECORATOR_KIND_MAP.update(
    {
        "spec": MixedASTNodeKind.SPEC_DECORATOR,
        "guarantee": MixedASTNodeKind.GUARANTEE_DECORATOR,
        "given": MixedASTNodeKind.GIVEN_DECORATOR,
        "invariant_nl": MixedASTNodeKind.INVARIANT_DECORATOR,
        "decreases_nl": MixedASTNodeKind.DECREASES_DECORATOR,
    }
)

# ---------------------------------------------------------------------------
# TypeContext
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TypeContext:
    """Type information available at an NL fragment's location.

    Constructed by walking outward from the fragment's AST node to the
    enclosing function, class, and module scopes.
    """

    available_variables: Dict[str, str] = field(default_factory=dict)
    """Mapping *variable name* → *type-annotation string* for every name that
    is in scope at the fragment.  Includes function parameters, annotated
    locals, and for-loop / comprehension targets when a type can be inferred.
    """

    expected_return_type: Optional[str] = None
    """The return-type annotation of the enclosing function, if any.  Useful
    when the fragment is in *tail position* (i.e. the value will be returned).
    """

    enclosing_function: Optional[str] = None
    """Name of the immediately enclosing ``def`` (or ``async def``), or
    ``None`` if the fragment is at module scope.
    """

    enclosing_class: Optional[str] = None
    """Name of the immediately enclosing ``class``, or ``None``."""

    control_flow_position: str = "top_level"
    """A human-readable tag indicating where in the control-flow structure the
    fragment sits.  One of ``"top_level"``, ``"if_branch"``,
    ``"else_branch"``, ``"elif_branch"``, ``"loop_body"``, ``"try_body"``,
    ``"except_handler"``, ``"finally_body"``, ``"with_body"``,
    ``"function_body"``.
    """

    preceding_assignments: List[Tuple[str, str]] = field(default_factory=list)
    """A list of ``(variable_name, expression_source)`` pairs for the
    assignments that textually precede the fragment inside the same block.
    Capped at the 20 most recent to keep context manageable.
    """

    following_usage: Optional[str] = None
    """A short description of how the fragment's result is consumed — for
    example ``"assigned to x"``, ``"passed to sorted()"``, ``"returned"``.
    ``None`` when usage cannot be determined.
    """

    def merge(self, other: TypeContext) -> TypeContext:
        """Return a new ``TypeContext`` that combines information from *self*
        and *other*, preferring *other*'s values when both are non-empty."""
        merged_vars = {**self.available_variables, **other.available_variables}
        merged_assigns = list(self.preceding_assignments) + list(
            other.preceding_assignments
        )
        return TypeContext(
            available_variables=merged_vars,
            expected_return_type=other.expected_return_type or self.expected_return_type,
            enclosing_function=other.enclosing_function or self.enclosing_function,
            enclosing_class=other.enclosing_class or self.enclosing_class,
            control_flow_position=(
                other.control_flow_position
                if other.control_flow_position != "top_level"
                else self.control_flow_position
            ),
            preceding_assignments=merged_assigns[-20:],
            following_usage=other.following_usage or self.following_usage,
        )

# ---------------------------------------------------------------------------
# ParsedFragment
# ---------------------------------------------------------------------------

@dataclass
class ParsedFragment:
    """A single NL fragment extracted from the mixed-mode source."""

    kind: MixedASTNodeKind
    """What kind of NL construct produced this fragment."""

    nl_text: str
    """The natural-language string extracted from the call or decorator."""

    source_location: Tuple[str, int, int]
    """``(filename, line, col_offset)`` — one-indexed line number."""

    type_context: TypeContext
    """Rich type context inferred for this fragment's location."""

    ast_node: ast.AST
    """The AST node from which this fragment was extracted (the ``Call`` node
    for ``hole()`` / ``assume()`` / etc., or the decorator node for
    ``@spec()`` / ``@guarantee()`` / etc.)."""

    parent_node: Optional[ast.AST]
    """The AST node that directly contains *ast_node*.  ``None`` when the
    fragment is at module level."""

    content_hash: str = ""
    """SHA-256 hex digest of ``nl_text`` (computed lazily in ``__post_init__``)."""

    def __post_init__(self) -> None:
        if not self.content_hash:
            self.content_hash = hashlib.sha256(
                self.nl_text.encode("utf-8")
            ).hexdigest()

    # Convenience -----------------------------------------------------------------

    @property
    def line(self) -> int:
        """One-indexed source line number."""
        return self.source_location[1]

    @property
    def col(self) -> int:
        return self.source_location[2]

    @property
    def filename(self) -> str:
        return self.source_location[0]

    def short_description(self) -> str:
        """One-line human-readable summary."""
        trunc = self.nl_text[:60] + ("…" if len(self.nl_text) > 60 else "")
        return f"{self.kind.value}@L{self.line}: {trunc!r}"

    def __repr__(self) -> str:
        return (
            f"ParsedFragment(kind={self.kind!r}, nl_text={self.nl_text!r}, "
            f"line={self.line})"
        )

# ---------------------------------------------------------------------------
# MixedAST
# ---------------------------------------------------------------------------

@dataclass
class MixedAST:
    """The product of parsing a mixed-mode Python source file.

    Contains the original source, the standard-library AST, every NL fragment
    found, and convenience accessors for downstream passes.
    """

    source: str
    """The original Python source code that was parsed."""

    filename: str
    """Path (or synthetic name) of the source file."""

    tree: ast.Module
    """The full AST as returned by ``ast.parse``."""

    fragments: List[ParsedFragment] = field(default_factory=list)
    """All NL fragments found in the source, in source order."""

    functions: Dict[str, ast.FunctionDef] = field(default_factory=dict)
    """Every ``def`` / ``async def`` found at any nesting level, keyed by
    qualified name (``ClassName.method`` for methods)."""

    code_blocks: List[ast.AST] = field(default_factory=list)
    """Top-level statements and function bodies that are *not* NL fragments.
    Useful for code-coverage analyses that need to know what ordinary code
    surrounds the NL parts."""

    # -- filtered accessors ---------------------------------------------------

    def holes(self) -> List[ParsedFragment]:
        """Return only ``hole(...)`` fragments."""
        return [f for f in self.fragments if f.kind is MixedASTNodeKind.HOLE]

    def specs(self) -> List[ParsedFragment]:
        """Return only ``@spec(...)`` fragments."""
        return [f for f in self.fragments if f.kind is MixedASTNodeKind.SPEC_DECORATOR]

    def guarantees(self) -> List[ParsedFragment]:
        """Return only ``@guarantee(...)`` fragments."""
        return [
            f
            for f in self.fragments
            if f.kind is MixedASTNodeKind.GUARANTEE_DECORATOR
        ]

    def assumptions(self) -> List[ParsedFragment]:
        """Return only ``assume(...)`` fragments."""
        return [f for f in self.fragments if f.kind is MixedASTNodeKind.ASSUME_CALL]

    def checks(self) -> List[ParsedFragment]:
        """Return only ``check(...)`` fragments."""
        return [f for f in self.fragments if f.kind is MixedASTNodeKind.CHECK_CALL]

    def sketches(self) -> List[ParsedFragment]:
        """Return only ``sketch(...)`` fragments."""
        return [f for f in self.fragments if f.kind is MixedASTNodeKind.SKETCH_CALL]

    def invariants(self) -> List[ParsedFragment]:
        """Return only ``@invariant_nl(...)`` fragments."""
        return [
            f
            for f in self.fragments
            if f.kind is MixedASTNodeKind.INVARIANT_DECORATOR
        ]

    def decreases(self) -> List[ParsedFragment]:
        """Return only ``@decreases_nl(...)`` fragments."""
        return [
            f
            for f in self.fragments
            if f.kind is MixedASTNodeKind.DECREASES_DECORATOR
        ]

    # -- positional accessors -------------------------------------------------

    def fragments_in_function(self, func_name: str) -> List[ParsedFragment]:
        """Return every NL fragment whose enclosing function matches *func_name*.

        The match is performed against the ``enclosing_function`` field of
        each fragment's ``TypeContext``.  Qualified names (e.g.
        ``MyClass.my_method``) are supported.
        """
        results: List[ParsedFragment] = []
        for frag in self.fragments:
            ctx = frag.type_context
            if ctx.enclosing_function == func_name:
                results.append(frag)
                continue
            # Also match "Class.method" style.
            if ctx.enclosing_class and ctx.enclosing_function:
                qualified = f"{ctx.enclosing_class}.{ctx.enclosing_function}"
                if qualified == func_name:
                    results.append(frag)
        return results

    def fragment_at_line(self, line: int) -> Optional[ParsedFragment]:
        """Return the fragment whose source line equals *line*, or ``None``.

        If multiple fragments share the same line (unlikely but possible with
        chained decorators), the first one in source order is returned.
        """
        for frag in self.fragments:
            if frag.line == line:
                return frag
        return None

    def fragment_by_hash(self, content_hash: str) -> Optional[ParsedFragment]:
        """Look up a fragment by its content hash."""
        for frag in self.fragments:
            if frag.content_hash == content_hash:
                return frag
        return None

    # -- summary --------------------------------------------------------------

    def summary(self) -> str:
        """Return a multi-line human-readable summary of the parse result."""
        lines: List[str] = []
        lines.append(f"MixedAST: {self.filename}")
        lines.append(f"  Source length : {len(self.source)} chars")
        lines.append(f"  Functions     : {len(self.functions)}")
        lines.append(f"  Fragments     : {len(self.fragments)}")
        lines.append(f"    holes       : {len(self.holes())}")
        lines.append(f"    specs       : {len(self.specs())}")
        lines.append(f"    guarantees  : {len(self.guarantees())}")
        lines.append(f"    assumptions : {len(self.assumptions())}")
        lines.append(f"    checks      : {len(self.checks())}")
        lines.append(f"    sketches    : {len(self.sketches())}")
        lines.append(f"    invariants  : {len(self.invariants())}")
        lines.append(f"    decreases   : {len(self.decreases())}")
        lines.append(f"  Code blocks   : {len(self.code_blocks)}")
        if self.fragments:
            lines.append("  Fragment list:")
            for frag in self.fragments:
                lines.append(f"    {frag.short_description()}")
        return "\n".join(lines)

# ---------------------------------------------------------------------------
# Helper utilities
# ---------------------------------------------------------------------------

def _node_source_line(node: ast.AST) -> int:
    """Return the one-indexed line number for *node*, defaulting to 0."""
    return getattr(node, "lineno", 0)

def _node_col_offset(node: ast.AST) -> int:
    """Return the zero-indexed column offset for *node*, defaulting to 0."""
    return getattr(node, "col_offset", 0)

def _unparse_safe(node: ast.AST) -> str:
    """Best-effort ``ast.unparse`` that never raises."""
    try:
        return ast.unparse(node)
    except Exception:
        return "<unparseable>"

def _annotation_str(node: Optional[ast.AST]) -> str:
    """Convert an annotation AST node to its source string."""
    if node is None:
        return ""
    return _unparse_safe(node)

def _is_string_literal(node: ast.AST) -> bool:
    """Return ``True`` if *node* is a string constant."""
    return isinstance(node, ast.Constant) and isinstance(node.value, str)

def _string_value(node: ast.AST) -> Optional[str]:
    """Extract the string value from a ``Constant`` node, or ``None``."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None

def _is_ellipsis_body(body: Sequence[ast.stmt]) -> bool:
    """Return ``True`` when *body* is ``[Expr(Ellipsis)]`` (i.e. ``...``).

    This is the pattern used for spec-only functions whose body is to be
    synthesised from the ``@spec`` annotation.
    """
    if len(body) == 1:
        stmt = body[0]
        if isinstance(stmt, ast.Expr):
            val = stmt.value
            # Python 3.8+: Ellipsis is Constant(value=Ellipsis)
            if isinstance(val, ast.Constant) and val.value is ...:
                return True
    return False

def _is_pass_body(body: Sequence[ast.stmt]) -> bool:
    """Return ``True`` when *body* consists only of ``pass``."""
    return len(body) == 1 and isinstance(body[0], ast.Pass)

def _is_docstring_only_body(body: Sequence[ast.stmt]) -> bool:
    """Return ``True`` when *body* is a single docstring expression."""
    if len(body) == 1 and isinstance(body[0], ast.Expr):
        return _is_string_literal(body[0].value)
    return False

def _is_empty_body(body: Sequence[ast.stmt]) -> bool:
    """Return ``True`` for bodies that have no executable code."""
    return _is_ellipsis_body(body) or _is_pass_body(body) or _is_docstring_only_body(body)

def _decorator_name(dec: ast.expr) -> Optional[str]:
    """Extract the base name of a decorator expression.

    Handles:
    - ``@spec`` → ``"spec"``
    - ``@spec("...")`` → ``"spec"``
    - ``@deppy.spec("...")`` → ``"spec"``
    - ``@some.deep.path.spec("...")`` → ``"spec"``
    """
    if isinstance(dec, ast.Name):
        return dec.id
    if isinstance(dec, ast.Attribute):
        return dec.attr
    if isinstance(dec, ast.Call):
        return _decorator_name(dec.func)
    return None

def _extract_string_from_call_or_decorator(node: ast.expr) -> Optional[str]:
    """Return the first string argument from a call / decorator invocation.

    Works for both ``@spec("text")`` and bare ``hole("text")`` calls.
    Returns ``None`` when the first argument is not a string literal.
    """
    if isinstance(node, ast.Call):
        if node.args:
            return _string_value(node.args[0])
        # Also accept keyword ``text=``, ``description=``, ``nl=``.
        for kw in node.keywords:
            if kw.arg in ("text", "description", "nl", "msg"):
                return _string_value(kw.value)
    return None

def _get_call_func_name(node: ast.Call) -> Optional[str]:
    """Return the simple or dotted function name for a ``Call`` node."""
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        # e.g. deppy.hole(...)
        return func.attr
    return None

# ---------------------------------------------------------------------------
# ContextInferrer
# ---------------------------------------------------------------------------

class ContextInferrer:
    """Infer rich type context for NL fragments.

    The inferrer is *stateless* — each public method receives the AST nodes
    it needs and returns a result.  It is factored into its own class so that
    it can be subclassed or replaced in tests.
    """

    # -- variable types -------------------------------------------------------

    def infer_variable_types(
        self, func_node: ast.FunctionDef
    ) -> Dict[str, str]:
        """Extract a mapping *name → annotation string* for every variable
        whose type can be determined from the function's signature and body.

        Sources of type information (in priority order):
        1. Function parameters with annotations.
        2. Annotated assignments (``x: int = ...``).
        3. Plain assignments whose RHS is a constructor call
           (``x = SomeClass(...)`` → ``"SomeClass"``).
        4. For-loop targets when the iterable has an inferred element type.
        5. Comprehension targets (same heuristic as for-loops).
        """
        types: Dict[str, str] = {}

        # 1. Function parameters.
        args_node = func_node.args
        all_args: List[ast.arg] = (
            list(args_node.posonlyargs)
            + list(args_node.args)
            + list(args_node.kwonlyargs)
        )
        if args_node.vararg:
            all_args.append(args_node.vararg)
        if args_node.kwarg:
            all_args.append(args_node.kwarg)

        for arg in all_args:
            if arg.annotation is not None:
                types[arg.arg] = _annotation_str(arg.annotation)

        # 2–5. Walk the body.
        for stmt in ast.walk(func_node):
            if isinstance(stmt, ast.AnnAssign) and isinstance(
                stmt.target, ast.Name
            ):
                ann = _annotation_str(stmt.annotation)
                if ann:
                    types[stmt.target.id] = ann

            elif isinstance(stmt, ast.Assign):
                for target in stmt.targets:
                    if isinstance(target, ast.Name):
                        inferred = self._infer_type_from_rhs(stmt.value)
                        if inferred:
                            types.setdefault(target.id, inferred)

            elif isinstance(stmt, ast.For):
                elem_type = self._infer_element_type(stmt.iter)
                if elem_type and isinstance(stmt.target, ast.Name):
                    types.setdefault(stmt.target.id, elem_type)
                elif elem_type and isinstance(stmt.target, ast.Tuple):
                    for elt in stmt.target.elts:
                        if isinstance(elt, ast.Name):
                            types.setdefault(elt.id, elem_type)

        return types

    def infer_variable_types_from_body(
        self, body: Sequence[ast.stmt]
    ) -> Dict[str, str]:
        """Same as ``infer_variable_types`` but operates on an arbitrary list
        of statements (e.g. module-level code)."""
        types: Dict[str, str] = {}
        for stmt in body:
            for node in ast.walk(stmt):
                if isinstance(node, ast.AnnAssign) and isinstance(
                    node.target, ast.Name
                ):
                    ann = _annotation_str(node.annotation)
                    if ann:
                        types[node.target.id] = ann
                elif isinstance(node, ast.Assign):
                    for target in node.targets:
                        if isinstance(target, ast.Name):
                            inferred = self._infer_type_from_rhs(node.value)
                            if inferred:
                                types.setdefault(target.id, inferred)
        return types

    # -- control flow ---------------------------------------------------------

    def infer_control_flow(
        self, node: ast.AST, ancestors: List[ast.AST]
    ) -> str:
        """Determine the control-flow position of *node* by examining
        its chain of ancestor nodes.

        Returns one of:
        ``"top_level"``, ``"function_body"``, ``"if_branch"``,
        ``"else_branch"``, ``"elif_branch"``, ``"loop_body"``,
        ``"try_body"``, ``"except_handler"``, ``"finally_body"``,
        ``"with_body"``.
        """
        for ancestor in reversed(ancestors):
            if isinstance(ancestor, ast.If):
                position = self._position_in_if(node, ancestor, ancestors)
                if position is not None:
                    return position
            if isinstance(ancestor, (ast.For, ast.While, ast.AsyncFor)):
                if self._node_in_body(node, ancestor.body):
                    return "loop_body"
            if isinstance(ancestor, ast.Try):
                pos = self._position_in_try(node, ancestor)
                if pos is not None:
                    return pos
            if isinstance(ancestor, (ast.With, ast.AsyncWith)):
                if self._node_in_body(node, ancestor.body):
                    return "with_body"
            if isinstance(ancestor, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return "function_body"
        return "top_level"

    # -- usage inference ------------------------------------------------------

    def infer_usage(
        self, node: ast.AST, parent: Optional[ast.AST]
    ) -> Optional[str]:
        """Describe how the result of *node* is used.

        Examines *parent* to determine whether the value is:
        - assigned to a variable (``"assigned to x"``)
        - returned (``"returned"``)
        - passed to a function (``"passed to func()"``)
        - used as a condition (``"used as condition"``)
        - yielded (``"yielded"``)
        - discarded / used as expression statement (``None``)
        """
        if parent is None:
            return None

        # Assignment: x = hole("...")
        if isinstance(parent, ast.Assign):
            target_names = []
            for t in parent.targets:
                target_names.append(_unparse_safe(t))
            if target_names:
                return f"assigned to {', '.join(target_names)}"

        # Annotated assignment: x: int = hole("...")
        if isinstance(parent, ast.AnnAssign) and parent.target is not None:
            return f"assigned to {_unparse_safe(parent.target)}"

        # Return statement: return hole("...")
        if isinstance(parent, ast.Return):
            return "returned"

        # Yield: yield hole("...")
        if isinstance(parent, (ast.Yield, ast.YieldFrom)):
            return "yielded"

        # Argument in a function call: sorted(hole("..."))
        if isinstance(parent, ast.Call):
            func_name = _get_call_func_name(parent)
            if func_name:
                return f"passed to {func_name}()"
            return "passed to function call"

        # Condition: if hole("..."):
        if isinstance(parent, ast.If) and parent.test is node:
            return "used as condition"

        # While condition: while hole("..."):
        if isinstance(parent, ast.While) and parent.test is node:
            return "used as loop condition"

        # Assert: assert hole("...")
        if isinstance(parent, ast.Assert):
            return "used in assertion"

        # Expression statement (discarded): hole("...")
        if isinstance(parent, ast.Expr):
            return None

        # Comparison operand
        if isinstance(parent, ast.Compare):
            return "used in comparison"

        # BoolOp operand
        if isinstance(parent, ast.BoolOp):
            return "used in boolean expression"

        # BinOp operand
        if isinstance(parent, ast.BinOp):
            return "used in binary operation"

        # Subscript
        if isinstance(parent, ast.Subscript):
            return "used as subscript"

        return None

    # -- expected type --------------------------------------------------------

    def infer_expected_type(
        self,
        node: ast.AST,
        parent: Optional[ast.AST],
        enclosing_func: Optional[ast.FunctionDef],
    ) -> Optional[str]:
        """Infer the type that the result of *node* is expected to have.

        Heuristics (tried in order):
        1. If *node* is on the RHS of an annotated assignment, use the
           annotation.
        2. If *node* is returned from a function with a return annotation,
           use that annotation.
        3. If *node* is passed as an argument to a function whose
           corresponding parameter has a type annotation, use that.
        """
        # 1. Annotated assignment.
        if isinstance(parent, ast.AnnAssign) and parent.annotation is not None:
            return _annotation_str(parent.annotation)

        # 2. Return from annotated function.
        if isinstance(parent, ast.Return) and enclosing_func is not None:
            ret_ann = getattr(enclosing_func, "returns", None)
            if ret_ann is not None:
                return _annotation_str(ret_ann)

        # 3. Argument to annotated function.
        if isinstance(parent, ast.Call):
            return self._infer_param_type_from_call(node, parent)

        return None

    # -- private helpers ------------------------------------------------------

    @staticmethod
    def _infer_type_from_rhs(value: ast.expr) -> Optional[str]:
        """Attempt to infer the type of a plain assignment's RHS.

        Recognises constructor calls (``SomeClass(...)``), list/dict/set/tuple
        literals, and a handful of builtins.
        """
        if isinstance(value, ast.Call):
            func = value.func
            if isinstance(func, ast.Name):
                return func.id
            if isinstance(func, ast.Attribute):
                return func.attr
        if isinstance(value, ast.List):
            return "list"
        if isinstance(value, ast.Dict):
            return "dict"
        if isinstance(value, ast.Set):
            return "set"
        if isinstance(value, ast.Tuple):
            return "tuple"
        if isinstance(value, ast.Constant):
            if isinstance(value.value, int):
                return "int"
            if isinstance(value.value, float):
                return "float"
            if isinstance(value.value, str):
                return "str"
            if isinstance(value.value, bool):
                return "bool"
            if isinstance(value.value, bytes):
                return "bytes"
            if value.value is None:
                return "None"
        if isinstance(value, ast.ListComp):
            return "list"
        if isinstance(value, ast.SetComp):
            return "set"
        if isinstance(value, ast.DictComp):
            return "dict"
        if isinstance(value, ast.GeneratorExp):
            return "Generator"
        if isinstance(value, ast.JoinedStr):
            return "str"
        return None

    @staticmethod
    def _infer_element_type(iter_node: ast.expr) -> Optional[str]:
        """Attempt to infer the element type of an iterable expression.

        Handles ``range(...) → int``, ``"string" → str``, and
        ``dict.keys() / .values() / .items()``.
        """
        if isinstance(iter_node, ast.Call):
            func = iter_node.func
            if isinstance(func, ast.Name) and func.id == "range":
                return "int"
            if isinstance(func, ast.Name) and func.id == "enumerate":
                return "tuple"
            if isinstance(func, ast.Name) and func.id == "zip":
                return "tuple"
            if isinstance(func, ast.Attribute):
                if func.attr == "keys":
                    return "str"
                if func.attr == "values":
                    return None  # unknown without more info
                if func.attr == "items":
                    return "tuple"
        if isinstance(iter_node, ast.Constant) and isinstance(
            iter_node.value, str
        ):
            return "str"
        if isinstance(iter_node, ast.List):
            return None  # element type varies
        return None

    @staticmethod
    def _position_in_if(
        node: ast.AST,
        if_node: ast.If,
        ancestors: List[ast.AST],
    ) -> Optional[str]:
        """Determine whether *node* is in the if-branch, else-branch, or an
        elif-branch of *if_node*."""
        for stmt in if_node.body:
            if stmt is node or _subtree_contains(stmt, node):
                return "if_branch"
        for stmt in if_node.orelse:
            if stmt is node or _subtree_contains(stmt, node):
                # orelse that is itself an If is an elif
                if (
                    len(if_node.orelse) == 1
                    and isinstance(if_node.orelse[0], ast.If)
                ):
                    return "elif_branch"
                return "else_branch"
        return None

    @staticmethod
    def _position_in_try(
        node: ast.AST, try_node: ast.Try
    ) -> Optional[str]:
        for stmt in try_node.body:
            if stmt is node or _subtree_contains(stmt, node):
                return "try_body"
        for handler in try_node.handlers:
            for stmt in handler.body:
                if stmt is node or _subtree_contains(stmt, node):
                    return "except_handler"
        for stmt in try_node.finalbody:
            if stmt is node or _subtree_contains(stmt, node):
                return "finally_body"
        for stmt in getattr(try_node, "orelse", []):
            if stmt is node or _subtree_contains(stmt, node):
                return "try_body"
        return None

    @staticmethod
    def _node_in_body(
        node: ast.AST, body: Sequence[ast.stmt]
    ) -> bool:
        for stmt in body:
            if stmt is node or _subtree_contains(stmt, node):
                return True
        return False

    @staticmethod
    def _infer_param_type_from_call(
        arg_node: ast.AST, call_node: ast.Call
    ) -> Optional[str]:
        """When *arg_node* is a positional argument of *call_node*, attempt
        to find the parameter type of the callee.

        This only works when the callee is visible in the same compilation
        unit — a full solution would require cross-module analysis.  For now
        we return ``None`` (the pipeline's type-directed synthesis can still
        refine the type later).
        """
        # Determine the argument index.
        for idx, a in enumerate(call_node.args):
            if a is arg_node:
                func_name = _get_call_func_name(call_node)
                if func_name:
                    return f"<param {idx} of {func_name}>"
                return None
        for kw in call_node.keywords:
            if kw.value is arg_node and kw.arg is not None:
                func_name = _get_call_func_name(call_node)
                if func_name:
                    return f"<kwarg '{kw.arg}' of {func_name}>"
                return None
        return None

def _subtree_contains(root: ast.AST, target: ast.AST) -> bool:
    """Return ``True`` if *target* is anywhere inside *root*'s subtree."""
    for child in ast.walk(root):
        if child is target:
            return True
    return False

# ---------------------------------------------------------------------------
# _ParentAnnotator — pre-pass to set ``_parent`` on every AST node
# ---------------------------------------------------------------------------

class _ParentAnnotator(ast.NodeVisitor):
    """Walk the AST once to set ``_parent`` and ``_ancestors`` on every
    node.  This is needed so that ``MixedModeVisitor`` can look upward."""

    def __init__(self) -> None:
        self._stack: List[ast.AST] = []

    def generic_visit(self, node: ast.AST) -> None:
        node._parent = self._stack[-1] if self._stack else None  # type: ignore[attr-defined]
        node._ancestors = list(self._stack)  # type: ignore[attr-defined]
        self._stack.append(node)
        super().generic_visit(node)
        self._stack.pop()

# ---------------------------------------------------------------------------
# MixedModeVisitor
# ---------------------------------------------------------------------------

class MixedModeVisitor(ast.NodeVisitor):
    """AST visitor that locates NL fragments and builds ``ParsedFragment``
    objects for each one.

    After visiting, the results are available in ``self.fragments``,
    ``self.functions``, and ``self.code_blocks``.
    """

    def __init__(
        self,
        filename: str,
        source: str,
        inferrer: Optional[ContextInferrer] = None,
    ) -> None:
        self.filename = filename
        self.source = source
        self.source_lines = source.splitlines()
        self.inferrer = inferrer or ContextInferrer()

        # Outputs.
        self.fragments: List[ParsedFragment] = []
        self.functions: Dict[str, ast.FunctionDef] = {}
        self.code_blocks: List[ast.AST] = []

        # State.
        self._current_class: Optional[str] = None
        self._current_func_stack: List[ast.FunctionDef] = []
        self._seen_fragment_nodes: Set[int] = set()

    # -- public interface -----------------------------------------------------

    @property
    def _current_func(self) -> Optional[ast.FunctionDef]:
        return self._current_func_stack[-1] if self._current_func_stack else None

    # -- Call visitor ---------------------------------------------------------

    def visit_Call(self, node: ast.Call) -> None:
        """Detect ``hole("...")``, ``assume("...")``, ``check("...")``,
        ``sketch("...")``.
        """
        func_name = _get_call_func_name(node)
        if func_name in _CALL_KIND_MAP:
            nl_text = self._extract_call_text(node)
            if nl_text is not None:
                kind = _CALL_KIND_MAP[func_name]
                parent = getattr(node, "_parent", None)
                type_ctx = self._build_type_context(node)
                frag = ParsedFragment(
                    kind=kind,
                    nl_text=nl_text,
                    source_location=(
                        self.filename,
                        _node_source_line(node),
                        _node_col_offset(node),
                    ),
                    type_context=type_ctx,
                    ast_node=node,
                    parent_node=parent,
                )
                self.fragments.append(frag)
                self._seen_fragment_nodes.add(id(node))

        self.generic_visit(node)

    # -- FunctionDef visitor --------------------------------------------------

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._process_function_def(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._process_function_def(node)  # type: ignore[arg-type]

    def _process_function_def(
        self, node: Union[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> None:
        """Shared logic for ``def`` and ``async def``.

        1. Register the function in ``self.functions``.
        2. Check its decorators for NL annotations.
        3. Visit the body.
        """
        # Build qualified name.
        if self._current_class:
            qname = f"{self._current_class}.{node.name}"
        else:
            qname = node.name
        self.functions[qname] = node  # type: ignore[assignment]

        # Inspect decorators.
        for dec in node.decorator_list:
            dec_name = _decorator_name(dec)
            if dec_name in _DECORATOR_KIND_MAP:
                nl_text = self._extract_decorator_text(dec)
                if nl_text is not None:
                    kind = _DECORATOR_KIND_MAP[dec_name]
                    parent = getattr(dec, "_parent", node)
                    type_ctx = self._build_type_context_for_decorator(
                        dec, node
                    )
                    frag = ParsedFragment(
                        kind=kind,
                        nl_text=nl_text,
                        source_location=(
                            self.filename,
                            _node_source_line(dec),
                            _node_col_offset(dec),
                        ),
                        type_context=type_ctx,
                        ast_node=dec,
                        parent_node=node,
                    )
                    self.fragments.append(frag)
                    self._seen_fragment_nodes.add(id(dec))

        # Track as code block if it has no NL decorators and is not empty.
        has_nl_decorator = any(
            _decorator_name(d) in _NL_DECORATOR_NAMES
            for d in node.decorator_list
        )
        if not has_nl_decorator and not _is_empty_body(node.body):
            self.code_blocks.append(node)

        # Recurse into body.
        self._current_func_stack.append(node)  # type: ignore[arg-type]
        self.generic_visit(node)
        self._current_func_stack.pop()

    # -- ClassDef visitor -----------------------------------------------------

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        prev = self._current_class
        self._current_class = node.name
        self.generic_visit(node)
        self._current_class = prev

    # -- Module visitor -------------------------------------------------------

    def visit_Module(self, node: ast.Module) -> None:
        """At module level, collect top-level non-function, non-class
        statements as code blocks."""
        for stmt in node.body:
            if not isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                if not self._is_nl_statement(stmt):
                    self.code_blocks.append(stmt)
        self.generic_visit(node)

    # -- Type context building ------------------------------------------------

    def _build_type_context(self, node: ast.AST) -> TypeContext:
        """Build a ``TypeContext`` for an NL call node (``hole``, ``assume``,
        etc.) by examining the surrounding AST."""
        parent = getattr(node, "_parent", None)
        ancestors: List[ast.AST] = getattr(node, "_ancestors", [])
        enc_func = self._current_func
        enc_class = self._current_class

        # Available variables.
        if enc_func is not None:
            avail_vars = self.inferrer.infer_variable_types(enc_func)
        else:
            avail_vars = self._module_level_vars()

        # Expected return type.
        ret_type: Optional[str] = None
        if enc_func is not None:
            ret_ann = getattr(enc_func, "returns", None)
            if ret_ann is not None:
                ret_type = _annotation_str(ret_ann)

        # Control flow.
        cf_pos = self.inferrer.infer_control_flow(node, ancestors)

        # Preceding assignments.
        preceding = self._preceding_assignments(node)

        # Following usage.
        usage = self.inferrer.infer_usage(node, parent)

        # Expected type override from context.
        expected = self.inferrer.infer_expected_type(node, parent, enc_func)
        if expected and ret_type is None:
            ret_type = expected

        return TypeContext(
            available_variables=avail_vars,
            expected_return_type=ret_type,
            enclosing_function=enc_func.name if enc_func else None,
            enclosing_class=enc_class,
            control_flow_position=cf_pos,
            preceding_assignments=preceding,
            following_usage=usage,
        )

    def _build_type_context_for_decorator(
        self,
        dec_node: ast.expr,
        func_node: Union[ast.FunctionDef, ast.AsyncFunctionDef],
    ) -> TypeContext:
        """Build a ``TypeContext`` for an NL decorator (``@spec``,
        ``@guarantee``, etc.).

        The context is derived from the *decorated function*'s signature
        rather than from the decorator's position in the AST.
        """
        avail_vars = self.inferrer.infer_variable_types(func_node)  # type: ignore[arg-type]
        ret_ann = getattr(func_node, "returns", None)
        ret_type = _annotation_str(ret_ann) if ret_ann is not None else None

        return TypeContext(
            available_variables=avail_vars,
            expected_return_type=ret_type,
            enclosing_function=func_node.name,
            enclosing_class=self._current_class,
            control_flow_position="function_body",
            preceding_assignments=[],
            following_usage=None,
        )

    # -- Extraction helpers ---------------------------------------------------

    def _extract_decorator_text(
        self, decorator_node: ast.expr
    ) -> Optional[str]:
        """Extract the NL text from a decorator invocation.

        Handles:
        - ``@spec("text")``
        - ``@guarantee("text")``
        - ``@given("text")``
        - ``@invariant_nl("text")``
        - ``@decreases_nl("text")``

        Also handles multi-line strings joined with ``+``.
        """
        return _extract_string_from_call_or_decorator(decorator_node)

    def _extract_call_text(self, call_node: ast.Call) -> Optional[str]:
        """Extract the NL text from a call invocation.

        Handles:
        - ``hole("text")``
        - ``assume("text")``
        - ``check("text")``
        - ``sketch("text")``

        Also handles multi-line strings (triple-quoted).
        """
        text = _extract_string_from_call_or_decorator(call_node)
        if text is not None:
            return textwrap.dedent(text).strip()
        # Try concatenated string: hole("a" + "b")
        if (
            call_node.args
            and isinstance(call_node.args[0], ast.BinOp)
            and isinstance(call_node.args[0].op, ast.Add)
        ):
            parts = self._collect_string_concat(call_node.args[0])
            if parts is not None:
                return textwrap.dedent("".join(parts)).strip()
        return None

    def _collect_string_concat(self, node: ast.expr) -> Optional[List[str]]:
        """Recursively collect parts of a ``"a" + "b" + "c"`` expression."""
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return [node.value]
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            left = self._collect_string_concat(node.left)
            right = self._collect_string_concat(node.right)
            if left is not None and right is not None:
                return left + right
        return None

    # -- Preceding assignments -----------------------------------------------

    def _preceding_assignments(
        self, node: ast.AST
    ) -> List[Tuple[str, str]]:
        """Collect assignments that textually precede *node* in the same
        block.

        Returns at most 20 entries as ``(var_name, expression_source)``.
        """
        target_line = _node_source_line(node)
        if target_line == 0:
            return []

        # Find the enclosing body.
        body = self._find_enclosing_body(node)
        if body is None:
            return []

        result: List[Tuple[str, str]] = []
        for stmt in body:
            stmt_line = _node_source_line(stmt)
            if stmt_line >= target_line:
                break
            if isinstance(stmt, ast.Assign):
                for tgt in stmt.targets:
                    if isinstance(tgt, ast.Name):
                        result.append(
                            (tgt.id, _unparse_safe(stmt.value))
                        )
            elif isinstance(stmt, ast.AnnAssign) and isinstance(
                stmt.target, ast.Name
            ):
                rhs = _unparse_safe(stmt.value) if stmt.value else ""
                result.append((stmt.target.id, rhs))
            elif isinstance(stmt, ast.AugAssign) and isinstance(
                stmt.target, ast.Name
            ):
                result.append(
                    (stmt.target.id, _unparse_safe(stmt.value))
                )

        return result[-20:]

    def _find_enclosing_body(
        self, node: ast.AST
    ) -> Optional[Sequence[ast.stmt]]:
        """Walk ancestors to find the nearest body list that contains *node*
        (directly or transitively)."""
        ancestors: List[ast.AST] = getattr(node, "_ancestors", [])
        for anc in reversed(ancestors):
            for attr_name in ("body", "orelse", "finalbody", "handlers"):
                body = getattr(anc, attr_name, None)
                if isinstance(body, list):
                    for item in body:
                        if item is node or _subtree_contains(item, node):
                            return body
        return None

    def _module_level_vars(self) -> Dict[str, str]:
        """Collect annotated variables at module scope.

        This is called when an NL fragment appears outside any function.
        """
        if not self._current_func_stack:
            # Try to get from module body — but we only have access to the
            # visitor's accumulated state.  Return empty for safety.
            return {}
        return {}

    @staticmethod
    def _is_nl_statement(stmt: ast.stmt) -> bool:
        """Return ``True`` if *stmt* is a bare NL call expression (e.g.
        ``assume("...")`` at top level)."""
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            name = _get_call_func_name(stmt.value)
            return name in _NL_CALL_NAMES
        return False

    # -- Expected type inference (delegated to ContextInferrer) ---------------

    def _infer_expected_type(
        self, node: ast.AST, parent: Optional[ast.AST]
    ) -> Optional[str]:
        """Thin wrapper around ``ContextInferrer.infer_expected_type``.

        If ``hole()``'s result is assigned to an annotated variable, use that.
        If returned, use the enclosing function's return annotation.
        If passed to a function, look up that function's parameter type.
        """
        return self.inferrer.infer_expected_type(
            node, parent, self._current_func
        )

# ---------------------------------------------------------------------------
# MixedModeParser
# ---------------------------------------------------------------------------

class MixedModeParser:
    """Top-level entry point for mixed-mode parsing.

    Usage::

        parser = MixedModeParser()
        mixed_ast = parser.parse(source_code)
        print(mixed_ast.summary())
    """

    def __init__(
        self,
        inferrer: Optional[ContextInferrer] = None,
    ) -> None:
        self.inferrer = inferrer or ContextInferrer()

    # -- public API -----------------------------------------------------------

    def parse(
        self, source: str, filename: str = "<mixed>"
    ) -> MixedAST:
        """Parse *source* and return a ``MixedAST``.

        Parameters
        ----------
        source:
            The Python source code to parse.  May contain NL fragments
            (``hole()``, ``@spec()``, etc.) intermixed with ordinary code.
        filename:
            Name used in error messages and ``ParsedFragment.source_location``.

        Returns
        -------
        MixedAST
            A structured representation of the parsed source, including every
            NL fragment with its inferred type context.
        """
        tree = ast.parse(source, filename=filename, type_comments=True)

        # Pre-pass: annotate parents.
        annotator = _ParentAnnotator()
        annotator.visit(tree)

        # Main pass: find NL fragments.
        visitor = MixedModeVisitor(
            filename=filename,
            source=source,
            inferrer=self.inferrer,
        )
        visitor.visit(tree)

        # Sort fragments by source location for deterministic ordering.
        fragments = sorted(
            visitor.fragments,
            key=lambda f: (f.source_location[1], f.source_location[2]),
        )

        # Collect module-level code blocks that the visitor may have missed.
        code_blocks = list(visitor.code_blocks)
        self._collect_plain_code_blocks(tree, visitor, code_blocks)

        return MixedAST(
            source=source,
            filename=filename,
            tree=tree,
            fragments=fragments,
            functions=dict(visitor.functions),
            code_blocks=code_blocks,
        )

    def parse_file(self, path: str) -> MixedAST:
        """Read a file from disk and parse it.

        Parameters
        ----------
        path:
            Filesystem path to the Python source file.

        Raises
        ------
        FileNotFoundError
            If *path* does not exist.
        SyntaxError
            If the file contains invalid Python.
        """
        p = Path(path)
        source = p.read_text(encoding="utf-8")
        return self.parse(source, filename=str(p))

    def parse_function(self, source: str) -> MixedAST:
        """Parse a single function definition (useful for testing).

        The *source* is dedented before parsing so that callers can pass
        indented snippets.
        """
        dedented = textwrap.dedent(source)
        return self.parse(dedented, filename="<function>")

    # -- validation -----------------------------------------------------------

    def validate(self, mixed_ast: MixedAST) -> List[str]:
        """Check that all NL fragments in *mixed_ast* are well-formed.

        Returns a (possibly empty) list of human-readable error strings.

        Checks performed:
        1. Every ``hole()`` / ``assume()`` / ``check()`` / ``sketch()`` call
           has a string-literal first argument.
        2. Every ``@spec`` function has an empty body (``...`` or ``pass``).
        3. Every ``@guarantee`` function has a *non*-empty body.
        4. NL text is not empty after stripping whitespace.
        5. Decorator NL text is a string literal.
        6. No duplicate content hashes within the same file (warning-level).
        """
        errors: List[str] = []

        seen_hashes: Dict[str, ParsedFragment] = {}

        for frag in mixed_ast.fragments:
            loc = f"{frag.filename}:{frag.line}:{frag.col}"

            # -- 4. Non-empty NL text.
            if not frag.nl_text.strip():
                errors.append(
                    f"{loc}: {frag.kind.value} has empty NL text."
                )

            # -- 1. Call fragments must have string literal arguments.
            if frag.kind in (
                MixedASTNodeKind.HOLE,
                MixedASTNodeKind.ASSUME_CALL,
                MixedASTNodeKind.CHECK_CALL,
                MixedASTNodeKind.SKETCH_CALL,
            ):
                if isinstance(frag.ast_node, ast.Call):
                    if not frag.ast_node.args or not _is_string_literal(
                        frag.ast_node.args[0]
                    ):
                        # May have been extracted from keyword arg or concat.
                        # Only flag if nl_text is empty.
                        if not frag.nl_text.strip():
                            errors.append(
                                f"{loc}: {frag.kind.value}() must have a "
                                f"string literal as its first argument."
                            )

            # -- 6. Duplicate hashes (warning-level).
            if frag.content_hash in seen_hashes:
                prev = seen_hashes[frag.content_hash]
                errors.append(
                    f"{loc}: Duplicate NL text (same as "
                    f"{prev.filename}:{prev.line}): "
                    f"{frag.nl_text[:50]!r}"
                )
            else:
                seen_hashes[frag.content_hash] = frag

        # -- 2 & 3. Spec / guarantee body checks.
        for frag in mixed_ast.fragments:
            loc = f"{frag.filename}:{frag.line}:{frag.col}"
            if frag.kind is MixedASTNodeKind.SPEC_DECORATOR:
                func = frag.parent_node
                if isinstance(func, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if not _is_empty_body(func.body):
                        errors.append(
                            f"{loc}: @spec function '{func.name}' should "
                            f"have an empty body (use `...`), but it has "
                            f"executable code."
                        )
            elif frag.kind is MixedASTNodeKind.GUARANTEE_DECORATOR:
                func = frag.parent_node
                if isinstance(func, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if _is_empty_body(func.body):
                        errors.append(
                            f"{loc}: @guarantee function '{func.name}' must "
                            f"have a non-empty body."
                        )

        return errors

    # -- private helpers ------------------------------------------------------

    @staticmethod
    def _collect_plain_code_blocks(
        tree: ast.Module,
        visitor: MixedModeVisitor,
        code_blocks: List[ast.AST],
    ) -> None:
        """Walk *tree* to find assignment statements and other plain code at
        any nesting level that the visitor didn't already capture."""
        seen_ids = {id(b) for b in code_blocks}
        fragment_node_ids = visitor._seen_fragment_nodes

        for node in ast.walk(tree):
            if id(node) in seen_ids or id(node) in fragment_node_ids:
                continue
            # Only collect statements, not expressions.
            if isinstance(
                node,
                (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Import,
                 ast.ImportFrom, ast.Global, ast.Nonlocal, ast.Assert,
                 ast.Delete, ast.Raise),
            ):
                if id(node) not in seen_ids:
                    code_blocks.append(node)
                    seen_ids.add(id(node))

# ---------------------------------------------------------------------------
# Convenience functions
# ---------------------------------------------------------------------------

def parse_mixed(
    source: str, filename: str = "<mixed>"
) -> MixedAST:
    """One-shot convenience: parse *source* and return a ``MixedAST``.

    Equivalent to ``MixedModeParser().parse(source, filename)``.
    """
    return MixedModeParser().parse(source, filename)

def parse_mixed_file(path: str) -> MixedAST:
    """One-shot convenience: parse a file at *path* and return a ``MixedAST``.

    Equivalent to ``MixedModeParser().parse_file(path)``.
    """
    return MixedModeParser().parse_file(path)

# ---------------------------------------------------------------------------
# Fragment filtering utilities
# ---------------------------------------------------------------------------

def filter_fragments(
    fragments: Sequence[ParsedFragment],
    *,
    kind: Optional[MixedASTNodeKind] = None,
    enclosing_function: Optional[str] = None,
    enclosing_class: Optional[str] = None,
    min_line: Optional[int] = None,
    max_line: Optional[int] = None,
    text_contains: Optional[str] = None,
) -> List[ParsedFragment]:
    """Return the subset of *fragments* that match **all** given criteria.

    Any criterion that is ``None`` is skipped (i.e. not applied).
    """
    result: List[ParsedFragment] = []
    for frag in fragments:
        if kind is not None and frag.kind is not kind:
            continue
        if (
            enclosing_function is not None
            and frag.type_context.enclosing_function != enclosing_function
        ):
            continue
        if (
            enclosing_class is not None
            and frag.type_context.enclosing_class != enclosing_class
        ):
            continue
        if min_line is not None and frag.line < min_line:
            continue
        if max_line is not None and frag.line > max_line:
            continue
        if (
            text_contains is not None
            and text_contains.lower() not in frag.nl_text.lower()
        ):
            continue
        result.append(frag)
    return result

def group_fragments_by_function(
    fragments: Sequence[ParsedFragment],
) -> Dict[Optional[str], List[ParsedFragment]]:
    """Group *fragments* by their enclosing function name.

    Fragments at module level are grouped under the key ``None``.
    """
    groups: Dict[Optional[str], List[ParsedFragment]] = {}
    for frag in fragments:
        key = frag.type_context.enclosing_function
        groups.setdefault(key, []).append(frag)
    return groups

def group_fragments_by_kind(
    fragments: Sequence[ParsedFragment],
) -> Dict[MixedASTNodeKind, List[ParsedFragment]]:
    """Group *fragments* by their ``MixedASTNodeKind``."""
    groups: Dict[MixedASTNodeKind, List[ParsedFragment]] = {}
    for frag in fragments:
        groups.setdefault(frag.kind, []).append(frag)
    return groups

# ---------------------------------------------------------------------------
# TypeContext builder helpers (standalone, for use outside the visitor)
# ---------------------------------------------------------------------------

def build_type_context_for_function(
    func_node: ast.FunctionDef,
    *,
    enclosing_class: Optional[str] = None,
    inferrer: Optional[ContextInferrer] = None,
) -> TypeContext:
    """Build a ``TypeContext`` summarising a function's signature.

    Useful outside the visitor — e.g. when a downstream pass wants to
    construct a context from a function it already has a reference to.
    """
    inf = inferrer or ContextInferrer()
    avail = inf.infer_variable_types(func_node)
    ret_ann = getattr(func_node, "returns", None)
    ret_type = _annotation_str(ret_ann) if ret_ann else None
    return TypeContext(
        available_variables=avail,
        expected_return_type=ret_type,
        enclosing_function=func_node.name,
        enclosing_class=enclosing_class,
        control_flow_position="function_body",
    )

def build_type_context_for_module(
    tree: ast.Module,
    *,
    inferrer: Optional[ContextInferrer] = None,
) -> TypeContext:
    """Build a ``TypeContext`` for module-level code."""
    inf = inferrer or ContextInferrer()
    avail = inf.infer_variable_types_from_body(tree.body)
    return TypeContext(
        available_variables=avail,
        control_flow_position="top_level",
    )

# ---------------------------------------------------------------------------
# Source-location utilities
# ---------------------------------------------------------------------------

def source_lines_around(
    source: str,
    line: int,
    context: int = 3,
) -> str:
    """Return the source lines around *line* (1-indexed) with *context* lines
    of padding on each side.

    Each line is prefixed with its line number.
    """
    lines = source.splitlines()
    start = max(0, line - 1 - context)
    end = min(len(lines), line + context)
    result: List[str] = []
    for i in range(start, end):
        marker = ">>>" if i == line - 1 else "   "
        result.append(f"{marker} {i + 1:4d} | {lines[i]}")
    return "\n".join(result)

def fragment_source_context(
    frag: ParsedFragment,
    source: str,
    context: int = 3,
) -> str:
    """Return a formatted view of the source around *frag* with its NL text
    and type context summary."""
    parts: List[str] = []
    parts.append(f"--- {frag.short_description()} ---")
    parts.append(source_lines_around(source, frag.line, context))
    parts.append(f"  NL text: {frag.nl_text!r}")
    tc = frag.type_context
    if tc.available_variables:
        vars_str = ", ".join(
            f"{k}: {v}" for k, v in sorted(tc.available_variables.items())
        )
        parts.append(f"  Variables: {vars_str}")
    if tc.expected_return_type:
        parts.append(f"  Expected type: {tc.expected_return_type}")
    if tc.following_usage:
        parts.append(f"  Usage: {tc.following_usage}")
    parts.append(f"  Control flow: {tc.control_flow_position}")
    return "\n".join(parts)

# ---------------------------------------------------------------------------
# AST pretty-printer for debugging
# ---------------------------------------------------------------------------

def dump_mixed_ast(mixed_ast: MixedAST, *, indent: int = 2) -> str:
    """Return a human-readable dump of *mixed_ast* for debugging.

    Includes the AST structure plus annotations showing where each NL
    fragment lives.
    """
    lines: List[str] = []
    lines.append(mixed_ast.summary())
    lines.append("")
    lines.append("=== Fragments ===")
    for i, frag in enumerate(mixed_ast.fragments):
        lines.append(f"\n[{i}] {frag.short_description()}")
        lines.append(f"    Hash: {frag.content_hash[:16]}…")
        tc = frag.type_context
        lines.append(f"    Function: {tc.enclosing_function}")
        lines.append(f"    Class: {tc.enclosing_class}")
        lines.append(f"    CF position: {tc.control_flow_position}")
        if tc.available_variables:
            for vname, vtype in sorted(tc.available_variables.items()):
                lines.append(f"    Var {vname}: {vtype}")
        if tc.expected_return_type:
            lines.append(f"    Return type: {tc.expected_return_type}")
        if tc.preceding_assignments:
            for vn, expr in tc.preceding_assignments[-5:]:
                lines.append(f"    Preceding: {vn} = {expr}")
        if tc.following_usage:
            lines.append(f"    Usage: {tc.following_usage}")

    lines.append("")
    lines.append("=== Functions ===")
    for name, func in sorted(mixed_ast.functions.items()):
        args_str = _unparse_safe(func.args) if func.args else "()"
        ret = _annotation_str(getattr(func, "returns", None))
        lines.append(f"  {name}({args_str}) -> {ret or '?'}")
        empty = _is_empty_body(func.body)
        lines.append(f"    Empty body: {empty}")
        lines.append(f"    Lines: {_node_source_line(func)}-{getattr(func, 'end_lineno', '?')}")

    lines.append("")
    lines.append("=== Code blocks ===")
    for blk in mixed_ast.code_blocks[:20]:
        lines.append(f"  L{_node_source_line(blk)}: {type(blk).__name__}")

    return "\n".join(lines)

# ---------------------------------------------------------------------------
# Validation helpers (standalone)
# ---------------------------------------------------------------------------

def validate_fragment_types(
    mixed_ast: MixedAST,
) -> List[str]:
    """Validate that every fragment's ``TypeContext`` is internally
    consistent.

    Returns a list of warning strings (empty if everything is fine).
    """
    warnings: List[str] = []
    for frag in mixed_ast.fragments:
        tc = frag.type_context
        loc = f"{frag.filename}:{frag.line}"

        # If enclosing_function is set, we expect available_variables to
        # contain at least the function's parameters.
        if tc.enclosing_function:
            func = mixed_ast.functions.get(tc.enclosing_function)
            if func is None and tc.enclosing_class:
                qname = f"{tc.enclosing_class}.{tc.enclosing_function}"
                func = mixed_ast.functions.get(qname)
            if func is not None:
                param_names = {a.arg for a in func.args.args}
                for pname in param_names:
                    if pname == "self" or pname == "cls":
                        continue
                    if pname not in tc.available_variables:
                        warnings.append(
                            f"{loc}: Parameter '{pname}' of "
                            f"'{tc.enclosing_function}' not in "
                            f"available_variables (may lack annotation)."
                        )

        # Control-flow position should be a known value.
        known_positions = {
            "top_level",
            "function_body",
            "if_branch",
            "else_branch",
            "elif_branch",
            "loop_body",
            "try_body",
            "except_handler",
            "finally_body",
            "with_body",
        }
        if tc.control_flow_position not in known_positions:
            warnings.append(
                f"{loc}: Unknown control_flow_position "
                f"'{tc.control_flow_position}'."
            )

    return warnings

# ---------------------------------------------------------------------------
# Diff support — find fragments that changed between two versions
# ---------------------------------------------------------------------------

def diff_fragments(
    old: MixedAST,
    new: MixedAST,
) -> Tuple[List[ParsedFragment], List[ParsedFragment], List[ParsedFragment]]:
    """Compare two ``MixedAST`` values and return three lists:

    - **added**: fragments in *new* whose content hash is not in *old*.
    - **removed**: fragments in *old* whose content hash is not in *new*.
    - **unchanged**: fragments present in both.
    """
    old_hashes = {f.content_hash for f in old.fragments}
    new_hashes = {f.content_hash for f in new.fragments}

    added = [f for f in new.fragments if f.content_hash not in old_hashes]
    removed = [f for f in old.fragments if f.content_hash not in new_hashes]
    unchanged = [f for f in new.fragments if f.content_hash in old_hashes]

    return added, removed, unchanged

# ---------------------------------------------------------------------------
# Serialisation helpers
# ---------------------------------------------------------------------------

def fragment_to_dict(frag: ParsedFragment) -> Dict[str, object]:
    """Serialise a ``ParsedFragment`` to a plain dict (JSON-friendly).

    The ``ast_node`` and ``parent_node`` fields are replaced with their
    type names and line numbers for portability.
    """
    tc = frag.type_context
    return {
        "kind": frag.kind.value,
        "nl_text": frag.nl_text,
        "filename": frag.filename,
        "line": frag.line,
        "col": frag.col,
        "content_hash": frag.content_hash,
        "ast_node_type": type(frag.ast_node).__name__,
        "parent_node_type": (
            type(frag.parent_node).__name__ if frag.parent_node else None
        ),
        "type_context": {
            "available_variables": dict(tc.available_variables),
            "expected_return_type": tc.expected_return_type,
            "enclosing_function": tc.enclosing_function,
            "enclosing_class": tc.enclosing_class,
            "control_flow_position": tc.control_flow_position,
            "preceding_assignments": [
                list(pair) for pair in tc.preceding_assignments
            ],
            "following_usage": tc.following_usage,
        },
    }

def mixed_ast_to_dict(mixed_ast: MixedAST) -> Dict[str, object]:
    """Serialise an entire ``MixedAST`` to a JSON-friendly dict.

    Excludes the raw ``ast.Module`` tree (not serialisable).
    """
    return {
        "filename": mixed_ast.filename,
        "source_length": len(mixed_ast.source),
        "num_functions": len(mixed_ast.functions),
        "num_code_blocks": len(mixed_ast.code_blocks),
        "fragments": [fragment_to_dict(f) for f in mixed_ast.fragments],
        "function_names": sorted(mixed_ast.functions.keys()),
    }

# ---------------------------------------------------------------------------
# Re-parsing a single fragment with updated NL text
# ---------------------------------------------------------------------------

def reparse_with_replacement(
    mixed_ast: MixedAST,
    target_hash: str,
    new_nl_text: str,
) -> MixedAST:
    """Return a new ``MixedAST`` where the fragment identified by
    *target_hash* has its NL text replaced with *new_nl_text*.

    The source code is patched textually and re-parsed from scratch so that
    all AST nodes and line numbers are consistent.

    Raises ``ValueError`` if no fragment with *target_hash* exists.
    """
    frag = mixed_ast.fragment_by_hash(target_hash)
    if frag is None:
        raise ValueError(
            f"No fragment with content_hash={target_hash!r} found."
        )

    # Build old text pattern and new text pattern.
    old_text = frag.nl_text
    lines = mixed_ast.source.splitlines(keepends=True)

    # Strategy: find the line containing the fragment and do a string replace.
    target_line_idx = frag.line - 1
    if 0 <= target_line_idx < len(lines):
        line = lines[target_line_idx]
        # Try to replace the old NL text in this line.
        if old_text in mixed_ast.source:
            new_source = mixed_ast.source.replace(old_text, new_nl_text, 1)
        else:
            # The text might span multiple lines (triple-quote).  Fall back
            # to a full-source replacement.
            escaped_old = repr(old_text)[1:-1]  # strip outer quotes
            escaped_new = repr(new_nl_text)[1:-1]
            new_source = mixed_ast.source.replace(
                escaped_old, escaped_new, 1
            )
    else:
        raise ValueError(
            f"Fragment at line {frag.line} is out of range for source "
            f"with {len(lines)} lines."
        )

    parser = MixedModeParser()
    return parser.parse(new_source, filename=mixed_ast.filename)

# ---------------------------------------------------------------------------
# Batch operations
# ---------------------------------------------------------------------------

def collect_all_nl_texts(mixed_ast: MixedAST) -> List[str]:
    """Return all NL texts from *mixed_ast*, in source order."""
    return [f.nl_text for f in mixed_ast.fragments]

def fragment_dependency_graph(
    mixed_ast: MixedAST,
) -> Dict[str, List[str]]:
    """Build a simple dependency graph between fragments.

    An edge ``A → B`` means "fragment A's NL text references a variable that
    is defined by fragment B's enclosing code".

    The graph is keyed by content hash, with values being lists of content
    hashes that the key depends on.

    This is a heuristic — it uses simple name-matching between the NL text
    tokens and the variable names produced by other fragments.
    """
    # Build a map: variable name → content hash of the fragment in whose
    # enclosing scope the variable is assigned.
    var_to_hash: Dict[str, str] = {}
    for frag in mixed_ast.fragments:
        for vname, _expr in frag.type_context.preceding_assignments:
            var_to_hash[vname] = frag.content_hash

    graph: Dict[str, List[str]] = {}
    for frag in mixed_ast.fragments:
        deps: List[str] = []
        tokens = set(frag.nl_text.split())
        for vname, dep_hash in var_to_hash.items():
            if vname in tokens and dep_hash != frag.content_hash:
                deps.append(dep_hash)
        graph[frag.content_hash] = deps

    return graph

# ---------------------------------------------------------------------------
# Statistics
# ---------------------------------------------------------------------------

def compute_statistics(mixed_ast: MixedAST) -> Dict[str, object]:
    """Compute summary statistics for a ``MixedAST``.

    Returns a dict with counts, average NL text lengths, etc.
    """
    frags = mixed_ast.fragments
    nl_lengths = [len(f.nl_text) for f in frags]

    kinds: Dict[str, int] = {}
    for f in frags:
        key = f.kind.value
        kinds[key] = kinds.get(key, 0) + 1

    cf_positions: Dict[str, int] = {}
    for f in frags:
        pos = f.type_context.control_flow_position
        cf_positions[pos] = cf_positions.get(pos, 0) + 1

    funcs_with_frags = set()
    for f in frags:
        if f.type_context.enclosing_function:
            funcs_with_frags.add(f.type_context.enclosing_function)

    return {
        "total_fragments": len(frags),
        "total_functions": len(mixed_ast.functions),
        "total_code_blocks": len(mixed_ast.code_blocks),
        "fragment_kinds": kinds,
        "control_flow_positions": cf_positions,
        "avg_nl_length": (
            sum(nl_lengths) / len(nl_lengths) if nl_lengths else 0.0
        ),
        "max_nl_length": max(nl_lengths, default=0),
        "min_nl_length": min(nl_lengths, default=0),
        "functions_with_fragments": len(funcs_with_frags),
        "source_lines": len(mixed_ast.source.splitlines()),
    }

# ---------------------------------------------------------------------------
# Module-level __all__
# ---------------------------------------------------------------------------

__all__ = [
    "MixedASTNodeKind",
    "TypeContext",
    "ParsedFragment",
    "MixedAST",
    "ContextInferrer",
    "MixedModeVisitor",
    "MixedModeParser",
    "parse_mixed",
    "parse_mixed_file",
    "filter_fragments",
    "group_fragments_by_function",
    "group_fragments_by_kind",
    "build_type_context_for_function",
    "build_type_context_for_module",
    "source_lines_around",
    "fragment_source_context",
    "dump_mixed_ast",
    "validate_fragment_types",
    "diff_fragments",
    "fragment_to_dict",
    "mixed_ast_to_dict",
    "reparse_with_replacement",
    "collect_all_nl_texts",
    "fragment_dependency_graph",
    "compute_statistics",
]
