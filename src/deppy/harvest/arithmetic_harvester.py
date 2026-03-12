"""Arithmetic bound harvester -- extract numeric bounds from comparisons.

Walks a Python AST to discover arithmetic constraints on variables:
``x > 0``, ``0 <= i < n``, ``len(lst) > 0``, and compound comparisons.
Each discovered bound is recorded as a frozen ``ArithmeticBound`` dataclass.
"""

from __future__ import annotations

import ast
import enum
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import TrustLevel
from deppy.predicates.base import (
    BinOp,
    Call,
    FloatLit,
    IntLit,
    Predicate,
    SourceLocation,
    Term,
    Var,
)
from deppy.predicates.arithmetic import Comparison, IntRange, LinearInequality
from deppy.static_analysis.observation_sites import SourceSpan


# ===================================================================
#  Bound type
# ===================================================================

class BoundType(enum.Enum):
    """Classification of the arithmetic bound."""
    LOWER = "lower"
    UPPER = "upper"
    EXACT = "exact"
    RANGE = "range"
    DIVISIBILITY = "divisibility"
    MODULAR = "modular"


class BoundOrigin(enum.Enum):
    """Where the bound was discovered."""
    IF_TEST = "if_test"
    ASSERT = "assert"
    WHILE_TEST = "while_test"
    FOR_RANGE = "for_range"
    ASSIGNMENT = "assignment"
    COMPARISON = "comparison"
    COMPREHENSION = "comprehension"
    SLICE = "slice"
    FUNCTION_ARG = "function_arg"


# ===================================================================
#  ArithmeticBound dataclass
# ===================================================================

@dataclass(frozen=True)
class ArithmeticBound:
    """An arithmetic bound on a variable extracted from the AST.

    Attributes:
        variable: The variable being bounded.
        operator: The comparison operator (``<``, ``<=``, ``>``, ``>=``, ``==``).
        bound_value: The bound as a predicate Term.
        bound_type: Classification (lower, upper, exact, range).
        predicate: The deppy Predicate representing this bound.
        source_span: Source location.
        trust_level: Provenance trust.
        bound_origin: Where the bound was discovered.
        enclosing_function: Name of the enclosing function.
        is_strict: Whether the bound is strict (``<`` / ``>``) vs non-strict.
        lower_bound: For range bounds, the lower bound.
        upper_bound: For range bounds, the upper bound.
        involves_len: Whether the bound involves ``len()``.
        len_target: If involves_len, the collection whose length is bounded.
        is_integer_bound: Whether both sides are known to be integer-valued.
        polarity: Whether this bound holds (true branch) or not (false branch).
    """
    variable: str
    operator: str
    bound_value: Term
    bound_type: BoundType = BoundType.LOWER
    predicate: Optional[Predicate] = None
    source_span: Optional[SourceSpan] = None
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    bound_origin: BoundOrigin = BoundOrigin.COMPARISON
    enclosing_function: Optional[str] = None
    is_strict: bool = False
    lower_bound: Optional[Term] = None
    upper_bound: Optional[Term] = None
    involves_len: bool = False
    len_target: Optional[str] = None
    is_integer_bound: bool = False
    polarity: bool = True


# ===================================================================
#  Helpers
# ===================================================================

_AST_CMP_MAP: Dict[type, str] = {
    ast.Lt: "<",
    ast.LtE: "<=",
    ast.Gt: ">",
    ast.GtE: ">=",
    ast.Eq: "==",
    ast.NotEq: "!=",
}


def _ast_to_term(node: ast.expr) -> Optional[Term]:
    """Best-effort conversion of AST expression to a predicate Term."""
    if isinstance(node, ast.Name):
        return Var(node.id)
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool):
            return None  # skip booleans for arithmetic
        if isinstance(node.value, int):
            return IntLit(node.value)
        if isinstance(node.value, float):
            return FloatLit(node.value)
        return None
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        inner = _ast_to_term(node.operand)
        if isinstance(inner, IntLit):
            return IntLit(-inner.value)
        if isinstance(inner, FloatLit):
            return FloatLit(-inner.value)
        if inner is not None:
            from deppy.predicates.base import UnaryOp
            return UnaryOp(op="-", operand=inner)
        return None
    if isinstance(node, ast.BinOp):
        op_map: Dict[type, str] = {
            ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
            ast.FloorDiv: "//", ast.Mod: "%",
        }
        op_str = op_map.get(type(node.op))
        if op_str is None:
            return None
        left = _ast_to_term(node.left)
        right = _ast_to_term(node.right)
        if left is not None and right is not None:
            return BinOp(op=op_str, left=left, right=right)
        return None
    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Name) and node.func.id == "len" and len(node.args) >= 1:
            arg = _ast_to_term(node.args[0])
            if arg is not None:
                return Call(func="len", args=[arg])
        if isinstance(node.func, ast.Name) and node.func.id == "abs" and len(node.args) >= 1:
            arg = _ast_to_term(node.args[0])
            if arg is not None:
                return Call(func="abs", args=[arg])
        # General call
        func_name = None
        if isinstance(node.func, ast.Name):
            func_name = node.func.id
        if func_name is not None:
            args: List[Term] = []
            for a in node.args:
                t = _ast_to_term(a)
                if t is None:
                    return None
                args.append(t)
            return Call(func=func_name, args=args)
        return None
    if isinstance(node, ast.Attribute):
        from deppy.predicates.base import Attr
        obj = _ast_to_term(node.value)
        if obj is not None:
            return Attr(obj=obj, attr=node.attr)
        return None
    return None


def _extract_var_name(node: ast.expr) -> Optional[str]:
    """Extract a simple variable name."""
    if isinstance(node, ast.Name):
        return node.id
    return None


def _involves_len_call(node: ast.expr) -> Tuple[bool, Optional[str]]:
    """Check if an expression is or contains a ``len()`` call."""
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "len":
        if node.args and isinstance(node.args[0], ast.Name):
            return True, node.args[0].id
        return True, None
    return False, None


def _is_integer_literal(node: ast.expr) -> bool:
    """Check if a node is an integer literal."""
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
        return True
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return _is_integer_literal(node.operand)
    return False


def _source_loc(node: ast.AST, file: str) -> SourceLocation:
    return SourceLocation(
        file=file,
        line=getattr(node, "lineno", 0),
        col=getattr(node, "col_offset", 0),
        end_line=getattr(node, "end_lineno", None),
        end_col=getattr(node, "end_col_offset", None),
    )


def _classify_bound(op: str) -> BoundType:
    """Classify a comparison operator as a bound type."""
    if op in (">", ">="):
        return BoundType.LOWER
    if op in ("<", "<="):
        return BoundType.UPPER
    if op == "==":
        return BoundType.EXACT
    return BoundType.LOWER


def _is_strict(op: str) -> bool:
    return op in ("<", ">")


# ===================================================================
#  ArithmeticHarvester visitor
# ===================================================================

class ArithmeticHarvester(ast.NodeVisitor):
    """AST visitor that extracts arithmetic bounds from comparisons.

    Handles:
    - Simple comparisons: ``x > 0``, ``y <= 10``
    - Chained comparisons: ``0 <= i < n``
    - len() comparisons: ``len(lst) > 0``
    - Compound expressions: ``x + y > z``
    - For-range bounds: ``for i in range(n)``
    - Assert bounds: ``assert x >= 0``
    - Slice bounds
    - Modular arithmetic: ``x % 2 == 0``

    Usage::

        harvester = ArithmeticHarvester(file="example.py")
        harvester.visit(tree)
        bounds = harvester.bounds
    """

    def __init__(self, file: str = "<unknown>") -> None:
        self._file = file
        self._bounds: List[ArithmeticBound] = []
        self._function_stack: List[str] = []

    @property
    def bounds(self) -> List[ArithmeticBound]:
        return list(self._bounds)

    @property
    def _current_function(self) -> Optional[str]:
        return self._function_stack[-1] if self._function_stack else None

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._file)

    def _add_bound(
        self,
        variable: str,
        operator: str,
        bound_value: Term,
        node: ast.AST,
        *,
        bound_type: Optional[BoundType] = None,
        origin: BoundOrigin = BoundOrigin.COMPARISON,
        trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
        lower_bound: Optional[Term] = None,
        upper_bound: Optional[Term] = None,
        involves_len: bool = False,
        len_target: Optional[str] = None,
        is_integer: bool = False,
        polarity: bool = True,
    ) -> None:
        if bound_type is None:
            bound_type = _classify_bound(operator)

        src = _source_loc(node, self._file)
        left_term = Var(variable)
        pred = Comparison(
            op=operator, left=left_term, right=bound_value,
            source_location=src,
        )
        self._bounds.append(ArithmeticBound(
            variable=variable,
            operator=operator,
            bound_value=bound_value,
            bound_type=bound_type,
            predicate=pred,
            source_span=self._span(node),
            trust_level=trust,
            bound_origin=origin,
            enclosing_function=self._current_function,
            is_strict=_is_strict(operator),
            lower_bound=lower_bound,
            upper_bound=upper_bound,
            involves_len=involves_len,
            len_target=len_target,
            is_integer_bound=is_integer,
            polarity=polarity,
        ))

    # -- Scope --

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._function_stack.append(node.name)
        self.generic_visit(node)
        self._function_stack.pop()

    # -- If statements --

    def visit_If(self, node: ast.If) -> None:
        self._extract_from_test(node.test, node, BoundOrigin.IF_TEST)
        # Handle elif
        for else_node in node.orelse:
            if isinstance(else_node, ast.If):
                self._extract_from_test(else_node.test, else_node, BoundOrigin.IF_TEST)
        self.generic_visit(node)

    # -- While --

    def visit_While(self, node: ast.While) -> None:
        self._extract_from_test(node.test, node, BoundOrigin.WHILE_TEST)
        self.generic_visit(node)

    # -- Assert --

    def visit_Assert(self, node: ast.Assert) -> None:
        self._extract_from_test(
            node.test, node, BoundOrigin.ASSERT,
            trust=TrustLevel.PROOF_BACKED,
        )
        self.generic_visit(node)

    # -- For loops with range() --

    def visit_For(self, node: ast.For) -> None:
        self._extract_for_range(node)
        self.generic_visit(node)

    def _extract_for_range(self, node: ast.For) -> None:
        """Extract bounds from ``for i in range(...)``."""
        if not isinstance(node.target, ast.Name):
            return
        var_name = node.target.id
        iter_node = node.iter

        if not (isinstance(iter_node, ast.Call) and isinstance(iter_node.func, ast.Name)
                and iter_node.func.id == "range"):
            return

        args = iter_node.args
        if len(args) == 1:
            # range(n): 0 <= i < n
            upper = _ast_to_term(args[0])
            if upper is not None:
                self._add_bound(
                    var_name, ">=", IntLit(0), node,
                    bound_type=BoundType.LOWER,
                    origin=BoundOrigin.FOR_RANGE,
                    lower_bound=IntLit(0),
                    upper_bound=upper,
                    is_integer=True,
                )
                self._add_bound(
                    var_name, "<", upper, node,
                    bound_type=BoundType.UPPER,
                    origin=BoundOrigin.FOR_RANGE,
                    lower_bound=IntLit(0),
                    upper_bound=upper,
                    is_integer=True,
                )
        elif len(args) >= 2:
            # range(start, stop) or range(start, stop, step)
            lower = _ast_to_term(args[0])
            upper = _ast_to_term(args[1])
            if lower is not None:
                self._add_bound(
                    var_name, ">=", lower, node,
                    bound_type=BoundType.LOWER,
                    origin=BoundOrigin.FOR_RANGE,
                    lower_bound=lower,
                    upper_bound=upper,
                    is_integer=True,
                )
            if upper is not None:
                self._add_bound(
                    var_name, "<", upper, node,
                    bound_type=BoundType.UPPER,
                    origin=BoundOrigin.FOR_RANGE,
                    lower_bound=lower,
                    upper_bound=upper,
                    is_integer=True,
                )
            # Step-based divisibility
            if len(args) >= 3:
                step = _ast_to_term(args[2])
                if step is not None and lower is not None:
                    self._add_bound(
                        var_name, "%", step, node,
                        bound_type=BoundType.DIVISIBILITY,
                        origin=BoundOrigin.FOR_RANGE,
                        is_integer=True,
                    )

    # -- Comprehension ifs --

    def visit_ListComp(self, node: ast.ListComp) -> None:
        self._extract_comprehension_bounds(node.generators, node)
        self.generic_visit(node)

    def visit_SetComp(self, node: ast.SetComp) -> None:
        self._extract_comprehension_bounds(node.generators, node)
        self.generic_visit(node)

    def visit_DictComp(self, node: ast.DictComp) -> None:
        self._extract_comprehension_bounds(node.generators, node)
        self.generic_visit(node)

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:
        self._extract_comprehension_bounds(node.generators, node)
        self.generic_visit(node)

    def _extract_comprehension_bounds(
        self,
        generators: List[ast.comprehension],
        parent: ast.AST,
    ) -> None:
        for gen in generators:
            for if_clause in gen.ifs:
                self._extract_from_test(if_clause, parent, BoundOrigin.COMPREHENSION)

    # -- Subscript / Slice bounds --

    def visit_Subscript(self, node: ast.Subscript) -> None:
        if isinstance(node.slice, ast.Slice):
            self._extract_slice_bounds(node)
        self.generic_visit(node)

    def _extract_slice_bounds(self, node: ast.Subscript) -> None:
        """Extract bounds from slice expressions."""
        sl = node.slice
        if not isinstance(sl, ast.Slice):
            return
        if sl.lower is not None:
            var_name = _extract_var_name(sl.lower)
            if var_name is not None:
                self._add_bound(
                    var_name, ">=", IntLit(0), node,
                    bound_type=BoundType.LOWER,
                    origin=BoundOrigin.SLICE,
                    is_integer=True,
                )
        if sl.upper is not None:
            var_name = _extract_var_name(sl.upper)
            if var_name is not None:
                # upper bound of a slice is typically <= len(container)
                self._add_bound(
                    var_name, ">=", IntLit(0), node,
                    bound_type=BoundType.LOWER,
                    origin=BoundOrigin.SLICE,
                    is_integer=True,
                )

    # -- Core extraction from test expressions --

    def _extract_from_test(
        self,
        test: ast.expr,
        parent_node: ast.AST,
        origin: BoundOrigin,
        *,
        trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
    ) -> None:
        """Extract arithmetic bounds from a test expression."""
        # not expr
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            # Negation flips bounds
            self._extract_from_test(test.operand, parent_node, origin, trust=trust)
            return

        # BoolOp: and / or
        if isinstance(test, ast.BoolOp):
            for val in test.values:
                self._extract_from_test(val, parent_node, origin, trust=trust)
            return

        # Compare (the main case)
        if isinstance(test, ast.Compare):
            self._extract_from_compare(test, parent_node, origin, trust=trust)
            return

    def _extract_from_compare(
        self,
        compare: ast.Compare,
        parent_node: ast.AST,
        origin: BoundOrigin,
        *,
        trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
    ) -> None:
        """Extract bounds from comparison chains.

        Handles simple comparisons and chained ones like ``0 <= x < n``.
        """
        comparators = [compare.left] + compare.comparators
        ops = compare.ops

        for i, op in enumerate(ops):
            left_ast = comparators[i]
            right_ast = comparators[i + 1]

            op_str = _AST_CMP_MAP.get(type(op))
            if op_str is None:
                continue

            left_term = _ast_to_term(left_ast)
            right_term = _ast_to_term(right_ast)
            if left_term is None or right_term is None:
                continue

            # Check for len() involvement
            left_is_len, left_len_target = _involves_len_call(left_ast)
            right_is_len, right_len_target = _involves_len_call(right_ast)

            is_int = (
                _is_integer_literal(left_ast) or _is_integer_literal(right_ast)
            )

            # Modular arithmetic: x % n == 0
            if op_str == "==" and isinstance(left_ast, ast.BinOp) and isinstance(left_ast.op, ast.Mod):
                mod_var = _extract_var_name(left_ast.left)
                mod_val = _ast_to_term(left_ast.right)
                if mod_var is not None and mod_val is not None:
                    self._add_bound(
                        mod_var, "%", mod_val, parent_node,
                        bound_type=BoundType.MODULAR,
                        origin=origin,
                        trust=trust,
                        is_integer=True,
                    )

            # left op right: e.g., x > 0
            # If left is a variable and right is a bound
            left_var = _extract_var_name(left_ast)
            right_var = _extract_var_name(right_ast)

            if left_var is not None:
                self._add_bound(
                    left_var, op_str, right_term, parent_node,
                    origin=origin,
                    trust=trust,
                    involves_len=left_is_len,
                    len_target=left_len_target,
                    is_integer=is_int,
                )

            # Flip: if right is a variable, record the flipped bound
            if right_var is not None:
                flipped = _flip_op(op_str)
                if flipped is not None:
                    self._add_bound(
                        right_var, flipped, left_term, parent_node,
                        origin=origin,
                        trust=trust,
                        involves_len=right_is_len,
                        len_target=right_len_target,
                        is_integer=is_int,
                    )

            # len(x) comparisons: extract bound on the collection
            if left_is_len and left_len_target is not None:
                self._add_bound(
                    f"len({left_len_target})", op_str, right_term, parent_node,
                    origin=origin,
                    trust=trust,
                    involves_len=True,
                    len_target=left_len_target,
                    is_integer=True,
                )
            if right_is_len and right_len_target is not None:
                flipped = _flip_op(op_str)
                if flipped is not None:
                    self._add_bound(
                        f"len({right_len_target})", flipped, left_term, parent_node,
                        origin=origin,
                        trust=trust,
                        involves_len=True,
                        len_target=right_len_target,
                        is_integer=True,
                    )

        # For chained comparisons (0 <= i < n), also record the range
        if len(ops) >= 2:
            self._extract_chain_range(comparators, ops, parent_node, origin, trust=trust)

    def _extract_chain_range(
        self,
        comparators: List[ast.expr],
        ops: List[ast.cmpop],
        parent_node: ast.AST,
        origin: BoundOrigin,
        *,
        trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
    ) -> None:
        """Extract range bounds from chained comparisons like ``0 <= x < n``."""
        # Look for patterns: a </<= x </<= b
        for i in range(len(ops) - 1):
            left = comparators[i]
            middle = comparators[i + 1]
            right = comparators[i + 2]

            op1 = _AST_CMP_MAP.get(type(ops[i]))
            op2 = _AST_CMP_MAP.get(type(ops[i + 1]))
            if op1 is None or op2 is None:
                continue

            mid_var = _extract_var_name(middle)
            if mid_var is None:
                continue

            # Check that both ops point the same direction (ascending chain)
            if op1 in ("<", "<=") and op2 in ("<", "<="):
                lower = _ast_to_term(left)
                upper = _ast_to_term(right)
                if lower is not None and upper is not None:
                    # Record as a range bound
                    self._bounds.append(ArithmeticBound(
                        variable=mid_var,
                        operator="range",
                        bound_value=lower,
                        bound_type=BoundType.RANGE,
                        predicate=None,
                        source_span=self._span(parent_node),
                        trust_level=trust,
                        bound_origin=origin,
                        enclosing_function=self._current_function,
                        is_strict=op1 == "<" or op2 == "<",
                        lower_bound=lower,
                        upper_bound=upper,
                        is_integer_bound=_is_integer_literal(left) or _is_integer_literal(right),
                        polarity=True,
                    ))

            # Descending chain: a >= x >= b
            elif op1 in (">", ">=") and op2 in (">", ">="):
                upper = _ast_to_term(left)
                lower = _ast_to_term(right)
                if lower is not None and upper is not None:
                    self._bounds.append(ArithmeticBound(
                        variable=mid_var,
                        operator="range",
                        bound_value=lower,
                        bound_type=BoundType.RANGE,
                        predicate=None,
                        source_span=self._span(parent_node),
                        trust_level=trust,
                        bound_origin=origin,
                        enclosing_function=self._current_function,
                        is_strict=op1 == ">" or op2 == ">",
                        lower_bound=lower,
                        upper_bound=upper,
                        is_integer_bound=_is_integer_literal(left) or _is_integer_literal(right),
                        polarity=True,
                    ))


def _flip_op(op: str) -> Optional[str]:
    """Flip a comparison operator."""
    flips = {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "==": "==", "!=": "!="}
    return flips.get(op)


# ===================================================================
#  Convenience function
# ===================================================================

def harvest_arithmetic_bounds(
    ast_tree: ast.AST,
    *,
    file: str = "<unknown>",
) -> List[ArithmeticBound]:
    """Extract all arithmetic bounds from a Python AST.

    Args:
        ast_tree: The parsed AST (typically from ``ast.parse``).
        file: Source file name for provenance.

    Returns:
        A list of ``ArithmeticBound`` facts.
    """
    harvester = ArithmeticHarvester(file=file)
    harvester.visit(ast_tree)
    return harvester.bounds


# ===================================================================
#  Filtering / query utilities
# ===================================================================

def filter_by_variable(
    bounds: List[ArithmeticBound],
    variable: str,
) -> List[ArithmeticBound]:
    """Return bounds for a specific variable."""
    return [b for b in bounds if b.variable == variable]


def lower_bounds(bounds: List[ArithmeticBound]) -> List[ArithmeticBound]:
    """Return only lower bounds."""
    return [b for b in bounds if b.bound_type == BoundType.LOWER]


def upper_bounds(bounds: List[ArithmeticBound]) -> List[ArithmeticBound]:
    """Return only upper bounds."""
    return [b for b in bounds if b.bound_type == BoundType.UPPER]


def exact_bounds(bounds: List[ArithmeticBound]) -> List[ArithmeticBound]:
    """Return only exact (equality) bounds."""
    return [b for b in bounds if b.bound_type == BoundType.EXACT]


def range_bounds(bounds: List[ArithmeticBound]) -> List[ArithmeticBound]:
    """Return only range bounds."""
    return [b for b in bounds if b.bound_type == BoundType.RANGE]


def len_bounds(bounds: List[ArithmeticBound]) -> List[ArithmeticBound]:
    """Return bounds that involve ``len()``."""
    return [b for b in bounds if b.involves_len]


def bounds_for_function(
    bounds: List[ArithmeticBound],
    function_name: str,
) -> List[ArithmeticBound]:
    """Return bounds from a specific function."""
    return [b for b in bounds if b.enclosing_function == function_name]


def to_int_range(bound: ArithmeticBound) -> Optional[IntRange]:
    """Convert an ArithmeticBound to an IntRange predicate if possible."""
    if bound.bound_type == BoundType.RANGE:
        lo: Optional[int] = None
        hi: Optional[int] = None
        if isinstance(bound.lower_bound, IntLit):
            lo = bound.lower_bound.value
        if isinstance(bound.upper_bound, IntLit):
            hi = bound.upper_bound.value
            if bound.is_strict:
                hi -= 1
        return IntRange(variable=bound.variable, lo=lo, hi=hi)
    if bound.bound_type == BoundType.LOWER:
        if isinstance(bound.bound_value, IntLit):
            lo_val = bound.bound_value.value
            if bound.is_strict:
                lo_val += 1
            return IntRange(variable=bound.variable, lo=lo_val)
    if bound.bound_type == BoundType.UPPER:
        if isinstance(bound.bound_value, IntLit):
            hi_val = bound.bound_value.value
            if bound.is_strict:
                hi_val -= 1
            return IntRange(variable=bound.variable, hi=hi_val)
    if bound.bound_type == BoundType.EXACT:
        if isinstance(bound.bound_value, IntLit):
            val = bound.bound_value.value
            return IntRange(variable=bound.variable, lo=val, hi=val)
    return None
