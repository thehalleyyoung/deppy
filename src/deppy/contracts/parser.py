"""Contract parser and extractor for Python AST.

:class:`ContractParser` converts individual AST nodes (decorator calls,
inline assertions, inline ``deppy.*`` calls) into typed contract objects.

:class:`ContractExtractor` walks an entire module AST and gathers all
contracts, grouping them by scope (function, class, module).
"""

from __future__ import annotations

import ast
import inspect
import textwrap
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
    ContractSet,
    Predicate,
    PredicateKind,
    SourceLocation,
    Term,
    TermKind,
    TypeBase,
)
from deppy.contracts.ensures import EnsuresContract, ExceptionalEnsures
from deppy.contracts.invariant import (
    ClassInvariant,
    InvariantContract,
    InvariantKind,
    LoopInvariant,
    ModuleInvariant,
)
from deppy.contracts.requires import RequiresContract
from deppy.contracts.theorem import (
    AssumptionContract,
    LemmaContract,
    TheoremContract,
    TransportContract,
)
from deppy.contracts.witness import WitnessContract
from deppy.core._protocols import TrustLevel


# ---------------------------------------------------------------------------
# AST → Term conversion
# ---------------------------------------------------------------------------

# Mapping from ast comparison operator types to string operators.
_CMP_OP_MAP: Dict[type, str] = {
    ast.Eq: "==",
    ast.NotEq: "!=",
    ast.Lt: "<",
    ast.LtE: "<=",
    ast.Gt: ">",
    ast.GtE: ">=",
    ast.Is: "is",
    ast.IsNot: "is not",
    ast.In: "in",
    ast.NotIn: "not in",
}

_BIN_OP_MAP: Dict[type, str] = {
    ast.Add: "+",
    ast.Sub: "-",
    ast.Mult: "*",
    ast.Div: "/",
    ast.FloorDiv: "//",
    ast.Mod: "%",
    ast.Pow: "**",
    ast.LShift: "<<",
    ast.RShift: ">>",
    ast.BitOr: "|",
    ast.BitXor: "^",
    ast.BitAnd: "&",
    ast.MatMult: "@",
}

_UNARY_OP_MAP: Dict[type, str] = {
    ast.UAdd: "+",
    ast.USub: "-",
    ast.Not: "not",
    ast.Invert: "~",
}

_BOOL_OP_MAP: Dict[type, str] = {
    ast.And: "and",
    ast.Or: "or",
}


def _ast_to_term(node: ast.expr) -> Term:
    """Convert a Python AST expression to a :class:`Term`."""
    source = _unparse_safe(node)

    if isinstance(node, ast.Name):
        return Term(kind=TermKind.VARIABLE, value=node.id, _source=source)

    if isinstance(node, ast.Constant):
        return Term(kind=TermKind.CONSTANT, value=node.value, _source=source)

    if isinstance(node, ast.UnaryOp):
        op = _UNARY_OP_MAP.get(type(node.op), "?")
        operand = _ast_to_term(node.operand)
        return Term(kind=TermKind.UNARY_OP, value=op, children=(operand,), _source=source)

    if isinstance(node, ast.BinOp):
        op = _BIN_OP_MAP.get(type(node.op), "?")
        left = _ast_to_term(node.left)
        right = _ast_to_term(node.right)
        return Term(kind=TermKind.BINARY_OP, value=op, children=(left, right), _source=source)

    if isinstance(node, ast.Call):
        func = _ast_to_term(node.func)
        args = tuple(_ast_to_term(a) for a in node.args)
        return Term(kind=TermKind.CALL, children=(func, *args), _source=source)

    if isinstance(node, ast.Attribute):
        obj = _ast_to_term(node.value)
        return Term(kind=TermKind.ATTRIBUTE, value=node.attr, children=(obj,), _source=source)

    if isinstance(node, ast.Subscript):
        obj = _ast_to_term(node.value)
        idx = _ast_to_term(node.slice)
        return Term(kind=TermKind.SUBSCRIPT, children=(obj, idx), _source=source)

    if isinstance(node, ast.Tuple):
        elts = tuple(_ast_to_term(e) for e in node.elts)
        return Term(kind=TermKind.CALL, value="tuple", children=elts, _source=source)

    if isinstance(node, ast.List):
        elts = tuple(_ast_to_term(e) for e in node.elts)
        return Term(kind=TermKind.CALL, value="list", children=elts, _source=source)

    # Fallback: wrap as a constant with the source text
    return Term(kind=TermKind.CONSTANT, value=source, _source=source)


def _ast_to_predicate(node: ast.expr) -> Predicate:
    """Convert a Python AST expression node to a :class:`Predicate`."""
    source = _unparse_safe(node)

    if isinstance(node, ast.Compare):
        return _ast_compare_to_predicate(node, source)

    if isinstance(node, ast.BoolOp):
        children = [_ast_to_predicate(v) for v in node.values]
        if isinstance(node.op, ast.And):
            return Predicate.conjunction(*children)
        return Predicate.disjunction(*children)

    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        child = _ast_to_predicate(node.operand)
        return Predicate.negation(child)

    if isinstance(node, ast.NameConstant) if hasattr(ast, "NameConstant") else False:
        if node.value is True:  # type: ignore[union-attr]
            return Predicate.true_()
        if node.value is False:  # type: ignore[union-attr]
            return Predicate.false_()

    if isinstance(node, ast.Constant):
        if node.value is True:
            return Predicate.true_()
        if node.value is False:
            return Predicate.false_()

    # Generic: wrap the whole expression as an atomic predicate
    term = _ast_to_term(node)
    return Predicate.atomic(term, description=source)


def _ast_compare_to_predicate(node: ast.Compare, source: str) -> Predicate:
    """Convert an AST Compare node (which may be chained) to a predicate."""
    # Python allows chained comparisons: a < b < c → (a < b) and (b < c)
    parts: List[Predicate] = []
    left = _ast_to_term(node.left)

    for op_node, comparator_node in zip(node.ops, node.comparators):
        right = _ast_to_term(comparator_node)
        op_str = _CMP_OP_MAP.get(type(op_node), "?")
        comp = Predicate.comparison(op_str, left, right)
        parts.append(comp)
        left = right

    if len(parts) == 1:
        return parts[0]
    return Predicate.conjunction(*parts)


def _unparse_safe(node: ast.AST) -> str:
    """Best-effort unparse of an AST node."""
    try:
        return ast.unparse(node)
    except Exception:
        return ast.dump(node)


# ---------------------------------------------------------------------------
# Lambda extraction
# ---------------------------------------------------------------------------


def _extract_lambda_info(node: ast.Lambda) -> Tuple[List[str], ast.expr]:
    """Extract parameter names and body expression from a lambda."""
    params: List[str] = []
    for arg in node.args.args:
        params.append(arg.arg)
    return params, node.body


# ---------------------------------------------------------------------------
# Decorator name resolution
# ---------------------------------------------------------------------------

# Recognised decorator patterns (attribute and bare name forms).
_REQUIRES_NAMES = frozenset({"requires", "deppy.requires"})
_ENSURES_NAMES = frozenset({"ensures", "deppy.ensures"})
_ENSURES_RAISES_NAMES = frozenset({"ensures_raises", "deppy.ensures_raises"})
_INVARIANT_NAMES = frozenset({"invariant", "deppy.invariant", "loop_invariant", "deppy.loop_invariant"})
_THEOREM_NAMES = frozenset({"theorem", "deppy.theorem"})
_LEMMA_NAMES = frozenset({"lemma", "deppy.lemma"})
_WITNESS_NAMES = frozenset({"witness", "deppy.witness"})
_ASSUME_NAMES = frozenset({"assume", "deppy.assume"})
_TRANSPORT_NAMES = frozenset({"transport", "deppy.transport"})


def _decorator_name(node: ast.expr) -> str:
    """Extract the full dotted name of a decorator expression.

    Handles ``@name``, ``@mod.name``, ``@name(...)`` and ``@mod.name(...)``.
    """
    if isinstance(node, ast.Call):
        return _decorator_name(node.func)
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _decorator_name(node.value)
        return f"{prefix}.{node.attr}"
    return ""


# ---------------------------------------------------------------------------
# ContractParser
# ---------------------------------------------------------------------------


class ContractParser:
    """Parses individual contract AST nodes into typed contract objects.

    This is a stateless parser — call its methods with AST nodes and
    get back contract objects.  For whole-module extraction, use
    :class:`ContractExtractor`.
    """

    def __init__(self, *, file_path: str = "<unknown>") -> None:
        self._file = file_path

    def _loc(self, node: ast.AST) -> Optional[SourceLocation]:
        """Build a SourceLocation from an AST node."""
        line = getattr(node, "lineno", 0)
        col = getattr(node, "col_offset", 0)
        end_line = getattr(node, "end_lineno", None)
        end_col = getattr(node, "end_col_offset", None)
        if line:
            return SourceLocation(
                file=self._file, line=line, col=col,
                end_line=end_line, end_col=end_col,
            )
        return None

    # -- top-level dispatch -------------------------------------------------

    def parse_decorator(self, decorator_node: ast.expr) -> Optional[Contract]:
        """Parse a decorator AST node into a Contract (if recognised).

        Returns None for unrecognised decorators.
        """
        name = _decorator_name(decorator_node)

        if name in _REQUIRES_NAMES:
            if isinstance(decorator_node, ast.Call):
                return self.parse_requires(decorator_node)
            return None

        if name in _ENSURES_NAMES:
            if isinstance(decorator_node, ast.Call):
                return self.parse_ensures(decorator_node)
            return None

        if name in _ENSURES_RAISES_NAMES:
            if isinstance(decorator_node, ast.Call):
                return self.parse_ensures_raises(decorator_node)
            return None

        if name in _INVARIANT_NAMES:
            if isinstance(decorator_node, ast.Call):
                return self.parse_invariant(decorator_node)
            return None

        if name in _THEOREM_NAMES:
            return self._make_theorem_marker(decorator_node)

        if name in _LEMMA_NAMES:
            return self._make_lemma_marker(decorator_node)

        if name in _WITNESS_NAMES:
            if isinstance(decorator_node, ast.Call):
                return self.parse_witness(decorator_node)
            return None

        return None

    # -- requires -----------------------------------------------------------

    def parse_requires(self, node: ast.Call) -> RequiresContract:
        """Parse ``@requires(lambda x: x > 0)``."""
        params: List[str] = []
        predicate: Optional[Predicate] = None
        description: Optional[str] = None

        if node.args:
            first = node.args[0]
            if isinstance(first, ast.Lambda):
                params, body = _extract_lambda_info(first)
                predicate = _ast_to_predicate(body)
            else:
                predicate = _ast_to_predicate(first)

        # Keyword arguments
        for kw in node.keywords:
            if kw.arg == "description" and isinstance(kw.value, ast.Constant):
                description = str(kw.value.value)
            elif kw.arg == "parameters" and isinstance(kw.value, (ast.List, ast.Tuple)):
                params = [
                    elt.value for elt in kw.value.elts  # type: ignore[union-attr]
                    if isinstance(elt, ast.Constant) and isinstance(elt.value, str)
                ]

        return RequiresContract(
            parameters=params,
            predicate=predicate or Predicate.true_(),
            description=description,
            source_location=self._loc(node),
        )

    # -- ensures ------------------------------------------------------------

    def parse_ensures(self, node: ast.Call) -> EnsuresContract:
        """Parse ``@ensures(lambda result, x: result > x)``."""
        params: List[str] = []
        result_name = "result"
        predicate: Optional[Predicate] = None
        description: Optional[str] = None

        if node.args:
            first = node.args[0]
            if isinstance(first, ast.Lambda):
                all_params, body = _extract_lambda_info(first)
                predicate = _ast_to_predicate(body)
                if all_params:
                    result_name = all_params[0]
                    params = all_params[1:]
            else:
                predicate = _ast_to_predicate(first)

        for kw in node.keywords:
            if kw.arg == "description" and isinstance(kw.value, ast.Constant):
                description = str(kw.value.value)
            elif kw.arg == "result_name" and isinstance(kw.value, ast.Constant):
                result_name = str(kw.value.value)

        return EnsuresContract(
            result_name=result_name,
            parameters=params,
            predicate=predicate or Predicate.true_(),
            description=description,
            source_location=self._loc(node),
        )

    # -- ensures_raises -----------------------------------------------------

    def parse_ensures_raises(self, node: ast.Call) -> ExceptionalEnsures:
        """Parse ``@ensures_raises(ValueError, lambda e: 'neg' in str(e))``."""
        exception_type = "Exception"
        predicate: Optional[Predicate] = None
        description: Optional[str] = None

        if node.args:
            first = node.args[0]
            if isinstance(first, ast.Name):
                exception_type = first.id
            elif isinstance(first, ast.Attribute):
                exception_type = _unparse_safe(first)
            elif isinstance(first, ast.Constant) and isinstance(first.value, str):
                exception_type = first.value

            if len(node.args) > 1:
                second = node.args[1]
                if isinstance(second, ast.Lambda):
                    _, body = _extract_lambda_info(second)
                    predicate = _ast_to_predicate(body)
                else:
                    predicate = _ast_to_predicate(second)

        for kw in node.keywords:
            if kw.arg == "description" and isinstance(kw.value, ast.Constant):
                description = str(kw.value.value)

        return ExceptionalEnsures(
            exception_type=exception_type,
            predicate=predicate,
            guarantees_raised=True,
            description=description,
            source_location=self._loc(node),
        )

    # -- invariant ----------------------------------------------------------

    def parse_invariant(self, node: ast.Call) -> InvariantContract:
        """Parse ``@invariant(lambda x: x > 0)`` or ``@loop_invariant(...)``."""
        predicate: Optional[Predicate] = None
        description: Optional[str] = None
        kind = InvariantKind.LOOP
        loop_variable: Optional[str] = None
        decreases_term: Optional[Term] = None

        name = _decorator_name(node)
        if "class" in name:
            kind = InvariantKind.CLASS
        elif "module" in name:
            kind = InvariantKind.MODULE

        if node.args:
            first = node.args[0]
            if isinstance(first, ast.Lambda):
                _, body = _extract_lambda_info(first)
                predicate = _ast_to_predicate(body)
            else:
                predicate = _ast_to_predicate(first)

        for kw in node.keywords:
            if kw.arg == "description" and isinstance(kw.value, ast.Constant):
                description = str(kw.value.value)
            elif kw.arg == "loop_variable" and isinstance(kw.value, ast.Constant):
                loop_variable = str(kw.value.value)
            elif kw.arg == "decreases":
                decreases_term = _ast_to_term(kw.value)

        if kind == InvariantKind.LOOP:
            return LoopInvariant(
                predicate=predicate or Predicate.true_(),
                loop_variable=loop_variable,
                decreases=decreases_term,
                description=description,
                source_location=self._loc(node),
            )

        return InvariantContract(
            kind=kind,
            predicate=predicate or Predicate.true_(),
            description=description,
            source_location=self._loc(node),
        )

    # -- theorem / lemma (decorator markers) --------------------------------

    def parse_theorem(self, func_def: ast.FunctionDef) -> TheoremContract:
        """Parse a function decorated with ``@theorem``."""
        name = func_def.name
        description: Optional[str] = None
        dependencies: List[str] = []

        # Check for keyword args in the decorator
        for dec in func_def.decorator_list:
            dec_name = _decorator_name(dec)
            if dec_name in _THEOREM_NAMES and isinstance(dec, ast.Call):
                for kw in dec.keywords:
                    if kw.arg == "description" and isinstance(kw.value, ast.Constant):
                        description = str(kw.value.value)
                    elif kw.arg == "dependencies" and isinstance(kw.value, (ast.List, ast.Tuple)):
                        dependencies = [
                            elt.value  # type: ignore[union-attr]
                            for elt in kw.value.elts
                            if isinstance(elt, ast.Constant) and isinstance(elt.value, str)
                        ]
                # Name override from first positional arg
                if dec.args and isinstance(dec.args[0], ast.Constant):
                    name = str(dec.args[0].value)

        # Extract docstring as potential description
        if description is None:
            description = _extract_docstring(func_def)

        return TheoremContract(
            name=name,
            description=description,
            dependencies=dependencies,
            source_location=self._loc(func_def),
        )

    def _make_theorem_marker(self, dec_node: ast.expr) -> TheoremContract:
        """Create a placeholder TheoremContract from a decorator.

        The actual statement is filled in by ``parse_theorem`` when the
        full FunctionDef is available.
        """
        name = ""
        if isinstance(dec_node, ast.Call) and dec_node.args:
            first = dec_node.args[0]
            if isinstance(first, ast.Constant) and isinstance(first.value, str):
                name = first.value
        return TheoremContract(
            name=name,
            source_location=self._loc(dec_node),
        )

    def _make_lemma_marker(self, dec_node: ast.expr) -> LemmaContract:
        """Create a placeholder LemmaContract from a decorator."""
        name = ""
        if isinstance(dec_node, ast.Call) and dec_node.args:
            first = dec_node.args[0]
            if isinstance(first, ast.Constant) and isinstance(first.value, str):
                name = first.value
        return LemmaContract(
            name=name,
            source_location=self._loc(dec_node),
        )

    # -- witness ------------------------------------------------------------

    def parse_witness(self, node: ast.Call) -> WitnessContract:
        """Parse ``@witness("name", proposition=lambda xs: ...)``."""
        witness_name = ""
        proposition: Optional[Predicate] = None
        description: Optional[str] = None

        if node.args:
            first = node.args[0]
            if isinstance(first, ast.Constant) and isinstance(first.value, str):
                witness_name = first.value

        for kw in node.keywords:
            if kw.arg == "proposition":
                if isinstance(kw.value, ast.Lambda):
                    _, body = _extract_lambda_info(kw.value)
                    proposition = _ast_to_predicate(body)
                else:
                    proposition = _ast_to_predicate(kw.value)
            elif kw.arg == "description" and isinstance(kw.value, ast.Constant):
                description = str(kw.value.value)

        return WitnessContract(
            witness_name=witness_name,
            proposition=proposition,
            description=description,
            source_location=self._loc(node),
        )

    # -- inline constructs --------------------------------------------------

    def parse_inline_assert(self, node: ast.Assert) -> Optional[Contract]:
        """Parse ``assert`` statements as potential contracts.

        Returns a :class:`RequiresContract` if the assert is at function
        top-level, otherwise returns None (ordinary assert).
        """
        if node.test is None:
            return None

        predicate = _ast_to_predicate(node.test)
        description: Optional[str] = None
        if node.msg is not None and isinstance(node.msg, ast.Constant):
            description = str(node.msg.value)

        return RequiresContract(
            predicate=predicate,
            description=description,
            source_location=self._loc(node),
            provenance="synthesized",
            trust=TrustLevel.TRACE_BACKED,
        )

    def parse_assume(self, node: ast.Call) -> AssumptionContract:
        """Parse ``deppy.assume(lambda x: x > 0, justification="...")``."""
        proposition: Optional[Predicate] = None
        justification: Optional[str] = None

        if node.args:
            first = node.args[0]
            if isinstance(first, ast.Lambda):
                _, body = _extract_lambda_info(first)
                proposition = _ast_to_predicate(body)
            else:
                proposition = _ast_to_predicate(first)

        for kw in node.keywords:
            if kw.arg == "justification" and isinstance(kw.value, ast.Constant):
                justification = str(kw.value.value)

        return AssumptionContract(
            proposition=proposition,
            justification=justification,
            source_location=self._loc(node),
        )

    def parse_transport(self, node: ast.Call) -> TransportContract:
        """Parse ``deppy.transport(source=..., target=...)``."""
        source_pred: Optional[Predicate] = None
        target_pred: Optional[Predicate] = None
        description: Optional[str] = None

        for kw in node.keywords:
            if kw.arg == "source":
                if isinstance(kw.value, ast.Lambda):
                    _, body = _extract_lambda_info(kw.value)
                    source_pred = _ast_to_predicate(body)
                else:
                    source_pred = _ast_to_predicate(kw.value)
            elif kw.arg == "target":
                if isinstance(kw.value, ast.Lambda):
                    _, body = _extract_lambda_info(kw.value)
                    target_pred = _ast_to_predicate(body)
                else:
                    target_pred = _ast_to_predicate(kw.value)
            elif kw.arg == "description" and isinstance(kw.value, ast.Constant):
                description = str(kw.value.value)

        return TransportContract(
            source_prop=source_pred,
            target_prop=target_pred,
            description=description,
            source_location=self._loc(node),
        )

    # -- lambda extraction --------------------------------------------------

    def extract_lambda_predicate(self, node: ast.Lambda) -> Tuple[List[str], ast.expr]:
        """Extract parameter names and body expression from a lambda.

        Returns ``(param_names, body_expr)``.
        """
        return _extract_lambda_info(node)


# ---------------------------------------------------------------------------
# ContractExtractor
# ---------------------------------------------------------------------------


class ContractExtractor:
    """Extract all contracts from a Python module AST.

    Usage::

        tree = ast.parse(source_code)
        extractor = ContractExtractor(file_path="mymodule.py")
        result = extractor.extract_from_module(tree)
        # result: {"function_name": ContractSet, ...}
    """

    def __init__(self, *, file_path: str = "<unknown>") -> None:
        self._parser = ContractParser(file_path=file_path)
        self._file = file_path

    def extract_from_module(self, tree: ast.Module) -> Dict[str, ContractSet]:
        """Extract contracts from every scope in a module.

        Returns a mapping from qualified name to ContractSet.  The
        module-level scope is keyed as ``"<module>"``.
        """
        result: Dict[str, ContractSet] = {}

        # Module-level contracts (inline assumes, transports, invariants)
        module_cs = self._extract_module_level(tree)
        if not module_cs.is_empty():
            result["<module>"] = module_cs

        for node in ast.iter_child_nodes(tree):
            if isinstance(node, ast.FunctionDef) or isinstance(node, ast.AsyncFunctionDef):
                cs = self.extract_from_function(node)
                if not cs.is_empty():
                    result[node.name] = cs

            elif isinstance(node, ast.ClassDef):
                class_contracts = self.extract_from_class(node)
                result.update(class_contracts)

        return result

    def extract_from_function(
        self, func: Union[ast.FunctionDef, ast.AsyncFunctionDef],
    ) -> ContractSet:
        """Extract contracts from a single function definition."""
        requires: List[RequiresContract] = []
        ensures: List[EnsuresContract] = []
        invariants: List[InvariantContract] = []
        witnesses: List[WitnessContract] = []
        theorems: List[Contract] = []

        is_theorem = False

        # Process decorators
        for dec in func.decorator_list:
            contract = self._parser.parse_decorator(dec)
            if contract is None:
                continue
            self._classify_contract(contract, requires, ensures, invariants, witnesses, theorems)
            if isinstance(contract, (TheoremContract, LemmaContract)):
                is_theorem = True

        # If this is a theorem function, parse the full definition
        if is_theorem and isinstance(func, ast.FunctionDef):
            thm = self._parser.parse_theorem(func)
            # Replace the placeholder
            theorems = [
                thm if isinstance(c, TheoremContract) and not c.name else c
                for c in theorems
            ]

        # Process function body for inline contracts
        self._extract_inline_contracts(
            func.body, requires, ensures, invariants, witnesses, theorems,
        )

        return ContractSet(
            requires=requires,
            ensures=ensures,
            invariants=invariants,
            witnesses=witnesses,
            theorems=theorems,
            scope_name=func.name,
        )

    def extract_from_class(self, cls: ast.ClassDef) -> Dict[str, ContractSet]:
        """Extract contracts from a class definition.

        Returns contracts keyed by ``ClassName`` (class-level invariants)
        and ``ClassName.method_name`` (per-method contracts).
        """
        result: Dict[str, ContractSet] = {}

        # Class-level decorators → class invariants
        class_invariants: List[InvariantContract] = []
        for dec in cls.decorator_list:
            contract = self._parser.parse_decorator(dec)
            if contract is not None and isinstance(contract, InvariantContract):
                class_invariants.append(contract)

        # Check for class_invariant calls in the class body
        for stmt in cls.body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                call_name = _decorator_name(stmt.value)
                if call_name in frozenset({"class_invariant", "deppy.class_invariant"}):
                    inv = self._parser.parse_invariant(stmt.value)
                    if isinstance(inv, InvariantContract):
                        # Convert to ClassInvariant
                        ci = ClassInvariant(
                            class_name=cls.name,
                            predicate=inv.predicate,
                            description=inv.description,
                            source_location=inv.source_location,
                        )
                        class_invariants.append(ci)

        if class_invariants:
            result[cls.name] = ContractSet(
                invariants=class_invariants,
                scope_name=cls.name,
            )

        # Methods
        for item in cls.body:
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                cs = self.extract_from_function(item)
                # Add class invariants as implicit pre/post for public methods
                if class_invariants:
                    for inv in class_invariants:
                        if isinstance(inv, ClassInvariant) and inv.applies_to_method(item.name):
                            # Invariant becomes both a requires and ensures
                            pre = RequiresContract(
                                predicate=inv.predicate,
                                description=f"class invariant for {cls.name}",
                                source_location=inv.source_location,
                                provenance="synthesized",
                            )
                            post = EnsuresContract(
                                predicate=inv.predicate,
                                description=f"class invariant for {cls.name}",
                                source_location=inv.source_location,
                                provenance="synthesized",
                            )
                            cs.requires.append(pre)
                            cs.ensures.append(post)
                if not cs.is_empty():
                    result[f"{cls.name}.{item.name}"] = cs

        return result

    # -- internals ----------------------------------------------------------

    def _extract_module_level(self, tree: ast.Module) -> ContractSet:
        """Extract module-level inline contracts."""
        invariants: List[InvariantContract] = []
        theorems: List[Contract] = []

        for stmt in tree.body:
            if not isinstance(stmt, ast.Expr):
                continue
            if not isinstance(stmt.value, ast.Call):
                continue

            call_name = _decorator_name(stmt.value)

            if call_name in _ASSUME_NAMES:
                contract = self._parser.parse_assume(stmt.value)
                theorems.append(contract)

            elif call_name in _TRANSPORT_NAMES:
                contract = self._parser.parse_transport(stmt.value)
                theorems.append(contract)

            elif call_name in frozenset({"module_invariant", "deppy.module_invariant"}):
                inv = self._parser.parse_invariant(stmt.value)
                if isinstance(inv, InvariantContract):
                    mod_inv = ModuleInvariant(
                        module_name=self._file,
                        predicate=inv.predicate,
                        description=inv.description,
                        source_location=inv.source_location,
                    )
                    invariants.append(mod_inv)

        return ContractSet(invariants=invariants, theorems=theorems, scope_name="<module>")

    def _extract_inline_contracts(
        self,
        body: Sequence[ast.stmt],
        requires: List[RequiresContract],
        ensures: List[EnsuresContract],
        invariants: List[InvariantContract],
        witnesses: List[WitnessContract],
        theorems: List[Contract],
    ) -> None:
        """Walk function body for inline asserts, assumes, transports."""
        for stmt in body:
            # assert as potential contract (only at top of function body)
            if isinstance(stmt, ast.Assert):
                contract = self._parser.parse_inline_assert(stmt)
                if contract is not None:
                    self._classify_contract(
                        contract, requires, ensures, invariants, witnesses, theorems,
                    )
                continue

            # Expression statements: deppy.assume(...), deppy.transport(...)
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                call_name = _decorator_name(stmt.value)
                if call_name in _ASSUME_NAMES:
                    theorems.append(self._parser.parse_assume(stmt.value))
                elif call_name in _TRANSPORT_NAMES:
                    theorems.append(self._parser.parse_transport(stmt.value))

            # Recurse into compound statements (if/for/while/with/try)
            if isinstance(stmt, (ast.If, ast.While)):
                self._extract_inline_contracts(
                    stmt.body, requires, ensures, invariants, witnesses, theorems,
                )
                self._extract_inline_contracts(
                    stmt.orelse, requires, ensures, invariants, witnesses, theorems,
                )
            elif isinstance(stmt, ast.For):
                self._extract_inline_contracts(
                    stmt.body, requires, ensures, invariants, witnesses, theorems,
                )
                self._extract_inline_contracts(
                    stmt.orelse, requires, ensures, invariants, witnesses, theorems,
                )
            elif isinstance(stmt, ast.With):
                self._extract_inline_contracts(
                    stmt.body, requires, ensures, invariants, witnesses, theorems,
                )
            elif isinstance(stmt, ast.Try):
                self._extract_inline_contracts(
                    stmt.body, requires, ensures, invariants, witnesses, theorems,
                )
                for handler in stmt.handlers:
                    self._extract_inline_contracts(
                        handler.body, requires, ensures, invariants, witnesses, theorems,
                    )
                self._extract_inline_contracts(
                    stmt.orelse, requires, ensures, invariants, witnesses, theorems,
                )
                self._extract_inline_contracts(
                    stmt.finalbody, requires, ensures, invariants, witnesses, theorems,
                )

    def _classify_contract(
        self,
        contract: Contract,
        requires: List[RequiresContract],
        ensures: List[EnsuresContract],
        invariants: List[InvariantContract],
        witnesses: List[WitnessContract],
        theorems: List[Contract],
    ) -> None:
        """Route a parsed contract into the appropriate bucket."""
        if isinstance(contract, RequiresContract):
            requires.append(contract)
        elif isinstance(contract, (EnsuresContract, ExceptionalEnsures)):
            if isinstance(contract, ExceptionalEnsures):
                ensures.append(contract.as_ensures())
            else:
                ensures.append(contract)
        elif isinstance(contract, InvariantContract):
            invariants.append(contract)
        elif isinstance(contract, WitnessContract):
            witnesses.append(contract)
        elif isinstance(contract, (TheoremContract, LemmaContract, TransportContract, AssumptionContract)):
            theorems.append(contract)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _extract_docstring(node: Union[ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef]) -> Optional[str]:
    """Extract the docstring from a function/class definition."""
    if (
        node.body
        and isinstance(node.body[0], ast.Expr)
        and isinstance(node.body[0].value, ast.Constant)
        and isinstance(node.body[0].value.value, str)
    ):
        return node.body[0].value.value.strip()
    return None
