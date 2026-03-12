"""List, dict, set, and generator comprehension analysis.

Analyzes Python comprehension expressions to determine:
- Element types from the comprehension body
- Filter conditions and their implied refinements
- Nested comprehension structure
- Iterable sources and their required protocols

In the sheaf-descent framework, comprehensions create derived sections
whose types depend on the element expression and filter predicates.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
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
)


# ---------------------------------------------------------------------------
# Comprehension kind
# ---------------------------------------------------------------------------

class ComprehensionKind:
    """Enumeration of comprehension types."""
    LIST = "list"
    SET = "set"
    DICT = "dict"
    GENERATOR = "generator"


# ---------------------------------------------------------------------------
# Generator info (for-clause in a comprehension)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GeneratorClauseInfo:
    """Information about a single for-clause in a comprehension.

    Attributes:
        _target_names: Variable names bound by the for-clause.
        _iterable_text: Text of the iterable expression.
        _is_async: Whether this is an async for-clause.
        _line: Source line number.
        _filters: Filter (if-clause) expressions.
        _iterable_is_name: Whether the iterable is a simple name reference.
        _iterable_name: The iterable variable name (if simple).
    """

    _target_names: Tuple[str, ...] = ()
    _iterable_text: str = ""
    _is_async: bool = False
    _line: int = 0
    _filters: Tuple[str, ...] = ()
    _iterable_is_name: bool = False
    _iterable_name: Optional[str] = None

    @property
    def target_names(self) -> Tuple[str, ...]:
        return self._target_names

    @property
    def iterable_text(self) -> str:
        return self._iterable_text

    @property
    def is_async(self) -> bool:
        return self._is_async

    @property
    def filters(self) -> Tuple[str, ...]:
        return self._filters

    @property
    def has_filters(self) -> bool:
        return len(self._filters) > 0

    @property
    def iterable_name(self) -> Optional[str]:
        return self._iterable_name


# ---------------------------------------------------------------------------
# Filter info
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class FilterInfo:
    """Information about a filter (if-clause) in a comprehension.

    Attributes:
        _text: Text representation of the filter expression.
        _variables_used: Variables referenced in the filter.
        _is_type_check: Whether this is a type-narrowing check.
        _type_check_var: Variable being type-checked (if is_type_check).
        _type_check_type: Type being checked against (if is_type_check).
        _is_none_check: Whether this checks for None.
        _is_comparison: Whether this is a comparison operation.
    """

    _text: str = ""
    _variables_used: FrozenSet[str] = frozenset()
    _is_type_check: bool = False
    _type_check_var: Optional[str] = None
    _type_check_type: Optional[str] = None
    _is_none_check: bool = False
    _is_comparison: bool = False

    @property
    def text(self) -> str:
        return self._text

    @property
    def variables_used(self) -> FrozenSet[str]:
        return self._variables_used

    @property
    def is_type_check(self) -> bool:
        return self._is_type_check

    @property
    def is_none_check(self) -> bool:
        return self._is_none_check


# ---------------------------------------------------------------------------
# Comprehension info
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ComprehensionInfo:
    """Complete analysis result for a comprehension expression.

    Attributes:
        _kind: The kind of comprehension (list, set, dict, generator).
        _element_text: Text of the element expression.
        _key_text: Text of the key expression (dict comprehensions only).
        _value_text: Text of the value expression (dict comprehensions only).
        _generators: For-clause information.
        _filters: All filter conditions.
        _nesting_depth: Number of nested for-clauses.
        _bound_variables: All variables bound by for-clauses.
        _free_variables: Variables referenced but not bound.
        _is_nested: Whether this comprehension is nested inside another.
        _line: Source line number.
        _has_conditional_element: Whether the element uses a conditional expr.
    """

    _kind: str = ComprehensionKind.LIST
    _element_text: str = ""
    _key_text: Optional[str] = None
    _value_text: Optional[str] = None
    _generators: Tuple[GeneratorClauseInfo, ...] = ()
    _filters: Tuple[FilterInfo, ...] = ()
    _nesting_depth: int = 1
    _bound_variables: FrozenSet[str] = frozenset()
    _free_variables: FrozenSet[str] = frozenset()
    _is_nested: bool = False
    _line: int = 0
    _has_conditional_element: bool = False

    @property
    def kind(self) -> str:
        return self._kind

    @property
    def element_text(self) -> str:
        return self._element_text

    @property
    def key_text(self) -> Optional[str]:
        return self._key_text

    @property
    def value_text(self) -> Optional[str]:
        return self._value_text

    @property
    def generators(self) -> Tuple[GeneratorClauseInfo, ...]:
        return self._generators

    @property
    def filters(self) -> Tuple[FilterInfo, ...]:
        return self._filters

    @property
    def nesting_depth(self) -> int:
        return self._nesting_depth

    @property
    def bound_variables(self) -> FrozenSet[str]:
        return self._bound_variables

    @property
    def free_variables(self) -> FrozenSet[str]:
        return self._free_variables

    @property
    def has_filters(self) -> bool:
        return len(self._filters) > 0

    @property
    def is_flat(self) -> bool:
        return self._nesting_depth == 1

    @property
    def is_dict(self) -> bool:
        return self._kind == ComprehensionKind.DICT


# ---------------------------------------------------------------------------
# AST helpers
# ---------------------------------------------------------------------------

def _extract_target_names(target: ast.expr) -> List[str]:
    """Extract variable names from a for-clause target."""
    if isinstance(target, ast.Name):
        return [target.id]
    if isinstance(target, (ast.Tuple, ast.List)):
        names: List[str] = []
        for elt in target.elts:
            names.extend(_extract_target_names(elt))
        return names
    if isinstance(target, ast.Starred):
        return _extract_target_names(target.value)
    return []


def _collect_names(node: ast.expr) -> Set[str]:
    """Collect all Name references in an expression."""
    names: Set[str] = set()

    class NameCollector(ast.NodeVisitor):
        def visit_Name(self, n: ast.Name) -> None:
            names.add(n.id)
        def visit_Attribute(self, n: ast.Attribute) -> None:
            self.visit(n.value)

    NameCollector().visit(node)
    return names


def _analyze_filter(filter_node: ast.expr) -> FilterInfo:
    """Analyze a single filter (if-clause) expression."""
    text = ast.unparse(filter_node)
    variables = frozenset(_collect_names(filter_node))

    is_type_check = False
    type_check_var: Optional[str] = None
    type_check_type: Optional[str] = None
    is_none_check = False
    is_comparison = False

    # isinstance(x, Type) check
    if (
        isinstance(filter_node, ast.Call)
        and isinstance(filter_node.func, ast.Name)
        and filter_node.func.id == "isinstance"
        and len(filter_node.args) >= 2
    ):
        is_type_check = True
        if isinstance(filter_node.args[0], ast.Name):
            type_check_var = filter_node.args[0].id
        type_check_type = ast.unparse(filter_node.args[1])

    # x is not None / x is None checks
    if isinstance(filter_node, ast.Compare):
        is_comparison = True
        for op, comparator in zip(filter_node.ops, filter_node.comparators):
            if isinstance(comparator, ast.Constant) and comparator.value is None:
                is_none_check = True
            elif isinstance(op, (ast.Is, ast.IsNot)):
                if isinstance(comparator, ast.Constant) and comparator.value is None:
                    is_none_check = True

    # x (truthy check)
    if isinstance(filter_node, ast.Name):
        is_none_check = True  # truthiness check implies non-None

    return FilterInfo(
        _text=text,
        _variables_used=variables,
        _is_type_check=is_type_check,
        _type_check_var=type_check_var,
        _type_check_type=type_check_type,
        _is_none_check=is_none_check,
        _is_comparison=is_comparison,
    )


def _has_conditional_element(node: ast.expr) -> bool:
    """Check if an element expression contains an IfExp."""
    if isinstance(node, ast.IfExp):
        return True
    for child in ast.walk(node):
        if isinstance(child, ast.IfExp):
            return True
    return False


def _check_nested_comprehension(node: ast.expr) -> bool:
    """Check if an expression contains a nested comprehension."""
    for child in ast.walk(node):
        if isinstance(child, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            if child is not node:
                return True
    return False


# ---------------------------------------------------------------------------
# ComprehensionAnalyzer
# ---------------------------------------------------------------------------

class ComprehensionAnalyzer:
    """Analyze list, dict, set, and generator comprehensions.

    Extracts element types, filter conditions, nesting structure, and
    variable binding patterns from comprehension expressions.
    """

    def __init__(self) -> None:
        self._analysis_cache: Dict[int, ComprehensionInfo] = {}

    def analyze_comprehension(
        self,
        comp_ast: ast.expr,
    ) -> ComprehensionInfo:
        """Analyze a comprehension AST node.

        Accepts ListComp, SetComp, DictComp, or GeneratorExp.
        """
        node_id = id(comp_ast)
        if node_id in self._analysis_cache:
            return self._analysis_cache[node_id]

        if isinstance(comp_ast, ast.ListComp):
            result = self._analyze_list_comp(comp_ast)
        elif isinstance(comp_ast, ast.SetComp):
            result = self._analyze_set_comp(comp_ast)
        elif isinstance(comp_ast, ast.DictComp):
            result = self._analyze_dict_comp(comp_ast)
        elif isinstance(comp_ast, ast.GeneratorExp):
            result = self._analyze_generator_exp(comp_ast)
        else:
            result = ComprehensionInfo()

        self._analysis_cache[node_id] = result
        return result

    def analyze_all_in_function(
        self,
        func_ast: ast.FunctionDef,
    ) -> List[ComprehensionInfo]:
        """Find and analyze all comprehensions in a function body."""
        results: List[ComprehensionInfo] = []

        class CompFinder(ast.NodeVisitor):
            def visit_ListComp(inner_self, node: ast.ListComp) -> None:
                results.append(self.analyze_comprehension(node))
                inner_self.generic_visit(node)

            def visit_SetComp(inner_self, node: ast.SetComp) -> None:
                results.append(self.analyze_comprehension(node))
                inner_self.generic_visit(node)

            def visit_DictComp(inner_self, node: ast.DictComp) -> None:
                results.append(self.analyze_comprehension(node))
                inner_self.generic_visit(node)

            def visit_GeneratorExp(inner_self, node: ast.GeneratorExp) -> None:
                results.append(self.analyze_comprehension(node))
                inner_self.generic_visit(node)

        finder = CompFinder()
        for stmt in func_ast.body:
            finder.visit(stmt)

        return results

    # -- Internal -----------------------------------------------------------

    def _analyze_generators(
        self, generators: List[ast.comprehension]
    ) -> Tuple[Tuple[GeneratorClauseInfo, ...], Tuple[FilterInfo, ...], FrozenSet[str]]:
        """Analyze the generator clauses of a comprehension."""
        gen_infos: List[GeneratorClauseInfo] = []
        all_filters: List[FilterInfo] = []
        bound_vars: Set[str] = set()

        for gen in generators:
            target_names = _extract_target_names(gen.target)
            bound_vars.update(target_names)

            iterable_text = ast.unparse(gen.iter)
            iterable_is_name = isinstance(gen.iter, ast.Name)
            iterable_name = gen.iter.id if iterable_is_name else None

            # Process filters
            filter_texts: List[str] = []
            for if_clause in gen.ifs:
                filter_info = _analyze_filter(if_clause)
                all_filters.append(filter_info)
                filter_texts.append(filter_info.text)

            gen_info = GeneratorClauseInfo(
                _target_names=tuple(target_names),
                _iterable_text=iterable_text,
                _is_async=gen.is_async,
                _line=getattr(gen, "lineno", 0),
                _filters=tuple(filter_texts),
                _iterable_is_name=iterable_is_name,
                _iterable_name=iterable_name,
            )
            gen_infos.append(gen_info)

        return tuple(gen_infos), tuple(all_filters), frozenset(bound_vars)

    def _compute_free_vars(
        self,
        element_node: ast.expr,
        bound_vars: FrozenSet[str],
        generators: List[ast.comprehension],
    ) -> FrozenSet[str]:
        """Compute free variables in the comprehension."""
        all_names: Set[str] = _collect_names(element_node)
        for gen in generators:
            all_names |= _collect_names(gen.iter)
            for if_clause in gen.ifs:
                all_names |= _collect_names(if_clause)
        return frozenset(all_names - bound_vars)

    def _analyze_list_comp(self, node: ast.ListComp) -> ComprehensionInfo:
        gens, filters, bound = self._analyze_generators(node.generators)
        free = self._compute_free_vars(node.elt, bound, node.generators)
        line = getattr(node, "lineno", 0)

        return ComprehensionInfo(
            _kind=ComprehensionKind.LIST,
            _element_text=ast.unparse(node.elt),
            _generators=gens,
            _filters=filters,
            _nesting_depth=len(node.generators),
            _bound_variables=bound,
            _free_variables=free,
            _is_nested=_check_nested_comprehension(node.elt),
            _line=line,
            _has_conditional_element=_has_conditional_element(node.elt),
        )

    def _analyze_set_comp(self, node: ast.SetComp) -> ComprehensionInfo:
        gens, filters, bound = self._analyze_generators(node.generators)
        free = self._compute_free_vars(node.elt, bound, node.generators)
        line = getattr(node, "lineno", 0)

        return ComprehensionInfo(
            _kind=ComprehensionKind.SET,
            _element_text=ast.unparse(node.elt),
            _generators=gens,
            _filters=filters,
            _nesting_depth=len(node.generators),
            _bound_variables=bound,
            _free_variables=free,
            _is_nested=_check_nested_comprehension(node.elt),
            _line=line,
            _has_conditional_element=_has_conditional_element(node.elt),
        )

    def _analyze_dict_comp(self, node: ast.DictComp) -> ComprehensionInfo:
        gens, filters, bound = self._analyze_generators(node.generators)
        key_names = _collect_names(node.key)
        val_names = _collect_names(node.value)
        all_names = key_names | val_names
        for gen in node.generators:
            all_names |= _collect_names(gen.iter)
            for if_clause in gen.ifs:
                all_names |= _collect_names(if_clause)
        free = frozenset(all_names - bound)
        line = getattr(node, "lineno", 0)

        return ComprehensionInfo(
            _kind=ComprehensionKind.DICT,
            _element_text=f"{ast.unparse(node.key)}: {ast.unparse(node.value)}",
            _key_text=ast.unparse(node.key),
            _value_text=ast.unparse(node.value),
            _generators=gens,
            _filters=filters,
            _nesting_depth=len(node.generators),
            _bound_variables=bound,
            _free_variables=free,
            _line=line,
            _has_conditional_element=(
                _has_conditional_element(node.key)
                or _has_conditional_element(node.value)
            ),
        )

    def _analyze_generator_exp(self, node: ast.GeneratorExp) -> ComprehensionInfo:
        gens, filters, bound = self._analyze_generators(node.generators)
        free = self._compute_free_vars(node.elt, bound, node.generators)
        line = getattr(node, "lineno", 0)

        return ComprehensionInfo(
            _kind=ComprehensionKind.GENERATOR,
            _element_text=ast.unparse(node.elt),
            _generators=gens,
            _filters=filters,
            _nesting_depth=len(node.generators),
            _bound_variables=bound,
            _free_variables=free,
            _is_nested=_check_nested_comprehension(node.elt),
            _line=line,
            _has_conditional_element=_has_conditional_element(node.elt),
        )

    def clear_cache(self) -> None:
        """Clear the analysis cache."""
        self._analysis_cache.clear()
