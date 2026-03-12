"""Collection harvester -- extract length/membership/emptiness facts.

Walks a Python AST to discover facts about collections: length constraints,
membership tests, emptiness checks, and iteration patterns.  Each fact is
recorded as a frozen ``CollectionFact`` dataclass.
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
    Call,
    IntLit,
    Predicate,
    SourceLocation,
    Term,
    Var,
)
from deppy.predicates.collection import Contains, LengthPred, NonEmpty
from deppy.static_analysis.observation_sites import SourceSpan


# ===================================================================
#  Fact kinds
# ===================================================================

class CollectionFactKind(enum.Enum):
    """Kind of collection fact."""
    LENGTH = "length"
    MEMBERSHIP = "membership"
    NON_MEMBERSHIP = "non_membership"
    EMPTINESS = "emptiness"
    NON_EMPTINESS = "non_emptiness"
    ITERATION = "iteration"
    SORTED = "sorted"
    UNIQUE = "unique"
    SUBSET = "subset"
    EQUALITY = "equality"
    CONSTRUCTION = "construction"
    APPEND = "append"
    EXTEND = "extend"
    REMOVAL = "removal"


class FactOrigin(enum.Enum):
    """Where the collection fact was discovered."""
    IF_TEST = "if_test"
    ASSERT = "assert"
    FOR_LOOP = "for_loop"
    COMPREHENSION = "comprehension"
    ASSIGNMENT = "assignment"
    METHOD_CALL = "method_call"
    TRUTHINESS = "truthiness"
    COMPARISON = "comparison"


# ===================================================================
#  CollectionFact dataclass
# ===================================================================

@dataclass(frozen=True)
class CollectionFact:
    """A fact about a collection extracted from the AST.

    Attributes:
        variable: The collection variable.
        fact_kind: The kind of fact.
        value: Associated value (e.g., bound for length, element for membership).
        predicate: The corresponding deppy predicate, if any.
        source_span: Source location.
        trust_level: Provenance trust.
        fact_origin: Where the fact was discovered.
        enclosing_function: Name of the enclosing function.
        element_variable: For membership/iteration, the element variable.
        length_operator: For length facts, the comparison operator.
        length_bound: For length facts, the bound value.
        is_negated: Whether the fact is negated.
        collection_type_hint: Inferred collection type (list, dict, set, tuple).
    """
    variable: str
    fact_kind: CollectionFactKind
    value: Optional[Term] = None
    predicate: Optional[Predicate] = None
    source_span: Optional[SourceSpan] = None
    trust_level: TrustLevel = TrustLevel.TRUSTED_AUTO
    fact_origin: FactOrigin = FactOrigin.COMPARISON
    enclosing_function: Optional[str] = None
    element_variable: Optional[str] = None
    length_operator: Optional[str] = None
    length_bound: Optional[Term] = None
    is_negated: bool = False
    collection_type_hint: Optional[str] = None


# ===================================================================
#  Helpers
# ===================================================================

_AST_CMP_MAP: Dict[type, str] = {
    ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">",
    ast.GtE: ">=", ast.Eq: "==", ast.NotEq: "!=",
}


def _ast_to_term(node: ast.expr) -> Optional[Term]:
    """Convert an AST expression to a Term."""
    if isinstance(node, ast.Name):
        return Var(node.id)
    if isinstance(node, ast.Constant):
        if isinstance(node.value, int) and not isinstance(node.value, bool):
            return IntLit(node.value)
        return None
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        if node.func.id == "len" and node.args:
            inner = _ast_to_term(node.args[0])
            if inner is not None:
                return Call(func="len", args=[inner])
        args: List[Term] = []
        for a in node.args:
            t = _ast_to_term(a)
            if t is None:
                return None
            args.append(t)
        return Call(func=node.func.id, args=args)
    return None


def _extract_var_name(node: ast.expr) -> Optional[str]:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _extract_var_name(node.value)
        if base is not None:
            return f"{base}.{node.attr}"
    return None


def _is_len_call(node: ast.expr) -> Tuple[bool, Optional[str]]:
    """Check if node is ``len(x)`` and return (True, variable_name)."""
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "len":
        if node.args and isinstance(node.args[0], ast.Name):
            return True, node.args[0].id
        if node.args:
            name = _extract_var_name(node.args[0])
            return True, name
    return False, None


def _source_loc(node: ast.AST, file: str) -> SourceLocation:
    return SourceLocation(
        file=file,
        line=getattr(node, "lineno", 0),
        col=getattr(node, "col_offset", 0),
        end_line=getattr(node, "end_lineno", None),
        end_col=getattr(node, "end_col_offset", None),
    )


def _infer_collection_type(node: ast.expr) -> Optional[str]:
    """Infer the collection type from a constructor or literal."""
    if isinstance(node, ast.List):
        return "list"
    if isinstance(node, ast.Set):
        return "set"
    if isinstance(node, ast.Dict):
        return "dict"
    if isinstance(node, ast.Tuple):
        return "tuple"
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        name = node.func.id
        if name in ("list", "set", "dict", "tuple", "frozenset", "deque"):
            return name
    if isinstance(node, ast.ListComp):
        return "list"
    if isinstance(node, ast.SetComp):
        return "set"
    if isinstance(node, ast.DictComp):
        return "dict"
    if isinstance(node, ast.GeneratorExp):
        return "generator"
    return None


# ===================================================================
#  CollectionHarvester visitor
# ===================================================================

class CollectionHarvester(ast.NodeVisitor):
    """AST visitor that extracts collection facts.

    Handles:
    - ``len(x) > 0``, ``len(x) == n``
    - ``item in collection``, ``item not in collection``
    - ``if lst:`` (truthiness implies non-empty)
    - ``for item in collection:`` (iteration implies iterable + non-empty)
    - Collection construction: ``x = []``, ``x = list()``, etc.
    - Method calls: ``.append()``, ``.extend()``, ``.remove()``, etc.
    - Comprehensions with filters

    Usage::

        harvester = CollectionHarvester(file="example.py")
        harvester.visit(tree)
        facts = harvester.facts
    """

    def __init__(self, file: str = "<unknown>") -> None:
        self._file = file
        self._facts: List[CollectionFact] = []
        self._function_stack: List[str] = []

    @property
    def facts(self) -> List[CollectionFact]:
        return list(self._facts)

    @property
    def _current_function(self) -> Optional[str]:
        return self._function_stack[-1] if self._function_stack else None

    def _span(self, node: ast.AST) -> SourceSpan:
        return SourceSpan.from_ast(node, self._file)

    def _add_fact(
        self,
        variable: str,
        kind: CollectionFactKind,
        node: ast.AST,
        *,
        value: Optional[Term] = None,
        predicate: Optional[Predicate] = None,
        origin: FactOrigin = FactOrigin.COMPARISON,
        trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
        element_variable: Optional[str] = None,
        length_operator: Optional[str] = None,
        length_bound: Optional[Term] = None,
        is_negated: bool = False,
        collection_type: Optional[str] = None,
    ) -> None:
        self._facts.append(CollectionFact(
            variable=variable,
            fact_kind=kind,
            value=value,
            predicate=predicate,
            source_span=self._span(node),
            trust_level=trust,
            fact_origin=origin,
            enclosing_function=self._current_function,
            element_variable=element_variable,
            length_operator=length_operator,
            length_bound=length_bound,
            is_negated=is_negated,
            collection_type_hint=collection_type,
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

    # -- If: truthiness and len checks --

    def visit_If(self, node: ast.If) -> None:
        self._extract_from_test(node.test, node, FactOrigin.IF_TEST)
        for else_node in node.orelse:
            if isinstance(else_node, ast.If):
                self._extract_from_test(else_node.test, else_node, FactOrigin.IF_TEST)
        self.generic_visit(node)

    def visit_While(self, node: ast.While) -> None:
        self._extract_from_test(node.test, node, FactOrigin.IF_TEST)
        self.generic_visit(node)

    def visit_Assert(self, node: ast.Assert) -> None:
        self._extract_from_test(node.test, node, FactOrigin.ASSERT, trust=TrustLevel.PROOF_BACKED)
        self.generic_visit(node)

    # -- For loops (iteration facts) --

    def visit_For(self, node: ast.For) -> None:
        iter_var = _extract_var_name(node.iter)
        target_var = _extract_var_name(node.target)

        if iter_var is not None:
            # Iteration implies the collection is iterable and non-empty
            # (assuming the loop body executes at least once)
            self._add_fact(
                iter_var, CollectionFactKind.ITERATION, node,
                origin=FactOrigin.FOR_LOOP,
                element_variable=target_var,
            )
            self._add_fact(
                iter_var, CollectionFactKind.NON_EMPTINESS, node,
                origin=FactOrigin.FOR_LOOP,
                predicate=NonEmpty(
                    collection=Var(iter_var),
                    source_location=_source_loc(node, self._file),
                ),
            )

        # Check for enumerate, zip, etc.
        if isinstance(node.iter, ast.Call) and isinstance(node.iter.func, ast.Name):
            func_name = node.iter.func.id
            if func_name == "enumerate" and node.iter.args:
                coll_var = _extract_var_name(node.iter.args[0])
                if coll_var is not None:
                    self._add_fact(
                        coll_var, CollectionFactKind.ITERATION, node,
                        origin=FactOrigin.FOR_LOOP,
                    )
            elif func_name == "zip" and node.iter.args:
                for arg in node.iter.args:
                    coll_var = _extract_var_name(arg)
                    if coll_var is not None:
                        self._add_fact(
                            coll_var, CollectionFactKind.ITERATION, node,
                            origin=FactOrigin.FOR_LOOP,
                        )
            elif func_name == "sorted" and node.iter.args:
                coll_var = _extract_var_name(node.iter.args[0])
                if coll_var is not None:
                    self._add_fact(
                        coll_var, CollectionFactKind.SORTED, node,
                        origin=FactOrigin.FOR_LOOP,
                    )
            elif func_name == "reversed" and node.iter.args:
                coll_var = _extract_var_name(node.iter.args[0])
                if coll_var is not None:
                    self._add_fact(
                        coll_var, CollectionFactKind.ITERATION, node,
                        origin=FactOrigin.FOR_LOOP,
                    )

        self.generic_visit(node)

    # -- Assignments (construction detection) --

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            var_name = _extract_var_name(target)
            if var_name is None:
                continue
            ctype = _infer_collection_type(node.value)
            if ctype is not None:
                self._add_fact(
                    var_name, CollectionFactKind.CONSTRUCTION, node,
                    origin=FactOrigin.ASSIGNMENT,
                    collection_type=ctype,
                )
                # Empty literal constructors
                if isinstance(node.value, (ast.List, ast.Set, ast.Tuple)):
                    if not node.value.elts:
                        self._add_fact(
                            var_name, CollectionFactKind.EMPTINESS, node,
                            origin=FactOrigin.ASSIGNMENT,
                            predicate=LengthPred(
                                collection=Var(var_name), op="==", bound=IntLit(0),
                                source_location=_source_loc(node, self._file),
                            ),
                            length_operator="==",
                            length_bound=IntLit(0),
                            collection_type=ctype,
                        )
                    else:
                        self._add_fact(
                            var_name, CollectionFactKind.LENGTH, node,
                            origin=FactOrigin.ASSIGNMENT,
                            value=IntLit(len(node.value.elts)),
                            length_operator="==",
                            length_bound=IntLit(len(node.value.elts)),
                            collection_type=ctype,
                        )
                if isinstance(node.value, ast.Dict):
                    n_keys = len(node.value.keys)
                    if n_keys == 0:
                        self._add_fact(
                            var_name, CollectionFactKind.EMPTINESS, node,
                            origin=FactOrigin.ASSIGNMENT,
                            length_operator="==",
                            length_bound=IntLit(0),
                            collection_type=ctype,
                        )
                    else:
                        self._add_fact(
                            var_name, CollectionFactKind.LENGTH, node,
                            origin=FactOrigin.ASSIGNMENT,
                            value=IntLit(n_keys),
                            length_operator="==",
                            length_bound=IntLit(n_keys),
                            collection_type=ctype,
                        )
        self.generic_visit(node)

    # -- Method calls: append, extend, remove, clear, pop, etc. --

    def visit_Expr(self, node: ast.Expr) -> None:
        if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute):
            call = node.value
            method = call.func.attr
            obj_var = _extract_var_name(call.func.value)
            if obj_var is not None:
                if method in ("append", "add", "insert"):
                    self._add_fact(
                        obj_var, CollectionFactKind.APPEND, node,
                        origin=FactOrigin.METHOD_CALL,
                    )
                elif method in ("extend", "update"):
                    self._add_fact(
                        obj_var, CollectionFactKind.EXTEND, node,
                        origin=FactOrigin.METHOD_CALL,
                    )
                elif method in ("remove", "pop", "discard", "clear"):
                    self._add_fact(
                        obj_var, CollectionFactKind.REMOVAL, node,
                        origin=FactOrigin.METHOD_CALL,
                    )
                elif method == "sort":
                    self._add_fact(
                        obj_var, CollectionFactKind.SORTED, node,
                        origin=FactOrigin.METHOD_CALL,
                    )
        self.generic_visit(node)

    # -- Comprehension extraction --

    def visit_ListComp(self, node: ast.ListComp) -> None:
        self._extract_comprehension_facts(node.generators, node, "list")
        self.generic_visit(node)

    def visit_SetComp(self, node: ast.SetComp) -> None:
        self._extract_comprehension_facts(node.generators, node, "set")
        self.generic_visit(node)

    def visit_DictComp(self, node: ast.DictComp) -> None:
        self._extract_comprehension_facts(node.generators, node, "dict")
        self.generic_visit(node)

    def _extract_comprehension_facts(
        self,
        generators: List[ast.comprehension],
        parent: ast.AST,
        comp_type: str,
    ) -> None:
        for gen in generators:
            iter_var = _extract_var_name(gen.iter)
            if iter_var is not None:
                self._add_fact(
                    iter_var, CollectionFactKind.ITERATION, parent,
                    origin=FactOrigin.COMPREHENSION,
                )
            for if_clause in gen.ifs:
                self._extract_from_test(if_clause, parent, FactOrigin.COMPREHENSION)

    # -- Core: extract facts from test expressions --

    def _extract_from_test(
        self,
        test: ast.expr,
        parent_node: ast.AST,
        origin: FactOrigin,
        *,
        trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
        is_negated: bool = False,
    ) -> None:
        # not expr
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            self._extract_from_test(
                test.operand, parent_node, origin,
                trust=trust, is_negated=not is_negated,
            )
            return

        # BoolOp
        if isinstance(test, ast.BoolOp):
            for val in test.values:
                self._extract_from_test(val, parent_node, origin, trust=trust, is_negated=is_negated)
            return

        # Compare: len(x) > 0, item in collection, etc.
        if isinstance(test, ast.Compare):
            self._extract_from_compare(test, parent_node, origin, trust=trust, is_negated=is_negated)
            return

        # Bare name: truthiness -> non-emptiness for collections
        if isinstance(test, ast.Name):
            if not is_negated:
                src = _source_loc(test, self._file)
                self._add_fact(
                    test.id, CollectionFactKind.NON_EMPTINESS, parent_node,
                    origin=FactOrigin.TRUTHINESS,
                    trust=trust,
                    predicate=NonEmpty(collection=Var(test.id), source_location=src),
                )
            else:
                self._add_fact(
                    test.id, CollectionFactKind.EMPTINESS, parent_node,
                    origin=FactOrigin.TRUTHINESS,
                    trust=trust,
                    is_negated=True,
                )
            return

        # len(x) used as truthiness
        if isinstance(test, ast.Call):
            is_len, var_name = _is_len_call(test)
            if is_len and var_name is not None:
                if not is_negated:
                    src = _source_loc(test, self._file)
                    self._add_fact(
                        var_name, CollectionFactKind.NON_EMPTINESS, parent_node,
                        origin=origin,
                        trust=trust,
                        predicate=NonEmpty(collection=Var(var_name), source_location=src),
                    )
                else:
                    self._add_fact(
                        var_name, CollectionFactKind.EMPTINESS, parent_node,
                        origin=origin,
                        trust=trust,
                        is_negated=True,
                    )
            return

    def _extract_from_compare(
        self,
        compare: ast.Compare,
        parent_node: ast.AST,
        origin: FactOrigin,
        *,
        trust: TrustLevel = TrustLevel.TRUSTED_AUTO,
        is_negated: bool = False,
    ) -> None:
        """Extract collection facts from comparisons."""
        comparators = [compare.left] + compare.comparators
        ops = compare.ops
        src = _source_loc(compare, self._file)

        for i, op in enumerate(ops):
            left = comparators[i]
            right = comparators[i + 1]

            # in / not in
            if isinstance(op, ast.In):
                elem_var = _extract_var_name(left)
                coll_var = _extract_var_name(right)
                if coll_var is not None:
                    elem_term = _ast_to_term(left) or Var(elem_var or "_")
                    coll_term = Var(coll_var)
                    kind = CollectionFactKind.NON_MEMBERSHIP if is_negated else CollectionFactKind.MEMBERSHIP
                    self._add_fact(
                        coll_var, kind, parent_node,
                        origin=origin,
                        trust=trust,
                        element_variable=elem_var,
                        predicate=Contains(element=elem_term, collection=coll_term, source_location=src),
                        is_negated=is_negated,
                    )
                continue

            if isinstance(op, ast.NotIn):
                elem_var = _extract_var_name(left)
                coll_var = _extract_var_name(right)
                if coll_var is not None:
                    elem_term = _ast_to_term(left) or Var(elem_var or "_")
                    coll_term = Var(coll_var)
                    kind = CollectionFactKind.MEMBERSHIP if is_negated else CollectionFactKind.NON_MEMBERSHIP
                    self._add_fact(
                        coll_var, kind, parent_node,
                        origin=origin,
                        trust=trust,
                        element_variable=elem_var,
                        is_negated=not is_negated,
                    )
                continue

            # len(x) comparisons
            op_str = _AST_CMP_MAP.get(type(op))
            if op_str is None:
                continue

            left_is_len, left_len_var = _is_len_call(left)
            right_is_len, right_len_var = _is_len_call(right)

            if left_is_len and left_len_var is not None:
                bound_term = _ast_to_term(right)
                if bound_term is not None:
                    coll_term = Var(left_len_var)
                    pred = LengthPred(
                        collection=coll_term, op=op_str, bound=bound_term,
                        source_location=src,
                    )
                    # Determine if this implies non-emptiness
                    kind = CollectionFactKind.LENGTH
                    if op_str == ">" and isinstance(bound_term, IntLit) and bound_term.value == 0:
                        kind = CollectionFactKind.NON_EMPTINESS
                    elif op_str == ">=" and isinstance(bound_term, IntLit) and bound_term.value >= 1:
                        kind = CollectionFactKind.NON_EMPTINESS
                    elif op_str == "==" and isinstance(bound_term, IntLit) and bound_term.value == 0:
                        kind = CollectionFactKind.EMPTINESS
                    elif op_str == "!=" and isinstance(bound_term, IntLit) and bound_term.value == 0:
                        kind = CollectionFactKind.NON_EMPTINESS

                    self._add_fact(
                        left_len_var, kind, parent_node,
                        origin=origin,
                        trust=trust,
                        predicate=pred,
                        length_operator=op_str,
                        length_bound=bound_term,
                        is_negated=is_negated,
                    )

            if right_is_len and right_len_var is not None:
                bound_term = _ast_to_term(left)
                if bound_term is not None:
                    flipped = {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "==": "==", "!=": "!="}.get(op_str)
                    if flipped is not None:
                        coll_term = Var(right_len_var)
                        pred = LengthPred(
                            collection=coll_term, op=flipped, bound=bound_term,
                            source_location=src,
                        )
                        kind = CollectionFactKind.LENGTH
                        if flipped == ">" and isinstance(bound_term, IntLit) and bound_term.value == 0:
                            kind = CollectionFactKind.NON_EMPTINESS
                        elif flipped == "==" and isinstance(bound_term, IntLit) and bound_term.value == 0:
                            kind = CollectionFactKind.EMPTINESS

                        self._add_fact(
                            right_len_var, kind, parent_node,
                            origin=origin,
                            trust=trust,
                            predicate=pred,
                            length_operator=flipped,
                            length_bound=bound_term,
                            is_negated=is_negated,
                        )


# ===================================================================
#  Convenience function
# ===================================================================

def harvest_collection_facts(
    ast_tree: ast.AST,
    *,
    file: str = "<unknown>",
) -> List[CollectionFact]:
    """Extract all collection facts from a Python AST.

    Args:
        ast_tree: The parsed AST (typically from ``ast.parse``).
        file: Source file name for provenance.

    Returns:
        A list of ``CollectionFact`` objects.
    """
    harvester = CollectionHarvester(file=file)
    harvester.visit(ast_tree)
    return harvester.facts


# ===================================================================
#  Filtering utilities
# ===================================================================

def filter_by_variable(
    facts: List[CollectionFact],
    variable: str,
) -> List[CollectionFact]:
    """Return facts about a specific collection."""
    return [f for f in facts if f.variable == variable]


def filter_by_kind(
    facts: List[CollectionFact],
    kind: CollectionFactKind,
) -> List[CollectionFact]:
    """Return facts of a specific kind."""
    return [f for f in facts if f.fact_kind == kind]


def non_empty_collections(
    facts: List[CollectionFact],
) -> FrozenSet[str]:
    """Return variables known to be non-empty."""
    return frozenset(
        f.variable for f in facts
        if f.fact_kind == CollectionFactKind.NON_EMPTINESS and not f.is_negated
    )


def empty_collections(
    facts: List[CollectionFact],
) -> FrozenSet[str]:
    """Return variables known to be empty."""
    return frozenset(
        f.variable for f in facts
        if f.fact_kind == CollectionFactKind.EMPTINESS and not f.is_negated
    )


def membership_facts(
    facts: List[CollectionFact],
) -> List[CollectionFact]:
    """Return membership and non-membership facts."""
    return [
        f for f in facts
        if f.fact_kind in (CollectionFactKind.MEMBERSHIP, CollectionFactKind.NON_MEMBERSHIP)
    ]
