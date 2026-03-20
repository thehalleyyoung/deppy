"""Guard harvesting stage for the sheaf-descent analysis pipeline.

Stage 1: Traverse the IR and harvest guards, assertions, type annotations,
contract decorators, and structural patterns that produce refinement
predicates.  Aggregates results from multiple harvester strategies.
"""

from __future__ import annotations

import ast
import enum
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

from deppy.core._protocols import SiteId, SiteKind, TrustLevel, LocalSection
from deppy.pipeline.pipeline_config import PipelineConfig
from deppy.pipeline.stage_registry import Stage, StageMetadata
from deppy.pipeline.stages.parse_stage import IRModule, ScopeInfo, ParseResult


# ===================================================================
#  Harvest data structures
# ===================================================================


class GuardKind(enum.Enum):
    """Classification of harvested guard sources."""

    IF_CONDITION = "if_condition"
    ASSERT_STATEMENT = "assert_statement"
    TYPE_ANNOTATION = "type_annotation"
    CONTRACT_REQUIRES = "contract_requires"
    CONTRACT_ENSURES = "contract_ensures"
    CONTRACT_INVARIANT = "contract_invariant"
    ISINSTANCE_CHECK = "isinstance_check"
    NONE_CHECK = "none_check"
    COMPARISON = "comparison"
    TRUTHINESS_CHECK = "truthiness_check"
    TRY_EXCEPT = "try_except"
    WHILE_CONDITION = "while_condition"
    COMPREHENSION_FILTER = "comprehension_filter"


@dataclass(frozen=True)
class HarvestedGuard:
    """A single guard harvested from source code.

    Represents a predicate-bearing code pattern such as an if-branch,
    assertion, isinstance check, or type annotation.
    """

    _kind: GuardKind
    _scope_name: str
    _line: int
    _col: int
    _source_text: str
    _variable_name: Optional[str] = None
    _negated: bool = False
    _branch: str = "true"  # "true" or "false" branch
    _trust: TrustLevel = TrustLevel.RESIDUAL
    _metadata: Optional[Dict[str, Any]] = None

    @property
    def kind(self) -> GuardKind:
        return self._kind

    @property
    def scope_name(self) -> str:
        return self._scope_name

    @property
    def line(self) -> int:
        return self._line

    @property
    def col(self) -> int:
        return self._col

    @property
    def source_text(self) -> str:
        return self._source_text

    @property
    def variable_name(self) -> Optional[str]:
        return self._variable_name

    @property
    def negated(self) -> bool:
        return self._negated

    @property
    def branch(self) -> str:
        return self._branch

    @property
    def trust(self) -> TrustLevel:
        return self._trust

    @property
    def metadata(self) -> Optional[Dict[str, Any]]:
        return self._metadata

    def site_kind(self) -> SiteKind:
        """Map guard kind to site kind."""
        mapping = {
            GuardKind.IF_CONDITION: SiteKind.BRANCH_GUARD,
            GuardKind.ASSERT_STATEMENT: SiteKind.BRANCH_GUARD,
            GuardKind.TYPE_ANNOTATION: SiteKind.ARGUMENT_BOUNDARY,
            GuardKind.CONTRACT_REQUIRES: SiteKind.ARGUMENT_BOUNDARY,
            GuardKind.CONTRACT_ENSURES: SiteKind.RETURN_OUTPUT_BOUNDARY,
            GuardKind.CONTRACT_INVARIANT: SiteKind.LOOP_HEADER_INVARIANT,
            GuardKind.ISINSTANCE_CHECK: SiteKind.BRANCH_GUARD,
            GuardKind.NONE_CHECK: SiteKind.BRANCH_GUARD,
            GuardKind.COMPARISON: SiteKind.BRANCH_GUARD,
            GuardKind.TRUTHINESS_CHECK: SiteKind.BRANCH_GUARD,
            GuardKind.TRY_EXCEPT: SiteKind.ERROR,
            GuardKind.WHILE_CONDITION: SiteKind.LOOP_HEADER_INVARIANT,
            GuardKind.COMPREHENSION_FILTER: SiteKind.BRANCH_GUARD,
        }
        return mapping.get(self._kind, SiteKind.BRANCH_GUARD)


@dataclass(frozen=True)
class HarvestResult:
    """Result of the harvest stage."""

    _guards: Tuple[HarvestedGuard, ...]
    _scope_guard_map: Dict[str, Tuple[HarvestedGuard, ...]]
    _annotation_count: int = 0
    _contract_count: int = 0
    _guard_count: int = 0
    _warnings: Tuple[str, ...] = ()

    @property
    def guards(self) -> Tuple[HarvestedGuard, ...]:
        return self._guards

    @property
    def scope_guard_map(self) -> Dict[str, Tuple[HarvestedGuard, ...]]:
        return self._scope_guard_map

    @property
    def annotation_count(self) -> int:
        return self._annotation_count

    @property
    def contract_count(self) -> int:
        return self._contract_count

    @property
    def guard_count(self) -> int:
        return self._guard_count

    @property
    def warnings(self) -> Tuple[str, ...]:
        return self._warnings

    @property
    def total_count(self) -> int:
        return len(self._guards)

    def guards_for_scope(self, scope_name: str) -> Tuple[HarvestedGuard, ...]:
        return self._scope_guard_map.get(scope_name, ())


# ===================================================================
#  Guard harvesters
# ===================================================================


class _GuardHarvester(ast.NodeVisitor):
    """AST visitor that harvests guard-bearing patterns."""

    def __init__(self, source_lines: List[str], scope_name: str) -> None:
        self._source_lines = source_lines
        self._scope_name = scope_name
        self._guards: List[HarvestedGuard] = []

    def _source_at(self, node: ast.AST) -> str:
        """Best-effort source reconstruction for a node."""
        try:
            return ast.unparse(node)
        except Exception:
            line = getattr(node, "lineno", 0)
            if 0 < line <= len(self._source_lines):
                return self._source_lines[line - 1].strip()
            return "<unknown>"

    def visit_If(self, node: ast.If) -> None:
        """Harvest if-condition guards."""
        source = self._source_at(node.test)
        var_name = self._extract_test_variable(node.test)

        self._guards.append(HarvestedGuard(
            _kind=self._classify_test(node.test),
            _scope_name=self._scope_name,
            _line=node.lineno,
            _col=node.col_offset,
            _source_text=source,
            _variable_name=var_name,
            _branch="true",
            _trust=TrustLevel.TRUSTED_AUTO,
        ))

        if node.orelse:
            self._guards.append(HarvestedGuard(
                _kind=self._classify_test(node.test),
                _scope_name=self._scope_name,
                _line=node.lineno,
                _col=node.col_offset,
                _source_text=source,
                _variable_name=var_name,
                _negated=True,
                _branch="false",
                _trust=TrustLevel.TRUSTED_AUTO,
            ))

        self.generic_visit(node)

    def visit_Assert(self, node: ast.Assert) -> None:
        """Harvest assert statements."""
        source = self._source_at(node.test)
        var_name = self._extract_test_variable(node.test)

        self._guards.append(HarvestedGuard(
            _kind=GuardKind.ASSERT_STATEMENT,
            _scope_name=self._scope_name,
            _line=node.lineno,
            _col=node.col_offset,
            _source_text=source,
            _variable_name=var_name,
            _trust=TrustLevel.TRUSTED_AUTO,
        ))
        self.generic_visit(node)

    def visit_While(self, node: ast.While) -> None:
        """Harvest while-loop conditions as loop invariant candidates."""
        source = self._source_at(node.test)
        self._guards.append(HarvestedGuard(
            _kind=GuardKind.WHILE_CONDITION,
            _scope_name=self._scope_name,
            _line=node.lineno,
            _col=node.col_offset,
            _source_text=source,
            _variable_name=self._extract_test_variable(node.test),
            _trust=TrustLevel.BOUNDED_AUTO,
        ))
        self.generic_visit(node)

    def visit_Try(self, node: ast.Try) -> None:
        """Harvest try/except patterns."""
        for handler in node.handlers:
            exc_type = ""
            if handler.type is not None:
                try:
                    exc_type = ast.unparse(handler.type)
                except Exception:
                    exc_type = "<exception>"
            self._guards.append(HarvestedGuard(
                _kind=GuardKind.TRY_EXCEPT,
                _scope_name=self._scope_name,
                _line=handler.lineno,
                _col=handler.col_offset,
                _source_text=f"except {exc_type}" if exc_type else "except",
                _variable_name=handler.name,
                _trust=TrustLevel.TRACE_BACKED,
                _metadata={"exception_type": exc_type},
            ))
        self.generic_visit(node)

    def visit_ListComp(self, node: ast.ListComp) -> None:
        self._harvest_comprehension_filters(node.generators, node.lineno, node.col_offset)
        self.generic_visit(node)

    def visit_SetComp(self, node: ast.SetComp) -> None:
        self._harvest_comprehension_filters(node.generators, node.lineno, node.col_offset)
        self.generic_visit(node)

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:
        self._harvest_comprehension_filters(node.generators, node.lineno, node.col_offset)
        self.generic_visit(node)

    def _harvest_comprehension_filters(
        self,
        generators: List[ast.comprehension],
        line: int,
        col: int,
    ) -> None:
        for gen in generators:
            for if_clause in gen.ifs:
                source = self._source_at(if_clause)
                self._guards.append(HarvestedGuard(
                    _kind=GuardKind.COMPREHENSION_FILTER,
                    _scope_name=self._scope_name,
                    _line=line,
                    _col=col,
                    _source_text=source,
                    _variable_name=self._extract_test_variable(if_clause),
                    _trust=TrustLevel.BOUNDED_AUTO,
                ))

    def _classify_test(self, node: ast.expr) -> GuardKind:
        """Classify a test expression into a guard kind."""
        if isinstance(node, ast.Call):
            func = node.func
            if isinstance(func, ast.Name) and func.id == "isinstance":
                return GuardKind.ISINSTANCE_CHECK
        if isinstance(node, ast.Compare):
            for op in node.ops:
                if isinstance(op, (ast.Is, ast.IsNot)):
                    if (node.comparators and
                        isinstance(node.comparators[0], ast.Constant) and
                        node.comparators[0].value is None):
                        return GuardKind.NONE_CHECK
            return GuardKind.COMPARISON
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return GuardKind.TRUTHINESS_CHECK
        if isinstance(node, ast.BoolOp):
            return GuardKind.IF_CONDITION
        return GuardKind.IF_CONDITION

    def _extract_test_variable(self, node: ast.expr) -> Optional[str]:
        """Extract the primary variable being tested."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Compare) and isinstance(node.left, ast.Name):
            return node.left.id
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id == "isinstance":
                if node.args and isinstance(node.args[0], ast.Name):
                    return node.args[0].id
        if isinstance(node, ast.UnaryOp) and isinstance(node.operand, ast.Name):
            return node.operand.id
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            return node.value.id
        return None


def _harvest_annotations(scope: ScopeInfo) -> List[HarvestedGuard]:
    """Harvest type annotations from a scope."""
    guards: List[HarvestedGuard] = []
    for param in scope.parameters:
        if param.has_annotation and param.annotation is not None:
            guards.append(HarvestedGuard(
                _kind=GuardKind.TYPE_ANNOTATION,
                _scope_name=scope.qualified_name,
                _line=param.annotation.line,
                _col=param.annotation.col,
                _source_text=param.annotation.annotation_text,
                _variable_name=param.name,
                _trust=TrustLevel.TRUSTED_AUTO,
                _metadata={"param_name": param.name},
            ))
    if scope.return_annotation is not None:
        guards.append(HarvestedGuard(
            _kind=GuardKind.TYPE_ANNOTATION,
            _scope_name=scope.qualified_name,
            _line=scope.return_annotation.line,
            _col=scope.return_annotation.col,
            _source_text=scope.return_annotation.annotation_text,
            _variable_name="<return>",
            _trust=TrustLevel.TRUSTED_AUTO,
            _metadata={"is_return": True},
        ))
    return guards


def _harvest_contracts(scope: ScopeInfo) -> List[HarvestedGuard]:
    """Harvest contract decorators from a scope."""
    guards: List[HarvestedGuard] = []
    contract_map = {
        "requires": GuardKind.CONTRACT_REQUIRES,
        "ensures": GuardKind.CONTRACT_ENSURES,
        "invariant": GuardKind.CONTRACT_INVARIANT,
        "loop_invariant": GuardKind.CONTRACT_INVARIANT,
        "class_invariant": GuardKind.CONTRACT_INVARIANT,
    }
    for dec in scope.decorators:
        base = dec.split("(")[0].split(".")[-1]
        if base in contract_map:
            kind = contract_map[base]
            trust = TrustLevel.TRUSTED_AUTO
            if base in ("ensures",):
                trust = TrustLevel.BOUNDED_AUTO
            guards.append(HarvestedGuard(
                _kind=kind,
                _scope_name=scope.qualified_name,
                _line=scope.line_start,
                _col=0,
                _source_text=dec,
                _trust=trust,
                _metadata={"decorator": dec},
            ))
    return guards


def _harvest_docstring_contracts(scope: ScopeInfo) -> List[HarvestedGuard]:
    """Harvest synthesized contracts from docstring text."""
    if not scope.docstring or scope.kind not in {"function", "method", "async_function"}:
        return []
    from deppy.nl_synthesis.docstring_parser import parse_docstring_fragments
    from deppy.nl_synthesis.verifier import verify_synthesized_constraints

    params = [
        param.name
        for param in scope.parameters
        if param.name and not param.is_self and not param.is_cls
    ]
    fragments = parse_docstring_fragments(scope.docstring)
    constraints = verify_synthesized_constraints(
        fragments,
        params,
    )
    fragment_texts: Dict[Tuple[str, Optional[str]], List[str]] = {}
    for fragment in fragments:
        key = (fragment.kind, fragment.target or ("result" if fragment.kind == "ensures" else None))
        fragment_texts.setdefault(key, []).append(fragment.normalized_text or fragment.text)

    kind_map = {
        "requires": GuardKind.CONTRACT_REQUIRES,
        "ensures": GuardKind.CONTRACT_ENSURES,
        "invariant": GuardKind.CONTRACT_INVARIANT,
    }
    guards: List[HarvestedGuard] = []
    for constraint in constraints:
        if constraint.verification_status != "accepted":
            continue
        kind = kind_map.get(constraint.kind)
        if kind is None:
            continue
        target = constraint.target
        variable_name = "<return>" if constraint.kind == "ensures" else target
        fragment_key = (constraint.kind, target)
        fragment_source = " && ".join(fragment_texts.get(fragment_key, ()))
        predicate_text = constraint.predicate_text or constraint.description
        if (
            target
            and constraint.kind in {"requires", "invariant"}
            and "result" in predicate_text
            and target not in predicate_text
        ):
            predicate_text = predicate_text.replace("result", target)
        source_text = fragment_source or predicate_text
        if fragment_source and predicate_text and predicate_text not in fragment_source:
            source_text = f"{fragment_source} [{predicate_text}]"
        guards.append(
            HarvestedGuard(
                _kind=kind,
                _scope_name=scope.qualified_name,
                _line=scope.line_start,
                _col=0,
                _source_text=source_text,
                _variable_name=variable_name,
                _trust=constraint.trust,
                _metadata={
                    "source": "docstring",
                    "fragment_text": fragment_source,
                    "description": constraint.description,
                    "predicate_text": predicate_text,
                    "template_name": constraint.template_name,
                    "verification_status": constraint.verification_status,
                },
            )
        )
    return guards


# ===================================================================
#  HarvestStage
# ===================================================================


class HarvestStage(Stage):
    """Stage 1: Harvest guards, annotations, and contracts from the IR.

    Traverses the AST via the IR module, running all harvester strategies,
    and aggregates results into a HarvestResult.
    """

    def metadata(self) -> StageMetadata:
        return StageMetadata(
            _name="harvest",
            _description="Harvest guards, annotations, and contracts",
            _dependencies=frozenset({"parse"}),
            _order_hint=10,
        )

    def run(self, context: Dict[str, Any], config: PipelineConfig) -> HarvestResult:
        """Execute harvest stage.

        Expects context to contain ``parse`` key with a ParseResult.
        """
        parse_result: ParseResult = context.get("parse")  # type: ignore[assignment]
        if parse_result is None or not parse_result.success:
            return HarvestResult(
                _guards=(),
                _scope_guard_map={},
                _warnings=("Parse stage did not produce a valid result",),
            )

        ir = parse_result.ir_module
        return self._harvest_module(ir, config)

    def _harvest_module(self, ir: IRModule, config: PipelineConfig) -> HarvestResult:
        """Harvest from an IR module."""
        all_guards: List[HarvestedGuard] = []
        scope_map: Dict[str, List[HarvestedGuard]] = {}
        warnings: List[str] = []
        annotation_count = 0
        contract_count = 0
        guard_count = 0

        source_lines = ir.source_info.source_text.splitlines()

        for scope in ir.scopes:
            scope_guards: List[HarvestedGuard] = []

            # Harvest type annotations
            ann_guards = _harvest_annotations(scope)
            scope_guards.extend(ann_guards)
            annotation_count += len(ann_guards)

            # Harvest contract decorators
            con_guards = _harvest_contracts(scope)
            scope_guards.extend(con_guards)
            contract_count += len(con_guards)

            # Harvest docstring-derived contracts
            doc_guards = _harvest_docstring_contracts(scope)
            scope_guards.extend(doc_guards)
            contract_count += len(doc_guards)

            # Harvest guards from AST if we have the tree
            if ir.ast_tree is not None:
                ast_guards = self._harvest_ast_guards(
                    ir.ast_tree, scope, source_lines
                )
                scope_guards.extend(ast_guards)
                guard_count += len(ast_guards)

            scope_map[scope.qualified_name] = scope_guards
            all_guards.extend(scope_guards)

        frozen_scope_map = {
            k: tuple(v) for k, v in scope_map.items()
        }

        return HarvestResult(
            _guards=tuple(all_guards),
            _scope_guard_map=frozen_scope_map,
            _annotation_count=annotation_count,
            _contract_count=contract_count,
            _guard_count=guard_count,
            _warnings=tuple(warnings),
        )

    def _harvest_ast_guards(
        self,
        tree: ast.AST,
        scope: ScopeInfo,
        source_lines: List[str],
    ) -> List[HarvestedGuard]:
        """Harvest guard patterns from the AST for a specific scope."""
        # Find the AST node corresponding to this scope
        scope_node = self._find_scope_node(tree, scope)
        if scope_node is None:
            return []

        harvester = _GuardHarvester(source_lines, scope.qualified_name)
        harvester.visit(scope_node)
        return harvester._guards

    @staticmethod
    def _find_scope_node(tree: ast.AST, scope: ScopeInfo) -> Optional[ast.AST]:
        """Find the AST node for a given scope by matching line numbers."""
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                if (getattr(node, "name", "") == scope.name and
                    getattr(node, "lineno", -1) == scope.line_start):
                    return node
        return None
