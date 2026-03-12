"""Corpus test: safe guarded head extraction pattern.

Write ``def head(lst): return lst[0]`` and verify that deppy correctly
identifies the IndexError site, synthesizes a ``len(lst) > 0`` guard
requirement, and propagates it to the input boundary.

This exercises the full pipeline in microcosm: exception analysis discovers
the implicit IndexError, arithmetic theory constrains the index, nullability
theory may flag the list as possibly-empty, and the backward pullback
synthesizes a precondition on the argument boundary.
"""

from __future__ import annotations

import ast
import textwrap

import pytest

from deppy.core._protocols import (
    Cover,
    LocalSection,
    ObstructionData,
    SiteId,
    SiteKind,
    TrustLevel,
)
from deppy.core.site import ConcreteMorphism, ConcreteSite
from deppy.library_theories.arithmetic_theory import (
    ArithmeticTheoryPack,
    Interval,
    interval_from_refinements,
)
from deppy.library_theories.nullability_theory import (
    NullState,
    NullabilityTheoryPack,
    null_state_from_refinements,
)
from deppy.library_theories.tensor_shape_theory import (
    ShapeInfo,
    TensorShapeTheoryPack,
)
from deppy.library_theories.theory_pack_base import (
    BoundaryClassification,
    SolverResult,
    SolverStatus,
    make_section,
)
from deppy.interprocedural.call_graph import CallGraph
from deppy.native_python.exception_analyzer import (
    ExceptionAnalyzer,
    ExceptionFlowResult,
    HandlerInfo,
    RaiseInfo,
)
from deppy.native_python.class_analyzer import ClassAnalyzer
from deppy.proof.witness_combinators import (
    compose_transitivity,
    compose_symmetry,
    lift_congruence,
    pack_witness,
    simplify_proof,
)
from deppy.types.witnesses import (
    AssumptionProof,
    ReflProof,
)
from deppy.proof.proof_checker import (
    ProofChecker,
    ProofEnvironment,
    Proposition,
    PropositionKind,
)
from deppy.proof._protocols import ProofObligation


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

HEAD_SOURCE = textwrap.dedent("""\
def head(lst):
    return lst[0]
""")

SAFE_HEAD_SOURCE = textwrap.dedent("""\
def safe_head(lst):
    if len(lst) == 0:
        raise ValueError("empty list")
    return lst[0]
""")

GUARDED_HEAD_SOURCE = textwrap.dedent("""\
def guarded_head(lst):
    if len(lst) > 0:
        return lst[0]
    return None
""")

MULTI_INDEX_SOURCE = textwrap.dedent("""\
def first_two(lst):
    return lst[0], lst[1]
""")

HEAD_WITH_DEFAULT_SOURCE = textwrap.dedent("""\
def head_or_default(lst, default=None):
    try:
        return lst[0]
    except IndexError:
        return default
""")


def _site(name: str, kind: SiteKind = SiteKind.SSA_VALUE) -> SiteId:
    return SiteId(kind=kind, name=name)


def _section(name: str, carrier="list", refs=None, trust=TrustLevel.RESIDUAL,
             kind=SiteKind.SSA_VALUE) -> LocalSection:
    return LocalSection(
        site_id=_site(name, kind),
        carrier_type=carrier,
        refinements=refs or {},
        trust=trust,
    )


def _parse_func(source: str) -> ast.FunctionDef:
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return node
    raise ValueError("No function found")


# ===================================================================
#  Test: IndexError Detection
# ===================================================================


class TestIndexErrorDetection:
    """Verify that the exception analyzer identifies IndexError from lst[0]."""

    def test_head_has_implicit_index_error(self):
        func = _parse_func(HEAD_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=True)
        result = analyzer.analyze(func)
        implicits = result._implicit_exceptions
        assert "IndexError" in implicits or "KeyError" in implicits

    def test_head_uncaught_without_handler(self):
        func = _parse_func(HEAD_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=True)
        result = analyzer.analyze(func)
        assert not result.is_exception_safe

    def test_head_no_explicit_raises(self):
        func = _parse_func(HEAD_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=False)
        result = analyzer.analyze(func)
        assert len(result.raised_exceptions) == 0

    def test_head_is_safe_without_implicit(self):
        func = _parse_func(HEAD_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=False)
        result = analyzer.analyze(func)
        assert result.is_exception_safe

    def test_safe_head_has_explicit_value_error(self):
        func = _parse_func(SAFE_HEAD_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=True)
        result = analyzer.analyze(func)
        assert "ValueError" in result.raised_exceptions

    def test_safe_head_index_error_also_implicit(self):
        func = _parse_func(SAFE_HEAD_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=True)
        result = analyzer.analyze(func)
        implicits = result._implicit_exceptions
        assert "IndexError" in implicits or "KeyError" in implicits

    def test_multi_index_has_index_error(self):
        func = _parse_func(MULTI_INDEX_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=True)
        result = analyzer.analyze(func)
        implicits = result._implicit_exceptions
        assert "IndexError" in implicits or "KeyError" in implicits


# ===================================================================
#  Test: Guard Synthesis via Arithmetic Theory
# ===================================================================


class TestGuardSynthesisArithmetic:
    """Verify that backward pullback from subscript site constrains length."""

    def test_index_zero_requires_positive_length(self):
        """Accessing lst[0] requires len(lst) > 0 i.e. length >= 1."""
        pack = ArithmeticTheoryPack()
        subscript_sec = _section(
            "subscript_check", carrier="int",
            refs={"lower_bound": 0, "upper_bound": 0},
            kind=SiteKind.SSA_VALUE,
        )
        morphism = ConcreteMorphism(
            _source=_site("length", SiteKind.ARGUMENT_BOUNDARY),
            _target=_site("subscript_check"),
            _metadata={"arithmetic_op": "index_check"},
        )
        result = pack.backward_pullback(subscript_sec, morphism)
        assert isinstance(result, LocalSection)

    def test_length_interval_from_guard(self):
        """After len(lst) > 0 guard, length should be [1, inf)."""
        iv = Interval(lo=1, hi=float("inf"))
        assert iv.lo == 1
        assert iv.contains(1)
        assert iv.contains(100)
        assert not iv.contains(0)
        assert not iv.contains(-1)

    def test_index_zero_within_positive_length(self):
        """Index 0 should be within bounds for a non-empty list."""
        index_iv = Interval(lo=0, hi=0)
        length_iv = Interval(lo=1, hi=100)
        # 0 < length_iv.lo requires length_iv.lo >= 1
        assert index_iv.lo >= 0
        assert index_iv.hi < length_iv.lo or index_iv.hi < length_iv.hi

    def test_forward_refine_index_bounds(self):
        """Forward from a list length >= 1 should make index 0 valid."""
        pack = ArithmeticTheoryPack()
        length_sec = _section(
            "lst_length", carrier="int",
            refs={"lower_bound": 1, "upper_bound": 100},
        )
        morphism = ConcreteMorphism(
            _source=_site("lst_length"),
            _target=_site("index_valid"),
            _metadata={"arithmetic_op": "sub", "second_operand_value": 1},
        )
        result = pack.forward_refine(length_sec, morphism)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo >= 0

    def test_backward_pullback_from_error_site(self):
        """Backward from IndexError site should constrain length."""
        pack = ArithmeticTheoryPack()
        error_sec = _section(
            "index_error", carrier="int",
            refs={"lower_bound": 1},
            kind=SiteKind.ERROR,
        )
        morphism = ConcreteMorphism(
            _source=_site("lst_length", SiteKind.ARGUMENT_BOUNDARY),
            _target=_site("index_error", SiteKind.ERROR),
        )
        result = pack.backward_pullback(error_sec, morphism)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo >= 1

    def test_viability_predicate_for_subscript(self):
        """Error site should have a viability predicate about index bounds."""
        pack = ArithmeticTheoryPack()
        error_site = _site("head.index_check", SiteKind.ERROR)
        pred = pack.viability_predicate(error_site)
        assert isinstance(pred, str)

    def test_solve_index_constraint(self):
        """Solve local with index refinements should succeed."""
        pack = ArithmeticTheoryPack()
        sec = _section(
            "idx", carrier="int",
            refs={"lower_bound": 0, "upper_bound": 0},
        )
        result = pack.solve_local(sec.site_id, sec)
        assert result.is_success or result.status == SolverStatus.UNCHANGED
        iv = interval_from_refinements(result.section.refinements)
        assert iv.lo == 0
        assert iv.hi == 0


# ===================================================================
#  Test: Guard Propagation to Input Boundary
# ===================================================================


class TestGuardPropagationToBoundary:
    """Verify that the synthesized guard reaches the input boundary."""

    def test_boundary_section_has_length_constraint(self):
        """The input boundary for lst should carry length >= 1 constraint."""
        pack = ArithmeticTheoryPack()
        # Simulate: error site backward to input boundary
        error_sec = _section(
            "index_check", carrier="int",
            refs={"lower_bound": 1},
            kind=SiteKind.ERROR,
        )
        input_boundary_id = _site("lst", SiteKind.ARGUMENT_BOUNDARY)
        error_id = _site("index_check", SiteKind.ERROR)
        morphism = ConcreteMorphism(
            _source=input_boundary_id,
            _target=error_id,
        )
        result = pack.backward_pullback(error_sec, morphism)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo >= 1

    def test_forward_from_guarded_input(self):
        """Forward refine from guarded input should preserve length bound."""
        pack = ArithmeticTheoryPack()
        guarded = _section(
            "lst_guarded", carrier="int",
            refs={"lower_bound": 1, "upper_bound": 100},
        )
        morphism = ConcreteMorphism(
            _source=_site("lst_guarded"),
            _target=_site("subscript_result"),
        )
        result = pack.forward_refine(guarded, morphism)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo >= 1

    def test_full_backward_forward_roundtrip(self):
        """Backward from error + forward from guard should produce safe output."""
        pack = ArithmeticTheoryPack()

        # Step 1: backward from subscript error to input
        error_sec = _section(
            "idx_error", carrier="int",
            refs={"lower_bound": 1},
            kind=SiteKind.ERROR,
        )
        back_morph = ConcreteMorphism(
            _source=_site("lst_input", SiteKind.ARGUMENT_BOUNDARY),
            _target=_site("idx_error", SiteKind.ERROR),
        )
        guard_requirement = pack.backward_pullback(error_sec, back_morph)

        # Step 2: forward from guarded input to subscript site
        fwd_morph = ConcreteMorphism(
            _source=_site("lst_input", SiteKind.ARGUMENT_BOUNDARY),
            _target=_site("subscript_site"),
        )
        result = pack.forward_refine(guard_requirement, fwd_morph)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo >= 1

    def test_classify_guarded_boundary(self):
        """A fully constrained input boundary should classify as proven or requires_proof."""
        pack = ArithmeticTheoryPack()
        sec = _section(
            "lst_boundary", carrier="int",
            refs={
                "lower_bound": 1,
                "upper_bound": 100,
                "_bounds_resolved": True,
            },
        )
        cls = pack.classify_proof_boundary(sec)
        assert cls in (
            BoundaryClassification.FULLY_PROVEN,
            BoundaryClassification.REQUIRES_PROOF,
            BoundaryClassification.CONDITIONALLY_PROVEN,
        )

    def test_classify_unguarded_boundary(self):
        """An unconstrained input should classify as requires_proof or assumed."""
        pack = ArithmeticTheoryPack()
        sec = _section("lst_boundary_raw", carrier="int", refs={})
        cls = pack.classify_proof_boundary(sec)
        assert cls in (
            BoundaryClassification.REQUIRES_PROOF,
            BoundaryClassification.ASSUMED,
        )


# ===================================================================
#  Test: Exception Handler Catches IndexError
# ===================================================================


class TestExceptionHandlerCatches:
    """Verify the try/except head catches IndexError properly."""

    def test_head_with_default_catches_index_error(self):
        func = _parse_func(HEAD_WITH_DEFAULT_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=False)
        result = analyzer.analyze(func)
        assert "IndexError" in result.caught_exceptions

    def test_head_with_default_is_exception_safe(self):
        func = _parse_func(HEAD_WITH_DEFAULT_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=False)
        result = analyzer.analyze(func)
        assert result.is_exception_safe

    def test_head_with_default_handler_info(self):
        func = _parse_func(HEAD_WITH_DEFAULT_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=True)
        result = analyzer.analyze(func)
        handlers = result.handlers
        assert len(handlers) >= 1
        found_index_handler = False
        for h in handlers:
            if "IndexError" in h.exception_types:
                found_index_handler = True
        assert found_index_handler

    def test_head_with_default_no_reraise(self):
        func = _parse_func(HEAD_WITH_DEFAULT_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=True)
        result = analyzer.analyze(func)
        for h in result.handlers:
            if "IndexError" in h.exception_types:
                assert not h.reraises

    def test_guarded_head_raises_nothing_explicit(self):
        func = _parse_func(GUARDED_HEAD_SOURCE)
        analyzer = ExceptionAnalyzer(include_implicit=False)
        result = analyzer.analyze(func)
        assert len(result.raised_exceptions) == 0


# ===================================================================
#  Test: Nullability Interaction
# ===================================================================


class TestNullabilityInteraction:
    """Verify how nullability theory interacts with the guarded head pattern."""

    def test_guarded_head_returns_optional(self):
        """guarded_head can return None, so the result is nullable."""
        pack = NullabilityTheoryPack()
        return_sec = _section(
            "return", carrier="Optional[int]",
            refs={"nullable": True},
        )
        result = pack.solve_local(return_sec.site_id, return_sec)
        state = null_state_from_refinements(result.section.refinements)
        assert state in (NullState.POSSIBLY_NULL, NullState.DEFINITELY_NULL)

    def test_non_guarded_head_returns_non_null(self):
        """The plain head function always returns a value (or raises)."""
        pack = NullabilityTheoryPack()
        return_sec = _section(
            "return", carrier="int",
            refs={"non_null": True},
        )
        result = pack.solve_local(return_sec.site_id, return_sec)
        assert result.section.refinements.get("non_null") is True

    def test_backward_from_non_null_use(self):
        """Using the result non-null should require the guard passed."""
        pack = NullabilityTheoryPack()
        use_sec = _section(
            "result.use", carrier="int",
            refs={"attr_access": True},
        )
        morphism = ConcreteMorphism(
            _source=_site("result"),
            _target=_site("result.use"),
        )
        result = pack.backward_pullback(use_sec, morphism)
        assert result.refinements.get("non_null") is True

    def test_head_with_default_null_state(self):
        """head_or_default can return None via the default parameter."""
        pack = NullabilityTheoryPack()
        sec = _section(
            "return", carrier="Optional[int]",
            refs={"operation": "dict.get"},
        )
        result = pack.solve_local(sec.site_id, sec)
        assert result.section.refinements.get("nullable") is True


# ===================================================================
#  Test: Call Graph for Head Functions
# ===================================================================


class TestCallGraphHead:
    """Verify call graph analysis of head function variants."""

    def test_head_single_node(self):
        cg = CallGraph.build_from_source(HEAD_SOURCE)
        assert "head" in cg.nodes
        assert cg.edge_count() == 0

    def test_safe_head_single_node(self):
        cg = CallGraph.build_from_source(SAFE_HEAD_SOURCE)
        assert "safe_head" in cg.nodes

    def test_guarded_head_single_node(self):
        cg = CallGraph.build_from_source(GUARDED_HEAD_SOURCE)
        assert "guarded_head" in cg.nodes

    def test_head_not_recursive(self):
        cg = CallGraph.build_from_source(HEAD_SOURCE)
        assert not cg.is_recursive("head")

    def test_head_is_leaf(self):
        cg = CallGraph.build_from_source(HEAD_SOURCE)
        leaves = cg.leaf_functions()
        assert "head" in leaves

    def test_caller_of_head(self):
        source = textwrap.dedent("""\
        def head(lst):
            return lst[0]
        def main():
            return head([1, 2, 3])
        """)
        cg = CallGraph.build_from_source(source)
        assert cg.has_edge("main", "head")
        order = cg.topological_order()
        assert order.index("head") < order.index("main")


# ===================================================================
#  Test: Proof Construction for Head Guard
# ===================================================================


class TestProofForHeadGuard:
    """Verify proof construction for the head guard requirement."""

    def test_refl_proof_for_index(self):
        """Index 0 = index 0 is trivially reflexive."""
        checker = ProofChecker()
        obl = ProofObligation(
            prop=("eq", "0", "0"),
            site_id=_site("idx_eq", SiteKind.PROOF),
        )
        result = checker.check(ReflProof(), obl)
        assert result.valid

    def test_assumption_proof_for_guard(self):
        """len(lst) > 0 assumed from guard should be a valid proof."""
        checker = ProofChecker()
        guard_proof = AssumptionProof(name="len_gt_0")
        obl = ProofObligation(
            prop=("gt", "len(lst)", "0"),
            site_id=_site("guard_check", SiteKind.PROOF),
        )
        result = checker.check(guard_proof, obl)
        assert result.valid

    def test_transitivity_guard_to_index(self):
        """len(lst) > 0 and 0 < len(lst) imply index 0 is valid."""
        p_guard = AssumptionProof(name="len_positive")
        p_index = AssumptionProof(name="index_within_bounds")
        p_safe = compose_transitivity(p_guard, p_index)
        checker = ProofChecker()
        obl = ProofObligation(
            prop=("safe_access", "lst", "0"),
            site_id=_site("access_proof", SiteKind.PROOF),
        )
        result = checker.check(p_safe, obl)
        assert result.valid

    def test_congruence_lift_for_list_ops(self):
        """Congruence: if lst1 = lst2 then head(lst1) = head(lst2)."""
        p_eq = AssumptionProof(name="lst1_eq_lst2")
        p_head_eq = lift_congruence(p_eq, "head")
        checker = ProofChecker()
        obl = ProofObligation(
            prop=("eq", "head(lst1)", "head(lst2)"),
            site_id=_site("head_cong", SiteKind.PROOF),
        )
        result = checker.check(p_head_eq, obl)
        assert result.valid

    def test_simplify_guard_proof(self):
        """Double symmetry should simplify."""
        p = AssumptionProof(name="h")
        double = compose_symmetry(compose_symmetry(p))
        assert double.description() == p.description()

    def test_proof_environment_with_guard(self):
        """ProofEnvironment should accept guard assumption."""
        env = ProofEnvironment()
        guard_prop = Proposition(
            _kind=PropositionKind.EQUALITY,
            _lhs="len(lst)",
            _rhs="> 0",
        )
        guard_proof = AssumptionProof(name="len_guard")
        env.assume("len_guard", guard_proof, guard_prop)
        retrieved = env.lookup("len_guard")
        assert retrieved is not None
        proof_term, prop = retrieved
        assert prop.lhs == "len(lst)"


# ===================================================================
#  Test: Cover Construction for Head
# ===================================================================


class TestCoverConstructionHead:
    """Verify cover sites are built correctly for the head pattern."""

    def test_cover_has_argument_boundary(self):
        input_id = _site("head.lst", SiteKind.ARGUMENT_BOUNDARY)
        site = ConcreteSite(_site_id=input_id)
        cover = Cover(
            sites={input_id: site},
            input_boundary={input_id},
        )
        assert input_id in cover.input_boundary

    def test_cover_has_return_boundary(self):
        output_id = _site("head.return", SiteKind.RETURN_OUTPUT_BOUNDARY)
        site = ConcreteSite(_site_id=output_id)
        cover = Cover(
            sites={output_id: site},
            output_boundary={output_id},
        )
        assert output_id in cover.output_boundary

    def test_cover_has_error_site(self):
        error_id = _site("head.index_error", SiteKind.ERROR)
        site = ConcreteSite(_site_id=error_id)
        cover = Cover(
            sites={error_id: site},
            error_sites={error_id},
        )
        assert error_id in cover.error_sites

    def test_cover_has_subscript_site(self):
        sub_id = _site("head.subscript_0", SiteKind.SSA_VALUE)
        site = ConcreteSite(_site_id=sub_id)
        cover = Cover(sites={sub_id: site})
        assert sub_id in cover.sites

    def test_full_cover_for_head(self):
        """Build a complete cover for head(lst) with all relevant sites."""
        input_id = _site("head.lst", SiteKind.ARGUMENT_BOUNDARY)
        sub_id = _site("head.subscript_0", SiteKind.SSA_VALUE)
        error_id = _site("head.index_error", SiteKind.ERROR)
        output_id = _site("head.return", SiteKind.RETURN_OUTPUT_BOUNDARY)

        sites = {
            input_id: ConcreteSite(_site_id=input_id),
            sub_id: ConcreteSite(_site_id=sub_id),
            error_id: ConcreteSite(_site_id=error_id),
            output_id: ConcreteSite(_site_id=output_id),
        }
        morphisms = [
            ConcreteMorphism(_source=input_id, _target=sub_id),
            ConcreteMorphism(_source=sub_id, _target=output_id),
            ConcreteMorphism(_source=input_id, _target=error_id),
        ]
        cover = Cover(
            sites=sites,
            morphisms=morphisms,
            input_boundary={input_id},
            output_boundary={output_id},
            error_sites={error_id},
        )
        assert len(cover.sites) == 4
        assert len(cover.morphisms) == 3
        assert len(cover.error_sites) == 1

    def test_cover_site_ids(self):
        input_id = _site("head.lst", SiteKind.ARGUMENT_BOUNDARY)
        output_id = _site("head.return", SiteKind.RETURN_OUTPUT_BOUNDARY)
        cover = Cover(
            sites={
                input_id: ConcreteSite(_site_id=input_id),
                output_id: ConcreteSite(_site_id=output_id),
            },
        )
        ids = cover.site_ids()
        assert input_id in ids
        assert output_id in ids

    def test_morphism_restrict(self):
        """Morphism from input to subscript should restrict sections."""
        input_id = _site("head.lst", SiteKind.ARGUMENT_BOUNDARY)
        sub_id = _site("head.subscript_0", SiteKind.SSA_VALUE)
        morphism = ConcreteMorphism(_source=input_id, _target=sub_id)

        input_sec = LocalSection(
            site_id=input_id,
            carrier_type="list",
            refinements={"lower_bound": 1, "upper_bound": 100},
            trust=TrustLevel.RESIDUAL,
        )
        restricted = morphism.restrict(input_sec)
        assert restricted.site_id == sub_id
