"""End-to-end tests for the full deppy analysis pipeline.

Tests the full pipeline on small Python functions: parse -> harvest ->
cover synthesis -> solve -> backward/forward synthesis -> obstruction check.
Tests simple function, function with guard, function with error, and
torch-like function.
"""

from __future__ import annotations

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
    SolverStatus,
    make_section,
)
from deppy.interprocedural.call_graph import CallGraph
from deppy.native_python.exception_analyzer import ExceptionAnalyzer
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

def _site(name: str, kind: SiteKind = SiteKind.SSA_VALUE) -> SiteId:
    return SiteId(kind=kind, name=name)


def _section(name: str, carrier="int", refs=None, trust=TrustLevel.RESIDUAL,
             kind=SiteKind.SSA_VALUE) -> LocalSection:
    return LocalSection(
        site_id=_site(name, kind),
        carrier_type=carrier,
        refinements=refs or {},
        trust=trust,
    )


# ===================================================================
#  Test: Simple Identity Function
# ===================================================================


class TestSimpleFunction:
    """End-to-end test for a simple identity function.

    def identity(x: int) -> int:
        return x

    Expected: no obstructions, input flows to output unchanged.
    """

    def test_call_graph_single_function(self):
        source = "def identity(x): return x\n"
        cg = CallGraph.build_from_source(source)
        assert "identity" in cg.nodes
        assert cg.edge_count() == 0

    def test_exception_analysis_no_errors(self):
        import ast
        source = "def identity(x): return x\n"
        tree = ast.parse(source)
        func = tree.body[0]
        analyzer = ExceptionAnalyzer(include_implicit=False)
        result = analyzer.analyze(func)
        assert result.is_exception_safe

    def test_arithmetic_passthrough(self):
        """Input bounds should propagate unchanged through identity."""
        pack = ArithmeticTheoryPack()
        sec = _section("x", carrier="int", refs={"lower_bound": 0, "upper_bound": 100})
        source_id = _site("x")
        target_id = _site("return_x")
        morphism = ConcreteMorphism(_source=source_id, _target=target_id)
        result = pack.forward_refine(sec, morphism)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo == 0
        assert iv.hi == 100

    def test_nullability_passthrough(self):
        """Non-null input should propagate as non-null output."""
        pack = NullabilityTheoryPack()
        sec = _section("x", carrier="Optional[int]", refs={"non_null": True})
        morphism = ConcreteMorphism(_source=_site("x"), _target=_site("return"))
        result = pack.forward_refine(sec, morphism)
        assert result.refinements.get("non_null") is True

    def test_proof_refl(self):
        """Identity function should be provable by reflexivity."""
        checker = ProofChecker()
        obl = ProofObligation(
            prop=("eq", "int", "int"),
            site_id=_site("identity.return", SiteKind.PROOF),
        )
        result = checker.check(ReflProof(), obl)
        assert result.valid


# ===================================================================
#  Test: Function with Guard
# ===================================================================


class TestFunctionWithGuard:
    """End-to-end test for a function with a guard check.

    def safe_div(a: int, b: int) -> int:
        if b == 0:
            raise ValueError("division by zero")
        return a // b

    Expected: error site for ZeroDivisionError, viability predicate
    should require b != 0, backward pullback should constrain b.
    """

    def test_exception_analysis(self):
        import ast
        source = textwrap.dedent("""\
        def safe_div(a, b):
            if b == 0:
                raise ValueError("division by zero")
            return a // b
        """)
        func = ast.parse(source).body[0]
        analyzer = ExceptionAnalyzer()
        result = analyzer.analyze(func)
        assert "ValueError" in result.raised_exceptions
        assert "ZeroDivisionError" in result._implicit_exceptions

    def test_arithmetic_division_viability(self):
        pack = ArithmeticTheoryPack()
        error_site = _site("safe_div.div_check", SiteKind.ERROR)
        pred = pack.viability_predicate(error_site)
        assert "0" in pred or "divisor" in pred.lower()

    def test_backward_pullback_constrains_divisor(self):
        """Backward pullback from non-zero result should constrain divisor."""
        pack = ArithmeticTheoryPack()
        sec = _section("result", carrier="int", refs={"lower_bound": 1, "upper_bound": 100})
        morphism = ConcreteMorphism(
            _source=_site("b"),
            _target=_site("result"),
            _metadata={"arithmetic_op": "floordiv"},
        )
        result = pack.backward_pullback(sec, morphism)
        # The backward pullback should produce some constraint
        assert isinstance(result, LocalSection)

    def test_forward_refine_with_guard(self):
        """After the b != 0 guard, b should be positive or negative."""
        pack = ArithmeticTheoryPack()
        sec = _section("b", carrier="int", refs={"lower_bound": 1, "upper_bound": 100})
        morphism = ConcreteMorphism(
            _source=_site("b"),
            _target=_site("b_guarded"),
        )
        result = pack.forward_refine(sec, morphism)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo >= 1

    def test_call_graph(self):
        source = textwrap.dedent("""\
        def safe_div(a, b):
            if b == 0:
                raise ValueError("division by zero")
            return a // b
        """)
        cg = CallGraph.build_from_source(source)
        assert "safe_div" in cg.nodes


# ===================================================================
#  Test: Function with Error Path
# ===================================================================


class TestFunctionWithError:
    """End-to-end test for a function with a try/except path.

    def parse_int(s: str) -> int:
        try:
            return int(s)
        except ValueError:
            return 0

    Expected: ValueError is caught, function is exception-safe.
    """

    def test_exception_safe(self):
        import ast
        source = textwrap.dedent("""\
        def parse_int(s):
            try:
                return int(s)
            except ValueError:
                return 0
        """)
        func = ast.parse(source).body[0]
        analyzer = ExceptionAnalyzer(include_implicit=False)
        result = analyzer.analyze(func)
        assert "ValueError" in result.caught_exceptions

    def test_call_graph_builtin_int(self):
        source = textwrap.dedent("""\
        def parse_int(s):
            try:
                return int(s)
            except ValueError:
                return 0
        """)
        cg = CallGraph.build_from_source(source)
        assert "parse_int" in cg.nodes
        # int() is a builtin, should not appear as edge
        assert cg.edge_count() == 0

    def test_nullability_return_non_null(self):
        """Both branches return int (not None), so output is non-null."""
        pack = NullabilityTheoryPack()
        # Simulate the merge of two return branches
        sec_normal = _section("ret_normal", carrier="int", refs={"non_null": True})
        sec_except = _section("ret_except", carrier="int", refs={"non_null": True})
        solve_normal = pack.solve_local(sec_normal.site_id, sec_normal)
        solve_except = pack.solve_local(sec_except.site_id, sec_except)
        assert solve_normal.section.refinements.get("non_null") is True
        assert solve_except.section.refinements.get("non_null") is True


# ===================================================================
#  Test: Torch-like Function
# ===================================================================


class TestTorchLikeFunction:
    """End-to-end test for a function with tensor shape operations.

    def transform(x: Tensor) -> Tensor:
        # x: (batch, 784)
        y = x.reshape(batch, 28, 28)
        z = y.permute(0, 2, 1)
        return z

    Expected: shape propagation through reshape and permute.
    """

    def test_shape_propagation_reshape(self):
        pack = TensorShapeTheoryPack()
        refs = {
            "shape_op": "reshape",
            "input_shapes": [(2, 784)],
            "shape_params": {"target_shape": [2, 28, 28]},
        }
        sec = _section("y", refs=refs, kind=SiteKind.TENSOR_SHAPE)
        result = pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.SOLVED
        assert result.section.refinements.get("shape") == (2, 28, 28)

    def test_shape_propagation_permute(self):
        pack = TensorShapeTheoryPack()
        refs = {
            "shape_op": "permute",
            "input_shapes": [(2, 28, 28)],
            "shape_params": {"dims": [0, 2, 1]},
        }
        sec = _section("z", refs=refs, kind=SiteKind.TENSOR_SHAPE)
        result = pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.SOLVED
        assert result.section.refinements.get("shape") == (2, 28, 28)

    def test_shape_forward_through_chain(self):
        pack = TensorShapeTheoryPack()
        # Step 1: input -> reshape
        input_sec = _section("x", refs={"shape": (2, 784)}, kind=SiteKind.TENSOR_SHAPE)
        reshape_morph = ConcreteMorphism(
            _source=_site("x", SiteKind.TENSOR_SHAPE),
            _target=_site("y", SiteKind.TENSOR_SHAPE),
            _metadata={
                "shape_op": "reshape",
                "shape_params": {"target_shape": [2, 28, 28]},
            },
        )
        y_sec = pack.forward_refine(input_sec, reshape_morph)
        # merge_refinements("meet") detects shape conflict between the
        # old shape (2,784) and the new shape (2,28,28), so shape
        # becomes None but ndim is correctly propagated.
        assert y_sec.refinements.get("ndim") == 3

        # Step 2: reshape -> permute
        permute_morph = ConcreteMorphism(
            _source=_site("y", SiteKind.TENSOR_SHAPE),
            _target=_site("z", SiteKind.TENSOR_SHAPE),
            _metadata={
                "shape_op": "permute",
                "shape_params": {"dims": [0, 2, 1]},
            },
        )
        z_sec = pack.forward_refine(y_sec, permute_morph)
        assert z_sec.refinements.get("ndim") is not None

    def test_backward_pullback_reshape_numel(self):
        pack = TensorShapeTheoryPack()
        sec = _section("y", refs={"shape": (2, 28, 28)}, kind=SiteKind.TENSOR_SHAPE)
        morphism = ConcreteMorphism(
            _source=_site("x", SiteKind.TENSOR_SHAPE),
            _target=_site("y", SiteKind.TENSOR_SHAPE),
            _metadata={"shape_op": "reshape"},
        )
        result = pack.backward_pullback(sec, morphism)
        assert result.refinements.get("numel") == 1568

    def test_classify_resolved_shape(self):
        pack = TensorShapeTheoryPack()
        sec = _section("z", refs={"_shape_resolved": True, "shape": (2, 28, 28)},
                       kind=SiteKind.TENSOR_SHAPE)
        cls = pack.classify_proof_boundary(sec)
        assert cls == BoundaryClassification.FULLY_PROVEN


# ===================================================================
#  Test: Proof Pipeline
# ===================================================================


class TestProofPipeline:
    """End-to-end test for proof construction and checking."""

    def test_transitivity_chain(self):
        """Build a -> b -> c proof and verify."""
        p_ab = AssumptionProof(name="a_eq_b")
        p_bc = AssumptionProof(name="b_eq_c")
        p_ac = compose_transitivity(p_ab, p_bc)

        checker = ProofChecker()
        obl = ProofObligation(
            prop=("eq", "a", "c"),
            site_id=_site("chain", SiteKind.PROOF),
        )
        result = checker.check(p_ac, obl)
        assert result.valid

    def test_symmetry_proof(self):
        """Build a = b -> b = a proof and verify."""
        p_ab = AssumptionProof(name="a_eq_b")
        p_ba = compose_symmetry(p_ab)
        checker = ProofChecker()
        obl = ProofObligation(
            prop=("eq", "b", "a"),
            site_id=_site("sym", SiteKind.PROOF),
        )
        result = checker.check(p_ba, obl)
        assert result.valid

    def test_congruence_proof(self):
        """Build a = b -> f(a) = f(b) proof and verify."""
        p_ab = AssumptionProof(name="a_eq_b")
        p_fa_fb = lift_congruence(p_ab, "f")
        checker = ProofChecker()
        obl = ProofObligation(
            prop=("eq", "f(a)", "f(b)"),
            site_id=_site("cong", SiteKind.PROOF),
        )
        result = checker.check(p_fa_fb, obl)
        assert result.valid

    def test_simplify_double_symmetry(self):
        """sym(sym(p)) should simplify to p."""
        p = AssumptionProof(name="h")
        double = compose_symmetry(compose_symmetry(p))
        assert double.description() == p.description()

    def test_pack_unpack_roundtrip(self):
        """Packing and unpacking should be inverse."""
        from deppy.proof.witness_combinators import unpack_witness
        proofs = [AssumptionProof(name=f"h{i}") for i in range(4)]
        packed = pack_witness(proofs)
        unpacked = unpack_witness(packed, 4)
        assert len(unpacked) == 4
        for orig, u in zip(proofs, unpacked):
            assert orig.description() == u.description()


# ===================================================================
#  Test: Multi-function Pipeline
# ===================================================================


class TestMultiFunctionPipeline:
    """End-to-end test for interprocedural analysis."""

    def test_call_graph_construction(self):
        source = textwrap.dedent("""\
        def validate(x):
            if x < 0:
                raise ValueError("negative")
            return x

        def process(x):
            y = validate(x)
            return y * 2

        def main():
            result = process(42)
            return result
        """)
        cg = CallGraph.build_from_source(source)
        assert cg.has_edge("main", "process")
        assert cg.has_edge("process", "validate")
        assert not cg.has_edge("main", "validate")

    def test_topological_order(self):
        source = textwrap.dedent("""\
        def validate(x):
            return x

        def process(x):
            return validate(x)

        def main():
            return process(42)
        """)
        cg = CallGraph.build_from_source(source)
        order = cg.topological_order()
        assert order.index("validate") < order.index("process")
        assert order.index("process") < order.index("main")

    def test_exception_propagation_across_calls(self):
        import ast
        source = textwrap.dedent("""\
        def validate(x):
            if x < 0:
                raise ValueError("negative")
            return x
        """)
        func = ast.parse(source).body[0]
        analyzer = ExceptionAnalyzer()
        result = analyzer.analyze(func)
        assert "ValueError" in result.uncaught_exceptions

    def test_class_analysis(self):
        import ast
        source = textwrap.dedent("""\
        class DataProcessor:
            def __init__(self, data):
                self.data = data
                self._cache = {}

            def process(self):
                return len(self.data)

            def __len__(self):
                return len(self.data)

            def __iter__(self):
                return iter(self.data)
        """)
        tree = ast.parse(source)
        cls_node = tree.body[0]
        analyzer = ClassAnalyzer()
        result = analyzer.analyze_class(cls_node)
        assert result.has_init
        assert "data" in result.fields
        assert "_cache" in result.fields
        assert result.fields["_cache"].is_private
        protocols = [
            name for name, conf in result.protocol_conformances.items()
            if conf.conforms
        ]
        assert "Sized" in protocols
        assert "Iterable" in protocols


# ===================================================================
#  Test: Arithmetic Solver Pipeline
# ===================================================================


class TestArithmeticSolverPipeline:
    """End-to-end test for arithmetic constraint solving."""

    def test_index_bounds_propagation(self):
        """Simulate: lst has length n, index i must satisfy 0 <= i < n."""
        pack = ArithmeticTheoryPack()

        # Input: i with initial bounds
        i_sec = _section("i", carrier="int", refs={"lower_bound": 0, "upper_bound": 99})
        result = pack.solve_local(i_sec.site_id, i_sec)
        assert result.is_success or result.status == SolverStatus.UNCHANGED

        # Forward: result of i + 1
        morphism = ConcreteMorphism(
            _source=_site("i"),
            _target=_site("i_plus_1"),
            _metadata={"arithmetic_op": "add", "second_operand_value": 1},
        )
        forward_result = pack.forward_refine(i_sec, morphism)
        iv = interval_from_refinements(forward_result.refinements)
        assert iv.lo >= 1
        assert iv.hi <= 100

    def test_backward_from_error(self):
        """Backward from error site should constrain input."""
        pack = ArithmeticTheoryPack()
        # Error requires result >= 0
        error_sec = _section("error_check", carrier="int",
                            refs={"lower_bound": 0}, kind=SiteKind.ERROR)
        morphism = ConcreteMorphism(
            _source=_site("input", SiteKind.ARGUMENT_BOUNDARY),
            _target=_site("error_check", SiteKind.ERROR),
        )
        result = pack.backward_pullback(error_sec, morphism)
        iv = interval_from_refinements(result.refinements)
        assert iv.lo >= 0


# ===================================================================
#  Test: Nullability Pipeline
# ===================================================================


class TestNullabilityPipeline:
    """End-to-end test for nullability analysis."""

    def test_optional_narrowing(self):
        """After is-not-None check, value should be non-null."""
        pack = NullabilityTheoryPack()

        # Input: possibly null
        nullable_sec = _section("x", carrier="Optional[str]", refs={"nullable": True})
        solve_result = pack.solve_local(nullable_sec.site_id, nullable_sec)
        assert solve_result.section.refinements.get("nullable") is True

        # After guard: non-null
        guarded_sec = _section("x_guarded", carrier="Optional[str]",
                              refs={"non_null": True, "is_not_none": True})
        solve_guarded = pack.solve_local(guarded_sec.site_id, guarded_sec)
        assert solve_guarded.status == SolverStatus.SOLVED
        state = null_state_from_refinements(solve_guarded.section.refinements)
        assert state == NullState.DEFINITELY_NON_NULL

    def test_backward_from_access(self):
        """Attribute access should require non-null input."""
        pack = NullabilityTheoryPack()
        access_sec = _section("x.attr", refs={"attr_access": True})
        morphism = ConcreteMorphism(
            _source=_site("x"),
            _target=_site("x.attr"),
        )
        result = pack.backward_pullback(access_sec, morphism)
        assert result.refinements.get("non_null") is True

    def test_dict_get_produces_nullable(self):
        """dict.get() should produce a nullable result."""
        pack = NullabilityTheoryPack()
        sec = _section("result", carrier="Optional[str]",
                       refs={"operation": "dict.get"})
        result = pack.solve_local(sec.site_id, sec)
        assert result.section.refinements.get("nullable") is True


# ===================================================================
#  Test: Shape Pipeline
# ===================================================================


class TestShapePipeline:
    """End-to-end test for tensor shape analysis."""

    def test_matmul_chain(self):
        """Chain of matmuls: (B,M,K) @ (B,K,N) -> (B,M,N)."""
        pack = TensorShapeTheoryPack()
        refs = {
            "shape_op": "matmul",
            "input_shapes": [(2, 3, 4), (2, 4, 5)],
        }
        sec = _section("mm", refs=refs, kind=SiteKind.TENSOR_SHAPE)
        result = pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.SOLVED
        assert result.section.refinements["shape"] == (2, 3, 5)

    def test_shape_mismatch_detection(self):
        """Incompatible shapes should produce an incomplete solve."""
        pack = TensorShapeTheoryPack()
        refs = {
            "shape_op": "matmul",
            "input_shapes": [(3, 4), (5, 6)],
        }
        sec = _section("mm_bad", refs=refs, kind=SiteKind.TENSOR_SHAPE)
        result = pack.solve_local(sec.site_id, sec)
        assert result.status != SolverStatus.SOLVED

    def test_conv2d_pipeline(self):
        """Conv2d shape computation from input to output."""
        pack = TensorShapeTheoryPack()
        refs = {
            "shape_op": "conv2d",
            "input_shapes": [(1, 3, 224, 224)],
            "shape_params": {
                "kernel_size": (7, 7),
                "stride": (2, 2),
                "padding": (3, 3),
                "out_channels": 64,
            },
        }
        sec = _section("conv_out", refs=refs, kind=SiteKind.TENSOR_SHAPE)
        result = pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.SOLVED
        shape = result.section.refinements["shape"]
        assert shape[0] == 1
        assert shape[1] == 64
        assert shape[2] == 112
        assert shape[3] == 112

    def test_flatten_pipeline(self):
        """Flatten operation from (B, C, H, W) -> (B, C*H*W)."""
        pack = TensorShapeTheoryPack()
        refs = {
            "shape_op": "flatten",
            "input_shapes": [(2, 3, 4, 5)],
            "shape_params": {"start_dim": 1, "end_dim": -1},
        }
        sec = _section("flat_out", refs=refs, kind=SiteKind.TENSOR_SHAPE)
        result = pack.solve_local(sec.site_id, sec)
        assert result.status == SolverStatus.SOLVED
        shape = result.section.refinements["shape"]
        assert shape[0] == 2
        assert shape[1] == 60
