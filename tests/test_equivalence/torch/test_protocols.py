"""Tests for protocol types, enums, and dataclasses in _protocols.py."""
import unittest

from deppy.core._protocols import SiteId, SiteKind
from deppy.equivalence.torch._protocols import (
    AnalysisJudgment,
    AnalysisMode,
    AnalysisVerdict,
    Bug,
    BugKind,
    CorrectnessJudgment,
    EquivalenceStrength,
    EquivalenceVerdict,
    MLIRDialect,
    MLIRLoweringStep,
    MLIRModuleSpec,
    MLIROpSpec,
    NumericalToleranceSpec,
    ProgramId,
    SheafConditionResult,
    SpecificationPresheaf,
    SpecificationSection,
    TensorCohomologyClass,
    TensorDescentDatum,
    TensorEquivalenceConfig,
    TensorGlobalJudgment,
    TensorLocalJudgment,
    TensorMorphismKind,
    TensorObstruction,
    TensorObstructionKind,
    TensorPair,
    TensorSignature,
    TensorSiteCategory,
    TensorSiteKind,
    TensorSiteMorphism,
    TensorSpec,
    TensorStratum,
    TritonBlockSpec,
    TritonKernelSpec,
    TritonMemoryAccessPattern,
    TritonReductionSpec,
)


# ── Enum tests ──────────────────────────────────────────────────────────


class TestTensorStratum(unittest.TestCase):
    def test_values(self):
        self.assertEqual(TensorStratum.METADATA.value, 0)
        self.assertEqual(TensorStratum.STRUCTURAL.value, 1)
        self.assertEqual(TensorStratum.NUMERICAL.value, 2)
        self.assertEqual(TensorStratum.BEHAVIORAL.value, 3)

    def test_ordering(self):
        self.assertLess(TensorStratum.METADATA.value, TensorStratum.STRUCTURAL.value)
        self.assertLess(TensorStratum.STRUCTURAL.value, TensorStratum.NUMERICAL.value)

    def test_count(self):
        self.assertEqual(len(TensorStratum), 4)


class TestTensorSiteKind(unittest.TestCase):
    def test_string_values(self):
        self.assertEqual(TensorSiteKind.SHAPE.value, "shape")
        self.assertEqual(TensorSiteKind.DTYPE.value, "dtype")
        self.assertEqual(TensorSiteKind.DEVICE.value, "device")
        self.assertEqual(TensorSiteKind.STRIDE.value, "stride")
        self.assertEqual(TensorSiteKind.AUTOGRAD.value, "autograd")
        self.assertEqual(TensorSiteKind.NUMERICAL.value, "numerical")
        self.assertEqual(TensorSiteKind.KERNEL_CONFIG.value, "kernel_config")
        self.assertEqual(TensorSiteKind.TRITON_BLOCK.value, "triton_block")
        self.assertEqual(TensorSiteKind.TRITON_MEMORY.value, "triton_memory")
        self.assertEqual(TensorSiteKind.TRITON_REDUCTION.value, "triton_reduction")
        self.assertEqual(TensorSiteKind.MLIR_OP.value, "mlir_op")

    def test_count(self):
        self.assertEqual(len(TensorSiteKind), 11)


class TestMLIRDialect(unittest.TestCase):
    def test_string_values(self):
        self.assertEqual(MLIRDialect.TRITON.value, "tt")
        self.assertEqual(MLIRDialect.TRITON_GPU.value, "ttg")
        self.assertEqual(MLIRDialect.ARITH.value, "arith")
        self.assertEqual(MLIRDialect.LLVM.value, "llvm")
        self.assertEqual(MLIRDialect.BUILTIN.value, "builtin")

    def test_count(self):
        self.assertEqual(len(MLIRDialect), 9)


class TestTensorMorphismKind(unittest.TestCase):
    def test_has_broadcast(self):
        self.assertIn("BROADCAST", [m.name for m in TensorMorphismKind])

    def test_count(self):
        self.assertEqual(len(TensorMorphismKind), 10)


class TestEquivalenceVerdict(unittest.TestCase):
    def test_values(self):
        self.assertEqual(EquivalenceVerdict.EQUIVALENT.value, "equivalent")
        self.assertEqual(EquivalenceVerdict.INEQUIVALENT.value, "inequivalent")
        self.assertEqual(EquivalenceVerdict.UNKNOWN.value, "unknown")

    def test_has_refined(self):
        self.assertEqual(EquivalenceVerdict.REFINED.value, "refined")


class TestTensorObstructionKind(unittest.TestCase):
    def test_has_common_kinds(self):
        names = {k.name for k in TensorObstructionKind}
        self.assertIn("SHAPE_MISMATCH", names)
        self.assertIn("DTYPE_MISMATCH", names)
        self.assertIn("NUMERICAL_DIVERGENCE", names)
        self.assertIn("GRADIENT_DIVERGENCE", names)

    def test_count(self):
        self.assertEqual(len(TensorObstructionKind), 16)


class TestAnalysisMode(unittest.TestCase):
    def test_values(self):
        self.assertEqual(AnalysisMode.EQUIVALENCE.value, "equivalence")
        self.assertEqual(AnalysisMode.BUG_FINDING.value, "bug_finding")
        self.assertEqual(AnalysisMode.CORRECTNESS.value, "correctness")
        self.assertEqual(AnalysisMode.REFINEMENT.value, "refinement")
        self.assertEqual(AnalysisMode.OPTIMIZATION.value, "optimization")

    def test_count(self):
        self.assertEqual(len(AnalysisMode), 5)


class TestAnalysisVerdict(unittest.TestCase):
    def test_values(self):
        self.assertEqual(AnalysisVerdict.VALID.value, "valid")
        self.assertEqual(AnalysisVerdict.INVALID.value, "invalid")
        self.assertEqual(AnalysisVerdict.UNKNOWN.value, "unknown")


class TestBugKind(unittest.TestCase):
    def test_has_all_kinds(self):
        names = {k.name for k in BugKind}
        expected = {
            # Tensor-level bug kinds
            "SHAPE_INCONSISTENCY", "DTYPE_INCONSISTENCY",
            "NUMERICAL_INSTABILITY", "GRADIENT_INCORRECTNESS",
            "MEMORY_VIOLATION", "UNMASKED_ACCESS", "REDUCTION_ORDER",
            "INVALID_LOWERING", "EXCEPTION_DIVERGENCE", "NONDETERMINISM",
            "ALIASING_HAZARD", "SHEAF_GLUING_FAILURE", "DESCENT_VIOLATION",
            # Python-level bug kinds (from base bug_detect)
            "DIV_ZERO", "NULL_DEREF", "INDEX_OUT_OF_BOUNDS", "KEY_MISSING",
            "TYPE_ERROR", "UNBOUND_VARIABLE", "INTEGER_OVERFLOW",
            "FP_DOMAIN_ERROR", "RESOURCE_LEAK", "USE_AFTER_CLOSE",
            "DATA_RACE", "TAINT_FLOW", "NON_TERMINATION", "STACK_OVERFLOW",
            "ASSERT_FAILURE", "PROTOCOL_VIOLATION",
        }
        self.assertEqual(names, expected)


# ── Dataclass tests ─────────────────────────────────────────────────────


class TestTensorSpec(unittest.TestCase):
    def test_construction_defaults(self):
        spec = TensorSpec()
        self.assertIsNone(spec.shape)
        self.assertIsNone(spec.dtype)
        self.assertIsNone(spec.device)
        self.assertIsNone(spec.requires_grad)

    def test_construction_with_values(self):
        spec = TensorSpec(shape=(4, 4), dtype="float32", device="cpu")
        self.assertEqual(spec.shape, (4, 4))
        self.assertEqual(spec.dtype, "float32")
        self.assertEqual(spec.device, "cpu")

    def test_frozen(self):
        spec = TensorSpec(shape=(2, 3))
        with self.assertRaises(AttributeError):
            spec.shape = (4, 4)

    def test_ndim(self):
        spec = TensorSpec(shape=(2, 3, 4))
        self.assertEqual(spec.ndim, 3)

    def test_numel(self):
        spec = TensorSpec(shape=(2, 3, 4))
        self.assertEqual(spec.numel, 24)


class TestTensorEquivalenceConfig(unittest.TestCase):
    def test_defaults(self):
        cfg = TensorEquivalenceConfig()
        self.assertEqual(cfg.strength, EquivalenceStrength.DENOTATIONAL)
        self.assertTrue(cfg.check_shape)
        self.assertTrue(cfg.check_dtype)
        self.assertTrue(cfg.check_device)
        self.assertFalse(cfg.check_stride)
        self.assertTrue(cfg.check_numerical)
        self.assertTrue(cfg.check_autograd)
        self.assertFalse(cfg.check_memory_aliasing)
        self.assertTrue(cfg.use_solver)
        self.assertEqual(cfg.solver_timeout_ms, 10000)
        self.assertFalse(cfg.verbose)

    def test_analysis_mode_default(self):
        cfg = TensorEquivalenceConfig()
        self.assertEqual(cfg.analysis_mode, AnalysisMode.EQUIVALENCE)

    def test_short_circuit_strata_default(self):
        cfg = TensorEquivalenceConfig()
        self.assertTrue(cfg.short_circuit_strata)

    def test_test_shapes_default(self):
        cfg = TensorEquivalenceConfig()
        self.assertEqual(cfg.test_shapes, ((4,), (4, 4), (2, 3, 4)))

    def test_test_dtypes_default(self):
        cfg = TensorEquivalenceConfig()
        self.assertEqual(cfg.test_dtypes, ("float32",))

    def test_test_devices_default(self):
        cfg = TensorEquivalenceConfig()
        self.assertEqual(cfg.test_devices, ("cpu",))

    def test_triton_ir_defaults(self):
        cfg = TensorEquivalenceConfig()
        self.assertTrue(cfg.check_triton_ir)
        self.assertTrue(cfg.check_triton_memory)
        self.assertTrue(cfg.check_triton_reductions)

    def test_mlir_defaults(self):
        cfg = TensorEquivalenceConfig()
        self.assertTrue(cfg.check_mlir_ops)
        self.assertTrue(cfg.check_mlir_lowering)

    def test_sheaf_defaults(self):
        cfg = TensorEquivalenceConfig()
        self.assertTrue(cfg.compute_cohomology)
        self.assertTrue(cfg.check_descent)
        self.assertFalse(cfg.use_stalk_check)


class TestNumericalToleranceSpec(unittest.TestCase):
    def test_defaults(self):
        tol = NumericalToleranceSpec()
        self.assertIsNotNone(tol.rtol)
        self.assertIsNotNone(tol.atol)

    def test_tol_for_dtype(self):
        tol = NumericalToleranceSpec()
        r, a = tol.tol_for_dtype("float32")
        self.assertIsInstance(r, float)
        self.assertIsInstance(a, float)


class TestTensorPair(unittest.TestCase):
    def test_construction(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="pair_test")
        spec_f = TensorSpec(shape=(4, 4), dtype="float32")
        spec_g = TensorSpec(shape=(4, 4), dtype="float32")
        pair = TensorPair(site_id=sid, spec_f=spec_f, spec_g=spec_g)
        self.assertTrue(pair.shapes_match)
        self.assertTrue(pair.dtypes_match)

    def test_mismatch(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="mismatch")
        pair = TensorPair(
            site_id=sid,
            spec_f=TensorSpec(shape=(4, 4)),
            spec_g=TensorSpec(shape=(2, 2)),
        )
        self.assertFalse(pair.shapes_match)


class TestTensorSignature(unittest.TestCase):
    def test_construction(self):
        sig = TensorSignature(
            inputs=(TensorSpec(shape=(4, 4)),),
            outputs=(TensorSpec(shape=(4, 4)),),
            name="sig",
        )
        self.assertEqual(sig.arity, 1)
        self.assertEqual(sig.name, "sig")


class TestTensorSiteCategory(unittest.TestCase):
    def test_empty(self):
        cat = TensorSiteCategory(sites={}, morphisms={}, _outgoing={})
        self.assertEqual(len(cat.sites), 0)

    def test_add_site(self):
        cat = TensorSiteCategory(sites={}, morphisms={}, _outgoing={})
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="s1")
        cat.add_site(sid, TensorSiteKind.SHAPE)
        self.assertIn(sid, cat.sites)
        self.assertEqual(cat.sites[sid], TensorSiteKind.SHAPE)


class TestTensorSiteMorphism(unittest.TestCase):
    def test_construction(self):
        s = SiteId(kind=SiteKind.TENSOR_SHAPE, name="src")
        t = SiteId(kind=SiteKind.TENSOR_SHAPE, name="tgt")
        m = TensorSiteMorphism(
            source=s, target=t, kind=TensorMorphismKind.BROADCAST,
        )
        self.assertEqual(m.source, s)
        self.assertEqual(m.target, t)
        self.assertEqual(m.kind, TensorMorphismKind.BROADCAST)


class TestTensorObstruction(unittest.TestCase):
    def test_construction(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="obs")
        obs = TensorObstruction(
            kind=TensorObstructionKind.SHAPE_MISMATCH,
            stratum=TensorStratum.STRUCTURAL,
            sites=[sid],
            description="Shapes differ",
        )
        self.assertEqual(obs.kind, TensorObstructionKind.SHAPE_MISMATCH)
        self.assertEqual(obs.stratum, TensorStratum.STRUCTURAL)
        self.assertEqual(obs.description, "Shapes differ")


class TestTensorLocalJudgment(unittest.TestCase):
    def test_equivalent(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="local")
        j = TensorLocalJudgment(
            site_id=sid,
            stratum=TensorStratum.STRUCTURAL,
            tensor_site_kind=TensorSiteKind.SHAPE,
            verdict=EquivalenceVerdict.EQUIVALENT,
        )
        self.assertTrue(j.is_equivalent)

    def test_inequivalent(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="local2")
        j = TensorLocalJudgment(
            site_id=sid,
            stratum=TensorStratum.NUMERICAL,
            tensor_site_kind=TensorSiteKind.NUMERICAL,
            verdict=EquivalenceVerdict.INEQUIVALENT,
        )
        self.assertFalse(j.is_equivalent)


class TestTensorGlobalJudgment(unittest.TestCase):
    def test_equivalent(self):
        j = TensorGlobalJudgment(
            verdict=EquivalenceVerdict.EQUIVALENT,
            program_f=ProgramId(name="f"),
            program_g=ProgramId(name="g"),
        )
        self.assertTrue(j.is_equivalent)

    def test_summary(self):
        j = TensorGlobalJudgment(
            verdict=EquivalenceVerdict.EQUIVALENT,
            program_f=ProgramId(name="f"),
            program_g=ProgramId(name="g"),
        )
        self.assertIsInstance(j.summary(), str)


class TestTritonSpecs(unittest.TestCase):
    def test_block_spec(self):
        bs = TritonBlockSpec(name="BLOCK_SIZE", size=256, constexpr=True, power_of_two=True)
        self.assertEqual(bs.name, "BLOCK_SIZE")
        self.assertEqual(bs.size, 256)

    def test_memory_access_pattern(self):
        ma = TritonMemoryAccessPattern(
            kind="load", pointer_name="x_ptr",
            offsets_expr="x_ptr + offsets", mask_expr="mask",
        )
        self.assertEqual(ma.kind, "load")
        self.assertEqual(ma.pointer_name, "x_ptr")

    def test_reduction_spec(self):
        rs = TritonReductionSpec(op="sum", axis=0, input_name="x")
        self.assertEqual(rs.op, "sum")
        self.assertEqual(rs.axis, 0)

    def test_kernel_spec(self):
        ks = TritonKernelSpec(name="kernel", grid=(1,))
        self.assertEqual(ks.name, "kernel")
        self.assertEqual(ks.grid, (1,))


class TestMLIRSpecs(unittest.TestCase):
    def test_op_spec(self):
        op = MLIROpSpec(dialect=MLIRDialect.ARITH, op_name="addf")
        self.assertEqual(op.full_name, "arith.addf")

    def test_lowering_step(self):
        step = MLIRLoweringStep(
            source_dialect=MLIRDialect.TRITON,
            target_dialect=MLIRDialect.LLVM,
            pass_name="lower_to_llvm",
            metadata={},
        )
        self.assertEqual(step.source_dialect, MLIRDialect.TRITON)

    def test_module_spec(self):
        ms = MLIRModuleSpec(
            name="mod",
            dialect_ops={MLIRDialect.ARITH: [MLIROpSpec(dialect=MLIRDialect.ARITH, op_name="addf")]},
        )
        self.assertIn(MLIRDialect.ARITH, ms.dialects_used)
        self.assertEqual(ms.op_count, 1)


class TestBugDataclass(unittest.TestCase):
    def test_construction(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="bug")
        b = Bug(
            kind=BugKind.NUMERICAL_INSTABILITY,
            stratum=TensorStratum.NUMERICAL,
            site_id=sid,
            description="NaN detected",
        )
        self.assertEqual(b.kind, BugKind.NUMERICAL_INSTABILITY)
        self.assertEqual(b.description, "NaN detected")


class TestAnalysisJudgment(unittest.TestCase):
    def test_valid(self):
        j = AnalysisJudgment(
            verdict=AnalysisVerdict.VALID,
            program=ProgramId(name="f"),
            mode=AnalysisMode.BUG_FINDING,
        )
        self.assertEqual(j.verdict, AnalysisVerdict.VALID)
        self.assertEqual(j.mode, AnalysisMode.BUG_FINDING)
        self.assertEqual(len(j.bugs), 0)


class TestCorrectnessJudgment(unittest.TestCase):
    def test_valid(self):
        j = CorrectnessJudgment(
            verdict=AnalysisVerdict.VALID,
            program=ProgramId(name="f"),
            specification="test_spec",
            violations=[],
            conforming_sites=[],
            violating_sites=[],
        )
        self.assertEqual(j.verdict, AnalysisVerdict.VALID)


class TestSheafConditionResult(unittest.TestCase):
    def test_satisfies(self):
        r = SheafConditionResult(
            satisfies_condition=True,
            gluing_failures=[],
            descent_failures=[],
        )
        self.assertTrue(r.satisfies_condition)
        self.assertEqual(len(r.gluing_failures), 0)


class TestSpecificationPresheaf(unittest.TestCase):
    def test_construction(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="spec_sec")
        sec = SpecificationSection(
            site_id=sid,
            property_name="no_nan",
            expected_value=True,
        )
        sp = SpecificationPresheaf(
            name="test_spec",
            sections={sid: sec},
            strata={TensorStratum.NUMERICAL},
        )
        self.assertEqual(sp.name, "test_spec")
        self.assertEqual(len(sp.sections), 1)


class TestTensorDescentDatum(unittest.TestCase):
    def test_empty(self):
        d = TensorDescentDatum(local_judgments={})
        self.assertTrue(d.cocycle_holds())


class TestTensorCohomologyClass(unittest.TestCase):
    def test_trivial_witnesses_equivalence(self):
        """is_trivial=True => witnesses equivalence (H^0 is trivial)."""
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="coh")
        c = TensorCohomologyClass(
            degree=0, representative_sites=[sid], is_trivial=True,
        )
        self.assertTrue(c.witnesses_equivalence)
        self.assertFalse(c.witnesses_obstruction)

    def test_degree1_not_trivial_witnesses_obstruction(self):
        """degree>=1 + not trivial => obstruction (H^1 class exists)."""
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="coh2")
        c = TensorCohomologyClass(
            degree=1, representative_sites=[sid], is_trivial=False,
            obstruction_description="mismatch",
        )
        self.assertFalse(c.witnesses_equivalence)
        self.assertTrue(c.witnesses_obstruction)

    def test_nontrivial_degree0(self):
        sid = SiteId(kind=SiteKind.TENSOR_SHAPE, name="coh3")
        c = TensorCohomologyClass(
            degree=0, representative_sites=[sid], is_trivial=False,
        )
        self.assertFalse(c.witnesses_equivalence)
        self.assertFalse(c.witnesses_obstruction)


class TestProgramId(unittest.TestCase):
    def test_construction(self):
        p = ProgramId(name="my_fn")
        self.assertEqual(p.name, "my_fn")
        self.assertIsNone(p.source_path)


if __name__ == "__main__":
    unittest.main()
