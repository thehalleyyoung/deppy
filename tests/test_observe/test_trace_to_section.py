"""Tests for deppy.observe.trace_to_section -- trace-to-section conversion.

Exercises conversion of VariableObservation, BranchObservation, and
ExceptionObservation into LocalSection objects, as well as enrichment,
merging, and static-agreement checking.
"""

from __future__ import annotations

import pytest

from deppy.observe.trace_to_section import (
    InferredRefinements,
    SectionEnrichment,
    _canonicalize_type_name,
    _infer_refinements,
    _refinements_to_dict,
    _witnesses_from_observation,
    branch_to_local_section,
    enrich_section,
    exception_to_local_section,
    function_to_local_sections,
    merge_trace_sections,
    section_agrees_with_static,
    trace_to_local_section,
    trace_to_sections,
    variable_to_local_section,
)
from deppy.observe.trace_parser import (
    BranchObservation,
    ExceptionObservation,
    FunctionObservation,
    ObservedType,
    ParsedTrace,
    VariableObservation,
)
from deppy.core._protocols import (
    Cover,
    LocalSection,
    SiteId,
    SiteKind,
    TrustLevel,
)


# ===================================================================
# Helpers
# ===================================================================

def _make_observed_type(
    type_name="int",
    count=5,
    shapes=(),
    dtypes=(),
    lengths=(),
    sample_reprs=(),
) -> ObservedType:
    return ObservedType(
        type_name=type_name,
        count=count,
        shapes=shapes,
        dtypes=dtypes,
        lengths=lengths,
        sample_reprs=sample_reprs,
    )


def _make_variable_obs(
    function="my_func",
    variable="x",
    types=None,
    assignment_count=5,
    is_parameter=False,
    is_return=False,
    first_location=("test.py", 10, 0),
    sample_values=("1", "2", "3"),
) -> VariableObservation:
    if types is None:
        types = (_make_observed_type(),)
    return VariableObservation(
        function=function,
        variable=variable,
        observed_types=types,
        assignment_count=assignment_count,
        first_location=first_location,
        is_parameter=is_parameter,
        is_return=is_return,
        sample_values=sample_values,
    )


def _make_branch_obs(
    function="my_func",
    location=("test.py", 20, 0),
    true_count=3,
    false_count=2,
    guard_repr="x > 0",
) -> BranchObservation:
    return BranchObservation(
        function=function,
        location=location,
        true_count=true_count,
        false_count=false_count,
        guard_repr=guard_repr,
    )


def _make_exception_obs(
    function="my_func",
    exception_type="ValueError",
    count=1,
    locations=(("test.py", 30, 0),),
    sample_messages=("bad value",),
) -> ExceptionObservation:
    return ExceptionObservation(
        function=function,
        exception_type=exception_type,
        count=count,
        locations=locations,
        sample_messages=sample_messages,
    )


# ===================================================================
# TestCanonicalizeTypeName
# ===================================================================

class TestCanonicalizeTypeName:
    """Test _canonicalize_type_name mapping."""

    def test_builtin_types(self):
        assert _canonicalize_type_name("int") == "int"
        assert _canonicalize_type_name("str") == "str"
        assert _canonicalize_type_name("float") == "float"
        assert _canonicalize_type_name("bool") == "bool"
        assert _canonicalize_type_name("NoneType") == "None"

    def test_container_types(self):
        assert _canonicalize_type_name("list") == "list"
        assert _canonicalize_type_name("dict") == "dict"
        assert _canonicalize_type_name("tuple") == "tuple"
        assert _canonicalize_type_name("set") == "set"

    def test_numpy(self):
        assert _canonicalize_type_name("numpy.ndarray") == "ndarray"

    def test_torch(self):
        assert _canonicalize_type_name("torch.Tensor") == "Tensor"

    def test_builtins_prefix_stripped(self):
        assert _canonicalize_type_name("builtins.int") == "int"

    def test_typing_prefix_stripped(self):
        assert _canonicalize_type_name("typing.List") == "List"

    def test_dotted_last_component(self):
        assert _canonicalize_type_name("my.custom.MyClass") == "MyClass"

    def test_simple_name_unchanged(self):
        assert _canonicalize_type_name("SomeType") == "SomeType"


# ===================================================================
# TestInferredRefinements
# ===================================================================

class TestInferredRefinements:
    """Test InferredRefinements dataclass."""

    def test_defaults(self):
        ir = InferredRefinements()
        assert ir.type_name == "Any"
        assert ir.is_monomorphic is True
        assert ir.shape is None
        assert ir.dtype is None
        assert ir.sample_count == 0

    def test_with_values(self):
        ir = InferredRefinements(
            type_name="int",
            is_monomorphic=True,
            observed_types=("int",),
            sample_count=10,
            is_parameter=True,
        )
        assert ir.type_name == "int"
        assert ir.is_parameter is True

    def test_with_shape(self):
        ir = InferredRefinements(
            type_name="Tensor",
            shape=(3, 4),
            all_shapes=((3, 4),),
            dtype="float32",
        )
        assert ir.shape == (3, 4)
        assert ir.dtype == "float32"


# ===================================================================
# TestInferRefinements
# ===================================================================

class TestInferRefinementsFunction:
    """Test _infer_refinements from VariableObservation."""

    def test_monomorphic_int(self):
        vo = _make_variable_obs(types=(_make_observed_type("int", count=10),))
        ir = _infer_refinements(vo)
        assert ir.type_name == "int"
        assert ir.is_monomorphic is True
        assert ir.sample_count == 5  # from assignment_count

    def test_polymorphic(self):
        types = (
            _make_observed_type("int", count=5),
            _make_observed_type("str", count=3),
        )
        vo = _make_variable_obs(types=types)
        ir = _infer_refinements(vo)
        assert ir.is_monomorphic is False
        assert "int" in ir.observed_types
        assert "str" in ir.observed_types

    def test_with_shapes(self):
        types = (_make_observed_type(
            "numpy.ndarray", count=5,
            shapes=((3, 4), (3, 4), (5, 6)),
        ),)
        vo = _make_variable_obs(types=types)
        ir = _infer_refinements(vo)
        assert ir.shape is not None
        assert len(ir.all_shapes) >= 1

    def test_with_dtypes(self):
        types = (_make_observed_type(
            "numpy.ndarray", count=5,
            dtypes=("float32",),
        ),)
        vo = _make_variable_obs(types=types)
        ir = _infer_refinements(vo)
        assert ir.dtype == "float32"

    def test_parameter_flag(self):
        vo = _make_variable_obs(is_parameter=True)
        ir = _infer_refinements(vo)
        assert ir.is_parameter is True

    def test_return_flag(self):
        vo = _make_variable_obs(is_return=True)
        ir = _infer_refinements(vo)
        assert ir.is_return is True

    def test_no_types(self):
        vo = _make_variable_obs(types=())
        ir = _infer_refinements(vo)
        assert ir.type_name == "Any"


# ===================================================================
# TestRefinementsToDict
# ===================================================================

class TestRefinementsToDict:
    """Test _refinements_to_dict conversion."""

    def test_basic_monomorphic(self):
        ir = InferredRefinements(type_name="int", is_monomorphic=True, sample_count=5)
        d = _refinements_to_dict(ir)
        assert d["observed_type"] == "int"
        assert d["monomorphic"] is True
        assert d["sample_count"] == 5

    def test_polymorphic_includes_types(self):
        ir = InferredRefinements(
            type_name="int",
            is_monomorphic=False,
            observed_types=("int", "str"),
        )
        d = _refinements_to_dict(ir)
        assert "observed_types" in d
        assert "int" in d["observed_types"]

    def test_shape_includes_rank(self):
        ir = InferredRefinements(
            type_name="Tensor",
            shape=(3, 4, 5),
            all_shapes=((3, 4, 5),),
        )
        d = _refinements_to_dict(ir)
        assert d["shape"] == (3, 4, 5)
        assert d["rank"] == 3
        assert d["shape_diversity"] == 1

    def test_parameter_flag_in_dict(self):
        ir = InferredRefinements(type_name="int", is_parameter=True)
        d = _refinements_to_dict(ir)
        assert d["is_parameter"] is True

    def test_return_flag_in_dict(self):
        ir = InferredRefinements(type_name="int", is_return=True)
        d = _refinements_to_dict(ir)
        assert d["is_return"] is True


# ===================================================================
# TestWitnessesFromObservation
# ===================================================================

class TestWitnessesFromObservation:
    """Test _witnesses_from_observation."""

    def test_sample_values_included(self):
        vo = _make_variable_obs(sample_values=("1", "2", "3"))
        w = _witnesses_from_observation(vo)
        assert "sample_values" in w
        assert len(w["sample_values"]) == 3

    def test_sample_reprs_included(self):
        types = (_make_observed_type(sample_reprs=("repr1", "repr2")),)
        vo = _make_variable_obs(types=types)
        w = _witnesses_from_observation(vo)
        assert "sample_reprs" in w

    def test_shapes_included(self):
        types = (_make_observed_type(shapes=((3, 4),)),)
        vo = _make_variable_obs(types=types)
        w = _witnesses_from_observation(vo)
        assert "observed_shapes" in w

    def test_empty_values(self):
        vo = _make_variable_obs(
            types=(_make_observed_type(sample_reprs=()),),
            sample_values=(),
        )
        w = _witnesses_from_observation(vo)
        assert "sample_values" not in w


# ===================================================================
# TestVariableToLocalSection
# ===================================================================

class TestVariableToLocalSection:
    """Test variable_to_local_section."""

    def test_basic_conversion(self):
        vo = _make_variable_obs()
        section = variable_to_local_section(vo)
        assert isinstance(section, LocalSection)
        assert section.trust == TrustLevel.TRACE_BACKED

    def test_carrier_type(self):
        vo = _make_variable_obs(types=(_make_observed_type("int"),))
        section = variable_to_local_section(vo)
        assert section.carrier_type == "int"

    def test_parameter_site_kind(self):
        vo = _make_variable_obs(is_parameter=True)
        section = variable_to_local_section(vo)
        assert section.site_id.kind == SiteKind.ARGUMENT_BOUNDARY

    def test_return_site_kind(self):
        vo = _make_variable_obs(is_return=True)
        section = variable_to_local_section(vo)
        assert section.site_id.kind == SiteKind.RETURN_OUTPUT_BOUNDARY

    def test_local_variable_site_kind(self):
        vo = _make_variable_obs(is_parameter=False, is_return=False)
        section = variable_to_local_section(vo)
        assert section.site_id.kind == SiteKind.TRACE

    def test_custom_site_id(self):
        vo = _make_variable_obs()
        custom_id = SiteId(kind=SiteKind.SSA_VALUE, name="custom")
        section = variable_to_local_section(vo, site_id=custom_id)
        assert section.site_id == custom_id

    def test_trace_id_in_provenance(self):
        vo = _make_variable_obs()
        section = variable_to_local_section(vo, trace_id="abc123")
        assert "abc123" in section.provenance

    def test_refinements_populated(self):
        vo = _make_variable_obs()
        section = variable_to_local_section(vo)
        assert "observed_type" in section.refinements
        assert "sample_count" in section.refinements

    def test_witnesses_populated(self):
        vo = _make_variable_obs(sample_values=("1", "2"))
        section = variable_to_local_section(vo)
        assert "sample_values" in section.witnesses


# ===================================================================
# TestBranchToLocalSection
# ===================================================================

class TestBranchToLocalSection:
    """Test branch_to_local_section."""

    def test_basic_conversion(self):
        bo = _make_branch_obs()
        section = branch_to_local_section(bo)
        assert isinstance(section, LocalSection)
        assert section.trust == TrustLevel.TRACE_BACKED
        assert section.carrier_type == "bool"

    def test_refinements_include_counts(self):
        bo = _make_branch_obs(true_count=5, false_count=3)
        section = branch_to_local_section(bo)
        assert section.refinements["true_count"] == 5
        assert section.refinements["false_count"] == 3

    def test_always_true(self):
        bo = _make_branch_obs(true_count=10, false_count=0)
        section = branch_to_local_section(bo)
        assert section.refinements["always_true"] is True
        assert section.refinements["always_false"] is False

    def test_always_false(self):
        bo = _make_branch_obs(true_count=0, false_count=10)
        section = branch_to_local_section(bo)
        assert section.refinements["always_true"] is False
        assert section.refinements["always_false"] is True

    def test_both_taken(self):
        bo = _make_branch_obs(true_count=5, false_count=5)
        section = branch_to_local_section(bo)
        assert section.refinements["both_taken"] is True

    def test_guard_repr_in_refinements(self):
        bo = _make_branch_obs(guard_repr="x > 0")
        section = branch_to_local_section(bo)
        assert section.refinements["guard_repr"] == "x > 0"

    def test_site_kind_is_branch_guard(self):
        bo = _make_branch_obs()
        section = branch_to_local_section(bo)
        assert section.site_id.kind == SiteKind.BRANCH_GUARD

    def test_custom_site_id(self):
        bo = _make_branch_obs()
        custom_id = SiteId(kind=SiteKind.BRANCH_GUARD, name="custom_guard")
        section = branch_to_local_section(bo, site_id=custom_id)
        assert section.site_id == custom_id

    def test_trace_id_in_provenance(self):
        bo = _make_branch_obs()
        section = branch_to_local_section(bo, trace_id="trace123")
        assert "trace123" in section.provenance


# ===================================================================
# TestExceptionToLocalSection
# ===================================================================

class TestExceptionToLocalSection:
    """Test exception_to_local_section."""

    def test_basic_conversion(self):
        eo = _make_exception_obs()
        section = exception_to_local_section(eo)
        assert isinstance(section, LocalSection)
        assert section.trust == TrustLevel.TRACE_BACKED

    def test_carrier_type_is_exception(self):
        eo = _make_exception_obs(exception_type="ValueError")
        section = exception_to_local_section(eo)
        assert section.carrier_type == "ValueError"

    def test_site_kind_is_error(self):
        eo = _make_exception_obs()
        section = exception_to_local_section(eo)
        assert section.site_id.kind == SiteKind.ERROR

    def test_refinements_include_count(self):
        eo = _make_exception_obs(count=3)
        section = exception_to_local_section(eo)
        assert section.refinements["count"] == 3
        assert section.refinements["viable"] is False

    def test_sample_messages_in_witnesses(self):
        eo = _make_exception_obs(sample_messages=("bad", "worse"))
        section = exception_to_local_section(eo)
        assert "sample_messages" in section.witnesses
        assert len(section.witnesses["sample_messages"]) == 2

    def test_locations_in_witnesses(self):
        eo = _make_exception_obs(locations=(("test.py", 10, 0),))
        section = exception_to_local_section(eo)
        assert "locations" in section.witnesses

    def test_trace_id_in_provenance(self):
        eo = _make_exception_obs()
        section = exception_to_local_section(eo, trace_id="trace456")
        assert "trace456" in section.provenance


# ===================================================================
# TestFunctionToLocalSections
# ===================================================================

class TestFunctionToLocalSections:
    """Test function_to_local_sections."""

    def test_produces_sections_for_params(self):
        param = _make_variable_obs(variable="x", is_parameter=True)
        fo = FunctionObservation(
            function="my_func",
            call_count=1,
            parameter_observations=(param,),
        )
        sections = function_to_local_sections(fo)
        assert len(sections) >= 1
        assert any(s.site_id.kind == SiteKind.ARGUMENT_BOUNDARY for s in sections)

    def test_produces_sections_for_variables(self):
        var = _make_variable_obs(variable="y")
        fo = FunctionObservation(
            function="my_func",
            call_count=1,
            variables=(var,),
        )
        sections = function_to_local_sections(fo)
        assert len(sections) >= 1

    def test_produces_section_for_return(self):
        ret = _make_variable_obs(variable="<return>", is_return=True)
        fo = FunctionObservation(
            function="my_func",
            call_count=1,
            return_observation=ret,
        )
        sections = function_to_local_sections(fo)
        assert any(s.site_id.kind == SiteKind.RETURN_OUTPUT_BOUNDARY for s in sections)

    def test_produces_sections_for_branches(self):
        branch = _make_branch_obs()
        fo = FunctionObservation(
            function="my_func",
            call_count=1,
            branches=(branch,),
        )
        sections = function_to_local_sections(fo)
        assert any(s.site_id.kind == SiteKind.BRANCH_GUARD for s in sections)

    def test_produces_sections_for_exceptions(self):
        exc = _make_exception_obs()
        fo = FunctionObservation(
            function="my_func",
            call_count=1,
            exceptions=(exc,),
        )
        sections = function_to_local_sections(fo)
        assert any(s.site_id.kind == SiteKind.ERROR for s in sections)

    def test_empty_function_observation(self):
        fo = FunctionObservation(function="empty_func", call_count=0)
        sections = function_to_local_sections(fo)
        assert len(sections) == 0


# ===================================================================
# TestTraceToLocalSection
# ===================================================================

class TestTraceToLocalSection:
    """Test trace_to_local_section (single summary section)."""

    def test_basic_conversion(self):
        vo = _make_variable_obs()
        fo = FunctionObservation(
            function="my_func", call_count=1, variables=(vo,),
        )
        pt = ParsedTrace(
            trace_id="trace1",
            target_function="my_func",
            function_observations=(fo,),
            all_variables=(vo,),
            unique_types=frozenset({"int"}),
            event_count=10,
            succeeded=True,
        )
        site_id = SiteId(kind=SiteKind.TRACE, name="summary")
        section = trace_to_local_section(pt, site_id)
        assert isinstance(section, LocalSection)
        assert section.trust == TrustLevel.TRACE_BACKED
        assert section.site_id == site_id

    def test_refinements_populated(self):
        vo = _make_variable_obs()
        fo = FunctionObservation(
            function="my_func", call_count=1, variables=(vo,),
        )
        pt = ParsedTrace(
            trace_id="trace1",
            target_function="my_func",
            function_observations=(fo,),
            all_variables=(vo,),
            unique_types=frozenset({"int"}),
            event_count=10,
        )
        site_id = SiteId(kind=SiteKind.TRACE, name="summary")
        section = trace_to_local_section(pt, site_id)
        assert "event_count" in section.refinements
        assert "succeeded" in section.refinements
        assert "variable_count" in section.refinements

    def test_witnesses_include_trace_id(self):
        pt = ParsedTrace(
            trace_id="trace1",
            target_function="my_func",
        )
        site_id = SiteId(kind=SiteKind.TRACE, name="summary")
        section = trace_to_local_section(pt, site_id)
        assert section.witnesses.get("trace_id") == "trace1"


# ===================================================================
# TestTraceToSections
# ===================================================================

class TestTraceToSections:
    """Test trace_to_sections (full ParsedTrace conversion)."""

    def test_empty_trace(self):
        pt = ParsedTrace(
            trace_id="empty",
            target_function="f",
        )
        sections = trace_to_sections(pt)
        assert len(sections) == 0

    def test_with_function_observations(self):
        var = _make_variable_obs()
        param = _make_variable_obs(variable="a", is_parameter=True)
        fo = FunctionObservation(
            function="my_func", call_count=1,
            variables=(var,),
            parameter_observations=(param,),
        )
        pt = ParsedTrace(
            trace_id="t1",
            target_function="my_func",
            function_observations=(fo,),
            all_variables=(var, param),
        )
        sections = trace_to_sections(pt)
        assert len(sections) >= 2  # at least var + param

    def test_all_trust_trace_backed(self):
        var = _make_variable_obs()
        fo = FunctionObservation(
            function="f", call_count=1, variables=(var,),
        )
        pt = ParsedTrace(
            trace_id="t1",
            target_function="f",
            function_observations=(fo,),
        )
        sections = trace_to_sections(pt)
        assert all(s.trust == TrustLevel.TRACE_BACKED for s in sections)


# ===================================================================
# TestSectionEnrichment
# ===================================================================

class TestSectionEnrichment:
    """Test SectionEnrichment dataclass and enrich_section."""

    def test_defaults(self):
        se = SectionEnrichment()
        assert se.extra_refinements == ()
        assert se.extra_witnesses == ()
        assert se.upgraded_trust is None
        assert se.appended_provenance == ""

    def test_enrich_adds_refinements(self):
        vo = _make_variable_obs()
        section = variable_to_local_section(vo)
        enrichment = SectionEnrichment(
            extra_refinements=(("extra_key", "extra_value"),),
        )
        enriched = enrich_section(section, enrichment)
        assert enriched.refinements["extra_key"] == "extra_value"
        # Original refinements preserved
        assert "observed_type" in enriched.refinements

    def test_enrich_adds_witnesses(self):
        vo = _make_variable_obs()
        section = variable_to_local_section(vo)
        enrichment = SectionEnrichment(
            extra_witnesses=(("witness_key", "witness_value"),),
        )
        enriched = enrich_section(section, enrichment)
        assert enriched.witnesses["witness_key"] == "witness_value"

    def test_enrich_upgrades_trust(self):
        vo = _make_variable_obs()
        section = variable_to_local_section(vo)
        assert section.trust == TrustLevel.TRACE_BACKED
        enrichment = SectionEnrichment(
            upgraded_trust=TrustLevel.PROOF_BACKED,
        )
        enriched = enrich_section(section, enrichment)
        assert enriched.trust == TrustLevel.PROOF_BACKED

    def test_enrich_appends_provenance(self):
        vo = _make_variable_obs()
        section = variable_to_local_section(vo, trace_id="abc")
        enrichment = SectionEnrichment(
            appended_provenance="verified by static analysis",
        )
        enriched = enrich_section(section, enrichment)
        assert "verified by static analysis" in enriched.provenance

    def test_enrich_preserves_site_id(self):
        vo = _make_variable_obs()
        section = variable_to_local_section(vo)
        enrichment = SectionEnrichment(
            extra_refinements=(("x", 1),),
        )
        enriched = enrich_section(section, enrichment)
        assert enriched.site_id == section.site_id


# ===================================================================
# TestMergeTraceSections
# ===================================================================

class TestMergeTraceSections:
    """Test merge_trace_sections."""

    def test_merge_empty_raises(self):
        with pytest.raises(ValueError, match="[Cc]annot merge empty"):
            merge_trace_sections([])

    def test_merge_single_returns_same(self):
        vo = _make_variable_obs()
        section = variable_to_local_section(vo, trace_id="t1")
        merged = merge_trace_sections([section])
        assert merged.site_id == section.site_id

    def test_merge_two_same_site(self):
        site_id = SiteId(kind=SiteKind.TRACE, name="my_func.trace_x")
        vo1 = _make_variable_obs(assignment_count=5)
        vo2 = _make_variable_obs(assignment_count=3)
        s1 = variable_to_local_section(vo1, site_id=site_id, trace_id="t1")
        s2 = variable_to_local_section(vo2, site_id=site_id, trace_id="t2")
        merged = merge_trace_sections([s1, s2])
        assert merged.site_id == site_id
        assert merged.trust == TrustLevel.TRACE_BACKED

    def test_merge_different_sites_raises(self):
        s1_id = SiteId(kind=SiteKind.TRACE, name="a")
        s2_id = SiteId(kind=SiteKind.TRACE, name="b")
        vo = _make_variable_obs()
        s1 = variable_to_local_section(vo, site_id=s1_id)
        s2 = variable_to_local_section(vo, site_id=s2_id)
        with pytest.raises(ValueError, match="different site_id"):
            merge_trace_sections([s1, s2])

    def test_merge_accumulates_sample_count(self):
        site_id = SiteId(kind=SiteKind.TRACE, name="x")
        vo1 = _make_variable_obs(assignment_count=5)
        vo2 = _make_variable_obs(assignment_count=3)
        s1 = variable_to_local_section(vo1, site_id=site_id, trace_id="t1")
        s2 = variable_to_local_section(vo2, site_id=site_id, trace_id="t2")
        merged = merge_trace_sections([s1, s2])
        assert merged.refinements.get("sample_count", 0) >= 5

    def test_merge_provenance_mentions_traces(self):
        site_id = SiteId(kind=SiteKind.TRACE, name="x")
        vo = _make_variable_obs()
        s1 = variable_to_local_section(vo, site_id=site_id, trace_id="t1")
        s2 = variable_to_local_section(vo, site_id=site_id, trace_id="t2")
        merged = merge_trace_sections([s1, s2])
        assert "merged" in merged.provenance.lower()


# ===================================================================
# TestSectionAgreesWithStatic
# ===================================================================

class TestSectionAgreesWithStatic:
    """Test section_agrees_with_static compatibility check."""

    def _make_section(self, carrier_type="int", refinements=None):
        site_id = SiteId(kind=SiteKind.TRACE, name="test")
        return LocalSection(
            site_id=site_id,
            carrier_type=carrier_type,
            refinements=refinements or {},
            trust=TrustLevel.TRACE_BACKED,
        )

    def test_same_type_agrees(self):
        trace_sec = self._make_section("int", {"observed_type": "int"})
        static_sec = self._make_section("int")
        assert section_agrees_with_static(trace_sec, static_sec) is True

    def test_any_always_agrees(self):
        trace_sec = self._make_section("int", {"observed_type": "Any"})
        static_sec = self._make_section("str")
        assert section_agrees_with_static(trace_sec, static_sec) is True

    def test_static_any_always_agrees(self):
        trace_sec = self._make_section("int", {"observed_type": "int"})
        static_sec = self._make_section("Any")
        assert section_agrees_with_static(trace_sec, static_sec) is True

    def test_static_none_carrier_agrees(self):
        trace_sec = self._make_section("int", {"observed_type": "int"})
        static_sec = self._make_section(None)
        assert section_agrees_with_static(trace_sec, static_sec) is True

    def test_conflicting_dtype_disagrees(self):
        # The implementation does a simple carrier-type name match first.
        # When observed_type matches static carrier, it returns True
        # without inspecting refinements.  To trigger a dtype conflict
        # the observed type must differ from the static carrier.
        trace_sec = self._make_section(
            "Tensor",
            {"observed_type": "Tensor", "dtype": "float32"},
        )
        static_sec = self._make_section(
            "DoubleTensor",
            {"dtype": "float64"},
        )
        assert section_agrees_with_static(trace_sec, static_sec) is False

    def test_compatible_shapes(self):
        trace_sec = self._make_section(
            "Tensor",
            {"observed_type": "Tensor", "all_shapes": [(3, 4)]},
        )
        static_sec = self._make_section(
            "Tensor",
            {"shape": (3, 4)},
        )
        assert section_agrees_with_static(trace_sec, static_sec) is True

    def test_incompatible_shapes(self):
        # As with dtype, use a different static carrier type so the
        # simple name match doesn't short-circuit before shape checks.
        trace_sec = self._make_section(
            "Tensor",
            {"observed_type": "Tensor", "all_shapes": [(3, 4)]},
        )
        static_sec = self._make_section(
            "NDArray",
            {"shape": (5, 6)},
        )
        assert section_agrees_with_static(trace_sec, static_sec) is False
