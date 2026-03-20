from __future__ import annotations

from deppy.core._protocols import SiteKind
from deppy.pipeline.pipeline_config import PipelineConfig
from deppy.pipeline.stages.cover_stage import CoverStage
from deppy.pipeline.stages.harvest_stage import GuardKind, HarvestStage
from deppy.pipeline.stages.parse_stage import ParseStage


def test_harvest_stage_synthesizes_docstring_contract_guards() -> None:
    source = '''
def normalize(items):
    """Args:
        items: non-empty list

    Returns:
        list: non-empty sorted list
    """
    return sorted(items)
'''
    config = PipelineConfig()
    parse_result = ParseStage().run_source(source, config)
    harvest_result = HarvestStage().run({"parse": parse_result}, config)

    guards = harvest_result.guards_for_scope("normalize")

    assert any(
        guard.kind == GuardKind.CONTRACT_REQUIRES and guard.variable_name == "items"
        for guard in guards
    )
    assert any(
        guard.kind == GuardKind.CONTRACT_ENSURES and guard.variable_name == "<return>"
        for guard in guards
    )


def test_cover_stage_propagates_docstring_contracts_to_boundary_sites() -> None:
    source = '''
def normalize(items):
    """Args:
        items: non-empty list

    Returns:
        list: non-empty sorted list
    """
    return sorted(items)
'''
    config = PipelineConfig()
    parse_result = ParseStage().run_source(source, config)
    harvest_result = HarvestStage().run({"parse": parse_result}, config)
    cover_result = CoverStage().run(
        {"parse": parse_result, "harvest": harvest_result},
        config,
    )

    arg_site = next(
        site
        for site_id, site in cover_result.cover.sites.items()
        if site_id.kind == SiteKind.ARGUMENT_BOUNDARY
        and site.metadata.get("param") == "items"
    )
    ret_site = next(
        site
        for site_id, site in cover_result.cover.sites.items()
        if site_id.kind == SiteKind.RETURN_OUTPUT_BOUNDARY
    )

    assert "non-empty" in arg_site.carrier_schema.get("source", "")
    assert "sorted" in ret_site.carrier_schema.get("source", "")
