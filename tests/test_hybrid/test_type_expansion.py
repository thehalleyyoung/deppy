from __future__ import annotations

import re

from deppy.hybrid.type_expansion import CodeGenPlan, LargeScaleGenerator, PlanVerifier, TypeExpander


def test_type_expander_emits_parseable_plan() -> None:
    expander = TypeExpander(atomic_loc=220)
    plan = expander.expand(
        "Build an API service that must enforce auth, keep audit logs, and ensure unique account ids.",
        target_loc=2400,
    )

    assert plan["modules"]
    assert plan["interfaces"]
    assert plan["constraints"]
    assert "expanded_type" in plan
    assert all("estimated_loc" in module for module in plan["modules"])
    assert plan["expanded_type"]["elaboration_tree"]["kind"] == "grothendieck_cover"
    assert plan["expanded_type"]["leaf_order"] == [module["name"] for module in plan["modules"]]
    assert all(not re.search(r"_part\d+$", module["name"]) for module in plan["modules"])
    assert all(module["class_specs"] for module in plan["modules"])
    assert all(module["function_specs"] for module in plan["modules"])
    assert all("invariants" in module["class_specs"][0] for module in plan["modules"])
    assert all("theorem_schema" in module["function_specs"][0] for module in plan["modules"])
    assert all("canonical_equation" in module["function_specs"][0] for module in plan["modules"])


def test_codegen_plan_compile_builds_phases() -> None:
    plan = CodeGenPlan.compile(
        spec="simple spec",
        target_loc=1200,
        nodes=[
            {
                "name": "core",
                "summary": "core logic",
                "depends_on": [],
                "exports": ["run_core"],
                "imports": [],
                "responsibilities": ["compute"],
                "estimated_loc": 150,
                "sigma_width": 1,
                "pi_arity": 2,
                "constraints": [{"expression": "x > 0"}],
                "test_obligations": ["x > 0"],
                "class_specs": [{"name": "CoreService", "role": "Core orchestration"}],
                "function_specs": [{"name": "run_core", "signature": "() -> dict"}],
            },
            {
                "name": "api",
                "summary": "api layer",
                "depends_on": ["core"],
                "exports": ["serve"],
                "imports": ["run_core"],
                "responsibilities": ["serve"],
                "estimated_loc": 120,
                "sigma_width": 1,
                "pi_arity": 1,
                "constraints": [],
                "test_obligations": [],
                "class_specs": [{"name": "ApiService", "role": "API orchestration"}],
                "function_specs": [{"name": "serve", "signature": "() -> dict"}],
            },
        ],
        interfaces=[
            {
                "name": "run_core",
                "provider": "core",
                "consumer": "api",
                "provider_type": "Callable[..., dict]",
                "consumer_type": "Callable[..., dict]",
                "obligation": "Id_API(core.run_core, api.run_core)",
            }
        ],
        constraints=[{"expression": "x > 0"}],
    )

    payload = plan.to_dict()
    assert payload["phases"]
    assert payload["tests"]
    assert payload["phases"][0]["module_names"] == ["core"]
    assert payload["modules"][0]["class_specs"][0]["name"] == "CoreService"
    assert payload["modules"][1]["function_specs"][0]["name"] == "serve"


def test_large_scale_generator_merges_component_plans() -> None:
    generator = LargeScaleGenerator()
    report = generator.generate(
        {
            "spec": "Platform with billing and analytics",
            "target_loc": 6000,
            "components": {
                "billing": "Track invoices and ensure non-negative balances.",
                "analytics": "Aggregate events and expose API for dashboards.",
            },
        }
    )

    assert report["component_count"] == 2
    assert report["global_plan"]["modules"]
    assert all("__" in mod["name"] for mod in report["global_plan"]["modules"])
    assert report["global_plan"]["elaboration_tree"]["kind"] == "global_grothendieck_cover"


def test_expanded_plan_verifies_quickly() -> None:
    expander = TypeExpander(atomic_loc=240)
    verifier = PlanVerifier(coverage_threshold=0.1)
    plan = expander.expand("Create an API with persistence and observability.", target_loc=1800)

    assert verifier.quick_verify(plan, "Create an API with persistence and observability.")
