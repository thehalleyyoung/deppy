from deppy import ideate, run_fleet, scaffold


PROMPT = (
    "Build a verified API with persistence, CLI support, structured JSON IO, "
    "bug diagnostics, equivalence checking, and fleet orchestration."
)


def test_ideation_and_fleet_produce_ranked_candidates() -> None:
    ideation = ideate(PROMPT)
    assert len(ideation.candidates) >= 3
    assert any("shared-core" in candidate.notes for candidate in ideation.candidates)

    fleet = run_fleet(PROMPT)
    assert fleet.winner.score >= fleet.candidates[-1].score
    assert fleet.certificate["task_kind"] == "fleet"


def test_scaffold_uses_same_project_plan_as_fleet() -> None:
    generated = scaffold(PROMPT)
    paths = {module.path for module in generated.modules}

    assert "src/generated_app/core.py" in paths
    assert "src/generated_app/api.py" in paths
    assert "src/generated_app/fleet.py" in paths
    assert "analysis" in generated.plan_summary
