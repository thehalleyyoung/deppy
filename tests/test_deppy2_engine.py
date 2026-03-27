from deppy import (
    check_equiv,
    refine,
    requires,
    ensures,
    synthesize_refinements,
    verify,
)


def test_refine_synthesize_and_equivalence_share_new_core() -> None:
    source = """
def average(values: list[int]) -> float:
    return sum(values) / len(values)
"""

    analysis = refine(source)
    assert analysis.has_bugs
    assert any(obstruction.bug_type == "DIV_ZERO" for obstruction in analysis.obstructions)

    synthesized = synthesize_refinements(source)
    assert any(item.site_name == "values" and item.carrier == "list[int]" for item in synthesized)

    equiv = check_equiv(
        "def f(x):\n    return x + x\n",
        "def f(x):\n    return x * 2\n",
    )
    assert equiv.equivalent


def test_verify_uses_contracts_to_discharge_safety_obligations() -> None:
    @requires(lambda values: len(values) > 0)
    @ensures(lambda result: isinstance(result, float))
    def safe_average(values: list[int]) -> float:
        return sum(values) / len(values)

    result = verify(safe_average)

    assert result.verified
    assert result.vcs_total >= 2
    assert result.vcs_proved == result.vcs_total
