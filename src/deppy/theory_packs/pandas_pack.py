from __future__ import annotations

from typing import Any, Tuple

from deppy.core._protocols import SiteKind

from .models import AxiomSpec, TheoryPackSpec, VerificationCase


PANDAS_AXIOMS: Tuple[AxiomSpec, ...] = (
    AxiomSpec(
        name="series-alignment",
        library="pandas",
        version_range=">=1.5",
        site_kinds=(SiteKind.CALL_RESULT, SiteKind.SSA_VALUE),
        rewrite_rule="Series arithmetic aligns on index labels",
        solver_formula="index(a + b) = union(index(a), index(b))",
        delegate_pack_names=("sequence_collection", "nullability"),
        verification_cases=(
            VerificationCase(
                name="series-add-aligns-index",
                operation="series_add_alignment",
                payload={
                    "left_values": [1, 2],
                    "left_index": ["a", "b"],
                    "right_values": [10, 20],
                    "right_index": ["b", "c"],
                },
                expected={"index": ["a", "b", "c"]},
            ),
        ),
    ),
    AxiomSpec(
        name="groupby-sum-preserves-groups",
        library="pandas",
        version_range=">=1.5",
        site_kinds=(SiteKind.CALL_RESULT, SiteKind.MODULE_SUMMARY),
        rewrite_rule="groupby(sum) yields one output row per group key",
        solver_formula="index(result) = distinct(keys)",
        delegate_pack_names=("sequence_collection",),
        verification_cases=(
            VerificationCase(
                name="groupby-sum-two-groups",
                operation="groupby_sum",
                payload={"rows": [{"k": "x", "v": 1}, {"k": "x", "v": 2}, {"k": "y", "v": 4}]},
                expected={"index": ["x", "y"], "values": [3, 4]},
            ),
        ),
    ),
    AxiomSpec(
        name="merge-inner-join",
        library="pandas",
        version_range=">=1.5",
        site_kinds=(SiteKind.CALL_RESULT, SiteKind.HEAP_PROTOCOL),
        rewrite_rule="inner merge keeps rows whose keys are present on both sides",
        solver_formula="rows(result) = rows(left ⋈ right)",
        delegate_pack_names=("heap_protocol", "sequence_collection"),
        verification_cases=(
            VerificationCase(
                name="inner-merge-on-id",
                operation="inner_merge",
                payload={
                    "left_rows": [{"id": 1, "x": "a"}, {"id": 2, "x": "b"}],
                    "right_rows": [{"id": 2, "y": 10}, {"id": 3, "y": 20}],
                    "on": "id",
                },
                expected={"ids": [2], "row_count": 1},
            ),
        ),
    ),
)


def build_pandas_pack_spec() -> TheoryPackSpec:
    return TheoryPackSpec(
        name="pandas",
        library="pandas",
        version_range=">=1.5",
        site_kinds=(SiteKind.CALL_RESULT, SiteKind.SSA_VALUE, SiteKind.HEAP_PROTOCOL, SiteKind.MODULE_SUMMARY),
        delegate_pack_names=("sequence_collection", "nullability", "heap_protocol"),
        axioms=PANDAS_AXIOMS,
        description="Pandas-oriented facade over collection, nullability, and heap protocol theories.",
    )


def verify_pandas_axiom_case(axiom: AxiomSpec, case: VerificationCase, module: Any) -> tuple[bool, str]:
    pd = module
    if case.operation == "series_add_alignment":
        left = pd.Series(case.payload["left_values"], index=case.payload["left_index"])
        right = pd.Series(case.payload["right_values"], index=case.payload["right_index"])
        result = left + right
        observed = list(result.index)
        return observed == list(case.expected["index"]), f"observed index={observed}"
    if case.operation == "groupby_sum":
        frame = pd.DataFrame(case.payload["rows"])
        result = frame.groupby("k")["v"].sum()
        observed_index = list(result.index)
        observed_values = list(result.tolist())
        return observed_index == list(case.expected["index"]) and observed_values == list(case.expected["values"]), f"observed index={observed_index} values={observed_values}"
    if case.operation == "inner_merge":
        left = pd.DataFrame(case.payload["left_rows"])
        right = pd.DataFrame(case.payload["right_rows"])
        result = left.merge(right, how="inner", on=case.payload["on"])
        observed_ids = list(result[case.payload["on"]].tolist())
        observed_count = int(len(result))
        return observed_ids == list(case.expected["ids"]) and observed_count == int(case.expected["row_count"]), f"observed ids={observed_ids} count={observed_count}"
    raise ValueError(f"unsupported pandas verification operation: {case.operation}")
