from __future__ import annotations

from deppy.nl_synthesis import (
    apply_synthesized_annotations,
    bundle_to_contract_annotations,
    parse_docstring_fragments,
    synthesize_types_from_docstring,
)
from deppy.solver.solver_interface import SolverResult, SolverStatus


def test_parse_google_numpy_and_rest_docstrings():
    google_doc = """
    Args:
        xs: non-empty
        x: not None
    Returns:
        result: len(result) == len(xs)
    """
    numpy_doc = """
    Parameters
    ----------
    xs : Sequence[int]
        sorted
    Returns
    -------
    list
        permutation of xs
    """
    rest_doc = ":param xs: non-empty\n:returns: sorted"

    google_fragments = parse_docstring_fragments(google_doc)
    numpy_fragments = parse_docstring_fragments(numpy_doc)
    rest_fragments = parse_docstring_fragments(rest_doc)

    assert [(f.kind, f.target) for f in google_fragments] == [
        ("requires", "xs"),
        ("requires", "x"),
        ("ensures", "result"),
    ]
    assert numpy_fragments[0].style == "numpy"
    assert numpy_fragments[0].target == "xs"
    assert rest_fragments[0].style == "rest"
    assert rest_fragments[1].target == "result"


def test_synthesis_marks_contradictory_and_accepted_constraints():
    doc = """
    Requires: x >= 0
    Requires: x < 0
    Ensures: result >= x
    """
    bundle = synthesize_types_from_docstring(doc, function_name="f", params=["x"])

    statuses = [constraint.verification_status for constraint in bundle.constraints]
    assert statuses[0] == "accepted"
    assert statuses[1] == "abstained_contradictory"
    assert statuses[2] == "accepted"
    assert bundle.constraints[1].evidence.proof_certificate_hash


def test_annotation_write_back_and_contract_conversion():
    def transform(xs):
        """Args:\n    xs: non-empty\nReturns:\n    result: len(result) == len(xs)"""
        return list(xs)

    bundle = synthesize_types_from_docstring(transform)
    contracts = bundle_to_contract_annotations(bundle)
    apply_synthesized_annotations(transform, bundle)

    assert len(bundle.accepted_constraints) == 2
    assert len(contracts) == 2
    assert "__docstring_constraints__" in transform.__annotations__
    assert len(transform.__annotations__["__contracts__"]) == 2


def test_timeout_abstains(monkeypatch):
    def fake_quick_check(*args, **kwargs):
        return SolverResult(status=SolverStatus.TIMEOUT, explanation="timed out")

    monkeypatch.setattr("deppy.nl_synthesis.verifier.quick_check", fake_quick_check)
    bundle = synthesize_types_from_docstring("Requires: x >= 0", function_name="f", params=["x"])
    assert bundle.constraints[0].verification_status == "abstained_unverified"
    assert "timed out" in bundle.constraints[0].evidence.explanation


def test_parse_returns_and_requires_clause_lines_separately():
    doc = """
    Requires:
        items is non-empty.

    Returns:
        result is sorted.
        result is unique.
    """

    fragments = parse_docstring_fragments(doc)

    assert [(f.kind, f.target, f.normalized_text) for f in fragments] == [
        ("requires", None, "items is non-empty."),
        ("ensures", "result", "result is sorted."),
        ("ensures", "result", "result is unique."),
    ]


def test_synthesis_accepts_multiple_return_property_clauses():
    doc = """
    Requires:
        items is non-empty.

    Returns:
        result is sorted.
        result is unique.
    """

    bundle = synthesize_types_from_docstring(doc, function_name="f", params=["items"])

    accepted = {
        constraint.predicate_text
        for constraint in bundle.accepted_constraints
    }
    assert "len(items) > 0" in accepted
    assert "sorted(result)" in accepted
    assert "unique(result)" in accepted
