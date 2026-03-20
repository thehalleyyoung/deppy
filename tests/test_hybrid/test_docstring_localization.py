from __future__ import annotations

from deppy.hybrid.diagnostics.localization import ExistingCodeChecker


def test_existing_code_checker_reports_docstring_code_mismatch() -> None:
    source = '''
def normalize(items):
    """Args:
        items: non-empty list

    Returns:
        list: non-empty sorted list
    """
    return []
'''
    result = ExistingCodeChecker(include_h1_names=True).check_source(
        source,
        file_path="sample.py",
    )

    assert any(diag.code.startswith("DEPPY-IC-") for diag in result.diagnostics)
    assert any(
        "non-empty" in ((diag.detail or "") + " " + (diag.message or "")).lower()
        for diag in result.diagnostics
    )


def test_existing_code_checker_allows_bare_return_for_none_annotation() -> None:
    source = '''
def update_state(flag: bool) -> None:
    if flag:
        return
'''
    result = ExistingCodeChecker(include_h1_names=True).check_source(
        source,
        file_path="sample.py",
    )

    assert not any(diag.code.startswith("DEPPY-SC-") for diag in result.diagnostics)


def test_existing_code_checker_ignores_nested_bare_return_in_outer_function() -> None:
    source = '''
def collect_cycles() -> list[list[str]]:
    items: list[list[str]] = []

    def visit(node: str) -> None:
        if node == "stop":
            return
        items.append([node])

    visit("start")
    return items
'''
    result = ExistingCodeChecker(include_h1_names=True).check_source(
        source,
        file_path="sample.py",
    )

    assert not any(diag.code.startswith("DEPPY-SC-") for diag in result.diagnostics)


def test_existing_code_checker_ignores_early_return_docstring_prose() -> None:
    source = '''
def div_zero_safe(total, count):
    """Guard site refines the section: early-return on count == 0
    provides restriction map from {int|True} -> {int|!=0}."""
    if count == 0:
        return 0.0
    average = total / count
    return round(average, 2)
'''
    result = ExistingCodeChecker(include_h1_names=True).check_source(
        source,
        file_path="sample.py",
    )

    assert not any(diag.code.startswith("DEPPY-IC-") for diag in result.diagnostics)
    assert not any(diag.code.startswith("DEPPY-IS-") for diag in result.diagnostics)


def test_existing_code_checker_ignores_summary_docstrings() -> None:
    source = '''
def producer(n):
    """Produce values from 0 to n-1."""
    return list(range(n))
'''
    result = ExistingCodeChecker(include_h1_names=True).check_source(
        source,
        file_path="sample.py",
    )

    assert not any(diag.code.startswith("DEPPY-IC-") for diag in result.diagnostics)
    assert not any(diag.code.startswith("DEPPY-IS-") for diag in result.diagnostics)


def test_existing_code_checker_ignores_plain_return_summary_docstrings() -> None:
    source = '''
def as_tool():
    """Return a LangChain-compatible tool definition."""
    return {"name": "demo", "func": lambda value: value}
'''
    result = ExistingCodeChecker(include_h1_names=True).check_source(
        source,
        file_path="sample.py",
    )

    assert not any(diag.code.startswith("DEPPY-IC-") for diag in result.diagnostics)
    assert not any(diag.code.startswith("DEPPY-IS-") for diag in result.diagnostics)


def test_existing_code_checker_reports_specific_sorted_bug_without_annotation() -> None:
    source = '''
def stable_unique_sorted(items):
    """Requires:
        items is non-empty.

    Returns:
        result is sorted.
        result is unique.
    """
    if not items:
        return []
    return list(dict.fromkeys(items))
'''
    result = ExistingCodeChecker(include_h1_names=True).check_source(
        source,
        file_path="sample.py",
    )

    details = [diag.detail or "" for diag in result.diagnostics if diag.code.startswith("DEPPY-IC-")]
    assert any("sorted" in detail.lower() for detail in details)
    assert not any("documented behavior says:\n  Returns:" in detail for detail in details)


def test_existing_code_checker_reports_specific_sorted_bug_with_annotation() -> None:
    source = '''
def stable_unique_sorted(items: list[int]) -> list[int]:
    """Requires:
        items is non-empty.

    Returns:
        result is sorted.
        result is unique.
    """
    if not items:
        return []
    return list(dict.fromkeys(items))
'''
    result = ExistingCodeChecker(include_h1_names=True).check_source(
        source,
        file_path="sample.py",
    )

    details = [diag.detail or "" for diag in result.diagnostics if diag.code.startswith("DEPPY-IC-")]
    assert any("sorted" in detail.lower() for detail in details)
