from __future__ import annotations

from deppy.render.bug_detect import detect_bugs


def _bug_types(source: str) -> set[str]:
    report = detect_bugs(source)
    return {
        obs.bug_type
        for obs in report.obstructions
        if not obs.resolved_by_guard and obs.confidence > 0
    }


def test_detect_bugs_tracks_interpolated_query_variables() -> None:
    source = """
def find_user(conn, username):
    query = f"SELECT * FROM users WHERE name = '{username}'"
    return conn.execute(query).fetchall()
"""

    assert "SQL_INJECTION" in _bug_types(source)


def test_detect_bugs_flags_unescaped_html_rendering() -> None:
    source = """
def render_comment(comment):
    return "<div class='comment'>" + comment + "</div>"
"""

    assert "REFLECTED_XSS" in _bug_types(source)


def test_detect_bugs_adds_runtime_type_witnesses() -> None:
    source = """
def build_msg(name, count):
    return "items: " + count
"""

    assert "TYPE_ERROR" in _bug_types(source)
