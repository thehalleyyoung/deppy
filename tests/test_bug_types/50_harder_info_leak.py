"""Harder INFO_LEAK: exception details, config exposure, stack traces in responses."""

BUG_TYPE = "INFO_LEAK"
BUG_DESC = "Information leak in complex error handling patterns"

EXAMPLES = [
    (
        "api_error_handler",
        # buggy: exception message exposed in API response
        '''\
def handle_request(request):
    try:
        result = process(request)
        return {"status": "ok", "data": result}
    except Exception as e:
        return {"status": "error", "detail": str(e)}
''',
        # safe: generic error message
        '''\
def handle_request(request):
    try:
        result = process(request)
        return {"status": "ok", "data": result}
    except Exception as e:
        log_error(e)
        return {"status": "error", "detail": "internal error"}
''',
        "Raw exception message returned in API response",
    ),
    (
        "db_error_detail",
        # buggy: database exception with connection details raised to caller
        '''\
def query_database(sql, params):
    try:
        conn = get_connection()
        return conn.execute(sql, params)
    except Exception as e:
        raise ValueError(f"DB error: {e}")
''',
        # safe: sanitized error
        '''\
def query_database(sql, params):
    try:
        conn = get_connection()
        return conn.execute(sql, params)
    except Exception as e:
        log_error(e)
        raise ValueError("database query failed")
''',
        "Database exception details re-raised exposing internals",
    ),
    (
        "debug_response",
        # buggy: full traceback included in HTTP response body
        '''\
import traceback
def error_page(request):
    try:
        return render(request)
    except Exception:
        tb = traceback.format_exc()
        return {"body": tb, "status": 500}
''',
        # safe: log traceback, return generic message
        '''\
import traceback
def error_page(request):
    try:
        return render(request)
    except Exception:
        tb = traceback.format_exc()
        log_debug(tb)
        return {"body": "internal server error", "status": 500}
''',
        "Full traceback included in response body",
    ),
]
