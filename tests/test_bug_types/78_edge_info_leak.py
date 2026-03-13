"""Edge-case INFO_LEAK: str(e) in dict return, repr(e), traceback returned."""

BUG_TYPE = "INFO_LEAK"
BUG_DESC = "Information leak in edge-case error handling"

EXAMPLES = [
    (
        "error_detail_dict",
        # buggy: str(e) in returned dict
        '''\
def api_call(endpoint):
    try:
        return fetch(endpoint)
    except Exception as e:
        return {"error": str(e)}
''',
        # safe: generic message
        '''\
def api_call(endpoint):
    try:
        return fetch(endpoint)
    except Exception as e:
        log(e)
        return {"error": "request failed"}
''',
        "Exception string returned in API response dict",
    ),
    (
        "raise_with_detail",
        # buggy: re-raise with exception details interpolated
        '''\
def process_order(order):
    try:
        validate(order)
    except Exception as e:
        raise RuntimeError(f"Order processing failed: {e}")
''',
        # safe: generic message without exception details
        '''\
def process_order(order):
    try:
        validate(order)
    except Exception as e:
        log_error(e)
        raise RuntimeError("Order processing failed")
''',
        "Exception details interpolated in re-raised error",
    ),
    (
        "repr_exception_return",
        # buggy: repr(e) returned to caller
        '''\
def run_query(sql):
    try:
        return execute(sql)
    except Exception as e:
        return {"status": "error", "info": repr(e)}
''',
        # safe: generic message
        '''\
def run_query(sql):
    try:
        return execute(sql)
    except Exception as e:
        log(e)
        return {"status": "error", "info": "query failed"}
''',
        "repr(e) returned exposing internal exception details",
    ),
    (
        "traceback_in_response",
        # buggy: traceback returned in response
        '''\
import traceback
def handle(request):
    try:
        return process(request)
    except Exception:
        tb = traceback.format_exc()
        return {"body": tb}
''',
        # safe: log traceback, return generic
        '''\
import traceback
def handle(request):
    try:
        return process(request)
    except Exception:
        log(traceback.format_exc())
        return {"body": "internal error"}
''',
        "Full traceback included in response body",
    ),
]
