"""Hard INFO_LEAK examples — log-based leaks, traceback exposure, verbose errors."""

BUG_TYPE = "INFO_LEAK"
BUG_DESC = "Information leak in harder patterns"

EXAMPLES = [
    (
        "log_credentials",
        # buggy: logging sensitive data in exception message
        '''\
def connect(host, password):
    try:
        db = open_connection(host, password)
    except Exception as e:
        raise RuntimeError(f"Connection to {host} with password {password} failed: {e}")
''',
        # safe: generic error with no interpolated secrets
        '''\
def connect(host, password):
    try:
        db = open_connection(host, password)
    except Exception as e:
        raise RuntimeError("Connection failed")
''',
        "Exception message includes password in f-string",
    ),
    (
        "traceback_in_response",
        # buggy: returning full traceback to caller
        '''\
import traceback
def handle_request(data):
    try:
        result = process(data)
    except Exception:
        return {"error": traceback.format_exc()}
    return {"result": result}
''',
        # safe: generic error message
        '''\
def handle_request(data):
    try:
        result = process(data)
    except Exception:
        return {"error": "Internal error occurred"}
    return {"result": result}
''',
        "Full traceback returned in API response exposes internals",
    ),
    (
        "config_in_error",
        # buggy: config dict with secrets included in error message
        '''\
def load_service(config):
    if "endpoint" not in config:
        raise ValueError("Bad config: {}".format(config))
    return config["endpoint"]
''',
        # safe: only mention the missing key
        '''\
def load_service(config):
    if "endpoint" not in config:
        raise ValueError("Missing required key: endpoint")
    return config["endpoint"]
''',
        "Entire config dict (may contain secrets) dumped into error message",
    ),
]
