"""INFO_LEAK: sensitive data interpolated into exception messages —
the secrecy presheaf requires that error-site sections do not
carry secret data, but f-string/format interpolation can leak it.
"""

BUG_TYPE = "INFO_LEAK"
BUG_DESC = "Information leak in exception message"

EXAMPLES = [
    (
        "exception_with_fstring",
        # buggy: interpolating exception details into raised error
        '''\
def process(request):
    try:
        result = handle(request)
    except Exception as e:
        raise ValueError(f"Failed to process: {e}")
''',
        # safe: generic message without interpolated data
        '''\
def process(request):
    try:
        result = handle(request)
    except Exception:
        raise ValueError("Failed to process request")
''',
        "f-string in raise may leak internal details",
    ),
    (
        "format_string_leak",
        # buggy: format() interpolation in exception
        '''\
def authenticate(user, password):
    if not check(user, password):
        raise PermissionError("Auth failed for user={} pass={}".format(user, password))
''',
        # safe: no sensitive data in message
        '''\
def authenticate(user, password):
    if not check(user, password):
        raise PermissionError("Authentication failed")
''',
        ".format() in raise leaks credentials",
    ),
    (
        "percent_format_leak",
        # buggy: %-formatting in raise
        '''\
def connect(host, port, token):
    try:
        sock = open_connection(host, port)
    except Exception as e:
        raise ConnectionError("Connection to %s:%d failed: %s" % (host, port, e))
''',
        # safe: no interpolated data
        '''\
def connect(host, port, token):
    try:
        sock = open_connection(host, port)
    except Exception:
        raise ConnectionError("Connection failed")
''',
        "%-format in raise leaks host/port details",
    ),
]
