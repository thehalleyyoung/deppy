"""Harder TIMING_CHANNEL: non-obvious timing leaks via comparison patterns."""

BUG_TYPE = "TIMING_CHANNEL"
BUG_DESC = "Timing side-channel in complex comparison patterns"

EXAMPLES = [
    (
        "api_key_check",
        # buggy: direct == on secret API key
        '''\
def verify_api_key(request_key, stored_key):
    if request_key == stored_key:
        return True
    return False
''',
        # safe: constant-time comparison
        '''\
import hmac
def verify_api_key(request_key, stored_key):
    if hmac.compare_digest(request_key, stored_key):
        return True
    return False
''',
        "Direct string equality on secret API key enables timing attack",
    ),
    (
        "session_token_verify",
        # buggy: char-by-char comparison via zip loop
        '''\
def verify_session(provided, expected):
    if len(provided) != len(expected):
        return False
    for a, b in zip(provided, expected):
        if a != b:
            return False
    return True
''',
        # safe: hmac.compare_digest
        '''\
import hmac
def verify_session(provided, expected):
    return hmac.compare_digest(provided, expected)
''',
        "Character-by-character zip comparison leaks token length prefix",
    ),
    (
        "mac_validation",
        # buggy: computed HMAC compared with ==
        '''\
import hashlib
def validate_mac(message, received_mac, secret):
    computed = hashlib.sha256(secret + message).hexdigest()
    if computed == received_mac:
        return True
    return False
''',
        # safe: hmac.compare_digest
        '''\
import hashlib
import hmac
def validate_mac(message, received_mac, secret):
    computed = hashlib.sha256(secret + message).hexdigest()
    if hmac.compare_digest(computed, received_mac):
        return True
    return False
''',
        "HMAC digest compared with == instead of constant-time comparison",
    ),
]
