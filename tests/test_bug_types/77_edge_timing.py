"""Edge-case TIMING_CHANNEL: direct ==, variable comparison, hash compare."""

BUG_TYPE = "TIMING_CHANNEL"
BUG_DESC = "Timing channel in edge-case comparison patterns"

EXAMPLES = [
    (
        "password_eq",
        # buggy: direct == on password
        '''\
def check_password(stored_password, input_password):
    return stored_password == input_password
''',
        # safe: hmac.compare_digest
        '''\
import hmac
def check_password(stored_password, input_password):
    return hmac.compare_digest(stored_password, input_password)
''',
        "Direct equality on password enables timing attack",
    ),
    (
        "api_token_check",
        # buggy: direct == on token
        '''\
def verify_token(expected_token, provided_token):
    if expected_token == provided_token:
        return True
    return False
''',
        # safe: hmac.compare_digest
        '''\
import hmac
def verify_token(expected_token, provided_token):
    if hmac.compare_digest(expected_token, provided_token):
        return True
    return False
''',
        "Direct equality on API token enables timing attack",
    ),
    (
        "secret_comparison",
        # buggy: direct != on secret
        '''\
def validate_secret(user_secret, db_secret):
    if user_secret != db_secret:
        raise ValueError("invalid")
    return True
''',
        # safe: hmac.compare_digest
        '''\
import hmac
def validate_secret(user_secret, db_secret):
    if not hmac.compare_digest(user_secret, db_secret):
        raise ValueError("invalid")
    return True
''',
        "Direct inequality on secret enables timing attack",
    ),
    (
        "credential_match",
        # buggy: direct == on credential
        '''\
def auth_check(stored_credential, given_credential):
    return stored_credential == given_credential
''',
        # safe: hmac.compare_digest
        '''\
import hmac
def auth_check(stored_credential, given_credential):
    return hmac.compare_digest(stored_credential, given_credential)
''',
        "Direct equality on credential enables timing attack",
    ),
]
