"""TIMING_CHANNEL: early-exit comparison leaks timing information —
the comparison presheaf is not constant-time, allowing an adversary
to observe timing differences.
"""

BUG_TYPE = "TIMING_CHANNEL"
BUG_DESC = "Timing side-channel in comparison"

EXAMPLES = [
    (
        "byte_compare_early_exit",
        # buggy: element-wise comparison with early return
        '''\
def verify_token(user_token, real_token):
    if len(user_token) != len(real_token):
        return False
    for i in range(len(user_token)):
        if user_token[i] != real_token[i]:
            return False
    return True
''',
        # safe: constant-time comparison via hmac.compare_digest
        '''\
import hmac
def verify_token(user_token, real_token):
    return hmac.compare_digest(user_token, real_token)
''',
        "Early exit in byte-wise compare leaks prefix length",
    ),
    (
        "password_compare",
        # buggy: direct string comparison character by character
        '''\
def check_password(attempt, stored):
    for i in range(min(len(attempt), len(stored))):
        if attempt[i] != stored[i]:
            return False
    return len(attempt) == len(stored)
''',
        # safe: use hmac.compare_digest
        '''\
import hmac
def check_password(attempt, stored):
    return hmac.compare_digest(attempt.encode(), stored.encode())
''',
        "Character-by-character password comparison",
    ),
    (
        "api_key_compare",
        # buggy: comparing API keys with early return
        '''\
def validate_key(provided, expected):
    for i in range(len(provided)):
        if provided[i] != expected[i]:
            return False
    return True
''',
        # safe: constant-time comparison
        '''\
import hmac
def validate_key(provided, expected):
    return hmac.compare_digest(provided, expected)
''',
        "API key comparison with timing leak",
    ),
]
