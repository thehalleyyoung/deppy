"""Hard TIMING_CHANNEL + INFO_LEAK examples — subtler side-channel patterns."""

BUG_TYPE = "TIMING_CHANNEL"
BUG_DESC = "Timing channel in harder patterns"

EXAMPLES = [
    (
        "token_prefix_leak",
        # buggy: early return on prefix mismatch leaks token length
        '''\
def check_token(provided, stored):
    if len(provided) != len(stored):
        return False
    for i in range(len(provided)):
        if provided[i] != stored[i]:
            return False
    return True
''',
        # safe: constant-time comparison
        '''\
import hmac
def check_token(provided, stored):
    return hmac.compare_digest(provided, stored)
''',
        "Byte-by-byte comparison with early exit leaks matched prefix length",
    ),
    (
        "hash_timing",
        # buggy: comparing hashes with == instead of constant-time
        '''\
import hashlib
def verify_hash(data, expected_hex):
    actual = hashlib.sha256(data).hexdigest()
    if actual == expected_hex:
        return True
    return False
''',
        # safe: constant-time
        '''\
import hashlib
import hmac
def verify_hash(data, expected_hex):
    actual = hashlib.sha256(data).hexdigest()
    return hmac.compare_digest(actual, expected_hex)
''',
        "Hash comparison with == operator leaks timing information",
    ),
    (
        "manual_loop_compare",
        # buggy: manual loop comparison of secrets
        '''\
def secrets_match(a, b):
    if len(a) != len(b):
        return False
    match = True
    for x, y in zip(a, b):
        if x != y:
            match = False
            break
    return match
''',
        # safe: no early break, use hmac
        '''\
import hmac
def secrets_match(a, b):
    return hmac.compare_digest(a, b)
''',
        "Manual loop with break on mismatch creates timing side channel",
    ),
]
