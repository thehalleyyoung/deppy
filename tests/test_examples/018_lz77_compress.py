"""LZ77 sliding window compression.

Bug: The offset calculation is wrong. Offset should be (current_pos - match_start),
the relative distance back from the current position. The bug uses match_start
(the absolute position in the text), so decompression with the wrong offsets
produces garbage output that doesn't match the original string.
"""

CORRECT = r"""
def lz77_compress(text, window_size):
    # LZ77 compression with sliding window.
    # At each position, find the longest match in the window (looking back
    # up to window_size characters). Emit (offset, length, next_char) tuples.
    # Offset is the relative distance back from current position to match start.
    i = 0
    tokens = []
    n = len(text)
    max_lookahead = window_size  # cap lookahead to window size
    while i < n:
        best_offset = 0
        best_length = 0
        best_match_pos = -1
        # Search window: positions max(0, i - window_size) to i-1
        search_start = max(0, i - window_size)
        search_end = i
        for j in range(search_start, search_end):
            match_len = 0
            # Compare characters starting from window position j and current i
            # Match can extend into lookahead but window part must stay in window
            lookahead_limit = min(n - i, max_lookahead)
            while match_len < lookahead_limit:
                # Window position must not cross into current position
                if j + match_len >= i:
                    break
                if text[j + match_len] != text[i + match_len]:
                    break
                match_len += 1
            # Keep longest match; on ties prefer closer match (larger offset)
            if match_len > best_length:
                best_length = match_len
                best_match_pos = j
                # CORRECT: offset is relative distance back from current pos
                best_offset = i - j
        # Emit token
        if best_length > 0:
            # Next character after the match (or empty if at end)
            if i + best_length < n:
                next_char = text[i + best_length]
            else:
                next_char = ''
            tokens.append((best_offset, best_length, next_char))
            i += best_length + 1
        else:
            # No match found: emit literal
            tokens.append((0, 0, text[i]))
            i += 1
    return tokens

def lz77_decompress(tokens):
    # Decompress a sequence of LZ77 tokens back to original string.
    output = []
    for offset, length, next_char in tokens:
        if length > 0:
            # Copy 'length' characters from 'offset' positions back
            start = len(output) - offset
            if start < 0:
                raise ValueError(f"Invalid offset {offset} at position {len(output)}")
            for k in range(length):
                # Index into already-decompressed output
                output.append(output[start + k])
        if next_char != '':
            output.append(next_char)
    return ''.join(output)

def verify_roundtrip(text, tokens):
    # Verify that decompressing tokens reproduces original text.
    decompressed = lz77_decompress(tokens)
    return decompressed == text

txt = TEXT
ws = WINDOW_SIZE
compressed = lz77_compress(txt, ws)
assert verify_roundtrip(txt, compressed), "Roundtrip verification failed"
result = compressed
"""

BUGGY = r"""
def lz77_compress(text, window_size):
    # LZ77 compression with sliding window.
    # At each position, find the longest match in the window (looking back
    # up to window_size characters). Emit (offset, length, next_char) tuples.
    # Offset is the relative distance back from current position to match start.
    i = 0
    tokens = []
    n = len(text)
    max_lookahead = window_size
    while i < n:
        best_offset = 0
        best_length = 0
        best_match_pos = -1
        # Search window: positions max(0, i - window_size) to i-1
        search_start = max(0, i - window_size)
        search_end = i
        for j in range(search_start, search_end):
            match_len = 0
            lookahead_limit = min(n - i, max_lookahead)
            while match_len < lookahead_limit:
                if j + match_len >= i:
                    break
                if text[j + match_len] != text[i + match_len]:
                    break
                match_len += 1
            if match_len > best_length:
                best_length = match_len
                best_match_pos = j
                # BUG: uses absolute position instead of relative offset
                # Should be: best_offset = i - j
                best_offset = j
        # Emit token
        if best_length > 0:
            if i + best_length < n:
                next_char = text[i + best_length]
            else:
                next_char = ''
            tokens.append((best_offset, best_length, next_char))
            i += best_length + 1
        else:
            tokens.append((0, 0, text[i]))
            i += 1
    return tokens

def lz77_decompress(tokens):
    # Decompress a sequence of LZ77 tokens back to original string.
    output = []
    for offset, length, next_char in tokens:
        if length > 0:
            start = len(output) - offset
            if start < 0:
                raise ValueError(f"Invalid offset {offset} at position {len(output)}")
            for k in range(length):
                output.append(output[start + k])
        if next_char != '':
            output.append(next_char)
    return ''.join(output)

def verify_roundtrip(text, tokens):
    # Verify that decompressing tokens reproduces original text.
    try:
        decompressed = lz77_decompress(tokens)
        return decompressed == text
    except (ValueError, IndexError):
        return False

txt = TEXT
ws = WINDOW_SIZE
compressed = lz77_compress(txt, ws)
# Note: verify_roundtrip will fail due to the bug, but we still return tokens
result = compressed
"""


def SPEC(TEXT, WINDOW_SIZE, result):
    """Verify LZ77 compression correctness:
    Decompress the output tokens and check that the result equals the input.
    Also verify token structure validity.
    """
    if not isinstance(result, list):
        return False

    # Verify each token is a valid (offset, length, char) triple
    for token in result:
        if not isinstance(token, tuple) or len(token) != 3:
            return False
        offset, length, next_char = token
        if not isinstance(offset, int) or not isinstance(length, int):
            return False
        if offset < 0 or length < 0:
            return False
        if not isinstance(next_char, str) or len(next_char) > 1:
            return False
        # If length > 0, offset must be positive
        if length > 0 and offset <= 0:
            return False
        # Offset must not exceed window_size
        if offset > WINDOW_SIZE:
            return False

    # Decompress and verify
    output = []
    for offset, length, next_char in result:
        if length > 0:
            start = len(output) - offset
            if start < 0:
                return False
            for k in range(length):
                if start + k >= len(output):
                    return False
                output.append(output[start + k])
        if next_char != '':
            output.append(next_char)

    decompressed = ''.join(output)
    return decompressed == TEXT


BUG_DESC = (
    "The offset in each LZ77 token should be the relative distance from the "
    "current position back to the match start (i - j), but the bug records the "
    "absolute position (j) instead. When decompressing, the wrong offset causes "
    "lookback to the wrong position, producing a string that differs from the "
    "original input."
)


def _generate_text():
    import random
    length = random.randint(20, 40)
    alphabet = 'abcd'
    # Build text with some repeated patterns for interesting compression
    text = []
    while len(text) < length:
        if random.random() < 0.3 and len(text) > 4:
            # Copy a recent substring to create repetition
            start = random.randint(max(0, len(text) - 8), len(text) - 2)
            end = min(start + random.randint(2, 5), len(text))
            text.extend(text[start:end])
        else:
            text.append(random.choice(alphabet))
    return ''.join(text[:length])


INPUT_OVERRIDES = {
    "TEXT": _generate_text,
    "WINDOW_SIZE": lambda: 8,
}
