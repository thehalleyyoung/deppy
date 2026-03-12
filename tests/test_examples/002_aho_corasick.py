"""Aho-Corasick multi-pattern string matching.

Bug: During the search phase, the algorithm only checks for matches at the
current trie node but does not follow the output/dictionary links (suffix
links that point to nodes representing patterns that are proper suffixes of
the string matched so far). This means patterns that are suffixes of other
patterns are missed (e.g., "he" inside "she").
"""

CORRECT = r"""
from collections import deque

def aho_corasick(patterns, text):
    # Build trie
    goto = [{}]        # goto[state][char] -> state
    fail = [0]         # failure links
    output = [[]]      # output[state] = list of pattern indices
    num_states = 1

    # Insert patterns into trie
    for pid, pat in enumerate(patterns):
        cur = 0
        for ch in pat:
            if ch not in goto[cur]:
                goto[cur][ch] = num_states
                goto.append({})
                fail.append(0)
                output.append([])
                num_states += 1
            cur = goto[cur][ch]
        output[cur].append(pid)

    # Build failure links via BFS
    queue = deque()
    for ch, s in goto[0].items():
        fail[s] = 0
        queue.append(s)

    while queue:
        r = queue.popleft()
        for ch, s in goto[r].items():
            queue.append(s)
            state = fail[r]
            while state != 0 and ch not in goto[state]:
                state = fail[state]
            fail[s] = goto[state].get(ch, 0)
            if fail[s] == s:
                fail[s] = 0
            # Merge output from failure link (dictionary/output links)
            output[s] = output[s] + output[fail[s]]
        # end for
    # end while

    # Search phase
    results = {pat: [] for pat in patterns}
    state = 0
    for i, ch in enumerate(text):
        while state != 0 and ch not in goto[state]:
            state = fail[state]
        state = goto[state].get(ch, 0)

        # CORRECT: check all outputs at current state
        # (output already includes dictionary link outputs from construction)
        for pid in output[state]:
            pat = patterns[pid]
            start = i - len(pat) + 1
            results[pat].append(start)

    return results

patterns = PATTERNS
text = TEXT
result = aho_corasick(patterns, text)
"""

BUGGY = r"""
from collections import deque

def aho_corasick(patterns, text):
    # Build trie
    goto = [{}]        # goto[state][char] -> state
    fail = [0]         # failure links
    output = [[]]      # output[state] = list of pattern indices
    num_states = 1

    # Insert patterns into trie
    for pid, pat in enumerate(patterns):
        cur = 0
        for ch in pat:
            if ch not in goto[cur]:
                goto[cur][ch] = num_states
                goto.append({})
                fail.append(0)
                output.append([])
                num_states += 1
            cur = goto[cur][ch]
        output[cur].append(pid)

    # Build failure links via BFS
    queue = deque()
    for ch, s in goto[0].items():
        fail[s] = 0
        queue.append(s)

    while queue:
        r = queue.popleft()
        for ch, s in goto[r].items():
            queue.append(s)
            state = fail[r]
            while state != 0 and ch not in goto[state]:
                state = fail[state]
            fail[s] = goto[state].get(ch, 0)
            if fail[s] == s:
                fail[s] = 0
            # BUG: Do NOT merge output from failure link
            # output[s] = output[s] + output[fail[s]]  <-- omitted
        # end for
    # end while

    # Search phase
    results = {pat: [] for pat in patterns}
    state = 0
    for i, ch in enumerate(text):
        while state != 0 and ch not in goto[state]:
            state = fail[state]
        state = goto[state].get(ch, 0)

        # Only reports matches at the exact trie node, missing
        # suffix-pattern matches that should come from output links
        for pid in output[state]:
            pat = patterns[pid]
            start = i - len(pat) + 1
            results[pat].append(start)

    return results

patterns = PATTERNS
text = TEXT
result = aho_corasick(patterns, text)
"""


def SPEC(patterns, text, result):
    """Verify Aho-Corasick result:
    1) Every reported position is a true match.
    2) No occurrences are missed (brute-force check).
    """
    if not isinstance(result, dict):
        return False

    for pat in patterns:
        if pat not in result:
            return False

        reported = result[pat]

        # Check all reported positions are correct
        for pos in reported:
            if pos < 0 or pos + len(pat) > len(text):
                return False
            if text[pos:pos + len(pat)] != pat:
                return False

        # Brute-force find all occurrences
        expected = []
        for i in range(len(text) - len(pat) + 1):
            if text[i:i + len(pat)] == pat:
                expected.append(i)

        if sorted(reported) != sorted(expected):
            return False

    return True


BUG_DESC = (
    "During construction, the algorithm does not merge output lists along "
    "failure links (dictionary/output links). During search, it only reports "
    "matches at the exact trie node reached, missing patterns that are proper "
    "suffixes of the current match. For example, with patterns ['he', 'she'] "
    "and text 'she', it finds 'she' at position 0 but misses 'he' at position 1."
)


def _generate_inputs():
    import random

    alphabet = 'abc'
    num_patterns = random.randint(3, 5)

    # Generate patterns, ensuring some are suffixes of others
    patterns = []
    # First generate a longer pattern
    base_len = random.randint(3, 4)
    base = ''.join(random.choice(alphabet) for _ in range(base_len))
    patterns.append(base)
    # Add a suffix of the base as another pattern
    suffix_len = random.randint(1, base_len - 1)
    patterns.append(base[-suffix_len:])

    # Add more random patterns
    while len(patterns) < num_patterns:
        plen = random.randint(2, 4)
        p = ''.join(random.choice(alphabet) for _ in range(plen))
        if p not in patterns:
            patterns.append(p)

    # Generate text that contains the base pattern at least once
    text_len = random.randint(20, 40)
    text_chars = list(random.choice(alphabet) for _ in range(text_len))
    # Embed base pattern at a random position
    pos = random.randint(0, text_len - len(base))
    for i, ch in enumerate(base):
        text_chars[pos + i] = ch
    text = ''.join(text_chars)

    return patterns, text


def _gen_patterns():
    p, _ = _generate_inputs()
    return p


def _gen_text():
    # We need coordinated generation; use a shared seed trick
    import random
    state = random.getstate()
    p, t = _generate_inputs()
    return t


# Because patterns and text need to be coordinated, we use a wrapper
_cached = {}

def _gen_patterns_coordinated():
    import random
    p, t = _generate_inputs()
    _cached['text'] = t
    _cached['patterns'] = p
    return p

def _gen_text_coordinated():
    if 'text' in _cached:
        t = _cached.pop('text')
        _cached.pop('patterns', None)
        return t
    _, t = _generate_inputs()
    return t


INPUT_OVERRIDES = {
    "PATTERNS": _gen_patterns_coordinated,
    "TEXT": _gen_text_coordinated,
}
