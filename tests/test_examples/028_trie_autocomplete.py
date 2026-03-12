"""Trie with insertion, prefix search, and top-k autocomplete by frequency.

Bug: In the DFS collection phase, the bug builds the current word by always
appending child characters to the original prefix instead of extending through
the recursion. All collected words end up being prefix + single character
instead of the full word, causing incorrect autocomplete results.
"""

CORRECT = r"""
def trie_autocomplete(words_with_counts, queries):
    # Build trie
    # Each node: {'children': {}, 'is_end': False, 'count': 0}
    root = {'children': {}, 'is_end': False, 'count': 0}

    def insert(word, count):
        node = root
        for ch in word:
            if ch not in node['children']:
                node['children'][ch] = {
                    'children': {}, 'is_end': False, 'count': 0
                }
            node = node['children'][ch]
        node['is_end'] = True
        node['count'] += count

    for word, count in words_with_counts:
        insert(word, count)

    def find_prefix_node(prefix):
        node = root
        for ch in prefix:
            if ch not in node['children']:
                return None
            node = node['children'][ch]
        return node

    def collect_words(node, current_prefix, results):
        # DFS to collect all words under this node
        if node['is_end']:
            results.append((current_prefix, node['count']))
        for ch in sorted(node['children'].keys()):
            child = node['children'][ch]
            # CORRECT: extend prefix through recursion
            collect_words(child, current_prefix + ch, results)

    all_results = {}
    for prefix, k in queries:
        prefix_node = find_prefix_node(prefix)
        if prefix_node is None:
            all_results[prefix] = []
            continue

        collected = []
        collect_words(prefix_node, prefix, collected)

        # Sort by (-count, word) and take top k
        collected.sort(key=lambda x: (-x[1], x[0]))
        all_results[prefix] = collected[:k]

    return all_results

words_with_counts = WORDS_WITH_COUNTS
queries = QUERIES
result = trie_autocomplete(words_with_counts, queries)
"""

BUGGY = r"""
def trie_autocomplete(words_with_counts, queries):
    # Build trie
    # Each node: {'children': {}, 'is_end': False, 'count': 0}
    root = {'children': {}, 'is_end': False, 'count': 0}

    def insert(word, count):
        node = root
        for ch in word:
            if ch not in node['children']:
                node['children'][ch] = {
                    'children': {}, 'is_end': False, 'count': 0
                }
            node = node['children'][ch]
        node['is_end'] = True
        node['count'] += count

    for word, count in words_with_counts:
        insert(word, count)

    def find_prefix_node(prefix):
        node = root
        for ch in prefix:
            if ch not in node['children']:
                return None
            node = node['children'][ch]
        return node

    def collect_words(node, current_prefix, results, original_prefix):
        # DFS to collect all words under this node
        if node['is_end']:
            results.append((current_prefix, node['count']))
        for ch in sorted(node['children'].keys()):
            child = node['children'][ch]
            # BUG: always appends to original_prefix instead of current_prefix
            # so words deeper than 1 level below prefix are truncated
            collect_words(child, original_prefix + ch, results, original_prefix)

    all_results = {}
    for prefix, k in queries:
        prefix_node = find_prefix_node(prefix)
        if prefix_node is None:
            all_results[prefix] = []
            continue

        collected = []
        collect_words(prefix_node, prefix, collected, prefix)

        # Sort by (-count, word) and take top k
        collected.sort(key=lambda x: (-x[1], x[0]))
        all_results[prefix] = collected[:k]

    return all_results

words_with_counts = WORDS_WITH_COUNTS
queries = QUERIES
result = trie_autocomplete(words_with_counts, queries)
"""


def SPEC(WORDS_WITH_COUNTS, QUERIES, result):
    """Verify trie autocomplete:
    1) Every returned word starts with the given prefix
    2) Every returned word was actually inserted
    3) Results are top-k most frequent (compare to brute force)
    4) Results sorted by (-count, word)
    """
    if not isinstance(result, dict):
        return False

    # Build ground truth: aggregate counts per word
    word_counts = {}
    for word, count in WORDS_WITH_COUNTS:
        word_counts[word] = word_counts.get(word, 0) + count

    for prefix, k in QUERIES:
        if prefix not in result:
            return False
        completions = result[prefix]
        if not isinstance(completions, list):
            return False

        # Check each returned entry
        for item in completions:
            if not isinstance(item, (list, tuple)) or len(item) != 2:
                return False
            word, count = item
            # (1) word starts with prefix
            if not word.startswith(prefix):
                return False
            # (2) word was inserted with this count
            if word not in word_counts:
                return False
            if word_counts[word] != count:
                return False

        # (3) Compare to brute force top-k
        matching = []
        for word, count in word_counts.items():
            if word.startswith(prefix):
                matching.append((word, count))
        matching.sort(key=lambda x: (-x[1], x[0]))
        expected = matching[:k]

        if len(completions) != len(expected):
            return False

        # (4) Check ordering and content
        for i, (word, count) in enumerate(completions):
            if word != expected[i][0] or count != expected[i][1]:
                return False

    return True


BUG_DESC = (
    "In the DFS word collection phase, the bug always appends the child character "
    "to the original prefix instead of the current accumulated prefix. This means "
    "for words like 'abcde' with prefix 'a', the recursion builds 'ab', then 'ac' "
    "(not 'abc'), then 'ad' (not 'abcd'), etc. Words deeper than one level below "
    "the prefix node are reconstructed incorrectly, producing non-existent words."
)


def _generate_words():
    import random
    chars = 'abcde'
    n_words = random.randint(15, 25)
    words_with_counts = []

    # Generate some words sharing prefixes
    prefixes = [''.join(random.choices(chars, k=random.randint(1, 3)))
                for _ in range(4)]

    for _ in range(n_words):
        if random.random() < 0.6 and prefixes:
            # Build on existing prefix
            p = random.choice(prefixes)
            suffix_len = random.randint(1, 5)
            suffix = ''.join(random.choices(chars, k=suffix_len))
            word = p + suffix
        else:
            length = random.randint(3, 8)
            word = ''.join(random.choices(chars, k=length))
        count = random.randint(1, 5)
        words_with_counts.append((word, count))

    return words_with_counts


def _generate_queries():
    import random
    chars = 'abcde'
    queries = []
    for _ in range(random.randint(3, 5)):
        prefix_len = random.randint(1, 3)
        prefix = ''.join(random.choices(chars, k=prefix_len))
        queries.append((prefix, 3))
    return queries


INPUT_OVERRIDES = {
    "WORDS_WITH_COUNTS": _generate_words,
    "QUERIES": _generate_queries,
}
