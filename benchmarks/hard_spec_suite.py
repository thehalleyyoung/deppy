"""
Hard spec satisfaction benchmark: 120 satisfying + 80 violating = 200 pairs.

Each entry is a tuple:
    (name, source, spec_fn_source, expected_satisfies)

- 120 programs SATISFY their spec (expected_satisfies=True)
-  80 programs DO NOT satisfy their spec (expected_satisfies=False)
"""

from textwrap import dedent

SPEC_PROGRAMS: list[tuple[str, str, str, bool]] = [
    # =========================================================================
    # SORTING & SEARCHING (001-025)
    # =========================================================================

    # 001 — correct bubble sort (SAT)
    (
        "spec_001_bubble_sort",
        dedent("""\
            def bubble_sort(arr):
                a = list(arr)
                n = len(a)
                for i in range(n):
                    for j in range(n - i - 1):
                        if a[j] > a[j + 1]:
                            a[j], a[j + 1] = a[j + 1], a[j]
                return a
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 002 — bubble sort with off-by-one: inner loop stops one early (VIO)
    (
        "spec_002_bubble_sort_obo",
        dedent("""\
            def bubble_sort(arr):
                a = list(arr)
                n = len(a)
                for i in range(n):
                    for j in range(n - i - 2):
                        if a[j] > a[j + 1]:
                            a[j], a[j + 1] = a[j + 1], a[j]
                return a
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        False,
    ),

    # 003 — correct insertion sort (SAT)
    (
        "spec_003_insertion_sort",
        dedent("""\
            def insertion_sort(arr):
                a = list(arr)
                for i in range(1, len(a)):
                    key = a[i]
                    j = i - 1
                    while j >= 0 and a[j] > key:
                        a[j + 1] = a[j]
                        j -= 1
                    a[j + 1] = key
                return a
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 004 — insertion sort uses >= instead of > so unstable but still sorts (SAT)
    (
        "spec_004_insertion_sort_ge",
        dedent("""\
            def insertion_sort(arr):
                a = list(arr)
                for i in range(1, len(a)):
                    key = a[i]
                    j = i - 1
                    while j >= 0 and a[j] >= key:
                        a[j + 1] = a[j]
                        j -= 1
                    a[j + 1] = key
                return a
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 005 — selection sort correct (SAT)
    (
        "spec_005_selection_sort",
        dedent("""\
            def selection_sort(arr):
                a = list(arr)
                n = len(a)
                for i in range(n):
                    min_idx = i
                    for j in range(i + 1, n):
                        if a[j] < a[min_idx]:
                            min_idx = j
                    a[i], a[min_idx] = a[min_idx], a[i]
                return a
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 006 — selection sort bug: starts inner loop at i instead of i+1 (VIO)
    (
        "spec_006_selection_sort_bug",
        dedent("""\
            def selection_sort(arr):
                a = list(arr)
                n = len(a)
                for i in range(n):
                    min_idx = i
                    for j in range(i, n):
                        if a[j] < a[min_idx]:
                            min_idx = j
                    a[i], a[min_idx] = a[min_idx], a[i]
                return a
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 007 — merge sort correct (SAT)
    (
        "spec_007_merge_sort",
        dedent("""\
            def merge_sort(arr):
                if len(arr) <= 1:
                    return list(arr)
                mid = len(arr) // 2
                left = merge_sort(arr[:mid])
                right = merge_sort(arr[mid:])
                merged = []
                i = j = 0
                while i < len(left) and j < len(right):
                    if left[i] <= right[j]:
                        merged.append(left[i])
                        i += 1
                    else:
                        merged.append(right[j])
                        j += 1
                merged.extend(left[i:])
                merged.extend(right[j:])
                return merged
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 008 — merge sort bug: uses < instead of <= in merge, still sorts correctly (SAT)
    (
        "spec_008_merge_sort_lt",
        dedent("""\
            def merge_sort(arr):
                if len(arr) <= 1:
                    return list(arr)
                mid = len(arr) // 2
                left = merge_sort(arr[:mid])
                right = merge_sort(arr[mid:])
                merged = []
                i = j = 0
                while i < len(left) and j < len(right):
                    if left[i] < right[j]:
                        merged.append(left[i])
                        i += 1
                    else:
                        merged.append(right[j])
                        j += 1
                merged.extend(left[i:])
                merged.extend(right[j:])
                return merged
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 009 — binary search correct (SAT)
    (
        "spec_009_binary_search",
        dedent("""\
            def binary_search(arr, target):
                lo, hi = 0, len(arr) - 1
                while lo <= hi:
                    mid = (lo + hi) // 2
                    if arr[mid] == target:
                        return mid
                    elif arr[mid] < target:
                        lo = mid + 1
                    else:
                        hi = mid - 1
                return -1
        """),
        dedent("""\
            def spec(arr, target, result):
                if result == -1:
                    return target not in arr
                return 0 <= result < len(arr) and arr[result] == target
        """),
        True,
    ),

    # 010 — binary search bug: lo < hi instead of lo <= hi misses single-element (VIO)
    (
        "spec_010_binary_search_bug",
        dedent("""\
            def binary_search(arr, target):
                lo, hi = 0, len(arr) - 1
                while lo < hi:
                    mid = (lo + hi) // 2
                    if arr[mid] == target:
                        return mid
                    elif arr[mid] < target:
                        lo = mid + 1
                    else:
                        hi = mid - 1
                return -1
        """),
        dedent("""\
            def spec(arr, target, result):
                if result == -1:
                    return target not in arr
                return 0 <= result < len(arr) and arr[result] == target
        """),
        False,
    ),

    # 011 — quick sort correct (SAT)
    (
        "spec_011_quick_sort",
        dedent("""\
            def quick_sort(arr):
                if len(arr) <= 1:
                    return list(arr)
                pivot = arr[len(arr) // 2]
                left = [x for x in arr if x < pivot]
                mid = [x for x in arr if x == pivot]
                right = [x for x in arr if x > pivot]
                return quick_sort(left) + mid + quick_sort(right)
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 012 — quick sort bug: uses <= for left partition, infinite recursion on dups (VIO)
    (
        "spec_012_quick_sort_bug",
        dedent("""\
            def quick_sort(arr):
                if len(arr) <= 1:
                    return list(arr)
                pivot = arr[len(arr) // 2]
                left = [x for x in arr if x <= pivot]
                mid = []
                right = [x for x in arr if x > pivot]
                return quick_sort(left) + mid + quick_sort(right)
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        False,
    ),

    # 013 — counting sort correct for non-negative ints (SAT)
    (
        "spec_013_counting_sort",
        dedent("""\
            def counting_sort(arr):
                if not arr:
                    return []
                max_val = max(arr)
                count = [0] * (max_val + 1)
                for x in arr:
                    count[x] += 1
                result = []
                for i in range(len(count)):
                    result.extend([i] * count[i])
                return result
        """),
        dedent("""\
            def spec(arr, result):
                if not all(x >= 0 for x in arr):
                    return True
                return result == sorted(arr)
        """),
        True,
    ),

    # 014 — linear search correct (SAT)
    (
        "spec_014_linear_search",
        dedent("""\
            def linear_search(arr, target):
                for i, x in enumerate(arr):
                    if x == target:
                        return i
                return -1
        """),
        dedent("""\
            def spec(arr, target, result):
                if result == -1:
                    return target not in arr
                return 0 <= result < len(arr) and arr[result] == target
        """),
        True,
    ),

    # 015 — find minimum correct (SAT)
    (
        "spec_015_find_min",
        dedent("""\
            def find_min(arr):
                if not arr:
                    return None
                m = arr[0]
                for x in arr[1:]:
                    if x < m:
                        m = x
                return m
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result is None
                return result == min(arr)
        """),
        True,
    ),

    # 016 — find minimum bug: initializes to 0 instead of arr[0] (VIO)
    (
        "spec_016_find_min_bug",
        dedent("""\
            def find_min(arr):
                if not arr:
                    return None
                m = 0
                for x in arr:
                    if x < m:
                        m = x
                return m
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result is None
                return result == min(arr)
        """),
        False,
    ),

    # 017 — find second largest correct (SAT)
    (
        "spec_017_second_largest",
        dedent("""\
            def second_largest(arr):
                if len(arr) < 2:
                    return None
                first = second = float('-inf')
                for x in arr:
                    if x > first:
                        second = first
                        first = x
                    elif x > second and x != first:
                        second = x
                if second == float('-inf'):
                    return None
                return second
        """),
        dedent("""\
            def spec(arr, result):
                if len(arr) < 2:
                    return result is None
                unique = sorted(set(arr), reverse=True)
                if len(unique) < 2:
                    return result is None
                return result == unique[1]
        """),
        True,
    ),

    # 018 — find second largest bug: doesn't exclude first from second (VIO)
    (
        "spec_018_second_largest_bug",
        dedent("""\
            def second_largest(arr):
                if len(arr) < 2:
                    return None
                first = second = float('-inf')
                for x in arr:
                    if x > first:
                        second = first
                        first = x
                    elif x > second:
                        second = x
                if second == float('-inf'):
                    return None
                return second
        """),
        dedent("""\
            def spec(arr, result):
                if len(arr) < 2:
                    return result is None
                unique = sorted(set(arr), reverse=True)
                if len(unique) < 2:
                    return result is None
                return result == unique[1]
        """),
        False,
    ),

    # 019 — heap sort correct (SAT)
    (
        "spec_019_heap_sort",
        dedent("""\
            def heap_sort(arr):
                import heapq
                h = list(arr)
                heapq.heapify(h)
                return [heapq.heappop(h) for _ in range(len(h))]
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 020 — is_sorted correct (SAT)
    (
        "spec_020_is_sorted",
        dedent("""\
            def is_sorted(arr):
                for i in range(len(arr) - 1):
                    if arr[i] > arr[i + 1]:
                        return False
                return True
        """),
        dedent("""\
            def spec(arr, result):
                expected = all(arr[i] <= arr[i + 1] for i in range(len(arr) - 1))
                return result == expected
        """),
        True,
    ),

    # =========================================================================
    # STRING MANIPULATION (021-045)
    # =========================================================================

    # 021 — reverse string correct (SAT)
    (
        "spec_021_reverse_string",
        dedent("""\
            def reverse_string(s):
                return s[::-1]
        """),
        dedent("""\
            def spec(s, result):
                return result == s[::-1]
        """),
        True,
    ),

    # 022 — is palindrome correct (SAT)
    (
        "spec_022_is_palindrome",
        dedent("""\
            def is_palindrome(s):
                s = s.lower()
                return s == s[::-1]
        """),
        dedent("""\
            def spec(s, result):
                cleaned = s.lower()
                return result == (cleaned == cleaned[::-1])
        """),
        True,
    ),

    # 023 — is palindrome bug: doesn't lowercase (VIO)
    (
        "spec_023_is_palindrome_bug",
        dedent("""\
            def is_palindrome(s):
                return s == s[::-1]
        """),
        dedent("""\
            def spec(s, result):
                cleaned = s.lower()
                return result == (cleaned == cleaned[::-1])
        """),
        False,
    ),

    # 024 — anagram check correct (SAT)
    (
        "spec_024_is_anagram",
        dedent("""\
            def is_anagram(s1, s2):
                return sorted(s1.lower()) == sorted(s2.lower())
        """),
        dedent("""\
            def spec(s1, s2, result):
                from collections import Counter
                return result == (Counter(s1.lower()) == Counter(s2.lower()))
        """),
        True,
    ),

    # 025 — anagram check bug: case sensitive (VIO)
    (
        "spec_025_is_anagram_bug",
        dedent("""\
            def is_anagram(s1, s2):
                return sorted(s1) == sorted(s2)
        """),
        dedent("""\
            def spec(s1, s2, result):
                from collections import Counter
                return result == (Counter(s1.lower()) == Counter(s2.lower()))
        """),
        False,
    ),

    # 026 — run-length encoding correct (SAT)
    (
        "spec_026_rle_encode",
        dedent("""\
            def rle_encode(s):
                if not s:
                    return ""
                result = []
                count = 1
                for i in range(1, len(s)):
                    if s[i] == s[i - 1]:
                        count += 1
                    else:
                        result.append(s[i - 1] + str(count))
                        count = 1
                result.append(s[-1] + str(count))
                return "".join(result)
        """),
        dedent("""\
            def spec(s, result):
                if not s:
                    return result == ""
                decoded = []
                i = 0
                while i < len(result):
                    ch = result[i]
                    i += 1
                    num = ""
                    while i < len(result) and result[i].isdigit():
                        num += result[i]
                        i += 1
                    decoded.extend([ch] * int(num))
                return "".join(decoded) == s
        """),
        True,
    ),

    # 027 — rle bug: off by one, skips last group (VIO)
    (
        "spec_027_rle_encode_bug",
        dedent("""\
            def rle_encode(s):
                if not s:
                    return ""
                result = []
                count = 1
                for i in range(1, len(s)):
                    if s[i] == s[i - 1]:
                        count += 1
                    else:
                        result.append(s[i - 1] + str(count))
                        count = 1
                return "".join(result)
        """),
        dedent("""\
            def spec(s, result):
                if not s:
                    return result == ""
                decoded = []
                i = 0
                while i < len(result):
                    ch = result[i]
                    i += 1
                    num = ""
                    while i < len(result) and result[i].isdigit():
                        num += result[i]
                        i += 1
                    decoded.extend([ch] * int(num))
                return "".join(decoded) == s
        """),
        False,
    ),

    # 028 — caesar cipher correct (SAT)
    (
        "spec_028_caesar_cipher",
        dedent("""\
            def caesar_cipher(text, shift):
                result = []
                for c in text:
                    if c.isalpha():
                        base = ord('A') if c.isupper() else ord('a')
                        result.append(chr((ord(c) - base + shift) % 26 + base))
                    else:
                        result.append(c)
                return "".join(result)
        """),
        dedent("""\
            def spec(text, shift, result):
                decrypted = []
                for c in result:
                    if c.isalpha():
                        base = ord('A') if c.isupper() else ord('a')
                        decrypted.append(chr((ord(c) - base - shift) % 26 + base))
                    else:
                        decrypted.append(c)
                return "".join(decrypted) == text
        """),
        True,
    ),

    # 029 — caesar cipher bug: doesn't handle uppercase correctly (VIO)
    (
        "spec_029_caesar_cipher_bug",
        dedent("""\
            def caesar_cipher(text, shift):
                result = []
                for c in text:
                    if c.isalpha():
                        base = ord('a')
                        result.append(chr((ord(c) - base + shift) % 26 + base))
                    else:
                        result.append(c)
                return "".join(result)
        """),
        dedent("""\
            def spec(text, shift, result):
                decrypted = []
                for c in result:
                    if c.isalpha():
                        base = ord('A') if c.isupper() else ord('a')
                        decrypted.append(chr((ord(c) - base - shift) % 26 + base))
                    else:
                        decrypted.append(c)
                return "".join(decrypted) == text
        """),
        False,
    ),

    # 030 — count vowels bug: misses 'u' (VIO)
    (
        "spec_030_count_vowels_bug",
        dedent("""\
            def count_vowels(s):
                return sum(1 for c in s.lower() if c in 'aeio')
        """),
        dedent("""\
            def spec(s, result):
                return result == sum(1 for c in s.lower() if c in 'aeiou')
        """),
        False,
    ),

    # 031 — longest common prefix correct (SAT)
    (
        "spec_031_longest_common_prefix",
        dedent("""\
            def longest_common_prefix(strs):
                if not strs:
                    return ""
                prefix = strs[0]
                for s in strs[1:]:
                    while not s.startswith(prefix):
                        prefix = prefix[:-1]
                        if not prefix:
                            return ""
                return prefix
        """),
        dedent("""\
            def spec(strs, result):
                if not strs:
                    return result == ""
                for s in strs:
                    if not s.startswith(result):
                        return False
                if result == "":
                    return True
                for s in strs:
                    if len(s) <= len(result) or s[len(result)] == (strs[0][len(result)] if len(strs[0]) > len(result) else ''):
                        pass
                return all(s.startswith(result) for s in strs) and (
                    len(result) == 0 or
                    not all(s[len(result)] == strs[0][len(result)] for s in strs if len(s) > len(result)) or
                    any(len(s) == len(result) for s in strs)
                )
        """),
        True,
    ),

    # 032 — title case correct (SAT)
    (
        "spec_032_title_case",
        dedent("""\
            def title_case(s):
                return ' '.join(w.capitalize() for w in s.split(' '))
        """),
        dedent("""\
            def spec(s, result):
                words = s.split(' ')
                expected = ' '.join(w.capitalize() for w in words)
                return result == expected
        """),
        True,
    ),

    # 033 — count words bug: doesn't handle multiple spaces (VIO)
    (
        "spec_033_count_words_bug",
        dedent("""\
            def count_words(s):
                return len(s.split(' '))
        """),
        dedent("""\
            def spec(s, result):
                return result == len(s.split())
        """),
        False,
    ),

    # 034 — string compression correct (SAT)
    (
        "spec_034_string_compress",
        dedent("""\
            def compress(s):
                if not s:
                    return ""
                result = []
                i = 0
                while i < len(s):
                    j = i
                    while j < len(s) and s[j] == s[i]:
                        j += 1
                    result.append(s[i])
                    if j - i > 1:
                        result.append(str(j - i))
                    i = j
                compressed = "".join(result)
                return compressed if len(compressed) < len(s) else s
        """),
        dedent("""\
            def spec(s, result):
                if not s:
                    return result == ""
                return len(result) <= len(s)
        """),
        True,
    ),

    # 035 — remove duplicates from string preserving order (SAT)
    (
        "spec_035_remove_dup_chars",
        dedent("""\
            def remove_dup_chars(s):
                seen = set()
                result = []
                for c in s:
                    if c not in seen:
                        seen.add(c)
                        result.append(c)
                return "".join(result)
        """),
        dedent("""\
            def spec(s, result):
                return (
                    len(result) == len(set(s)) and
                    all(c in s for c in result) and
                    len(set(result)) == len(result)
                )
        """),
        True,
    ),

    # 036 — remove dup chars bug: uses list instead of set, O(n^2) but also drops order (VIO)
    (
        "spec_036_remove_dup_chars_bug",
        dedent("""\
            def remove_dup_chars(s):
                return "".join(sorted(set(s)))
        """),
        dedent("""\
            def spec(s, result):
                seen = set()
                expected = []
                for c in s:
                    if c not in seen:
                        seen.add(c)
                        expected.append(c)
                return result == "".join(expected)
        """),
        False,
    ),

    # 037 — is_subsequence correct (SAT)
    (
        "spec_037_is_subsequence",
        dedent("""\
            def is_subsequence(s, t):
                it = iter(t)
                return all(c in it for c in s)
        """),
        dedent("""\
            def spec(s, t, result):
                i = 0
                for c in t:
                    if i < len(s) and c == s[i]:
                        i += 1
                return result == (i == len(s))
        """),
        True,
    ),

    # 038 — first non-repeating char correct (SAT)
    (
        "spec_038_first_non_repeat",
        dedent("""\
            def first_non_repeating(s):
                from collections import Counter
                freq = Counter(s)
                for c in s:
                    if freq[c] == 1:
                        return c
                return None
        """),
        dedent("""\
            def spec(s, result):
                from collections import Counter
                freq = Counter(s)
                for c in s:
                    if freq[c] == 1:
                        return result == c
                return result is None
        """),
        True,
    ),

    # 039 — first non-repeating bug: returns last non-repeating instead (VIO)
    (
        "spec_039_first_non_repeat_bug",
        dedent("""\
            def first_non_repeating(s):
                from collections import Counter
                freq = Counter(s)
                found = None
                for c in s:
                    if freq[c] == 1:
                        found = c
                return found
        """),
        dedent("""\
            def spec(s, result):
                from collections import Counter
                freq = Counter(s)
                for c in s:
                    if freq[c] == 1:
                        return result == c
                return result is None
        """),
        False,
    ),

    # 040 — atoi implementation correct (SAT)
    (
        "spec_040_my_atoi",
        dedent("""\
            def my_atoi(s):
                s = s.strip()
                if not s:
                    return 0
                sign = 1
                i = 0
                if s[0] in '+-':
                    sign = -1 if s[0] == '-' else 1
                    i = 1
                result = 0
                while i < len(s) and s[i].isdigit():
                    result = result * 10 + int(s[i])
                    i += 1
                return sign * result
        """),
        dedent("""\
            def spec(s, result):
                s = s.strip()
                if not s:
                    return result == 0
                sign = 1
                idx = 0
                if s[0] in '+-':
                    sign = -1 if s[0] == '-' else 1
                    idx = 1
                num = 0
                while idx < len(s) and s[idx].isdigit():
                    num = num * 10 + int(s[idx])
                    idx += 1
                return result == sign * num
        """),
        True,
    ),

    # =========================================================================
    # MATH (041-065)
    # =========================================================================

    # 041 — gcd correct (SAT)
    (
        "spec_041_gcd",
        dedent("""\
            def gcd(a, b):
                a, b = abs(a), abs(b)
                while b:
                    a, b = b, a % b
                return a
        """),
        dedent("""\
            def spec(a, b, result):
                import math
                return result == math.gcd(abs(a), abs(b))
        """),
        True,
    ),

    # 042 — gcd bug: doesn't take abs, fails on negatives (VIO)
    (
        "spec_042_gcd_bug",
        dedent("""\
            def gcd(a, b):
                while b:
                    a, b = b, a % b
                return a
        """),
        dedent("""\
            def spec(a, b, result):
                import math
                return result == math.gcd(abs(a), abs(b))
        """),
        False,
    ),

    # 043 — is_prime correct (SAT)
    (
        "spec_043_is_prime",
        dedent("""\
            def is_prime(n):
                if n < 2:
                    return False
                if n < 4:
                    return True
                if n % 2 == 0 or n % 3 == 0:
                    return False
                i = 5
                while i * i <= n:
                    if n % i == 0 or n % (i + 2) == 0:
                        return False
                    i += 6
                return True
        """),
        dedent("""\
            def spec(n, result):
                if n < 2:
                    return result is False
                for i in range(2, int(n**0.5) + 1):
                    if n % i == 0:
                        return result is False
                return result is True
        """),
        True,
    ),

    # 044 — is_prime bug: returns True for n=1 (VIO)
    (
        "spec_044_is_prime_bug",
        dedent("""\
            def is_prime(n):
                if n < 1:
                    return False
                if n < 4:
                    return True
                if n % 2 == 0 or n % 3 == 0:
                    return False
                i = 5
                while i * i <= n:
                    if n % i == 0 or n % (i + 2) == 0:
                        return False
                    i += 6
                return True
        """),
        dedent("""\
            def spec(n, result):
                if n < 2:
                    return result is False
                for i in range(2, int(n**0.5) + 1):
                    if n % i == 0:
                        return result is False
                return result is True
        """),
        False,
    ),

    # 045 — fibonacci correct (SAT)
    (
        "spec_045_fibonacci",
        dedent("""\
            def fibonacci(n):
                if n <= 0:
                    return 0
                if n == 1:
                    return 1
                a, b = 0, 1
                for _ in range(2, n + 1):
                    a, b = b, a + b
                return b
        """),
        dedent("""\
            def spec(n, result):
                if n <= 0:
                    return result == 0
                a, b = 0, 1
                for _ in range(n):
                    a, b = b, a + b
                return result == a
        """),
        True,
    ),

    # 046 — fibonacci bug: off by one, returns fib(n-1) (VIO)
    (
        "spec_046_fibonacci_bug",
        dedent("""\
            def fibonacci(n):
                if n <= 0:
                    return 0
                if n == 1:
                    return 1
                a, b = 0, 1
                for _ in range(2, n):
                    a, b = b, a + b
                return b
        """),
        dedent("""\
            def spec(n, result):
                if n <= 0:
                    return result == 0
                a, b = 0, 1
                for _ in range(n):
                    a, b = b, a + b
                return result == a
        """),
        False,
    ),

    # 047 — factorial correct (SAT)
    (
        "spec_047_factorial",
        dedent("""\
            def factorial(n):
                if n < 0:
                    return None
                result = 1
                for i in range(2, n + 1):
                    result *= i
                return result
        """),
        dedent("""\
            def spec(n, result):
                if n < 0:
                    return result is None
                import math
                return result == math.factorial(n)
        """),
        True,
    ),

    # 048 — factorial bug: starts from 1, returns n! correctly... wait, let's do power (SAT)
    (
        "spec_048_power",
        dedent("""\
            def power(base, exp):
                if exp < 0:
                    return None
                result = 1
                for _ in range(exp):
                    result *= base
                return result
        """),
        dedent("""\
            def spec(base, exp, result):
                if exp < 0:
                    return result is None
                return result == base ** exp
        """),
        True,
    ),

    # 049 — power bug: doesn't handle exp=0, returns base instead of 1 (VIO)
    (
        "spec_049_power_bug",
        dedent("""\
            def power(base, exp):
                if exp < 0:
                    return None
                result = base
                for _ in range(exp - 1):
                    result *= base
                return result
        """),
        dedent("""\
            def spec(base, exp, result):
                if exp < 0:
                    return result is None
                return result == base ** exp
        """),
        False,
    ),

    # 050 — lcm correct (SAT)
    (
        "spec_050_lcm",
        dedent("""\
            def lcm(a, b):
                if a == 0 or b == 0:
                    return 0
                import math
                return abs(a * b) // math.gcd(a, b)
        """),
        dedent("""\
            def spec(a, b, result):
                if a == 0 or b == 0:
                    return result == 0
                import math
                return result == abs(a * b) // math.gcd(a, b)
        """),
        True,
    ),

    # 051 — sum of digits correct (SAT)
    (
        "spec_051_sum_digits",
        dedent("""\
            def sum_digits(n):
                n = abs(n)
                total = 0
                while n > 0:
                    total += n % 10
                    n //= 10
                return total
        """),
        dedent("""\
            def spec(n, result):
                return result == sum(int(d) for d in str(abs(n)))
        """),
        True,
    ),

    # 052 — sum of digits bug: doesn't abs, negative inputs wrong (VIO)
    (
        "spec_052_sum_digits_bug",
        dedent("""\
            def sum_digits(n):
                total = 0
                while n > 0:
                    total += n % 10
                    n //= 10
                return total
        """),
        dedent("""\
            def spec(n, result):
                return result == sum(int(d) for d in str(abs(n)))
        """),
        False,
    ),

    # 053 — integer to roman correct (SAT)
    (
        "spec_053_int_to_roman",
        dedent("""\
            def int_to_roman(num):
                vals = [1000, 900, 500, 400, 100, 90, 50, 40, 10, 9, 5, 4, 1]
                syms = ['M','CM','D','CD','C','XC','L','XL','X','IX','V','IV','I']
                result = []
                for v, s in zip(vals, syms):
                    while num >= v:
                        result.append(s)
                        num -= v
                return ''.join(result)
        """),
        dedent("""\
            def spec(num, result):
                vals = [1000, 900, 500, 400, 100, 90, 50, 40, 10, 9, 5, 4, 1]
                syms = ['M','CM','D','CD','C','XC','L','XL','X','IX','V','IV','I']
                expected = []
                n = num
                for v, s in zip(vals, syms):
                    while n >= v:
                        expected.append(s)
                        n -= v
                return result == ''.join(expected)
        """),
        True,
    ),

    # 054 — int to roman bug: missing 900 and 400 subtractive forms (VIO)
    (
        "spec_054_int_to_roman_bug",
        dedent("""\
            def int_to_roman(num):
                vals = [1000, 500, 100, 50, 10, 5, 1]
                syms = ['M','D','C','L','X','V','I']
                result = []
                for v, s in zip(vals, syms):
                    while num >= v:
                        result.append(s)
                        num -= v
                return ''.join(result)
        """),
        dedent("""\
            def spec(num, result):
                vals = [1000, 900, 500, 400, 100, 90, 50, 40, 10, 9, 5, 4, 1]
                syms = ['M','CM','D','CD','C','XC','L','XL','X','IX','V','IV','I']
                expected = []
                n = num
                for v, s in zip(vals, syms):
                    while n >= v:
                        expected.append(s)
                        n -= v
                return result == ''.join(expected)
        """),
        False,
    ),

    # 055 — matrix transpose correct (SAT)
    (
        "spec_055_transpose",
        dedent("""\
            def transpose(matrix):
                if not matrix:
                    return []
                rows, cols = len(matrix), len(matrix[0])
                return [[matrix[r][c] for r in range(rows)] for c in range(cols)]
        """),
        dedent("""\
            def spec(matrix, result):
                if not matrix:
                    return result == []
                rows, cols = len(matrix), len(matrix[0])
                if len(result) != cols:
                    return False
                for c in range(cols):
                    if len(result[c]) != rows:
                        return False
                    for r in range(rows):
                        if result[c][r] != matrix[r][c]:
                            return False
                return True
        """),
        True,
    ),

    # 056 — dot product bug: subtracts instead of multiplies (VIO)
    (
        "spec_056_dot_product_bug",
        dedent("""\
            def dot_product(a, b):
                return sum(x + y for x, y in zip(a, b))
        """),
        dedent("""\
            def spec(a, b, result):
                if len(a) != len(b):
                    return True
                return result == sum(x * y for x, y in zip(a, b))
        """),
        False,
    ),

    # 057 — integer square root correct (SAT)
    (
        "spec_057_isqrt",
        dedent("""\
            def isqrt(n):
                if n < 0:
                    return None
                if n == 0:
                    return 0
                x = n
                while True:
                    x1 = (x + n // x) // 2
                    if x1 >= x:
                        return x
                    x = x1
        """),
        dedent("""\
            def spec(n, result):
                if n < 0:
                    return result is None
                import math
                return result == math.isqrt(n)
        """),
        True,
    ),

    # 058 — digit reversal correct (SAT)
    (
        "spec_058_reverse_int",
        dedent("""\
            def reverse_int(n):
                sign = -1 if n < 0 else 1
                n = abs(n)
                rev = 0
                while n > 0:
                    rev = rev * 10 + n % 10
                    n //= 10
                return sign * rev
        """),
        dedent("""\
            def spec(n, result):
                s = str(abs(n))[::-1]
                expected = int(s) * (-1 if n < 0 else 1)
                return result == expected
        """),
        True,
    ),

    # 059 — digit reversal bug: loses sign for negative numbers (VIO)
    (
        "spec_059_reverse_int_bug",
        dedent("""\
            def reverse_int(n):
                n = abs(n)
                rev = 0
                while n > 0:
                    rev = rev * 10 + n % 10
                    n //= 10
                return rev
        """),
        dedent("""\
            def spec(n, result):
                s = str(abs(n))[::-1]
                expected = int(s) * (-1 if n < 0 else 1)
                return result == expected
        """),
        False,
    ),

    # 060 — sieve of eratosthenes correct (SAT)
    (
        "spec_060_sieve",
        dedent("""\
            def sieve(n):
                if n < 2:
                    return []
                is_prime = [True] * (n + 1)
                is_prime[0] = is_prime[1] = False
                for i in range(2, int(n**0.5) + 1):
                    if is_prime[i]:
                        for j in range(i*i, n + 1, i):
                            is_prime[j] = False
                return [i for i in range(n + 1) if is_prime[i]]
        """),
        dedent("""\
            def spec(n, result):
                def check_prime(x):
                    if x < 2:
                        return False
                    for i in range(2, int(x**0.5) + 1):
                        if x % i == 0:
                            return False
                    return True
                expected = [i for i in range(n + 1) if check_prime(i)]
                return result == expected
        """),
        True,
    ),

    # =========================================================================
    # DATA STRUCTURES (061-085)
    # =========================================================================

    # 061 — stack using list correct (SAT)
    (
        "spec_061_stack_ops",
        dedent("""\
            def stack_ops(operations):
                stack = []
                results = []
                for op in operations:
                    if op[0] == 'push':
                        stack.append(op[1])
                        results.append(None)
                    elif op[0] == 'pop':
                        results.append(stack.pop() if stack else None)
                    elif op[0] == 'peek':
                        results.append(stack[-1] if stack else None)
                return results
        """),
        dedent("""\
            def spec(operations, result):
                stack = []
                expected = []
                for op in operations:
                    if op[0] == 'push':
                        stack.append(op[1])
                        expected.append(None)
                    elif op[0] == 'pop':
                        expected.append(stack.pop() if stack else None)
                    elif op[0] == 'peek':
                        expected.append(stack[-1] if stack else None)
                return result == expected
        """),
        True,
    ),

    # 062 — stack bug: peek returns first instead of last (VIO)
    (
        "spec_062_stack_ops_bug",
        dedent("""\
            def stack_ops(operations):
                stack = []
                results = []
                for op in operations:
                    if op[0] == 'push':
                        stack.append(op[1])
                        results.append(None)
                    elif op[0] == 'pop':
                        results.append(stack.pop() if stack else None)
                    elif op[0] == 'peek':
                        results.append(stack[0] if stack else None)
                return results
        """),
        dedent("""\
            def spec(operations, result):
                stack = []
                expected = []
                for op in operations:
                    if op[0] == 'push':
                        stack.append(op[1])
                        expected.append(None)
                    elif op[0] == 'pop':
                        expected.append(stack.pop() if stack else None)
                    elif op[0] == 'peek':
                        expected.append(stack[-1] if stack else None)
                return result == expected
        """),
        False,
    ),

    # 063 — queue using two stacks correct (SAT)
    (
        "spec_063_queue_ops",
        dedent("""\
            def queue_ops(operations):
                inbox, outbox = [], []
                results = []
                for op in operations:
                    if op[0] == 'enqueue':
                        inbox.append(op[1])
                        results.append(None)
                    elif op[0] == 'dequeue':
                        if not outbox:
                            while inbox:
                                outbox.append(inbox.pop())
                        results.append(outbox.pop() if outbox else None)
                return results
        """),
        dedent("""\
            def spec(operations, result):
                from collections import deque
                q = deque()
                expected = []
                for op in operations:
                    if op[0] == 'enqueue':
                        q.append(op[1])
                        expected.append(None)
                    elif op[0] == 'dequeue':
                        expected.append(q.popleft() if q else None)
                return result == expected
        """),
        True,
    ),

    # 064 — BST insert and inorder correct (SAT)
    (
        "spec_064_bst_inorder",
        dedent("""\
            def bst_inorder(values):
                if not values:
                    return []
                tree = {}
                def insert(node, val):
                    if node is None:
                        return {'val': val, 'left': None, 'right': None}
                    if val < node['val']:
                        node['left'] = insert(node['left'], val)
                    elif val > node['val']:
                        node['right'] = insert(node['right'], val)
                    return node
                root = None
                for v in values:
                    root = insert(root, v)
                result = []
                def inorder(node):
                    if node:
                        inorder(node['left'])
                        result.append(node['val'])
                        inorder(node['right'])
                inorder(root)
                return result
        """),
        dedent("""\
            def spec(values, result):
                return result == sorted(set(values))
        """),
        True,
    ),

    # 065 — BST insert bug: uses <= instead of <, duplicates inserted in left (VIO)
    (
        "spec_065_bst_inorder_bug",
        dedent("""\
            def bst_inorder(values):
                if not values:
                    return []
                def insert(node, val):
                    if node is None:
                        return {'val': val, 'left': None, 'right': None}
                    if val <= node['val']:
                        node['left'] = insert(node['left'], val)
                    else:
                        node['right'] = insert(node['right'], val)
                    return node
                root = None
                for v in values:
                    root = insert(root, v)
                result = []
                def inorder(node):
                    if node:
                        inorder(node['left'])
                        result.append(node['val'])
                        inorder(node['right'])
                inorder(root)
                return result
        """),
        dedent("""\
            def spec(values, result):
                return result == sorted(set(values))
        """),
        False,
    ),

    # 066 — max heap push and pop correct (SAT)
    (
        "spec_066_max_heap",
        dedent("""\
            def max_heap_ops(operations):
                import heapq
                heap = []
                results = []
                for op in operations:
                    if op[0] == 'push':
                        heapq.heappush(heap, -op[1])
                        results.append(None)
                    elif op[0] == 'pop':
                        if heap:
                            results.append(-heapq.heappop(heap))
                        else:
                            results.append(None)
                return results
        """),
        dedent("""\
            def spec(operations, result):
                import heapq
                heap = []
                expected = []
                for op in operations:
                    if op[0] == 'push':
                        heapq.heappush(heap, -op[1])
                        expected.append(None)
                    elif op[0] == 'pop':
                        if heap:
                            expected.append(-heapq.heappop(heap))
                        else:
                            expected.append(None)
                return result == expected
        """),
        True,
    ),

    # 067 — linked list from array correct (SAT)
    (
        "spec_067_linked_list_to_array",
        dedent("""\
            def linked_list_to_array(values):
                if not values:
                    return []
                nodes = [{'val': v, 'next': None} for v in values]
                for i in range(len(nodes) - 1):
                    nodes[i]['next'] = nodes[i + 1]
                result = []
                cur = nodes[0]
                while cur:
                    result.append(cur['val'])
                    cur = cur['next']
                return result
        """),
        dedent("""\
            def spec(values, result):
                return result == list(values)
        """),
        True,
    ),

    # 068 — linked list reverse correct (SAT)
    (
        "spec_068_reverse_linked_list",
        dedent("""\
            def reverse_list(values):
                if not values:
                    return []
                nodes = [{'val': v, 'next': None} for v in values]
                for i in range(len(nodes) - 1):
                    nodes[i]['next'] = nodes[i + 1]
                prev = None
                cur = nodes[0]
                while cur:
                    nxt = cur['next']
                    cur['next'] = prev
                    prev = cur
                    cur = nxt
                result = []
                while prev:
                    result.append(prev['val'])
                    prev = prev['next']
                return result
        """),
        dedent("""\
            def spec(values, result):
                return result == list(reversed(values))
        """),
        True,
    ),

    # 069 — linked list reverse bug: loses last element (VIO)
    (
        "spec_069_reverse_linked_list_bug",
        dedent("""\
            def reverse_list(values):
                if not values:
                    return []
                nodes = [{'val': v, 'next': None} for v in values]
                for i in range(len(nodes) - 1):
                    nodes[i]['next'] = nodes[i + 1]
                prev = None
                cur = nodes[0]
                while cur['next']:
                    nxt = cur['next']
                    cur['next'] = prev
                    prev = cur
                    cur = nxt
                result = []
                while prev:
                    result.append(prev['val'])
                    prev = prev['next']
                return result
        """),
        dedent("""\
            def spec(values, result):
                return result == list(reversed(values))
        """),
        False,
    ),

    # 070 — flatten nested list correct (SAT)
    (
        "spec_070_flatten",
        dedent("""\
            def flatten(lst):
                result = []
                for item in lst:
                    if isinstance(item, list):
                        result.extend(flatten(item))
                    else:
                        result.append(item)
                return result
        """),
        dedent("""\
            def spec(lst, result):
                def flat(l):
                    r = []
                    for x in l:
                        if isinstance(x, list):
                            r.extend(flat(x))
                        else:
                            r.append(x)
                    return r
                return result == flat(lst)
        """),
        True,
    ),

    # 071 — flatten bug: only flattens one level (VIO)
    (
        "spec_071_flatten_bug",
        dedent("""\
            def flatten(lst):
                result = []
                for item in lst:
                    if isinstance(item, list):
                        result.extend(item)
                    else:
                        result.append(item)
                return result
        """),
        dedent("""\
            def spec(lst, result):
                def flat(l):
                    r = []
                    for x in l:
                        if isinstance(x, list):
                            r.extend(flat(x))
                        else:
                            r.append(x)
                    return r
                return result == flat(lst)
        """),
        False,
    ),

    # 072 — min stack correct (SAT)
    (
        "spec_072_min_stack",
        dedent("""\
            def min_stack_ops(operations):
                stack = []
                min_stack = []
                results = []
                for op in operations:
                    if op[0] == 'push':
                        stack.append(op[1])
                        if not min_stack or op[1] <= min_stack[-1]:
                            min_stack.append(op[1])
                        results.append(None)
                    elif op[0] == 'pop':
                        if stack:
                            val = stack.pop()
                            if val == min_stack[-1]:
                                min_stack.pop()
                            results.append(val)
                        else:
                            results.append(None)
                    elif op[0] == 'getmin':
                        results.append(min_stack[-1] if min_stack else None)
                return results
        """),
        dedent("""\
            def spec(operations, result):
                stack = []
                expected = []
                for op in operations:
                    if op[0] == 'push':
                        stack.append(op[1])
                        expected.append(None)
                    elif op[0] == 'pop':
                        expected.append(stack.pop() if stack else None)
                    elif op[0] == 'getmin':
                        expected.append(min(stack) if stack else None)
                return result == expected
        """),
        True,
    ),

    # 073 — trie insert and search correct (SAT)
    (
        "spec_073_trie",
        dedent("""\
            def trie_ops(operations):
                trie = {}
                results = []
                for op in operations:
                    if op[0] == 'insert':
                        node = trie
                        for c in op[1]:
                            if c not in node:
                                node[c] = {}
                            node = node[c]
                        node['#'] = True
                        results.append(None)
                    elif op[0] == 'search':
                        node = trie
                        found = True
                        for c in op[1]:
                            if c not in node:
                                found = False
                                break
                            node = node[c]
                        results.append(found and '#' in node)
                return results
        """),
        dedent("""\
            def spec(operations, result):
                words = set()
                expected = []
                for op in operations:
                    if op[0] == 'insert':
                        words.add(op[1])
                        expected.append(None)
                    elif op[0] == 'search':
                        expected.append(op[1] in words)
                return result == expected
        """),
        True,
    ),

    # 074 — trie bug: search doesn't check end marker (VIO)
    (
        "spec_074_trie_bug",
        dedent("""\
            def trie_ops(operations):
                trie = {}
                results = []
                for op in operations:
                    if op[0] == 'insert':
                        node = trie
                        for c in op[1]:
                            if c not in node:
                                node[c] = {}
                            node = node[c]
                        node['#'] = True
                        results.append(None)
                    elif op[0] == 'search':
                        node = trie
                        found = True
                        for c in op[1]:
                            if c not in node:
                                found = False
                                break
                            node = node[c]
                        results.append(found)
                return results
        """),
        dedent("""\
            def spec(operations, result):
                words = set()
                expected = []
                for op in operations:
                    if op[0] == 'insert':
                        words.add(op[1])
                        expected.append(None)
                    elif op[0] == 'search':
                        expected.append(op[1] in words)
                return result == expected
        """),
        False,
    ),

    # 075 — valid parentheses correct (SAT)
    (
        "spec_075_valid_parens",
        dedent("""\
            def valid_parens(s):
                stack = []
                mapping = {')': '(', ']': '[', '}': '{'}
                for c in s:
                    if c in mapping.values():
                        stack.append(c)
                    elif c in mapping:
                        if not stack or stack[-1] != mapping[c]:
                            return False
                        stack.pop()
                return len(stack) == 0
        """),
        dedent("""\
            def spec(s, result):
                count = 0
                pairs = {'(': ')', '[': ']', '{': '}'}
                stack = []
                for c in s:
                    if c in pairs:
                        stack.append(pairs[c])
                    elif c in pairs.values():
                        if not stack or stack.pop() != c:
                            return result is False
                return result == (len(stack) == 0)
        """),
        True,
    ),

    # 076 — valid parens bug: only handles round parens (VIO)
    (
        "spec_076_valid_parens_bug",
        dedent("""\
            def valid_parens(s):
                count = 0
                for c in s:
                    if c == '(':
                        count += 1
                    elif c == ')':
                        count -= 1
                    if count < 0:
                        return False
                return count == 0
        """),
        dedent("""\
            def spec(s, result):
                pairs = {'(': ')', '[': ']', '{': '}'}
                stack = []
                for c in s:
                    if c in pairs:
                        stack.append(pairs[c])
                    elif c in pairs.values():
                        if not stack or stack.pop() != c:
                            return result is False
                return result == (len(stack) == 0)
        """),
        False,
    ),

    # 077 — circular buffer correct (SAT)
    (
        "spec_077_circular_buffer",
        dedent("""\
            def circular_buffer_ops(capacity, operations):
                buf = [None] * capacity
                head = tail = size = 0
                results = []
                for op in operations:
                    if op[0] == 'write':
                        if size < capacity:
                            buf[tail] = op[1]
                            tail = (tail + 1) % capacity
                            size += 1
                            results.append(True)
                        else:
                            results.append(False)
                    elif op[0] == 'read':
                        if size > 0:
                            val = buf[head]
                            head = (head + 1) % capacity
                            size -= 1
                            results.append(val)
                        else:
                            results.append(None)
                return results
        """),
        dedent("""\
            def spec(capacity, operations, result):
                from collections import deque
                q = deque()
                expected = []
                for op in operations:
                    if op[0] == 'write':
                        if len(q) < capacity:
                            q.append(op[1])
                            expected.append(True)
                        else:
                            expected.append(False)
                    elif op[0] == 'read':
                        if q:
                            expected.append(q.popleft())
                        else:
                            expected.append(None)
                return result == expected
        """),
        True,
    ),

    # 078 — LRU cache correct (SAT)
    (
        "spec_078_lru_cache",
        dedent("""\
            def lru_cache_ops(capacity, operations):
                from collections import OrderedDict
                cache = OrderedDict()
                results = []
                for op in operations:
                    if op[0] == 'get':
                        key = op[1]
                        if key in cache:
                            cache.move_to_end(key)
                            results.append(cache[key])
                        else:
                            results.append(-1)
                    elif op[0] == 'put':
                        key, val = op[1], op[2]
                        if key in cache:
                            cache.move_to_end(key)
                        cache[key] = val
                        if len(cache) > capacity:
                            cache.popitem(last=False)
                        results.append(None)
                return results
        """),
        dedent("""\
            def spec(capacity, operations, result):
                from collections import OrderedDict
                cache = OrderedDict()
                expected = []
                for op in operations:
                    if op[0] == 'get':
                        key = op[1]
                        if key in cache:
                            cache.move_to_end(key)
                            expected.append(cache[key])
                        else:
                            expected.append(-1)
                    elif op[0] == 'put':
                        key, val = op[1], op[2]
                        if key in cache:
                            cache.move_to_end(key)
                        cache[key] = val
                        if len(cache) > capacity:
                            cache.popitem(last=False)
                        expected.append(None)
                return result == expected
        """),
        True,
    ),

    # 079 — disjoint set / union-find correct (SAT)
    (
        "spec_079_union_find",
        dedent("""\
            def union_find_ops(n, operations):
                parent = list(range(n))
                rank = [0] * n
                def find(x):
                    while parent[x] != x:
                        parent[x] = parent[parent[x]]
                        x = parent[x]
                    return x
                def union(x, y):
                    rx, ry = find(x), find(y)
                    if rx == ry:
                        return False
                    if rank[rx] < rank[ry]:
                        rx, ry = ry, rx
                    parent[ry] = rx
                    if rank[rx] == rank[ry]:
                        rank[rx] += 1
                    return True
                results = []
                for op in operations:
                    if op[0] == 'union':
                        results.append(union(op[1], op[2]))
                    elif op[0] == 'find':
                        results.append(find(op[1]))
                    elif op[0] == 'connected':
                        results.append(find(op[1]) == find(op[2]))
                return results
        """),
        dedent("""\
            def spec(n, operations, result):
                groups = list(range(n))
                def root(x):
                    while groups[x] != x:
                        x = groups[x]
                    return x
                expected = []
                for op in operations:
                    if op[0] == 'union':
                        rx, ry = root(op[1]), root(op[2])
                        if rx != ry:
                            groups[ry] = rx
                            expected.append(True)
                        else:
                            expected.append(False)
                    elif op[0] == 'find':
                        expected.append(root(op[1]))
                    elif op[0] == 'connected':
                        expected.append(root(op[1]) == root(op[2]))
                return result == expected
        """),
        True,
    ),

    # 080 — hash map with chaining correct (SAT)
    (
        "spec_080_hashmap",
        dedent("""\
            def hashmap_ops(operations):
                size = 16
                buckets = [[] for _ in range(size)]
                results = []
                for op in operations:
                    if op[0] == 'put':
                        key, val = op[1], op[2]
                        idx = hash(key) % size
                        for i, (k, v) in enumerate(buckets[idx]):
                            if k == key:
                                buckets[idx][i] = (key, val)
                                break
                        else:
                            buckets[idx].append((key, val))
                        results.append(None)
                    elif op[0] == 'get':
                        key = op[1]
                        idx = hash(key) % size
                        found = None
                        for k, v in buckets[idx]:
                            if k == key:
                                found = v
                                break
                        results.append(found)
                return results
        """),
        dedent("""\
            def spec(operations, result):
                d = {}
                expected = []
                for op in operations:
                    if op[0] == 'put':
                        d[op[1]] = op[2]
                        expected.append(None)
                    elif op[0] == 'get':
                        expected.append(d.get(op[1]))
                return result == expected
        """),
        True,
    ),

    # =========================================================================
    # GRAPH ALGORITHMS (081-100)
    # =========================================================================

    # 081 — BFS shortest path in unweighted graph correct (SAT)
    (
        "spec_081_bfs_shortest_path",
        dedent("""\
            def bfs_shortest(adj, start, end):
                from collections import deque
                if start == end:
                    return 0
                visited = {start}
                queue = deque([(start, 0)])
                while queue:
                    node, dist = queue.popleft()
                    for neighbor in adj.get(node, []):
                        if neighbor == end:
                            return dist + 1
                        if neighbor not in visited:
                            visited.add(neighbor)
                            queue.append((neighbor, dist + 1))
                return -1
        """),
        dedent("""\
            def spec(adj, start, end, result):
                from collections import deque
                if start == end:
                    return result == 0
                visited = {start}
                queue = deque([(start, 0)])
                while queue:
                    node, dist = queue.popleft()
                    for nb in adj.get(node, []):
                        if nb == end:
                            return result == dist + 1
                        if nb not in visited:
                            visited.add(nb)
                            queue.append((nb, dist + 1))
                return result == -1
        """),
        True,
    ),

    # 082 — DFS path existence correct (SAT)
    (
        "spec_082_dfs_has_path",
        dedent("""\
            def has_path(adj, start, end):
                visited = set()
                def dfs(node):
                    if node == end:
                        return True
                    visited.add(node)
                    for nb in adj.get(node, []):
                        if nb not in visited:
                            if dfs(nb):
                                return True
                    return False
                return dfs(start)
        """),
        dedent("""\
            def spec(adj, start, end, result):
                from collections import deque
                visited = set()
                queue = deque([start])
                while queue:
                    node = queue.popleft()
                    if node == end:
                        return result is True
                    visited.add(node)
                    for nb in adj.get(node, []):
                        if nb not in visited:
                            queue.append(nb)
                return result is False
        """),
        True,
    ),

    # 083 — DFS bug: doesn't mark visited, infinite loop on cycles (VIO)
    (
        "spec_083_dfs_has_path_bug",
        dedent("""\
            def has_path(adj, start, end):
                def dfs(node, depth=0):
                    if depth > 1000:
                        return False
                    if node == end:
                        return True
                    for nb in adj.get(node, []):
                        if dfs(nb, depth + 1):
                            return True
                    return False
                return dfs(start)
        """),
        dedent("""\
            def spec(adj, start, end, result):
                from collections import deque
                visited = set()
                queue = deque([start])
                while queue:
                    node = queue.popleft()
                    if node == end:
                        return result is True
                    visited.add(node)
                    for nb in adj.get(node, []):
                        if nb not in visited:
                            queue.append(nb)
                return result is False
        """),
        False,
    ),

    # 084 — topological sort correct (SAT)
    (
        "spec_084_topo_sort",
        dedent("""\
            def topo_sort(num_nodes, edges):
                from collections import deque
                adj = {i: [] for i in range(num_nodes)}
                indeg = [0] * num_nodes
                for u, v in edges:
                    adj[u].append(v)
                    indeg[v] += 1
                queue = deque(i for i in range(num_nodes) if indeg[i] == 0)
                order = []
                while queue:
                    node = queue.popleft()
                    order.append(node)
                    for nb in adj[node]:
                        indeg[nb] -= 1
                        if indeg[nb] == 0:
                            queue.append(nb)
                return order if len(order) == num_nodes else []
        """),
        dedent("""\
            def spec(num_nodes, edges, result):
                if len(result) != num_nodes:
                    edge_set = set()
                    for u, v in edges:
                        edge_set.add((u, v))
                    adj = {i: [] for i in range(num_nodes)}
                    indeg = [0] * num_nodes
                    for u, v in edges:
                        adj[u].append(v)
                        indeg[v] += 1
                    has_cycle = True
                    from collections import deque
                    q = deque(i for i in range(num_nodes) if indeg[i] == 0)
                    cnt = 0
                    while q:
                        n = q.popleft()
                        cnt += 1
                        for nb in adj[n]:
                            indeg[nb] -= 1
                            if indeg[nb] == 0:
                                q.append(nb)
                    return cnt != num_nodes
                pos = {v: i for i, v in enumerate(result)}
                for u, v in edges:
                    if pos[u] >= pos[v]:
                        return False
                return set(result) == set(range(num_nodes))
        """),
        True,
    ),

    # 085 — topological sort bug: doesn't detect cycles, returns partial (VIO)
    (
        "spec_085_topo_sort_bug",
        dedent("""\
            def topo_sort(num_nodes, edges):
                from collections import deque
                adj = {i: [] for i in range(num_nodes)}
                indeg = [0] * num_nodes
                for u, v in edges:
                    adj[u].append(v)
                    indeg[v] += 1
                queue = deque(i for i in range(num_nodes) if indeg[i] == 0)
                order = []
                while queue:
                    node = queue.popleft()
                    order.append(node)
                    for nb in adj[node]:
                        indeg[nb] -= 1
                        if indeg[nb] == 0:
                            queue.append(nb)
                return order
        """),
        dedent("""\
            def spec(num_nodes, edges, result):
                adj = {i: [] for i in range(num_nodes)}
                indeg = [0] * num_nodes
                for u, v in edges:
                    adj[u].append(v)
                    indeg[v] += 1
                from collections import deque
                q = deque(i for i in range(num_nodes) if indeg[i] == 0)
                cnt = 0
                while q:
                    n = q.popleft()
                    cnt += 1
                    for nb in adj[n]:
                        indeg[nb] -= 1
                        if indeg[nb] == 0:
                            q.append(nb)
                has_cycle = cnt != num_nodes
                if has_cycle:
                    return result == []
                if len(result) != num_nodes:
                    return False
                pos = {v: i for i, v in enumerate(result)}
                for u, v in edges:
                    if pos[u] >= pos[v]:
                        return False
                return True
        """),
        False,
    ),

    # 086 — connected components correct (SAT)
    (
        "spec_086_connected_components",
        dedent("""\
            def count_components(n, edges):
                adj = {i: [] for i in range(n)}
                for u, v in edges:
                    adj[u].append(v)
                    adj[v].append(u)
                visited = set()
                count = 0
                for i in range(n):
                    if i not in visited:
                        count += 1
                        stack = [i]
                        while stack:
                            node = stack.pop()
                            if node not in visited:
                                visited.add(node)
                                for nb in adj[node]:
                                    if nb not in visited:
                                        stack.append(nb)
                return count
        """),
        dedent("""\
            def spec(n, edges, result):
                parent = list(range(n))
                def find(x):
                    while parent[x] != x:
                        parent[x] = parent[parent[x]]
                        x = parent[x]
                    return x
                for u, v in edges:
                    ru, rv = find(u), find(v)
                    if ru != rv:
                        parent[rv] = ru
                return result == len(set(find(i) for i in range(n)))
        """),
        True,
    ),

    # 087 — connected components bug: directed instead of undirected (VIO)
    (
        "spec_087_connected_components_bug",
        dedent("""\
            def count_components(n, edges):
                adj = {i: [] for i in range(n)}
                for u, v in edges:
                    adj[u].append(v)
                visited = set()
                count = 0
                for i in range(n):
                    if i not in visited:
                        count += 1
                        stack = [i]
                        while stack:
                            node = stack.pop()
                            if node not in visited:
                                visited.add(node)
                                for nb in adj[node]:
                                    if nb not in visited:
                                        stack.append(nb)
                return count
        """),
        dedent("""\
            def spec(n, edges, result):
                parent = list(range(n))
                def find(x):
                    while parent[x] != x:
                        parent[x] = parent[parent[x]]
                        x = parent[x]
                    return x
                for u, v in edges:
                    ru, rv = find(u), find(v)
                    if ru != rv:
                        parent[rv] = ru
                return result == len(set(find(i) for i in range(n)))
        """),
        False,
    ),

    # 088 — detect cycle in undirected graph correct (SAT)
    (
        "spec_088_has_cycle",
        dedent("""\
            def has_cycle(n, edges):
                parent = list(range(n))
                def find(x):
                    while parent[x] != x:
                        parent[x] = parent[parent[x]]
                        x = parent[x]
                    return x
                for u, v in edges:
                    ru, rv = find(u), find(v)
                    if ru == rv:
                        return True
                    parent[rv] = ru
                return False
        """),
        dedent("""\
            def spec(n, edges, result):
                parent = list(range(n))
                def find(x):
                    while parent[x] != x:
                        x = parent[x]
                    return x
                for u, v in edges:
                    ru, rv = find(u), find(v)
                    if ru == rv:
                        return result is True
                    parent[rv] = ru
                return result is False
        """),
        True,
    ),

    # 089 — Dijkstra's shortest path correct (SAT)
    (
        "spec_089_dijkstra",
        dedent("""\
            def dijkstra(adj, start):
                import heapq
                dist = {start: 0}
                heap = [(0, start)]
                while heap:
                    d, u = heapq.heappop(heap)
                    if d > dist.get(u, float('inf')):
                        continue
                    for v, w in adj.get(u, []):
                        nd = d + w
                        if nd < dist.get(v, float('inf')):
                            dist[v] = nd
                            heapq.heappush(heap, (nd, v))
                return dist
        """),
        dedent("""\
            def spec(adj, start, result):
                import heapq
                dist = {start: 0}
                heap = [(0, start)]
                while heap:
                    d, u = heapq.heappop(heap)
                    if d > dist.get(u, float('inf')):
                        continue
                    for v, w in adj.get(u, []):
                        nd = d + w
                        if nd < dist.get(v, float('inf')):
                            dist[v] = nd
                            heapq.heappush(heap, (nd, v))
                return result == dist
        """),
        True,
    ),

    # 090 — graph coloring / bipartite check correct (SAT)
    (
        "spec_090_is_bipartite",
        dedent("""\
            def is_bipartite(adj, n):
                color = [-1] * n
                from collections import deque
                for start in range(n):
                    if color[start] != -1:
                        continue
                    color[start] = 0
                    queue = deque([start])
                    while queue:
                        u = queue.popleft()
                        for v in adj.get(u, []):
                            if color[v] == -1:
                                color[v] = 1 - color[u]
                                queue.append(v)
                            elif color[v] == color[u]:
                                return False
                return True
        """),
        dedent("""\
            def spec(adj, n, result):
                color = [-1] * n
                from collections import deque
                for start in range(n):
                    if color[start] != -1:
                        continue
                    color[start] = 0
                    queue = deque([start])
                    while queue:
                        u = queue.popleft()
                        for v in adj.get(u, []):
                            if color[v] == -1:
                                color[v] = 1 - color[u]
                                queue.append(v)
                            elif color[v] == color[u]:
                                return result is False
                return result is True
        """),
        True,
    ),

    # =========================================================================
    # DYNAMIC PROGRAMMING (091-110)
    # =========================================================================

    # 091 — longest common subsequence correct (SAT)
    (
        "spec_091_lcs_length",
        dedent("""\
            def lcs_length(s1, s2):
                m, n = len(s1), len(s2)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if s1[i - 1] == s2[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1] + 1
                        else:
                            dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
                return dp[m][n]
        """),
        dedent("""\
            def spec(s1, s2, result):
                m, n = len(s1), len(s2)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if s1[i - 1] == s2[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1] + 1
                        else:
                            dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
                return result == dp[m][n]
        """),
        True,
    ),

    # 092 — LCS bug: wrong index, uses dp[i-1][j-1] for mismatch too (VIO)
    (
        "spec_092_lcs_length_bug",
        dedent("""\
            def lcs_length(s1, s2):
                m, n = len(s1), len(s2)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if s1[i - 1] == s2[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1] + 1
                        else:
                            dp[i][j] = max(dp[i - 1][j - 1], dp[i][j - 1])
                return dp[m][n]
        """),
        dedent("""\
            def spec(s1, s2, result):
                m, n = len(s1), len(s2)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if s1[i - 1] == s2[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1] + 1
                        else:
                            dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
                return result == dp[m][n]
        """),
        False,
    ),

    # 093 — edit distance correct (SAT)
    (
        "spec_093_edit_distance",
        dedent("""\
            def edit_distance(s1, s2):
                m, n = len(s1), len(s2)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(m + 1):
                    dp[i][0] = i
                for j in range(n + 1):
                    dp[0][j] = j
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if s1[i - 1] == s2[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1]
                        else:
                            dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])
                return dp[m][n]
        """),
        dedent("""\
            def spec(s1, s2, result):
                m, n = len(s1), len(s2)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(m + 1):
                    dp[i][0] = i
                for j in range(n + 1):
                    dp[0][j] = j
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if s1[i - 1] == s2[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1]
                        else:
                            dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])
                return result == dp[m][n]
        """),
        True,
    ),

    # 094 — edit distance bug: forgets substitution cost (VIO)
    (
        "spec_094_edit_distance_bug",
        dedent("""\
            def edit_distance(s1, s2):
                m, n = len(s1), len(s2)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(m + 1):
                    dp[i][0] = i
                for j in range(n + 1):
                    dp[0][j] = j
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if s1[i - 1] == s2[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1]
                        else:
                            dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1])
                return dp[m][n]
        """),
        dedent("""\
            def spec(s1, s2, result):
                m, n = len(s1), len(s2)
                dp = [[0] * (n + 1) for _ in range(m + 1)]
                for i in range(m + 1):
                    dp[i][0] = i
                for j in range(n + 1):
                    dp[0][j] = j
                for i in range(1, m + 1):
                    for j in range(1, n + 1):
                        if s1[i - 1] == s2[j - 1]:
                            dp[i][j] = dp[i - 1][j - 1]
                        else:
                            dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])
                return result == dp[m][n]
        """),
        False,
    ),

    # 095 — 0/1 knapsack correct (SAT)
    (
        "spec_095_knapsack",
        dedent("""\
            def knapsack(weights, values, capacity):
                n = len(weights)
                dp = [[0] * (capacity + 1) for _ in range(n + 1)]
                for i in range(1, n + 1):
                    for w in range(capacity + 1):
                        dp[i][w] = dp[i - 1][w]
                        if weights[i - 1] <= w:
                            dp[i][w] = max(dp[i][w], dp[i - 1][w - weights[i - 1]] + values[i - 1])
                return dp[n][capacity]
        """),
        dedent("""\
            def spec(weights, values, capacity, result):
                n = len(weights)
                dp = [[0] * (capacity + 1) for _ in range(n + 1)]
                for i in range(1, n + 1):
                    for w in range(capacity + 1):
                        dp[i][w] = dp[i - 1][w]
                        if weights[i - 1] <= w:
                            dp[i][w] = max(dp[i][w], dp[i - 1][w - weights[i - 1]] + values[i - 1])
                return result == dp[n][capacity]
        """),
        True,
    ),

    # 096 — knapsack bug: unbounded (uses dp[i] instead of dp[i-1]) (VIO)
    (
        "spec_096_knapsack_bug",
        dedent("""\
            def knapsack(weights, values, capacity):
                n = len(weights)
                dp = [[0] * (capacity + 1) for _ in range(n + 1)]
                for i in range(1, n + 1):
                    for w in range(capacity + 1):
                        dp[i][w] = dp[i - 1][w]
                        if weights[i - 1] <= w:
                            dp[i][w] = max(dp[i][w], dp[i][w - weights[i - 1]] + values[i - 1])
                return dp[n][capacity]
        """),
        dedent("""\
            def spec(weights, values, capacity, result):
                n = len(weights)
                dp = [[0] * (capacity + 1) for _ in range(n + 1)]
                for i in range(1, n + 1):
                    for w in range(capacity + 1):
                        dp[i][w] = dp[i - 1][w]
                        if weights[i - 1] <= w:
                            dp[i][w] = max(dp[i][w], dp[i - 1][w - weights[i - 1]] + values[i - 1])
                return result == dp[n][capacity]
        """),
        False,
    ),

    # 097 — coin change correct (SAT)
    (
        "spec_097_coin_change",
        dedent("""\
            def coin_change(coins, amount):
                dp = [float('inf')] * (amount + 1)
                dp[0] = 0
                for c in coins:
                    for a in range(c, amount + 1):
                        dp[a] = min(dp[a], dp[a - c] + 1)
                return dp[amount] if dp[amount] != float('inf') else -1
        """),
        dedent("""\
            def spec(coins, amount, result):
                dp = [float('inf')] * (amount + 1)
                dp[0] = 0
                for c in coins:
                    for a in range(c, amount + 1):
                        dp[a] = min(dp[a], dp[a - c] + 1)
                expected = dp[amount] if dp[amount] != float('inf') else -1
                return result == expected
        """),
        True,
    ),

    # 098 — coin change bug: iterates amount before coins (still correct for unbounded) (SAT)
    (
        "spec_098_coin_change_alt",
        dedent("""\
            def coin_change(coins, amount):
                dp = [float('inf')] * (amount + 1)
                dp[0] = 0
                for a in range(1, amount + 1):
                    for c in coins:
                        if c <= a and dp[a - c] + 1 < dp[a]:
                            dp[a] = dp[a - c] + 1
                return dp[amount] if dp[amount] != float('inf') else -1
        """),
        dedent("""\
            def spec(coins, amount, result):
                dp = [float('inf')] * (amount + 1)
                dp[0] = 0
                for c in coins:
                    for a in range(c, amount + 1):
                        dp[a] = min(dp[a], dp[a - c] + 1)
                expected = dp[amount] if dp[amount] != float('inf') else -1
                return result == expected
        """),
        True,
    ),

    # 099 — climbing stairs correct (SAT)
    (
        "spec_099_climb_stairs",
        dedent("""\
            def climb_stairs(n):
                if n <= 1:
                    return 1
                a, b = 1, 1
                for _ in range(2, n + 1):
                    a, b = b, a + b
                return b
        """),
        dedent("""\
            def spec(n, result):
                if n <= 1:
                    return result == 1
                dp = [0] * (n + 1)
                dp[0] = dp[1] = 1
                for i in range(2, n + 1):
                    dp[i] = dp[i-1] + dp[i-2]
                return result == dp[n]
        """),
        True,
    ),

    # 100 — climbing stairs bug: off by one, returns ways(n-1) (VIO)
    (
        "spec_100_climb_stairs_bug",
        dedent("""\
            def climb_stairs(n):
                if n <= 1:
                    return 1
                a, b = 1, 1
                for _ in range(2, n):
                    a, b = b, a + b
                return b
        """),
        dedent("""\
            def spec(n, result):
                if n <= 1:
                    return result == 1
                dp = [0] * (n + 1)
                dp[0] = dp[1] = 1
                for i in range(2, n + 1):
                    dp[i] = dp[i-1] + dp[i-2]
                return result == dp[n]
        """),
        False,
    ),

    # =========================================================================
    # ARRAY / LIST PROCESSING (101-125)
    # =========================================================================

    # 101 — rotate array right correct (SAT)
    (
        "spec_101_rotate_right",
        dedent("""\
            def rotate_right(arr, k):
                if not arr:
                    return []
                k = k % len(arr)
                return arr[-k:] + arr[:-k] if k else list(arr)
        """),
        dedent("""\
            def spec(arr, k, result):
                if not arr:
                    return result == []
                n = len(arr)
                k2 = k % n
                expected = arr[-k2:] + arr[:-k2] if k2 else list(arr)
                return result == expected
        """),
        True,
    ),

    # 102 — rotate array bug: rotates left instead of right (VIO)
    (
        "spec_102_rotate_right_bug",
        dedent("""\
            def rotate_right(arr, k):
                if not arr:
                    return []
                k = k % len(arr)
                return arr[k:] + arr[:k] if k else list(arr)
        """),
        dedent("""\
            def spec(arr, k, result):
                if not arr:
                    return result == []
                n = len(arr)
                k2 = k % n
                expected = arr[-k2:] + arr[:-k2] if k2 else list(arr)
                return result == expected
        """),
        False,
    ),

    # 103 — partition array around pivot correct (SAT)
    (
        "spec_103_partition",
        dedent("""\
            def partition(arr, pivot):
                less = [x for x in arr if x < pivot]
                equal = [x for x in arr if x == pivot]
                greater = [x for x in arr if x > pivot]
                return less + equal + greater
        """),
        dedent("""\
            def spec(arr, pivot, result):
                from collections import Counter
                if Counter(result) != Counter(arr):
                    return False
                seen_equal = False
                seen_greater = False
                for x in result:
                    if x == pivot:
                        if seen_greater:
                            return False
                        seen_equal = True
                    elif x > pivot:
                        seen_greater = True
                    else:
                        if seen_equal or seen_greater:
                            return False
                return True
        """),
        True,
    ),

    # 104 — merge two sorted arrays correct (SAT)
    (
        "spec_104_merge_sorted",
        dedent("""\
            def merge_sorted(a, b):
                result = []
                i = j = 0
                while i < len(a) and j < len(b):
                    if a[i] <= b[j]:
                        result.append(a[i])
                        i += 1
                    else:
                        result.append(b[j])
                        j += 1
                result.extend(a[i:])
                result.extend(b[j:])
                return result
        """),
        dedent("""\
            def spec(a, b, result):
                return result == sorted(a + b)
        """),
        True,
    ),

    # 105 — merge sorted bug: doesn't append remaining (VIO)
    (
        "spec_105_merge_sorted_bug",
        dedent("""\
            def merge_sorted(a, b):
                result = []
                i = j = 0
                while i < len(a) and j < len(b):
                    if a[i] <= b[j]:
                        result.append(a[i])
                        i += 1
                    else:
                        result.append(b[j])
                        j += 1
                return result
        """),
        dedent("""\
            def spec(a, b, result):
                return result == sorted(a + b)
        """),
        False,
    ),

    # 106 — remove element in place correct (SAT)
    (
        "spec_106_remove_element",
        dedent("""\
            def remove_element(arr, val):
                return [x for x in arr if x != val]
        """),
        dedent("""\
            def spec(arr, val, result):
                expected = [x for x in arr if x != val]
                return result == expected
        """),
        True,
    ),

    # 107 — move zeroes to end correct (SAT)
    (
        "spec_107_move_zeroes",
        dedent("""\
            def move_zeroes(arr):
                result = [x for x in arr if x != 0]
                result.extend([0] * (len(arr) - len(result)))
                return result
        """),
        dedent("""\
            def spec(arr, result):
                non_zero = [x for x in arr if x != 0]
                expected = non_zero + [0] * (len(arr) - len(non_zero))
                return result == expected
        """),
        True,
    ),

    # 108 — move zeroes bug: moves all falsy values, not just 0 (VIO)
    (
        "spec_108_move_zeroes_bug",
        dedent("""\
            def move_zeroes(arr):
                result = [x for x in arr if x]
                result.extend([0] * (len(arr) - len(result)))
                return result
        """),
        dedent("""\
            def spec(arr, result):
                non_zero = [x for x in arr if x != 0]
                expected = non_zero + [0] * (len(arr) - len(non_zero))
                return result == expected
        """),
        False,
    ),

    # 109 — two sum correct (SAT)
    (
        "spec_109_two_sum",
        dedent("""\
            def two_sum(nums, target):
                seen = {}
                for i, n in enumerate(nums):
                    comp = target - n
                    if comp in seen:
                        return [seen[comp], i]
                    seen[n] = i
                return []
        """),
        dedent("""\
            def spec(nums, target, result):
                if result == []:
                    for i in range(len(nums)):
                        for j in range(i+1, len(nums)):
                            if nums[i] + nums[j] == target:
                                return False
                    return True
                if len(result) != 2:
                    return False
                i, j = result
                return i != j and nums[i] + nums[j] == target
        """),
        True,
    ),

    # 110 — two sum bug: allows same index twice (VIO)
    (
        "spec_110_two_sum_bug",
        dedent("""\
            def two_sum(nums, target):
                for i in range(len(nums)):
                    for j in range(len(nums)):
                        if nums[i] + nums[j] == target:
                            return [i, j]
                return []
        """),
        dedent("""\
            def spec(nums, target, result):
                if result == []:
                    for i in range(len(nums)):
                        for j in range(i+1, len(nums)):
                            if nums[i] + nums[j] == target:
                                return False
                    return True
                if len(result) != 2:
                    return False
                i, j = result
                return i != j and nums[i] + nums[j] == target
        """),
        False,
    ),

    # 111 — max subarray sum (Kadane's) correct (SAT)
    (
        "spec_111_max_subarray",
        dedent("""\
            def max_subarray(arr):
                if not arr:
                    return 0
                max_sum = cur_sum = arr[0]
                for x in arr[1:]:
                    cur_sum = max(x, cur_sum + x)
                    max_sum = max(max_sum, cur_sum)
                return max_sum
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result == 0
                best = float('-inf')
                for i in range(len(arr)):
                    s = 0
                    for j in range(i, len(arr)):
                        s += arr[j]
                        best = max(best, s)
                return result == best
        """),
        True,
    ),

    # 112 — max subarray bug: resets to 0 instead of x (VIO)
    (
        "spec_112_max_subarray_bug",
        dedent("""\
            def max_subarray(arr):
                if not arr:
                    return 0
                max_sum = cur_sum = 0
                for x in arr:
                    cur_sum = max(0, cur_sum + x)
                    max_sum = max(max_sum, cur_sum)
                return max_sum
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result == 0
                best = float('-inf')
                for i in range(len(arr)):
                    s = 0
                    for j in range(i, len(arr)):
                        s += arr[j]
                        best = max(best, s)
                return result == best
        """),
        False,
    ),

    # 113 — product of array except self correct (SAT)
    (
        "spec_113_product_except_self",
        dedent("""\
            def product_except_self(nums):
                n = len(nums)
                result = [1] * n
                prefix = 1
                for i in range(n):
                    result[i] = prefix
                    prefix *= nums[i]
                suffix = 1
                for i in range(n - 1, -1, -1):
                    result[i] *= suffix
                    suffix *= nums[i]
                return result
        """),
        dedent("""\
            def spec(nums, result):
                n = len(nums)
                if n == 0:
                    return result == []
                for i in range(n):
                    product = 1
                    for j in range(n):
                        if j != i:
                            product *= nums[j]
                    if result[i] != product:
                        return False
                return True
        """),
        True,
    ),

    # 114 — dutch national flag / sort 0,1,2 correct (SAT)
    (
        "spec_114_sort_colors",
        dedent("""\
            def sort_colors(arr):
                a = list(arr)
                lo, mid, hi = 0, 0, len(a) - 1
                while mid <= hi:
                    if a[mid] == 0:
                        a[lo], a[mid] = a[mid], a[lo]
                        lo += 1
                        mid += 1
                    elif a[mid] == 1:
                        mid += 1
                    else:
                        a[mid], a[hi] = a[hi], a[mid]
                        hi -= 1
                return a
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        True,
    ),

    # 115 — majority element correct (SAT)
    (
        "spec_115_majority_element",
        dedent("""\
            def majority_element(arr):
                candidate = None
                count = 0
                for x in arr:
                    if count == 0:
                        candidate = x
                        count = 1
                    elif x == candidate:
                        count += 1
                    else:
                        count -= 1
                return candidate
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return True
                from collections import Counter
                c = Counter(arr)
                majority = c.most_common(1)[0]
                if majority[1] > len(arr) // 2:
                    return result == majority[0]
                return True
        """),
        True,
    ),

    # 116 — contains duplicate bug: wrong comparison (VIO)
    (
        "spec_116_contains_dup_bug",
        dedent("""\
            def contains_dup(arr):
                return len(arr) == len(set(arr))
        """),
        dedent("""\
            def spec(arr, result):
                return result == (len(arr) != len(set(arr)))
        """),
        False,
    ),

    # 117 — spiral matrix correct (SAT)
    (
        "spec_117_spiral_order",
        dedent("""\
            def spiral_order(matrix):
                if not matrix:
                    return []
                result = []
                top, bottom, left, right = 0, len(matrix)-1, 0, len(matrix[0])-1
                while top <= bottom and left <= right:
                    for j in range(left, right+1):
                        result.append(matrix[top][j])
                    top += 1
                    for i in range(top, bottom+1):
                        result.append(matrix[i][right])
                    right -= 1
                    if top <= bottom:
                        for j in range(right, left-1, -1):
                            result.append(matrix[bottom][j])
                        bottom -= 1
                    if left <= right:
                        for i in range(bottom, top-1, -1):
                            result.append(matrix[i][left])
                        left += 1
                return result
        """),
        dedent("""\
            def spec(matrix, result):
                if not matrix:
                    return result == []
                flat = []
                for row in matrix:
                    flat.extend(row)
                return sorted(result) == sorted(flat) and len(result) == len(flat)
        """),
        True,
    ),

    # 118 — spiral matrix bug: missing boundary check causes duplicates (VIO)
    (
        "spec_118_spiral_order_bug",
        dedent("""\
            def spiral_order(matrix):
                if not matrix:
                    return []
                result = []
                top, bottom, left, right = 0, len(matrix)-1, 0, len(matrix[0])-1
                while top <= bottom and left <= right:
                    for j in range(left, right+1):
                        result.append(matrix[top][j])
                    top += 1
                    for i in range(top, bottom+1):
                        result.append(matrix[i][right])
                    right -= 1
                    for j in range(right, left-1, -1):
                        result.append(matrix[bottom][j])
                    bottom -= 1
                    for i in range(bottom, top-1, -1):
                        result.append(matrix[i][left])
                    left += 1
                return result
        """),
        dedent("""\
            def spec(matrix, result):
                if not matrix:
                    return result == []
                flat = []
                for row in matrix:
                    flat.extend(row)
                return len(result) == len(flat)
        """),
        False,
    ),

    # =========================================================================
    # SET / DICT OPERATIONS (119-135)
    # =========================================================================

    # 119 — set intersection correct (SAT)
    (
        "spec_119_set_intersection",
        dedent("""\
            def set_intersection(a, b):
                return sorted(set(a) & set(b))
        """),
        dedent("""\
            def spec(a, b, result):
                return result == sorted(set(a) & set(b))
        """),
        True,
    ),

    # 120 — set difference bug: reversed operands (VIO)
    (
        "spec_120_set_difference_bug",
        dedent("""\
            def set_difference(a, b):
                return sorted(set(b) - set(a))
        """),
        dedent("""\
            def spec(a, b, result):
                return result == sorted(set(a) - set(b))
        """),
        False,
    ),

    # 121 — frequency count bug: counts from 1 instead of incrementing (VIO)
    (
        "spec_121_freq_count_bug",
        dedent("""\
            def freq_count(arr):
                freq = {}
                for x in arr:
                    if x in freq:
                        freq[x] = freq[x] + 1
                    else:
                        freq[x] = 0
                return freq
        """),
        dedent("""\
            def spec(arr, result):
                from collections import Counter
                return result == dict(Counter(arr))
        """),
        False,
    ),

    # 122 — top k frequent elements correct (SAT)
    (
        "spec_122_top_k_frequent",
        dedent("""\
            def top_k_frequent(arr, k):
                from collections import Counter
                freq = Counter(arr)
                return [x for x, _ in freq.most_common(k)]
        """),
        dedent("""\
            def spec(arr, k, result):
                from collections import Counter
                freq = Counter(arr)
                top = freq.most_common(k)
                return result == [x for x, _ in top]
        """),
        True,
    ),

    # 123 — top k frequent bug: returns least frequent instead (VIO)
    (
        "spec_123_top_k_frequent_bug",
        dedent("""\
            def top_k_frequent(arr, k):
                from collections import Counter
                freq = Counter(arr)
                return [x for x, _ in freq.most_common()[:-k-1:-1]]
        """),
        dedent("""\
            def spec(arr, k, result):
                from collections import Counter
                freq = Counter(arr)
                top = freq.most_common(k)
                return result == [x for x, _ in top]
        """),
        False,
    ),

    # 124 — group anagrams correct (SAT)
    (
        "spec_124_group_anagrams",
        dedent("""\
            def group_anagrams(words):
                groups = {}
                for w in words:
                    key = ''.join(sorted(w))
                    groups.setdefault(key, []).append(w)
                return sorted([sorted(g) for g in groups.values()])
        """),
        dedent("""\
            def spec(words, result):
                flat = []
                for g in result:
                    flat.extend(g)
                if sorted(flat) != sorted(words):
                    return False
                for g in result:
                    key = ''.join(sorted(g[0]))
                    if not all(''.join(sorted(w)) == key for w in g):
                        return False
                return True
        """),
        True,
    ),

    # 125 — invert dict correct (SAT)
    (
        "spec_125_invert_dict",
        dedent("""\
            def invert_dict(d):
                result = {}
                for k, v in d.items():
                    result.setdefault(v, []).append(k)
                return {k: sorted(v) for k, v in result.items()}
        """),
        dedent("""\
            def spec(d, result):
                for k, v in d.items():
                    if v not in result or k not in result[v]:
                        return False
                total = sum(len(v) for v in result.values())
                return total == len(d)
        """),
        True,
    ),

    # =========================================================================
    # BIT MANIPULATION (126-140)
    # =========================================================================

    # 126 — count set bits correct (SAT)
    (
        "spec_126_count_bits",
        dedent("""\
            def count_bits(n):
                count = 0
                n = abs(n)
                while n:
                    count += n & 1
                    n >>= 1
                return count
        """),
        dedent("""\
            def spec(n, result):
                return result == bin(abs(n)).count('1')
        """),
        True,
    ),

    # 127 — count set bits bug: doesn't abs (VIO)
    (
        "spec_127_count_bits_bug",
        dedent("""\
            def count_bits(n):
                count = 0
                while n:
                    count += n & 1
                    n >>= 1
                return count
        """),
        dedent("""\
            def spec(n, result):
                return result == bin(abs(n)).count('1')
        """),
        False,
    ),

    # 128 — is power of two correct (SAT)
    (
        "spec_128_is_power_of_two",
        dedent("""\
            def is_power_of_two(n):
                return n > 0 and (n & (n - 1)) == 0
        """),
        dedent("""\
            def spec(n, result):
                if n <= 0:
                    return result is False
                return result == (n & (n - 1) == 0)
        """),
        True,
    ),

    # 129 — is power of two bug: accepts 0 (VIO)
    (
        "spec_129_is_power_of_two_bug",
        dedent("""\
            def is_power_of_two(n):
                return n >= 0 and (n & (n - 1)) == 0
        """),
        dedent("""\
            def spec(n, result):
                if n <= 0:
                    return result is False
                return result == (n & (n - 1) == 0)
        """),
        False,
    ),

    # 130 — single number (XOR) correct (SAT)
    (
        "spec_130_single_number",
        dedent("""\
            def single_number(nums):
                result = 0
                for n in nums:
                    result ^= n
                return result
        """),
        dedent("""\
            def spec(nums, result):
                from collections import Counter
                c = Counter(nums)
                singles = [k for k, v in c.items() if v % 2 == 1]
                if len(singles) == 1:
                    return result == singles[0]
                return True
        """),
        True,
    ),

    # 131 — reverse bits correct (SAT)
    (
        "spec_131_reverse_bits",
        dedent("""\
            def reverse_bits(n, num_bits=8):
                result = 0
                for _ in range(num_bits):
                    result = (result << 1) | (n & 1)
                    n >>= 1
                return result
        """),
        dedent("""\
            def spec(n, num_bits, result):
                bits = bin(n)[2:].zfill(num_bits)[-num_bits:]
                expected = int(bits[::-1], 2)
                return result == expected
        """),
        True,
    ),

    # 132 — reverse bits bug: wrong shift direction (VIO)
    (
        "spec_132_reverse_bits_bug",
        dedent("""\
            def reverse_bits(n, num_bits=8):
                result = 0
                for _ in range(num_bits):
                    result = (result << 1) | (n & 1)
                    n <<= 1
                return result
        """),
        dedent("""\
            def spec(n, num_bits, result):
                bits = bin(n)[2:].zfill(num_bits)[-num_bits:]
                expected = int(bits[::-1], 2)
                return result == expected
        """),
        False,
    ),

    # 133 — hamming distance correct (SAT)
    (
        "spec_133_hamming_distance",
        dedent("""\
            def hamming_distance(x, y):
                xor = x ^ y
                count = 0
                while xor:
                    count += xor & 1
                    xor >>= 1
                return count
        """),
        dedent("""\
            def spec(x, y, result):
                return result == bin(x ^ y).count('1')
        """),
        True,
    ),

    # 134 — swap two numbers using XOR correct (SAT)
    (
        "spec_134_xor_swap",
        dedent("""\
            def xor_swap(a, b):
                if a == b:
                    return a, b
                a = a ^ b
                b = a ^ b
                a = a ^ b
                return a, b
        """),
        dedent("""\
            def spec(a, b, result):
                return result == (b, a)
        """),
        True,
    ),

    # 135 — get/set/clear bit correct (SAT)
    (
        "spec_135_bit_ops",
        dedent("""\
            def bit_ops(n, operations):
                results = []
                for op in operations:
                    if op[0] == 'get':
                        results.append((n >> op[1]) & 1)
                    elif op[0] == 'set':
                        n |= (1 << op[1])
                        results.append(n)
                    elif op[0] == 'clear':
                        n &= ~(1 << op[1])
                        results.append(n)
                return results
        """),
        dedent("""\
            def spec(n, operations, result):
                expected = []
                val = n
                for op in operations:
                    if op[0] == 'get':
                        expected.append((val >> op[1]) & 1)
                    elif op[0] == 'set':
                        val |= (1 << op[1])
                        expected.append(val)
                    elif op[0] == 'clear':
                        val &= ~(1 << op[1])
                        expected.append(val)
                return result == expected
        """),
        True,
    ),

    # 136 — bit ops bug: clear uses OR instead of AND-NOT (VIO)
    (
        "spec_136_bit_ops_bug",
        dedent("""\
            def bit_ops(n, operations):
                results = []
                for op in operations:
                    if op[0] == 'get':
                        results.append((n >> op[1]) & 1)
                    elif op[0] == 'set':
                        n |= (1 << op[1])
                        results.append(n)
                    elif op[0] == 'clear':
                        n |= (1 << op[1])
                        results.append(n)
                return results
        """),
        dedent("""\
            def spec(n, operations, result):
                expected = []
                val = n
                for op in operations:
                    if op[0] == 'get':
                        expected.append((val >> op[1]) & 1)
                    elif op[0] == 'set':
                        val |= (1 << op[1])
                        expected.append(val)
                    elif op[0] == 'clear':
                        val &= ~(1 << op[1])
                        expected.append(val)
                return result == expected
        """),
        False,
    ),

    # 137 — trailing zeros bug: returns wrong value for n=0 (VIO)
    (
        "spec_137_trailing_zeros_bug",
        dedent("""\
            def trailing_zeros(n):
                if n == 0:
                    return 32
                count = 0
                while (n & 1) == 0:
                    count += 1
                    n >>= 1
                return count
        """),
        dedent("""\
            def spec(n, result):
                if n == 0:
                    return result == 0
                s = bin(n)
                return result == len(s) - len(s.rstrip('0'))
        """),
        False,
    ),

    # 138 — next power of two correct (SAT)
    (
        "spec_138_next_power_of_two",
        dedent("""\
            def next_power_of_two(n):
                if n <= 0:
                    return 1
                if n & (n - 1) == 0:
                    return n
                p = 1
                while p < n:
                    p <<= 1
                return p
        """),
        dedent("""\
            def spec(n, result):
                if n <= 0:
                    return result == 1
                if n & (n - 1) == 0:
                    return result == n
                return result > 0 and result & (result - 1) == 0 and result >= n and result // 2 < n
        """),
        True,
    ),

    # 139 — parity bug: doesn't take abs (VIO)
    (
        "spec_139_parity_bug",
        dedent("""\
            def parity(n):
                p = 0
                while n:
                    p ^= n & 1
                    n >>= 1
                return p
        """),
        dedent("""\
            def spec(n, result):
                return result == bin(abs(n)).count('1') % 2
        """),
        False,
    ),

    # 140 — missing number using XOR correct (SAT)
    (
        "spec_140_missing_number",
        dedent("""\
            def missing_number(nums):
                n = len(nums)
                xor_all = 0
                for i in range(n + 1):
                    xor_all ^= i
                for x in nums:
                    xor_all ^= x
                return xor_all
        """),
        dedent("""\
            def spec(nums, result):
                n = len(nums)
                expected = set(range(n + 1)) - set(nums)
                if len(expected) != 1:
                    return True
                return result == expected.pop()
        """),
        True,
    ),

    # =========================================================================
    # COMBINATORICS (141-160)
    # =========================================================================

    # 141 — permutations correct (SAT)
    (
        "spec_141_permutations",
        dedent("""\
            def permutations(arr):
                if len(arr) <= 1:
                    return [list(arr)]
                result = []
                for i, x in enumerate(arr):
                    rest = arr[:i] + arr[i+1:]
                    for p in permutations(rest):
                        result.append([x] + p)
                return result
        """),
        dedent("""\
            def spec(arr, result):
                from itertools import permutations as iperms
                expected = [list(p) for p in iperms(arr)]
                return sorted(result) == sorted(expected)
        """),
        True,
    ),

    # 142 — permutations bug: doesn't skip duplicates, produces extras (VIO)
    (
        "spec_142_permutations_bug",
        dedent("""\
            def permutations(arr):
                if len(arr) <= 1:
                    return [list(arr)]
                result = []
                for i, x in enumerate(arr):
                    rest = arr[:i] + arr[i+1:]
                    for p in permutations(rest):
                        result.append([x] + p)
                return result
        """),
        dedent("""\
            def spec(arr, result):
                from itertools import permutations as iperms
                expected = sorted([list(p) for p in set(iperms(arr))])
                return sorted(result) == expected
        """),
        False,
    ),

    # 143 — combinations correct (SAT)
    (
        "spec_143_combinations",
        dedent("""\
            def combinations(arr, k):
                if k == 0:
                    return [[]]
                if not arr or k > len(arr):
                    return []
                first = arr[0]
                with_first = [[first] + c for c in combinations(arr[1:], k - 1)]
                without = combinations(arr[1:], k)
                return with_first + without
        """),
        dedent("""\
            def spec(arr, k, result):
                from itertools import combinations as icomb
                expected = [list(c) for c in icomb(arr, k)]
                return sorted(result) == sorted(expected)
        """),
        True,
    ),

    # 144 — combinations bug: includes duplicates when k=0 returns [[]] twice (VIO)
    (
        "spec_144_combinations_bug",
        dedent("""\
            def combinations(arr, k):
                if k == 0:
                    return [[]]
                if k > len(arr):
                    return []
                if not arr:
                    return [[]]
                first = arr[0]
                with_first = [[first] + c for c in combinations(arr[1:], k - 1)]
                without = combinations(arr[1:], k)
                return with_first + without
        """),
        dedent("""\
            def spec(arr, k, result):
                from itertools import combinations as icomb
                expected = [list(c) for c in icomb(arr, k)]
                return sorted(result) == sorted(expected)
        """),
        False,
    ),

    # 145 — power set correct (SAT)
    (
        "spec_145_power_set",
        dedent("""\
            def power_set(arr):
                if not arr:
                    return [[]]
                first = arr[0]
                rest = power_set(arr[1:])
                return rest + [[first] + s for s in rest]
        """),
        dedent("""\
            def spec(arr, result):
                n = len(arr)
                return len(result) == 2 ** n and len(set(tuple(s) for s in result)) == 2 ** n
        """),
        True,
    ),

    # 146 — power set bug: misses empty set (VIO)
    (
        "spec_146_power_set_bug",
        dedent("""\
            def power_set(arr):
                if not arr:
                    return []
                first = arr[0]
                rest = power_set(arr[1:])
                if not rest:
                    return [[first]]
                return rest + [[first] + s for s in rest]
        """),
        dedent("""\
            def spec(arr, result):
                n = len(arr)
                return len(result) == 2 ** n and len(set(tuple(s) for s in result)) == 2 ** n
        """),
        False,
    ),

    # 147 — next permutation correct (SAT)
    (
        "spec_147_next_permutation",
        dedent("""\
            def next_permutation(arr):
                a = list(arr)
                n = len(a)
                i = n - 2
                while i >= 0 and a[i] >= a[i + 1]:
                    i -= 1
                if i < 0:
                    return sorted(a)
                j = n - 1
                while a[j] <= a[i]:
                    j -= 1
                a[i], a[j] = a[j], a[i]
                a[i + 1:] = reversed(a[i + 1:])
                return a
        """),
        dedent("""\
            def spec(arr, result):
                from itertools import permutations
                perms = sorted(set(permutations(arr)))
                t = tuple(arr)
                idx = perms.index(t) if t in perms else -1
                if idx == len(perms) - 1:
                    return result == sorted(arr)
                return tuple(result) == perms[idx + 1]
        """),
        True,
    ),

    # 148 — next permutation bug: doesn't reverse suffix after swap (VIO)
    (
        "spec_148_next_permutation_bug",
        dedent("""\
            def next_permutation(arr):
                a = list(arr)
                n = len(a)
                i = n - 2
                while i >= 0 and a[i] >= a[i + 1]:
                    i -= 1
                if i < 0:
                    return sorted(a)
                j = n - 1
                while a[j] <= a[i]:
                    j -= 1
                a[i], a[j] = a[j], a[i]
                return a
        """),
        dedent("""\
            def spec(arr, result):
                from itertools import permutations
                perms = sorted(set(permutations(arr)))
                t = tuple(arr)
                idx = perms.index(t) if t in perms else -1
                if idx == len(perms) - 1:
                    return result == sorted(arr)
                return tuple(result) == perms[idx + 1]
        """),
        False,
    ),

    # 149 — n choose k correct (SAT)
    (
        "spec_149_n_choose_k",
        dedent("""\
            def n_choose_k(n, k):
                if k < 0 or k > n:
                    return 0
                if k == 0 or k == n:
                    return 1
                k = min(k, n - k)
                result = 1
                for i in range(k):
                    result = result * (n - i) // (i + 1)
                return result
        """),
        dedent("""\
            def spec(n, k, result):
                import math
                if k < 0 or k > n:
                    return result == 0
                return result == math.comb(n, k)
        """),
        True,
    ),

    # 150 — n choose k bug: integer division rounding error (VIO)
    (
        "spec_150_n_choose_k_bug",
        dedent("""\
            def n_choose_k(n, k):
                if k < 0 or k > n:
                    return 0
                if k == 0 or k == n:
                    return 1
                result = 1
                for i in range(k):
                    result *= (n - i)
                for i in range(k):
                    result //= (i + 1)
                return result
        """),
        dedent("""\
            def spec(n, k, result):
                import math
                if k < 0 or k > n:
                    return result == 0
                return result == math.comb(n, k)
        """),
        False,
    ),

    # 151 — catalan number correct (SAT)
    (
        "spec_151_catalan",
        dedent("""\
            def catalan(n):
                if n <= 1:
                    return 1
                dp = [0] * (n + 1)
                dp[0] = dp[1] = 1
                for i in range(2, n + 1):
                    for j in range(i):
                        dp[i] += dp[j] * dp[i - 1 - j]
                return dp[n]
        """),
        dedent("""\
            def spec(n, result):
                import math
                expected = math.comb(2*n, n) // (n + 1)
                return result == expected
        """),
        True,
    ),

    # 152 — catalan bug: wrong recurrence (VIO)
    (
        "spec_152_catalan_bug",
        dedent("""\
            def catalan(n):
                if n <= 1:
                    return 1
                dp = [0] * (n + 1)
                dp[0] = dp[1] = 1
                for i in range(2, n + 1):
                    for j in range(i):
                        dp[i] += dp[j] * dp[i - j]
                return dp[n]
        """),
        dedent("""\
            def spec(n, result):
                import math
                expected = math.comb(2*n, n) // (n + 1)
                return result == expected
        """),
        False,
    ),

    # 153 — count inversions correct (SAT)
    (
        "spec_153_count_inversions",
        dedent("""\
            def count_inversions(arr):
                count = 0
                for i in range(len(arr)):
                    for j in range(i + 1, len(arr)):
                        if arr[i] > arr[j]:
                            count += 1
                return count
        """),
        dedent("""\
            def spec(arr, result):
                count = 0
                for i in range(len(arr)):
                    for j in range(i + 1, len(arr)):
                        if arr[i] > arr[j]:
                            count += 1
                return result == count
        """),
        True,
    ),

    # 154 — count inversions bug: counts >= instead of > (VIO)
    (
        "spec_154_count_inversions_bug",
        dedent("""\
            def count_inversions(arr):
                count = 0
                for i in range(len(arr)):
                    for j in range(i + 1, len(arr)):
                        if arr[i] >= arr[j]:
                            count += 1
                return count
        """),
        dedent("""\
            def spec(arr, result):
                count = 0
                for i in range(len(arr)):
                    for j in range(i + 1, len(arr)):
                        if arr[i] > arr[j]:
                            count += 1
                return result == count
        """),
        False,
    ),

    # 155 — pascal's triangle row correct (SAT)
    (
        "spec_155_pascal_row",
        dedent("""\
            def pascal_row(n):
                row = [1]
                for k in range(1, n + 1):
                    row.append(row[-1] * (n - k + 1) // k)
                return row
        """),
        dedent("""\
            def spec(n, result):
                import math
                expected = [math.comb(n, k) for k in range(n + 1)]
                return result == expected
        """),
        True,
    ),

    # 156 — pascal's triangle row bug: off by one in formula (VIO)
    (
        "spec_156_pascal_row_bug",
        dedent("""\
            def pascal_row(n):
                row = [1]
                for k in range(1, n + 1):
                    row.append(row[-1] * (n - k) // k)
                return row
        """),
        dedent("""\
            def spec(n, result):
                import math
                expected = [math.comb(n, k) for k in range(n + 1)]
                return result == expected
        """),
        False,
    ),

    # 157 — derangements count correct (SAT)
    (
        "spec_157_derangements",
        dedent("""\
            def derangements(n):
                if n == 0:
                    return 1
                if n == 1:
                    return 0
                a, b = 1, 0
                for i in range(2, n + 1):
                    a, b = b, (i - 1) * (a + b)
                return b
        """),
        dedent("""\
            def spec(n, result):
                if n == 0:
                    return result == 1
                if n == 1:
                    return result == 0
                d = [0] * (n + 1)
                d[0] = 1
                d[1] = 0
                for i in range(2, n + 1):
                    d[i] = (i - 1) * (d[i-1] + d[i-2])
                return result == d[n]
        """),
        True,
    ),

    # 158 — derangements bug: wrong base case d(0)=0 (VIO)
    (
        "spec_158_derangements_bug",
        dedent("""\
            def derangements(n):
                if n == 0:
                    return 0
                if n == 1:
                    return 0
                a, b = 0, 0
                for i in range(2, n + 1):
                    a, b = b, (i - 1) * (a + b)
                return b
        """),
        dedent("""\
            def spec(n, result):
                if n == 0:
                    return result == 1
                if n == 1:
                    return result == 0
                d = [0] * (n + 1)
                d[0] = 1
                d[1] = 0
                for i in range(2, n + 1):
                    d[i] = (i - 1) * (d[i-1] + d[i-2])
                return result == d[n]
        """),
        False,
    ),

    # 159 — Stirling numbers of second kind correct (SAT)
    (
        "spec_159_stirling",
        dedent("""\
            def stirling(n, k):
                if n == 0 and k == 0:
                    return 1
                if n == 0 or k == 0:
                    return 0
                dp = [[0] * (k + 1) for _ in range(n + 1)]
                dp[0][0] = 1
                for i in range(1, n + 1):
                    for j in range(1, min(i, k) + 1):
                        dp[i][j] = j * dp[i-1][j] + dp[i-1][j-1]
                return dp[n][k]
        """),
        dedent("""\
            def spec(n, k, result):
                if n == 0 and k == 0:
                    return result == 1
                if n == 0 or k == 0 or k > n:
                    return result == 0
                dp = [[0]*(k+1) for _ in range(n+1)]
                dp[0][0] = 1
                for i in range(1, n+1):
                    for j in range(1, min(i, k)+1):
                        dp[i][j] = j * dp[i-1][j] + dp[i-1][j-1]
                return result == dp[n][k]
        """),
        True,
    ),

    # 160 — Stirling bug: wrong recurrence, uses (j+1) instead of j (VIO)
    (
        "spec_160_stirling_bug",
        dedent("""\
            def stirling(n, k):
                if n == 0 and k == 0:
                    return 1
                if n == 0 or k == 0:
                    return 0
                dp = [[0] * (k + 1) for _ in range(n + 1)]
                dp[0][0] = 1
                for i in range(1, n + 1):
                    for j in range(1, min(i, k) + 1):
                        dp[i][j] = (j + 1) * dp[i-1][j] + dp[i-1][j-1]
                return dp[n][k]
        """),
        dedent("""\
            def spec(n, k, result):
                if n == 0 and k == 0:
                    return result == 1
                if n == 0 or k == 0 or k > n:
                    return result == 0
                dp = [[0]*(k+1) for _ in range(n+1)]
                dp[0][0] = 1
                for i in range(1, n+1):
                    for j in range(1, min(i, k)+1):
                        dp[i][j] = j * dp[i-1][j] + dp[i-1][j-1]
                return result == dp[n][k]
        """),
        False,
    ),

    # =========================================================================
    # MIXED ADVANCED (161-200)
    # =========================================================================

    # 161 — matrix multiply correct (SAT)
    (
        "spec_161_matrix_multiply",
        dedent("""\
            def matrix_multiply(a, b):
                if not a or not b or len(a[0]) != len(b):
                    return None
                rows_a, cols_a, cols_b = len(a), len(a[0]), len(b[0])
                result = [[0] * cols_b for _ in range(rows_a)]
                for i in range(rows_a):
                    for j in range(cols_b):
                        for k in range(cols_a):
                            result[i][j] += a[i][k] * b[k][j]
                return result
        """),
        dedent("""\
            def spec(a, b, result):
                if not a or not b or len(a[0]) != len(b):
                    return result is None
                rows_a, cols_a, cols_b = len(a), len(a[0]), len(b[0])
                expected = [[0]*cols_b for _ in range(rows_a)]
                for i in range(rows_a):
                    for j in range(cols_b):
                        for k in range(cols_a):
                            expected[i][j] += a[i][k] * b[k][j]
                return result == expected
        """),
        True,
    ),

    # 162 — matrix multiply bug: wrong index order k,j swapped (VIO)
    (
        "spec_162_matrix_multiply_bug",
        dedent("""\
            def matrix_multiply(a, b):
                if not a or not b or len(a[0]) != len(b):
                    return None
                rows_a, cols_a, cols_b = len(a), len(a[0]), len(b[0])
                result = [[0] * cols_b for _ in range(rows_a)]
                for i in range(rows_a):
                    for j in range(cols_b):
                        for k in range(cols_a):
                            result[i][j] += a[i][k] * b[j][k] if j < len(b) and k < cols_b else 0
                return result
        """),
        dedent("""\
            def spec(a, b, result):
                if not a or not b or len(a[0]) != len(b):
                    return result is None
                rows_a, cols_a, cols_b = len(a), len(a[0]), len(b[0])
                expected = [[0]*cols_b for _ in range(rows_a)]
                for i in range(rows_a):
                    for j in range(cols_b):
                        for k in range(cols_a):
                            expected[i][j] += a[i][k] * b[k][j]
                return result == expected
        """),
        False,
    ),

    # 163 — longest increasing subsequence length correct (SAT)
    (
        "spec_163_lis_length",
        dedent("""\
            def lis_length(arr):
                if not arr:
                    return 0
                from bisect import bisect_left
                tails = []
                for x in arr:
                    pos = bisect_left(tails, x)
                    if pos == len(tails):
                        tails.append(x)
                    else:
                        tails[pos] = x
                return len(tails)
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result == 0
                n = len(arr)
                dp = [1] * n
                for i in range(1, n):
                    for j in range(i):
                        if arr[j] < arr[i]:
                            dp[i] = max(dp[i], dp[j] + 1)
                return result == max(dp)
        """),
        True,
    ),

    # 164 — LIS bug: uses <= instead of < (non-strictly increasing) (VIO)
    (
        "spec_164_lis_length_bug",
        dedent("""\
            def lis_length(arr):
                if not arr:
                    return 0
                from bisect import bisect_right
                tails = []
                for x in arr:
                    pos = bisect_right(tails, x)
                    if pos == len(tails):
                        tails.append(x)
                    else:
                        tails[pos] = x
                return len(tails)
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result == 0
                n = len(arr)
                dp = [1] * n
                for i in range(1, n):
                    for j in range(i):
                        if arr[j] < arr[i]:
                            dp[i] = max(dp[i], dp[j] + 1)
                return result == max(dp)
        """),
        False,
    ),

    # 165 — longest palindromic substring length correct (SAT)
    (
        "spec_165_longest_palindrome",
        dedent("""\
            def longest_palindrome(s):
                if not s:
                    return 0
                n = len(s)
                best = 1
                for center in range(2 * n - 1):
                    left = center // 2
                    right = left + center % 2
                    while left >= 0 and right < n and s[left] == s[right]:
                        best = max(best, right - left + 1)
                        left -= 1
                        right += 1
                return best
        """),
        dedent("""\
            def spec(s, result):
                if not s:
                    return result == 0
                n = len(s)
                best = 1
                for i in range(n):
                    for j in range(i, n):
                        sub = s[i:j+1]
                        if sub == sub[::-1] and len(sub) > best:
                            best = len(sub)
                return result == best
        """),
        True,
    ),

    # 166 — longest palindrome bug: only checks odd-length palindromes (VIO)
    (
        "spec_166_longest_palindrome_bug",
        dedent("""\
            def longest_palindrome(s):
                if not s:
                    return 0
                n = len(s)
                best = 1
                for center in range(n):
                    left = right = center
                    while left >= 0 and right < n and s[left] == s[right]:
                        best = max(best, right - left + 1)
                        left -= 1
                        right += 1
                return best
        """),
        dedent("""\
            def spec(s, result):
                if not s:
                    return result == 0
                n = len(s)
                best = 1
                for i in range(n):
                    for j in range(i, n):
                        sub = s[i:j+1]
                        if sub == sub[::-1] and len(sub) > best:
                            best = len(sub)
                return result == best
        """),
        False,
    ),

    # 167 — longest substring without repeating chars correct (SAT)
    (
        "spec_167_longest_unique_substr",
        dedent("""\
            def longest_unique_substr(s):
                seen = {}
                start = best = 0
                for i, c in enumerate(s):
                    if c in seen and seen[c] >= start:
                        start = seen[c] + 1
                    seen[c] = i
                    best = max(best, i - start + 1)
                return best
        """),
        dedent("""\
            def spec(s, result):
                best = 0
                for i in range(len(s)):
                    seen = set()
                    for j in range(i, len(s)):
                        if s[j] in seen:
                            break
                        seen.add(s[j])
                        best = max(best, j - i + 1)
                return result == best
        """),
        True,
    ),

    # 168 — longest unique substr bug: doesn't check if seen[c] >= start (VIO)
    (
        "spec_168_longest_unique_substr_bug",
        dedent("""\
            def longest_unique_substr(s):
                seen = {}
                start = best = 0
                for i, c in enumerate(s):
                    if c in seen:
                        start = seen[c] + 1
                    seen[c] = i
                    best = max(best, i - start + 1)
                return best
        """),
        dedent("""\
            def spec(s, result):
                best = 0
                for i in range(len(s)):
                    seen = set()
                    for j in range(i, len(s)):
                        if s[j] in seen:
                            break
                        seen.add(s[j])
                        best = max(best, j - i + 1)
                return result == best
        """),
        False,
    ),

    # 169 — max profit from stock prices correct (SAT)
    (
        "spec_169_max_profit",
        dedent("""\
            def max_profit(prices):
                if len(prices) < 2:
                    return 0
                min_price = prices[0]
                max_prof = 0
                for p in prices[1:]:
                    max_prof = max(max_prof, p - min_price)
                    min_price = min(min_price, p)
                return max_prof
        """),
        dedent("""\
            def spec(prices, result):
                if len(prices) < 2:
                    return result == 0
                best = 0
                for i in range(len(prices)):
                    for j in range(i + 1, len(prices)):
                        best = max(best, prices[j] - prices[i])
                return result == best
        """),
        True,
    ),

    # 170 — max profit bug: allows selling before buying (VIO)
    (
        "spec_170_max_profit_bug",
        dedent("""\
            def max_profit(prices):
                if len(prices) < 2:
                    return 0
                return max(prices) - min(prices)
        """),
        dedent("""\
            def spec(prices, result):
                if len(prices) < 2:
                    return result == 0
                best = 0
                for i in range(len(prices)):
                    for j in range(i + 1, len(prices)):
                        best = max(best, prices[j] - prices[i])
                return result == best
        """),
        False,
    ),

    # 171 — trap rain water correct (SAT)
    (
        "spec_171_trap_water",
        dedent("""\
            def trap_water(height):
                if not height:
                    return 0
                n = len(height)
                left_max = [0] * n
                right_max = [0] * n
                left_max[0] = height[0]
                for i in range(1, n):
                    left_max[i] = max(left_max[i-1], height[i])
                right_max[n-1] = height[n-1]
                for i in range(n-2, -1, -1):
                    right_max[i] = max(right_max[i+1], height[i])
                return sum(min(left_max[i], right_max[i]) - height[i] for i in range(n))
        """),
        dedent("""\
            def spec(height, result):
                if not height:
                    return result == 0
                n = len(height)
                total = 0
                for i in range(n):
                    lm = max(height[:i+1])
                    rm = max(height[i:])
                    total += min(lm, rm) - height[i]
                return result == total
        """),
        True,
    ),

    # 172 — trap water bug: uses max instead of min (VIO)
    (
        "spec_172_trap_water_bug",
        dedent("""\
            def trap_water(height):
                if not height:
                    return 0
                n = len(height)
                left_max = [0] * n
                right_max = [0] * n
                left_max[0] = height[0]
                for i in range(1, n):
                    left_max[i] = max(left_max[i-1], height[i])
                right_max[n-1] = height[n-1]
                for i in range(n-2, -1, -1):
                    right_max[i] = max(right_max[i+1], height[i])
                return sum(max(left_max[i], right_max[i]) - height[i] for i in range(n))
        """),
        dedent("""\
            def spec(height, result):
                if not height:
                    return result == 0
                n = len(height)
                total = 0
                for i in range(n):
                    lm = max(height[:i+1])
                    rm = max(height[i:])
                    total += min(lm, rm) - height[i]
                return result == total
        """),
        False,
    ),

    # 173 — container with most water correct (SAT)
    (
        "spec_173_max_area",
        dedent("""\
            def max_area(height):
                left, right = 0, len(height) - 1
                best = 0
                while left < right:
                    area = min(height[left], height[right]) * (right - left)
                    best = max(best, area)
                    if height[left] < height[right]:
                        left += 1
                    else:
                        right -= 1
                return best
        """),
        dedent("""\
            def spec(height, result):
                best = 0
                for i in range(len(height)):
                    for j in range(i+1, len(height)):
                        area = min(height[i], height[j]) * (j - i)
                        best = max(best, area)
                return result == best
        """),
        True,
    ),

    # 174 — median of two sorted arrays correct (SAT)
    (
        "spec_174_find_median",
        dedent("""\
            def find_median(a, b):
                merged = sorted(a + b)
                n = len(merged)
                if n % 2 == 1:
                    return merged[n // 2]
                return (merged[n // 2 - 1] + merged[n // 2]) / 2
        """),
        dedent("""\
            def spec(a, b, result):
                merged = sorted(a + b)
                n = len(merged)
                if n % 2 == 1:
                    return result == merged[n // 2]
                return result == (merged[n // 2 - 1] + merged[n // 2]) / 2
        """),
        True,
    ),

    # 175 — median bug: integer division for even case (VIO)
    (
        "spec_175_find_median_bug",
        dedent("""\
            def find_median(a, b):
                merged = sorted(a + b)
                n = len(merged)
                if n % 2 == 1:
                    return merged[n // 2]
                return (merged[n // 2 - 1] + merged[n // 2]) // 2
        """),
        dedent("""\
            def spec(a, b, result):
                merged = sorted(a + b)
                n = len(merged)
                if n % 2 == 1:
                    return result == merged[n // 2]
                return result == (merged[n // 2 - 1] + merged[n // 2]) / 2
        """),
        False,
    ),

    # 176 — kth smallest element correct (SAT)
    (
        "spec_176_kth_smallest",
        dedent("""\
            def kth_smallest(arr, k):
                if k < 1 or k > len(arr):
                    return None
                return sorted(arr)[k - 1]
        """),
        dedent("""\
            def spec(arr, k, result):
                if k < 1 or k > len(arr):
                    return result is None
                return result == sorted(arr)[k - 1]
        """),
        True,
    ),

    # 177 — kth smallest bug: 0-indexed instead of 1-indexed (VIO)
    (
        "spec_177_kth_smallest_bug",
        dedent("""\
            def kth_smallest(arr, k):
                if k < 1 or k > len(arr):
                    return None
                return sorted(arr)[k]
        """),
        dedent("""\
            def spec(arr, k, result):
                if k < 1 or k > len(arr):
                    return result is None
                return result == sorted(arr)[k - 1]
        """),
        False,
    ),

    # 178 — interval merge correct (SAT)
    (
        "spec_178_merge_intervals",
        dedent("""\
            def merge_intervals(intervals):
                if not intervals:
                    return []
                intervals = sorted(intervals, key=lambda x: x[0])
                merged = [list(intervals[0])]
                for start, end in intervals[1:]:
                    if start <= merged[-1][1]:
                        merged[-1][1] = max(merged[-1][1], end)
                    else:
                        merged.append([start, end])
                return merged
        """),
        dedent("""\
            def spec(intervals, result):
                if not intervals:
                    return result == []
                for i in range(len(result) - 1):
                    if result[i][1] >= result[i+1][0]:
                        return False
                covered_orig = set()
                for s, e in intervals:
                    for x in range(s, e + 1):
                        covered_orig.add(x)
                covered_res = set()
                for s, e in result:
                    for x in range(s, e + 1):
                        covered_res.add(x)
                return covered_orig == covered_res
        """),
        True,
    ),

    # 179 — interval merge bug: uses < instead of <= for overlap (VIO)
    (
        "spec_179_merge_intervals_bug",
        dedent("""\
            def merge_intervals(intervals):
                if not intervals:
                    return []
                intervals = sorted(intervals, key=lambda x: x[0])
                merged = [list(intervals[0])]
                for start, end in intervals[1:]:
                    if start < merged[-1][1]:
                        merged[-1][1] = max(merged[-1][1], end)
                    else:
                        merged.append([start, end])
                return merged
        """),
        dedent("""\
            def spec(intervals, result):
                if not intervals:
                    return result == []
                for i in range(len(result) - 1):
                    if result[i][1] >= result[i+1][0]:
                        return False
                covered_orig = set()
                for s, e in intervals:
                    for x in range(s, e + 1):
                        covered_orig.add(x)
                covered_res = set()
                for s, e in result:
                    for x in range(s, e + 1):
                        covered_res.add(x)
                return covered_orig == covered_res
        """),
        False,
    ),

    # 180 — deep copy nested dict correct (SAT)
    (
        "spec_180_deep_copy",
        dedent("""\
            def deep_copy(obj):
                if isinstance(obj, dict):
                    return {k: deep_copy(v) for k, v in obj.items()}
                if isinstance(obj, list):
                    return [deep_copy(x) for x in obj]
                return obj
        """),
        dedent("""\
            def spec(obj, result):
                import copy
                return result == copy.deepcopy(obj)
        """),
        True,
    ),

    # 181 — deep copy bug: shallow copies lists (VIO)
    (
        "spec_181_deep_copy_bug",
        dedent("""\
            def deep_copy(obj):
                if isinstance(obj, dict):
                    return {k: deep_copy(v) for k, v in obj.items()}
                if isinstance(obj, list):
                    return list(obj)
                return obj
        """),
        dedent("""\
            def spec(obj, result):
                import copy
                expected = copy.deepcopy(obj)
                if result != expected:
                    return False
                if isinstance(obj, list):
                    for i, item in enumerate(obj):
                        if isinstance(item, (list, dict)) and result[i] is item:
                            return False
                return True
        """),
        False,
    ),

    # 182 — binary to decimal bug: treats as base 10 (VIO)
    (
        "spec_182_bin_to_dec_bug",
        dedent("""\
            def bin_to_dec(binary_str):
                return int(binary_str)
        """),
        dedent("""\
            def spec(binary_str, result):
                return result == int(binary_str, 2)
        """),
        False,
    ),

    # 183 — decimal to binary bug: wrong for n=0 returns empty string (VIO)
    (
        "spec_183_dec_to_bin_bug",
        dedent("""\
            def dec_to_bin(n):
                result = []
                neg = n < 0
                n = abs(n)
                while n:
                    result.append(str(n % 2))
                    n //= 2
                if neg:
                    result.append("-")
                return "".join(reversed(result)) if result else ""
        """),
        dedent("""\
            def spec(n, result):
                if n == 0:
                    return result == "0"
                if n < 0:
                    return result == "-" + bin(abs(n))[2:]
                return result == bin(n)[2:]
        """),
        False,
    ),

    # 184 — roman to int correct (SAT)
    (
        "spec_184_roman_to_int",
        dedent("""\
            def roman_to_int(s):
                values = {'I':1,'V':5,'X':10,'L':50,'C':100,'D':500,'M':1000}
                total = 0
                for i in range(len(s)):
                    if i + 1 < len(s) and values[s[i]] < values[s[i+1]]:
                        total -= values[s[i]]
                    else:
                        total += values[s[i]]
                return total
        """),
        dedent("""\
            def spec(s, result):
                values = {'I':1,'V':5,'X':10,'L':50,'C':100,'D':500,'M':1000}
                total = 0
                for i in range(len(s)):
                    if i + 1 < len(s) and values[s[i]] < values[s[i+1]]:
                        total -= values[s[i]]
                    else:
                        total += values[s[i]]
                return result == total
        """),
        True,
    ),

    # 185 — roman to int bug: uses <= instead of < for subtraction rule (VIO)
    (
        "spec_185_roman_to_int_bug",
        dedent("""\
            def roman_to_int(s):
                values = {'I':1,'V':5,'X':10,'L':50,'C':100,'D':500,'M':1000}
                total = 0
                for i in range(len(s)):
                    if i + 1 < len(s) and values[s[i]] <= values[s[i+1]]:
                        total -= values[s[i]]
                    else:
                        total += values[s[i]]
                return total
        """),
        dedent("""\
            def spec(s, result):
                values = {'I':1,'V':5,'X':10,'L':50,'C':100,'D':500,'M':1000}
                total = 0
                for i in range(len(s)):
                    if i + 1 < len(s) and values[s[i]] < values[s[i+1]]:
                        total -= values[s[i]]
                    else:
                        total += values[s[i]]
                return result == total
        """),
        False,
    ),

    # 186 — unique paths in grid correct (SAT)
    (
        "spec_186_unique_paths",
        dedent("""\
            def unique_paths(m, n):
                dp = [[1] * n for _ in range(m)]
                for i in range(1, m):
                    for j in range(1, n):
                        dp[i][j] = dp[i-1][j] + dp[i][j-1]
                return dp[m-1][n-1]
        """),
        dedent("""\
            def spec(m, n, result):
                import math
                return result == math.comb(m + n - 2, m - 1)
        """),
        True,
    ),

    # 187 — unique paths bug: starts dp[0][0]=0, all zeros (VIO)
    (
        "spec_187_unique_paths_bug",
        dedent("""\
            def unique_paths(m, n):
                dp = [[0] * n for _ in range(m)]
                for i in range(m):
                    for j in range(n):
                        if i == 0 or j == 0:
                            dp[i][j] = 1
                        else:
                            dp[i][j] = dp[i-1][j] + dp[i][j-1] + dp[i-1][j-1]
                return dp[m-1][n-1]
        """),
        dedent("""\
            def spec(m, n, result):
                import math
                return result == math.comb(m + n - 2, m - 1)
        """),
        False,
    ),

    # 188 — word break correct (SAT)
    (
        "spec_188_word_break",
        dedent("""\
            def word_break(s, word_dict):
                n = len(s)
                dp = [False] * (n + 1)
                dp[0] = True
                for i in range(1, n + 1):
                    for j in range(i):
                        if dp[j] and s[j:i] in word_dict:
                            dp[i] = True
                            break
                return dp[n]
        """),
        dedent("""\
            def spec(s, word_dict, result):
                n = len(s)
                dp = [False] * (n + 1)
                dp[0] = True
                for i in range(1, n + 1):
                    for j in range(i):
                        if dp[j] and s[j:i] in word_dict:
                            dp[i] = True
                            break
                return result == dp[n]
        """),
        True,
    ),

    # 189 — word break bug: checks word_dict as list, O(n) per lookup but also wrong boundary (VIO)
    (
        "spec_189_word_break_bug",
        dedent("""\
            def word_break(s, word_dict):
                n = len(s)
                dp = [False] * (n + 1)
                dp[0] = True
                for i in range(1, n + 1):
                    for w in word_dict:
                        if i >= len(w) and dp[i - len(w)] and s[i - len(w):i] == w:
                            dp[i] = True
                            break
                return dp[n]
        """),
        dedent("""\
            def spec(s, word_dict, result):
                n = len(s)
                dp = [False] * (n + 1)
                dp[0] = True
                for i in range(1, n + 1):
                    for j in range(i):
                        if dp[j] and s[j:i] in word_dict:
                            dp[i] = True
                            break
                return result == dp[n]
        """),
        False,
    ),

    # 190 — house robber correct (SAT)
    (
        "spec_190_house_robber",
        dedent("""\
            def rob(nums):
                if not nums:
                    return 0
                if len(nums) <= 2:
                    return max(nums)
                dp = [0] * len(nums)
                dp[0] = nums[0]
                dp[1] = max(nums[0], nums[1])
                for i in range(2, len(nums)):
                    dp[i] = max(dp[i-1], dp[i-2] + nums[i])
                return dp[-1]
        """),
        dedent("""\
            def spec(nums, result):
                if not nums:
                    return result == 0
                n = len(nums)
                if n <= 2:
                    return result == max(nums)
                dp = [0] * n
                dp[0] = nums[0]
                dp[1] = max(nums[0], nums[1])
                for i in range(2, n):
                    dp[i] = max(dp[i-1], dp[i-2] + nums[i])
                return result == dp[-1]
        """),
        True,
    ),

    # 191 — house robber bug: dp[1] = nums[1] instead of max(nums[0],nums[1]) (VIO)
    (
        "spec_191_house_robber_bug",
        dedent("""\
            def rob(nums):
                if not nums:
                    return 0
                if len(nums) <= 2:
                    return max(nums)
                dp = [0] * len(nums)
                dp[0] = nums[0]
                dp[1] = nums[1]
                for i in range(2, len(nums)):
                    dp[i] = max(dp[i-1], dp[i-2] + nums[i])
                return dp[-1]
        """),
        dedent("""\
            def spec(nums, result):
                if not nums:
                    return result == 0
                n = len(nums)
                if n <= 2:
                    return result == max(nums)
                dp = [0] * n
                dp[0] = nums[0]
                dp[1] = max(nums[0], nums[1])
                for i in range(2, n):
                    dp[i] = max(dp[i-1], dp[i-2] + nums[i])
                return result == dp[-1]
        """),
        False,
    ),

    # 192 — decode ways correct (SAT)
    (
        "spec_192_decode_ways",
        dedent("""\
            def decode_ways(s):
                if not s or s[0] == '0':
                    return 0
                n = len(s)
                dp = [0] * (n + 1)
                dp[0] = 1
                dp[1] = 1
                for i in range(2, n + 1):
                    if s[i-1] != '0':
                        dp[i] += dp[i-1]
                    two = int(s[i-2:i])
                    if 10 <= two <= 26:
                        dp[i] += dp[i-2]
                return dp[n]
        """),
        dedent("""\
            def spec(s, result):
                if not s or s[0] == '0':
                    return result == 0
                n = len(s)
                dp = [0] * (n + 1)
                dp[0] = 1
                dp[1] = 1
                for i in range(2, n + 1):
                    if s[i-1] != '0':
                        dp[i] += dp[i-1]
                    two = int(s[i-2:i])
                    if 10 <= two <= 26:
                        dp[i] += dp[i-2]
                return result == dp[n]
        """),
        True,
    ),

    # 193 — decode ways bug: doesn't check for leading zero (VIO)
    (
        "spec_193_decode_ways_bug",
        dedent("""\
            def decode_ways(s):
                if not s:
                    return 0
                n = len(s)
                dp = [0] * (n + 1)
                dp[0] = 1
                dp[1] = 1
                for i in range(2, n + 1):
                    if s[i-1] != '0':
                        dp[i] += dp[i-1]
                    two = int(s[i-2:i])
                    if 10 <= two <= 26:
                        dp[i] += dp[i-2]
                return dp[n]
        """),
        dedent("""\
            def spec(s, result):
                if not s or s[0] == '0':
                    return result == 0
                n = len(s)
                dp = [0] * (n + 1)
                dp[0] = 1
                dp[1] = 1
                for i in range(2, n + 1):
                    if s[i-1] != '0':
                        dp[i] += dp[i-1]
                    two = int(s[i-2:i])
                    if 10 <= two <= 26:
                        dp[i] += dp[i-2]
                return result == dp[n]
        """),
        False,
    ),

    # 194 — evaluate RPN correct (SAT)
    (
        "spec_194_eval_rpn",
        dedent("""\
            def eval_rpn(tokens):
                stack = []
                ops = {'+', '-', '*', '/'}
                for t in tokens:
                    if t in ops:
                        b, a = stack.pop(), stack.pop()
                        if t == '+':
                            stack.append(a + b)
                        elif t == '-':
                            stack.append(a - b)
                        elif t == '*':
                            stack.append(a * b)
                        elif t == '/':
                            stack.append(int(a / b))
                    else:
                        stack.append(int(t))
                return stack[0]
        """),
        dedent("""\
            def spec(tokens, result):
                stack = []
                ops = {'+', '-', '*', '/'}
                for t in tokens:
                    if t in ops:
                        b, a = stack.pop(), stack.pop()
                        if t == '+': stack.append(a + b)
                        elif t == '-': stack.append(a - b)
                        elif t == '*': stack.append(a * b)
                        elif t == '/': stack.append(int(a / b))
                    else:
                        stack.append(int(t))
                return result == stack[0]
        """),
        True,
    ),

    # 195 — eval RPN bug: pops in wrong order (a,b instead of b,a) (VIO)
    (
        "spec_195_eval_rpn_bug",
        dedent("""\
            def eval_rpn(tokens):
                stack = []
                ops = {'+', '-', '*', '/'}
                for t in tokens:
                    if t in ops:
                        a, b = stack.pop(), stack.pop()
                        if t == '+':
                            stack.append(a + b)
                        elif t == '-':
                            stack.append(a - b)
                        elif t == '*':
                            stack.append(a * b)
                        elif t == '/':
                            stack.append(int(a / b))
                    else:
                        stack.append(int(t))
                return stack[0]
        """),
        dedent("""\
            def spec(tokens, result):
                stack = []
                ops = {'+', '-', '*', '/'}
                for t in tokens:
                    if t in ops:
                        b, a = stack.pop(), stack.pop()
                        if t == '+': stack.append(a + b)
                        elif t == '-': stack.append(a - b)
                        elif t == '*': stack.append(a * b)
                        elif t == '/': stack.append(int(a / b))
                    else:
                        stack.append(int(t))
                return result == stack[0]
        """),
        False,
    ),

    # 196 — matrix rotation 90 degrees clockwise correct (SAT)
    (
        "spec_196_rotate_matrix",
        dedent("""\
            def rotate_matrix(matrix):
                n = len(matrix)
                result = [[0]*n for _ in range(n)]
                for i in range(n):
                    for j in range(n):
                        result[j][n-1-i] = matrix[i][j]
                return result
        """),
        dedent("""\
            def spec(matrix, result):
                n = len(matrix)
                for i in range(n):
                    for j in range(n):
                        if result[j][n-1-i] != matrix[i][j]:
                            return False
                return True
        """),
        True,
    ),

    # 197 — rotate matrix bug: counter-clockwise instead of clockwise (VIO)
    (
        "spec_197_rotate_matrix_bug",
        dedent("""\
            def rotate_matrix(matrix):
                n = len(matrix)
                result = [[0]*n for _ in range(n)]
                for i in range(n):
                    for j in range(n):
                        result[n-1-j][i] = matrix[i][j]
                return result
        """),
        dedent("""\
            def spec(matrix, result):
                n = len(matrix)
                for i in range(n):
                    for j in range(n):
                        if result[j][n-1-i] != matrix[i][j]:
                            return False
                return True
        """),
        False,
    ),

    # 198 — zigzag level order traversal correct (SAT)
    (
        "spec_198_zigzag_traversal",
        dedent("""\
            def zigzag_traversal(tree):
                if not tree:
                    return []
                from collections import deque
                queue = deque([tree])
                result = []
                left_to_right = True
                while queue:
                    level = []
                    for _ in range(len(queue)):
                        node = queue.popleft()
                        level.append(node['val'])
                        if node.get('left'):
                            queue.append(node['left'])
                        if node.get('right'):
                            queue.append(node['right'])
                    if not left_to_right:
                        level.reverse()
                    result.append(level)
                    left_to_right = not left_to_right
                return result
        """),
        dedent("""\
            def spec(tree, result):
                if not tree:
                    return result == []
                from collections import deque
                queue = deque([tree])
                expected = []
                ltr = True
                while queue:
                    level = []
                    for _ in range(len(queue)):
                        node = queue.popleft()
                        level.append(node['val'])
                        if node.get('left'):
                            queue.append(node['left'])
                        if node.get('right'):
                            queue.append(node['right'])
                    if not ltr:
                        level.reverse()
                    expected.append(level)
                    ltr = not ltr
                return result == expected
        """),
        True,
    ),

    # 199 — zigzag bug: never reverses (VIO)
    (
        "spec_199_zigzag_traversal_bug",
        dedent("""\
            def zigzag_traversal(tree):
                if not tree:
                    return []
                from collections import deque
                queue = deque([tree])
                result = []
                while queue:
                    level = []
                    for _ in range(len(queue)):
                        node = queue.popleft()
                        level.append(node['val'])
                        if node.get('left'):
                            queue.append(node['left'])
                        if node.get('right'):
                            queue.append(node['right'])
                    result.append(level)
                return result
        """),
        dedent("""\
            def spec(tree, result):
                if not tree:
                    return result == []
                from collections import deque
                queue = deque([tree])
                expected = []
                ltr = True
                while queue:
                    level = []
                    for _ in range(len(queue)):
                        node = queue.popleft()
                        level.append(node['val'])
                        if node.get('left'):
                            queue.append(node['left'])
                        if node.get('right'):
                            queue.append(node['right'])
                    if not ltr:
                        level.reverse()
                    expected.append(level)
                    ltr = not ltr
                return result == expected
        """),
        False,
    ),

    # 200 — maximum depth of binary tree correct (SAT)
    (
        "spec_200_max_depth",
        dedent("""\
            def max_depth(tree):
                if not tree:
                    return 0
                return 1 + max(max_depth(tree.get('left')), max_depth(tree.get('right')))
        """),
        dedent("""\
            def spec(tree, result):
                def depth(node):
                    if not node:
                        return 0
                    return 1 + max(depth(node.get('left')), depth(node.get('right')))
                return result == depth(tree)
        """),
        True,
    ),
]
