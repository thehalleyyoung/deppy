"""
Benchmark suite of 100 spec-satisfaction pairs.

Each entry is a tuple:
    (name, source, spec_fn_source, expected_satisfies)

- 60 programs SATISFY their spec (expected_satisfies=True)
- 40 programs DO NOT satisfy their spec (expected_satisfies=False)
"""

from textwrap import dedent

SPEC_PROGRAMS = [
    # =========================================================================
    # SORTING (1-12)
    # =========================================================================

    # 1 — correct bubble sort (SAT)
    (
        "bubble_sort",
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

    # 2 — insertion sort (SAT)
    (
        "insertion_sort",
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

    # 3 — selection sort (SAT)
    (
        "selection_sort",
        dedent("""\
            def selection_sort(arr):
                a = list(arr)
                for i in range(len(a)):
                    m = i
                    for j in range(i + 1, len(a)):
                        if a[j] < a[m]:
                            m = j
                    a[i], a[m] = a[m], a[i]
                return a
        """),
        dedent("""\
            def spec(arr, result):
                return sorted(result) == sorted(arr) and result == sorted(arr)
        """),
        True,
    ),

    # 4 — broken sort: off-by-one in bubble sort (VIO)
    (
        "broken_bubble_sort",
        dedent("""\
            def broken_bubble_sort(arr):
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

    # 5 — sort that reverses instead of sorting (VIO)
    (
        "reverse_not_sort",
        dedent("""\
            def reverse_not_sort(arr):
                return list(reversed(arr))
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        False,
    ),

    # 6 — merge sort (SAT)
    (
        "merge_sort",
        dedent("""\
            def merge_sort(arr):
                if len(arr) <= 1:
                    return list(arr)
                mid = len(arr) // 2
                left = merge_sort(arr[:mid])
                right = merge_sort(arr[mid:])
                merged, i, j = [], 0, 0
                while i < len(left) and j < len(right):
                    if left[i] <= right[j]:
                        merged.append(left[i]); i += 1
                    else:
                        merged.append(right[j]); j += 1
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

    # 7 — sort preserves length (SAT)
    (
        "sort_preserves_length",
        dedent("""\
            def sort_preserves_length(arr):
                return sorted(arr)
        """),
        dedent("""\
            def spec(arr, result):
                return len(result) == len(arr)
        """),
        True,
    ),

    # 8 — sort preserves multiset (SAT)
    (
        "sort_preserves_multiset",
        dedent("""\
            def sort_preserves_multiset(arr):
                return sorted(arr)
        """),
        dedent("""\
            def spec(arr, result):
                from collections import Counter
                return Counter(result) == Counter(arr)
        """),
        True,
    ),

    # 9 — sort drops duplicates (VIO)
    (
        "sort_drops_dupes",
        dedent("""\
            def sort_drops_dupes(arr):
                return sorted(set(arr))
        """),
        dedent("""\
            def spec(arr, result):
                from collections import Counter
                return Counter(result) == Counter(arr)
        """),
        False,
    ),

    # 10 — is_sorted check (SAT)
    (
        "is_sorted",
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

    # 11 — partial sort (only first half sorted) (VIO)
    (
        "partial_sort",
        dedent("""\
            def partial_sort(arr):
                a = list(arr)
                mid = len(a) // 2
                a[:mid] = sorted(a[:mid])
                return a
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        False,
    ),

    # 12 — sort but only returns first element (VIO)
    (
        "sort_returns_min_only",
        dedent("""\
            def sort_returns_min_only(arr):
                if not arr:
                    return []
                return [min(arr)]
        """),
        dedent("""\
            def spec(arr, result):
                return result == sorted(arr)
        """),
        False,
    ),

    # =========================================================================
    # SEARCHING (13-24)
    # =========================================================================

    # 13 — binary search (SAT)
    (
        "binary_search",
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

    # 14 — linear search (SAT)
    (
        "linear_search",
        dedent("""\
            def linear_search(arr, target):
                for i, v in enumerate(arr):
                    if v == target:
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

    # 15 — search always returns 0 (VIO)
    (
        "search_always_zero",
        dedent("""\
            def search_always_zero(arr, target):
                return 0
        """),
        dedent("""\
            def spec(arr, target, result):
                if result == -1:
                    return target not in arr
                return 0 <= result < len(arr) and arr[result] == target
        """),
        False,
    ),

    # 16 — find minimum index (SAT)
    (
        "find_min_index",
        dedent("""\
            def find_min_index(arr):
                if not arr:
                    return -1
                mi = 0
                for i in range(1, len(arr)):
                    if arr[i] < arr[mi]:
                        mi = i
                return mi
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result == -1
                return arr[result] == min(arr)
        """),
        True,
    ),

    # 17 — find max index (SAT)
    (
        "find_max_index",
        dedent("""\
            def find_max_index(arr):
                if not arr:
                    return -1
                mi = 0
                for i in range(1, len(arr)):
                    if arr[i] > arr[mi]:
                        mi = i
                return mi
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result == -1
                return arr[result] == max(arr)
        """),
        True,
    ),

    # 18 — search returns last index instead of first (VIO)
    (
        "search_last_not_first",
        dedent("""\
            def search_last_not_first(arr, target):
                result = -1
                for i, v in enumerate(arr):
                    if v == target:
                        result = i
                return result
        """),
        dedent("""\
            def spec(arr, target, result):
                if result == -1:
                    return target not in arr
                return arr[result] == target and all(
                    arr[j] != target for j in range(result)
                )
        """),
        False,
    ),

    # 19 — count occurrences (SAT)
    (
        "count_occurrences",
        dedent("""\
            def count_occurrences(arr, target):
                count = 0
                for v in arr:
                    if v == target:
                        count += 1
                return count
        """),
        dedent("""\
            def spec(arr, target, result):
                return result == sum(1 for v in arr if v == target)
        """),
        True,
    ),

    # 20 — index_of with wrong default (returns 0 instead of -1) (VIO)
    (
        "index_of_wrong_default",
        dedent("""\
            def index_of_wrong_default(arr, target):
                for i, v in enumerate(arr):
                    if v == target:
                        return i
                return 0
        """),
        dedent("""\
            def spec(arr, target, result):
                if target not in arr:
                    return result == -1
                return 0 <= result < len(arr) and arr[result] == target
        """),
        False,
    ),

    # 21 — contains check (SAT)
    (
        "contains",
        dedent("""\
            def contains(arr, target):
                for v in arr:
                    if v == target:
                        return True
                return False
        """),
        dedent("""\
            def spec(arr, target, result):
                return result == (target in arr)
        """),
        True,
    ),

    # 22 — find_all indices (SAT)
    (
        "find_all_indices",
        dedent("""\
            def find_all_indices(arr, target):
                return [i for i, v in enumerate(arr) if v == target]
        """),
        dedent("""\
            def spec(arr, target, result):
                return all(arr[i] == target for i in result) and len(result) == sum(1 for v in arr if v == target)
        """),
        True,
    ),

    # 23 — binary search but forgets to check equality (VIO)
    (
        "binary_search_no_eq",
        dedent("""\
            def binary_search_no_eq(arr, target):
                lo, hi = 0, len(arr) - 1
                while lo <= hi:
                    mid = (lo + hi) // 2
                    if arr[mid] < target:
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

    # 24 — find second largest (SAT)
    (
        "find_second_largest",
        dedent("""\
            def find_second_largest(arr):
                if len(arr) < 2:
                    return None
                uniq = sorted(set(arr), reverse=True)
                if len(uniq) < 2:
                    return None
                return uniq[1]
        """),
        dedent("""\
            def spec(arr, result):
                uniq = sorted(set(arr), reverse=True)
                if len(uniq) < 2:
                    return result is None
                return result == uniq[1]
        """),
        True,
    ),

    # =========================================================================
    # MATH (25-44)
    # =========================================================================

    # 25 — integer sqrt floor (SAT)
    (
        "isqrt",
        dedent("""\
            def isqrt(n):
                if n < 0:
                    return -1
                x = n
                while x * x > n:
                    x = (x + n // x) // 2
                return x
        """),
        dedent("""\
            def spec(n, result):
                if n < 0:
                    return result == -1
                return result * result <= n < (result + 1) * (result + 1)
        """),
        True,
    ),

    # 26 — sqrt that always returns n//2 (VIO)
    (
        "bad_isqrt",
        dedent("""\
            def bad_isqrt(n):
                if n < 0:
                    return -1
                return n // 2
        """),
        dedent("""\
            def spec(n, result):
                if n < 0:
                    return result == -1
                return result * result <= n < (result + 1) * (result + 1)
        """),
        False,
    ),

    # 27 — gcd (SAT)
    (
        "gcd",
        dedent("""\
            def gcd(a, b):
                a, b = abs(a), abs(b)
                while b:
                    a, b = b, a % b
                return a
        """),
        dedent("""\
            def spec(a, b, result):
                if a == 0 and b == 0:
                    return result == 0
                return result > 0 and a % result == 0 and b % result == 0
        """),
        True,
    ),

    # 28 — gcd returns min instead (VIO)
    (
        "bad_gcd",
        dedent("""\
            def bad_gcd(a, b):
                return min(abs(a), abs(b)) if a and b else abs(a) + abs(b)
        """),
        dedent("""\
            def spec(a, b, result):
                if a == 0 and b == 0:
                    return result == 0
                return result > 0 and a % result == 0 and b % result == 0
        """),
        False,
    ),

    # 29 — is_prime (SAT)
    (
        "is_prime",
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
                for d in range(2, int(n**0.5) + 1):
                    if n % d == 0:
                        return result is False
                return result is True
        """),
        True,
    ),

    # 30 — is_prime that says all odds are prime (VIO)
    (
        "bad_is_prime",
        dedent("""\
            def bad_is_prime(n):
                if n < 2:
                    return False
                return n % 2 != 0
        """),
        dedent("""\
            def spec(n, result):
                if n < 2:
                    return result is False
                for d in range(2, int(n**0.5) + 1):
                    if n % d == 0:
                        return result is False
                return result is True
        """),
        False,
    ),

    # 31 — factorial (SAT)
    (
        "factorial",
        dedent("""\
            def factorial(n):
                if n <= 1:
                    return 1
                result = 1
                for i in range(2, n + 1):
                    result *= i
                return result
        """),
        dedent("""\
            def spec(n, result):
                import math
                return result == math.factorial(max(n, 0)) if n >= 0 else result == 1
        """),
        True,
    ),

    # 32 — fibonacci (SAT)
    (
        "fibonacci",
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
                a, b = 0, 1
                for _ in range(n):
                    a, b = b, a + b
                return result == a
        """),
        True,
    ),

    # 33 — fibonacci off by one (VIO)
    (
        "fibonacci_off_by_one",
        dedent("""\
            def fibonacci_off_by_one(n):
                if n <= 0:
                    return 0
                a, b = 0, 1
                for _ in range(n):
                    a, b = b, a + b
                return a
        """),
        dedent("""\
            def spec(n, result):
                a, b = 0, 1
                for _ in range(n):
                    a, b = b, a + b
                return result == b
        """),
        False,
    ),

    # 34 — power (SAT)
    (
        "power",
        dedent("""\
            def power(base, exp):
                if exp == 0:
                    return 1
                result = 1
                for _ in range(exp):
                    result *= base
                return result
        """),
        dedent("""\
            def spec(base, exp, result):
                return result == base ** exp
        """),
        True,
    ),

    # 35 — absolute value (SAT)
    (
        "absolute_value",
        dedent("""\
            def absolute_value(x):
                return x if x >= 0 else -x
        """),
        dedent("""\
            def spec(x, result):
                return result >= 0 and (result == x or result == -x)
        """),
        True,
    ),

    # 36 — abs that doesn't negate negatives (VIO)
    (
        "bad_absolute",
        dedent("""\
            def bad_absolute(x):
                return x if x > 0 else x
        """),
        dedent("""\
            def spec(x, result):
                return result >= 0 and (result == x or result == -x)
        """),
        False,
    ),

    # 37 — lcm (SAT)
    (
        "lcm",
        dedent("""\
            def lcm(a, b):
                if a == 0 or b == 0:
                    return 0
                def gcd(x, y):
                    while y:
                        x, y = y, x % y
                    return x
                return abs(a * b) // gcd(abs(a), abs(b))
        """),
        dedent("""\
            def spec(a, b, result):
                if a == 0 or b == 0:
                    return result == 0
                return result > 0 and result % a == 0 and result % b == 0
        """),
        True,
    ),

    # 38 — modular exponentiation (SAT)
    (
        "mod_pow",
        dedent("""\
            def mod_pow(base, exp, mod):
                result = 1
                base = base % mod
                while exp > 0:
                    if exp % 2 == 1:
                        result = (result * base) % mod
                    exp = exp >> 1
                    base = (base * base) % mod
                return result
        """),
        dedent("""\
            def spec(base, exp, mod, result):
                return result == pow(base, exp, mod)
        """),
        True,
    ),

    # 39 — sum of digits (SAT)
    (
        "digit_sum",
        dedent("""\
            def digit_sum(n):
                n = abs(n)
                s = 0
                while n > 0:
                    s += n % 10
                    n //= 10
                return s
        """),
        dedent("""\
            def spec(n, result):
                return result == sum(int(d) for d in str(abs(n))) if n != 0 else result == 0
        """),
        True,
    ),

    # 40 — digit sum that ignores last digit (VIO)
    (
        "bad_digit_sum",
        dedent("""\
            def bad_digit_sum(n):
                n = abs(n) // 10
                s = 0
                while n > 0:
                    s += n % 10
                    n //= 10
                return s
        """),
        dedent("""\
            def spec(n, result):
                return result == sum(int(d) for d in str(abs(n))) if n != 0 else result == 0
        """),
        False,
    ),

    # 41 — clamp value (SAT)
    (
        "clamp",
        dedent("""\
            def clamp(x, lo, hi):
                if x < lo:
                    return lo
                if x > hi:
                    return hi
                return x
        """),
        dedent("""\
            def spec(x, lo, hi, result):
                return lo <= result <= hi and (result == x or result == lo or result == hi)
        """),
        True,
    ),

    # 42 — integer division rounding toward zero (SAT)
    (
        "int_div",
        dedent("""\
            def int_div(a, b):
                if b == 0:
                    return None
                return int(a / b)
        """),
        dedent("""\
            def spec(a, b, result):
                if b == 0:
                    return result is None
                import math
                return result == math.trunc(a / b)
        """),
        True,
    ),

    # 43 — collatz step (SAT)
    (
        "collatz_step",
        dedent("""\
            def collatz_step(n):
                if n <= 0:
                    return n
                if n % 2 == 0:
                    return n // 2
                return 3 * n + 1
        """),
        dedent("""\
            def spec(n, result):
                if n <= 0:
                    return result == n
                if n % 2 == 0:
                    return result == n // 2
                return result == 3 * n + 1
        """),
        True,
    ),

    # 44 — sum of first n naturals with wrong formula (VIO)
    (
        "bad_sum_naturals",
        dedent("""\
            def bad_sum_naturals(n):
                return n * n // 2
        """),
        dedent("""\
            def spec(n, result):
                return result == n * (n + 1) // 2
        """),
        False,
    ),

    # =========================================================================
    # DATA STRUCTURES — STACK / QUEUE (45-56)
    # =========================================================================

    # 45 — stack push (SAT)
    (
        "stack_push",
        dedent("""\
            def stack_push(stack, item):
                new_stack = list(stack)
                new_stack.append(item)
                return new_stack
        """),
        dedent("""\
            def spec(stack, item, result):
                return len(result) == len(stack) + 1 and result[-1] == item
        """),
        True,
    ),

    # 46 — stack pop (SAT)
    (
        "stack_pop",
        dedent("""\
            def stack_pop(stack):
                if not stack:
                    return (None, [])
                new_stack = list(stack)
                item = new_stack.pop()
                return (item, new_stack)
        """),
        dedent("""\
            def spec(stack, result):
                item, new_stack = result
                if not stack:
                    return item is None and new_stack == []
                return item == stack[-1] and new_stack == list(stack[:-1])
        """),
        True,
    ),

    # 47 — stack pop from front instead of back (VIO)
    (
        "stack_pop_wrong_end",
        dedent("""\
            def stack_pop_wrong_end(stack):
                if not stack:
                    return (None, [])
                new_stack = list(stack)
                item = new_stack.pop(0)
                return (item, new_stack)
        """),
        dedent("""\
            def spec(stack, result):
                item, new_stack = result
                if not stack:
                    return item is None and new_stack == []
                return item == stack[-1] and new_stack == list(stack[:-1])
        """),
        False,
    ),

    # 48 — queue enqueue (SAT)
    (
        "queue_enqueue",
        dedent("""\
            def queue_enqueue(queue, item):
                new_q = list(queue)
                new_q.append(item)
                return new_q
        """),
        dedent("""\
            def spec(queue, item, result):
                return len(result) == len(queue) + 1 and result[-1] == item and result[:-1] == list(queue)
        """),
        True,
    ),

    # 49 — queue dequeue (SAT)
    (
        "queue_dequeue",
        dedent("""\
            def queue_dequeue(queue):
                if not queue:
                    return (None, [])
                new_q = list(queue)
                item = new_q.pop(0)
                return (item, new_q)
        """),
        dedent("""\
            def spec(queue, result):
                item, new_q = result
                if not queue:
                    return item is None and new_q == []
                return item == queue[0] and new_q == list(queue[1:])
        """),
        True,
    ),

    # 50 — queue dequeue from wrong end (VIO)
    (
        "queue_dequeue_wrong_end",
        dedent("""\
            def queue_dequeue_wrong_end(queue):
                if not queue:
                    return (None, [])
                new_q = list(queue)
                item = new_q.pop()
                return (item, new_q)
        """),
        dedent("""\
            def spec(queue, result):
                item, new_q = result
                if not queue:
                    return item is None and new_q == []
                return item == queue[0] and new_q == list(queue[1:])
        """),
        False,
    ),

    # 51 — max stack: push and track max (SAT)
    (
        "max_stack_push",
        dedent("""\
            def max_stack_push(stack, maxes, item):
                new_stack = list(stack) + [item]
                new_max = max(maxes[-1], item) if maxes else item
                new_maxes = list(maxes) + [new_max]
                return (new_stack, new_maxes)
        """),
        dedent("""\
            def spec(stack, maxes, item, result):
                new_stack, new_maxes = result
                return new_maxes[-1] == max(new_stack) and len(new_maxes) == len(new_stack)
        """),
        True,
    ),

    # 52 — priority queue insert (SAT)
    (
        "pq_insert",
        dedent("""\
            def pq_insert(pq, item):
                import bisect
                new_pq = list(pq)
                bisect.insort(new_pq, item)
                return new_pq
        """),
        dedent("""\
            def spec(pq, item, result):
                return result == sorted(result) and len(result) == len(pq) + 1 and item in result
        """),
        True,
    ),

    # 53 — stack peek returns second element (VIO)
    (
        "stack_peek_wrong",
        dedent("""\
            def stack_peek_wrong(stack):
                if len(stack) < 2:
                    return None
                return stack[-2]
        """),
        dedent("""\
            def spec(stack, result):
                if not stack:
                    return result is None
                return result == stack[-1]
        """),
        False,
    ),

    # 54 — stack size (SAT)
    (
        "stack_size",
        dedent("""\
            def stack_size(stack):
                return len(stack)
        """),
        dedent("""\
            def spec(stack, result):
                return result == len(stack)
        """),
        True,
    ),

    # 55 — is_empty always returns True (VIO)
    (
        "is_empty_always_true",
        dedent("""\
            def is_empty_always_true(collection):
                return True
        """),
        dedent("""\
            def spec(collection, result):
                return result == (len(collection) == 0)
        """),
        False,
    ),

    # 56 — stack push that drops old elements (VIO)
    (
        "stack_push_drops",
        dedent("""\
            def stack_push_drops(stack, item):
                new_stack = list(stack[-2:])
                new_stack.append(item)
                return new_stack
        """),
        dedent("""\
            def spec(stack, item, result):
                return len(result) == len(stack) + 1 and result[-1] == item
        """),
        False,
    ),

    # =========================================================================
    # TREE / GRAPH (57-64)
    # =========================================================================

    # 57 — BST insert (SAT)
    (
        "bst_insert",
        dedent("""\
            def bst_insert(sorted_list, value):
                import bisect
                new_list = list(sorted_list)
                bisect.insort(new_list, value)
                return new_list
        """),
        dedent("""\
            def spec(sorted_list, value, result):
                return value in result and result == sorted(result) and len(result) == len(sorted_list) + 1
        """),
        True,
    ),

    # 58 — BST insert that doesn't maintain order (VIO)
    (
        "bst_insert_broken",
        dedent("""\
            def bst_insert_broken(sorted_list, value):
                new_list = list(sorted_list)
                new_list.append(value)
                return new_list
        """),
        dedent("""\
            def spec(sorted_list, value, result):
                return value in result and result == sorted(result) and len(result) == len(sorted_list) + 1
        """),
        False,
    ),

    # 59 — tree depth (SAT)
    (
        "tree_depth",
        dedent("""\
            def tree_depth(tree):
                if tree is None:
                    return 0
                if isinstance(tree, (int, float)):
                    return 1
                left = tree_depth(tree[1] if len(tree) > 1 else None)
                right = tree_depth(tree[2] if len(tree) > 2 else None)
                return 1 + max(left, right)
        """),
        dedent("""\
            def spec(tree, result):
                return result >= 0 and (result == 0) == (tree is None)
        """),
        True,
    ),

    # 60 — tree depth always returns 1 (VIO: fails for nested trees)
    (
        "tree_depth_always_one",
        dedent("""\
            def tree_depth_always_one(tree):
                if tree is None:
                    return 0
                return 1
        """),
        dedent("""\
            def spec(tree, result):
                def real_depth(t):
                    if t is None:
                        return 0
                    if isinstance(t, (int, float)):
                        return 1
                    ld = real_depth(t[1] if len(t) > 1 else None)
                    rd = real_depth(t[2] if len(t) > 2 else None)
                    return 1 + max(ld, rd)
                return result == real_depth(tree)
        """),
        False,
    ),

    # 61 — flatten nested list (SAT)
    (
        "flatten",
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
                return all(not isinstance(x, list) for x in result)
        """),
        True,
    ),

    # 62 — flatten that only goes one level (VIO)
    (
        "shallow_flatten",
        dedent("""\
            def shallow_flatten(lst):
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
                return all(not isinstance(x, list) for x in result)
        """),
        False,
    ),

    # 63 — inorder traversal of BST-as-sorted-list (SAT)
    (
        "inorder_sorted",
        dedent("""\
            def inorder_sorted(sorted_arr):
                return list(sorted_arr)
        """),
        dedent("""\
            def spec(sorted_arr, result):
                return result == sorted(result) and len(result) == len(sorted_arr)
        """),
        True,
    ),

    # 64 — graph has_self_loop (SAT)
    (
        "has_self_loop",
        dedent("""\
            def has_self_loop(adj):
                for node, neighbors in adj.items():
                    if node in neighbors:
                        return True
                return False
        """),
        dedent("""\
            def spec(adj, result):
                expected = any(node in neighbors for node, neighbors in adj.items())
                return result == expected
        """),
        True,
    ),

    # =========================================================================
    # STRING PROCESSING (65-80)
    # =========================================================================

    # 65 — reverse string (SAT)
    (
        "reverse_string",
        dedent("""\
            def reverse_string(s):
                return s[::-1]
        """),
        dedent("""\
            def spec(s, result):
                return len(result) == len(s) and all(result[i] == s[len(s) - 1 - i] for i in range(len(s)))
        """),
        True,
    ),

    # 66 — reverse string but drops last char (VIO)
    (
        "reverse_string_drops",
        dedent("""\
            def reverse_string_drops(s):
                return s[-1:0:-1]
        """),
        dedent("""\
            def spec(s, result):
                return len(result) == len(s) and result == s[::-1]
        """),
        False,
    ),

    # 67 — to_upper (SAT)
    (
        "to_upper",
        dedent("""\
            def to_upper(s):
                return s.upper()
        """),
        dedent("""\
            def spec(s, result):
                return len(result) == len(s) and result == s.upper()
        """),
        True,
    ),

    # 68 — to_lower (SAT)
    (
        "to_lower",
        dedent("""\
            def to_lower(s):
                return s.lower()
        """),
        dedent("""\
            def spec(s, result):
                return len(result) == len(s) and result == s.lower()
        """),
        True,
    ),

    # 69 — is_palindrome (SAT)
    (
        "is_palindrome",
        dedent("""\
            def is_palindrome(s):
                return s == s[::-1]
        """),
        dedent("""\
            def spec(s, result):
                return result == (s == s[::-1])
        """),
        True,
    ),

    # 70 — is_palindrome ignores case but spec is case-sensitive (VIO)
    (
        "is_palindrome_case_insensitive",
        dedent("""\
            def is_palindrome_case_insensitive(s):
                lower = s.lower()
                return lower == lower[::-1]
        """),
        dedent("""\
            def spec(s, result):
                return result == (s == s[::-1])
        """),
        False,
    ),

    # 71 — count vowels (SAT)
    (
        "count_vowels",
        dedent("""\
            def count_vowels(s):
                return sum(1 for c in s if c.lower() in 'aeiou')
        """),
        dedent("""\
            def spec(s, result):
                expected = sum(1 for c in s if c.lower() in 'aeiou')
                return result == expected
        """),
        True,
    ),

    # 72 — count vowels missing 'u' (VIO)
    (
        "count_vowels_missing_u",
        dedent("""\
            def count_vowels_missing_u(s):
                return sum(1 for c in s if c.lower() in 'aeio')
        """),
        dedent("""\
            def spec(s, result):
                expected = sum(1 for c in s if c.lower() in 'aeiou')
                return result == expected
        """),
        False,
    ),

    # 73 — word count (SAT)
    (
        "word_count",
        dedent("""\
            def word_count(s):
                return len(s.split())
        """),
        dedent("""\
            def spec(s, result):
                return result == len(s.split())
        """),
        True,
    ),

    # 74 — char frequency (SAT)
    (
        "char_frequency",
        dedent("""\
            def char_frequency(s):
                freq = {}
                for c in s:
                    freq[c] = freq.get(c, 0) + 1
                return freq
        """),
        dedent("""\
            def spec(s, result):
                return all(result.get(c, 0) == s.count(c) for c in set(s)) and sum(result.values()) == len(s)
        """),
        True,
    ),

    # 75 — strip whitespace but also strips letters (VIO)
    (
        "strip_too_much",
        dedent("""\
            def strip_too_much(s):
                return s.strip().replace('a', '')
        """),
        dedent("""\
            def spec(s, result):
                return result == s.strip()
        """),
        False,
    ),

    # 76 — capitalize first letter (SAT)
    (
        "capitalize_first",
        dedent("""\
            def capitalize_first(s):
                if not s:
                    return s
                return s[0].upper() + s[1:]
        """),
        dedent("""\
            def spec(s, result):
                if not s:
                    return result == ''
                return result[0] == s[0].upper() and result[1:] == s[1:]
        """),
        True,
    ),

    # 77 — replace char but only first occurrence (VIO: spec says replace all)
    (
        "replace_first_only",
        dedent("""\
            def replace_first_only(s, old, new):
                return s.replace(old, new, 1)
        """),
        dedent("""\
            def spec(s, old, new, result):
                return result == s.replace(old, new)
        """),
        False,
    ),

    # 78 — truncate string (SAT)
    (
        "truncate",
        dedent("""\
            def truncate(s, max_len):
                return s[:max_len]
        """),
        dedent("""\
            def spec(s, max_len, result):
                return len(result) <= max_len and s.startswith(result)
        """),
        True,
    ),

    # 79 — remove_digits (SAT)
    (
        "remove_digits",
        dedent("""\
            def remove_digits(s):
                return ''.join(c for c in s if not c.isdigit())
        """),
        dedent("""\
            def spec(s, result):
                return all(not c.isdigit() for c in result) and len(result) == sum(1 for c in s if not c.isdigit())
        """),
        True,
    ),

    # 80 — remove_digits that also removes 'a' (VIO)
    (
        "remove_digits_and_a",
        dedent("""\
            def remove_digits_and_a(s):
                return ''.join(c for c in s if not c.isdigit() and c != 'a')
        """),
        dedent("""\
            def spec(s, result):
                expected_len = sum(1 for c in s if not c.isdigit())
                return all(not c.isdigit() for c in result) and len(result) == expected_len
        """),
        False,
    ),

    # =========================================================================
    # ARRAY PROCESSING (81-100)
    # =========================================================================

    # 81 — array sum (SAT)
    (
        "array_sum",
        dedent("""\
            def array_sum(arr):
                total = 0
                for x in arr:
                    total += x
                return total
        """),
        dedent("""\
            def spec(arr, result):
                return result == sum(arr)
        """),
        True,
    ),

    # 82 — array max (SAT)
    (
        "array_max",
        dedent("""\
            def array_max(arr):
                if not arr:
                    return None
                m = arr[0]
                for x in arr[1:]:
                    if x > m:
                        m = x
                return m
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result is None
                return result == max(arr) and result in arr
        """),
        True,
    ),

    # 83 — array min returns max instead (VIO)
    (
        "array_min_returns_max",
        dedent("""\
            def array_min_returns_max(arr):
                if not arr:
                    return None
                m = arr[0]
                for x in arr[1:]:
                    if x > m:
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

    # 84 — average that uses integer division (VIO)
    (
        "bad_average",
        dedent("""\
            def bad_average(arr):
                if not arr:
                    return 0
                return sum(arr) // len(arr)
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result == 0
                return result == sum(arr) / len(arr)
        """),
        False,
    ),

    # 85 — filter positives (SAT)
    (
        "filter_positives",
        dedent("""\
            def filter_positives(arr):
                return [x for x in arr if x > 0]
        """),
        dedent("""\
            def spec(arr, result):
                return all(x > 0 for x in result) and len(result) == sum(1 for x in arr if x > 0)
        """),
        True,
    ),

    # 86 — filter evens but also keeps 1 (VIO: spec requires all even)
    (
        "filter_evens_keeps_one",
        dedent("""\
            def filter_evens_keeps_one(arr):
                return [x for x in arr if x % 2 == 0 or x == 1]
        """),
        dedent("""\
            def spec(arr, result):
                return all(x % 2 == 0 for x in result) and len(result) == sum(1 for x in arr if x % 2 == 0)
        """),
        False,
    ),

    # 87 — filter evens but includes odds too (VIO)
    (
        "filter_evens_broken",
        dedent("""\
            def filter_evens_broken(arr):
                return [x for x in arr if x % 2 == 0 or x > 10]
        """),
        dedent("""\
            def spec(arr, result):
                return all(x % 2 == 0 for x in result)
        """),
        False,
    ),

    # 88 — map double (SAT)
    (
        "map_double",
        dedent("""\
            def map_double(arr):
                return [x * 2 for x in arr]
        """),
        dedent("""\
            def spec(arr, result):
                return len(result) == len(arr) and all(result[i] == arr[i] * 2 for i in range(len(arr)))
        """),
        True,
    ),

    # 89 — map cube instead of square (VIO)
    (
        "map_cube_not_square",
        dedent("""\
            def map_cube_not_square(arr):
                return [x * x * x for x in arr]
        """),
        dedent("""\
            def spec(arr, result):
                return len(result) == len(arr) and all(result[i] == arr[i] ** 2 for i in range(len(arr)))
        """),
        False,
    ),

    # 90 — cumulative sum (SAT)
    (
        "cumulative_sum",
        dedent("""\
            def cumulative_sum(arr):
                result = []
                total = 0
                for x in arr:
                    total += x
                    result.append(total)
                return result
        """),
        dedent("""\
            def spec(arr, result):
                if len(result) != len(arr):
                    return False
                return all(result[i] == sum(arr[:i+1]) for i in range(len(arr)))
        """),
        True,
    ),

    # 91 — remove duplicates preserving order (SAT)
    (
        "remove_duplicates",
        dedent("""\
            def remove_duplicates(arr):
                seen = set()
                result = []
                for x in arr:
                    if x not in seen:
                        seen.add(x)
                        result.append(x)
                return result
        """),
        dedent("""\
            def spec(arr, result):
                return len(result) == len(set(arr)) and all(x in arr for x in result) and len(set(result)) == len(result)
        """),
        True,
    ),

    # 92 — remove duplicates but reverses order (VIO)
    (
        "remove_duplicates_reversed",
        dedent("""\
            def remove_duplicates_reversed(arr):
                seen = set()
                result = []
                for x in reversed(arr):
                    if x not in seen:
                        seen.add(x)
                        result.append(x)
                return result
        """),
        dedent("""\
            def spec(arr, result):
                seen = set()
                expected = []
                for x in arr:
                    if x not in seen:
                        seen.add(x)
                        expected.append(x)
                return result == expected
        """),
        False,
    ),

    # 93 — zip two arrays (SAT)
    (
        "zip_arrays",
        dedent("""\
            def zip_arrays(a, b):
                return list(zip(a, b))
        """),
        dedent("""\
            def spec(a, b, result):
                n = min(len(a), len(b))
                return len(result) == n and all(result[i] == (a[i], b[i]) for i in range(n))
        """),
        True,
    ),

    # 94 — dot product wrong: adds instead of multiplies (VIO)
    (
        "bad_dot_product",
        dedent("""\
            def bad_dot_product(a, b):
                return sum(x + y for x, y in zip(a, b))
        """),
        dedent("""\
            def spec(a, b, result):
                n = min(len(a), len(b))
                return result == sum(a[i] * b[i] for i in range(n))
        """),
        False,
    ),

    # 95 — rotate array left (SAT)
    (
        "rotate_left",
        dedent("""\
            def rotate_left(arr, k):
                if not arr:
                    return []
                k = k % len(arr)
                return arr[k:] + arr[:k]
        """),
        dedent("""\
            def spec(arr, k, result):
                if not arr:
                    return result == []
                n = len(arr)
                k2 = k % n
                return len(result) == n and all(result[i] == arr[(i + k2) % n] for i in range(n))
        """),
        True,
    ),

    # 96 — rotate right that actually rotates left (VIO)
    (
        "rotate_right_broken",
        dedent("""\
            def rotate_right_broken(arr, k):
                if not arr:
                    return []
                k = k % len(arr)
                return arr[k:] + arr[:k]
        """),
        dedent("""\
            def spec(arr, k, result):
                if not arr:
                    return result == []
                n = len(arr)
                k2 = k % n
                return len(result) == n and all(result[i] == arr[(i - k2) % n] for i in range(n))
        """),
        False,
    ),

    # 97 — chunk array (SAT)
    (
        "chunk_array",
        dedent("""\
            def chunk_array(arr, size):
                if size <= 0:
                    return []
                return [arr[i:i+size] for i in range(0, len(arr), size)]
        """),
        dedent("""\
            def spec(arr, size, result):
                if size <= 0:
                    return result == []
                flat = [x for chunk in result for x in chunk]
                return flat == list(arr) and all(len(c) <= size for c in result)
        """),
        True,
    ),

    # 98 — running max that resets at negative (VIO)
    (
        "running_max_resets",
        dedent("""\
            def running_max_resets(arr):
                if not arr:
                    return []
                result = [arr[0]]
                for x in arr[1:]:
                    if x < 0:
                        result.append(x)
                    else:
                        result.append(max(result[-1], x))
                return result
        """),
        dedent("""\
            def spec(arr, result):
                if not arr:
                    return result == []
                return len(result) == len(arr) and all(result[i] == max(arr[:i+1]) for i in range(len(arr)))
        """),
        False,
    ),

    # 99 — partition around pivot (SAT)
    (
        "partition",
        dedent("""\
            def partition(arr, pivot):
                left = [x for x in arr if x <= pivot]
                right = [x for x in arr if x > pivot]
                return left + right
        """),
        dedent("""\
            def spec(arr, pivot, result):
                from collections import Counter
                if Counter(result) != Counter(arr):
                    return False
                idx = len([x for x in arr if x <= pivot])
                return all(result[i] <= pivot for i in range(idx)) and all(result[i] > pivot for i in range(idx, len(result)))
        """),
        True,
    ),

    # 100 — product of array that skips zeros (VIO)
    (
        "product_skip_zeros",
        dedent("""\
            def product_skip_zeros(arr):
                result = 1
                for x in arr:
                    if x != 0:
                        result *= x
                return result
        """),
        dedent("""\
            def spec(arr, result):
                expected = 1
                for x in arr:
                    expected *= x
                return result == expected
        """),
        False,
    ),
]

# Sanity check: verify counts
_satisfy = sum(1 for _, _, _, e in SPEC_PROGRAMS if e is True)
_violate = sum(1 for _, _, _, e in SPEC_PROGRAMS if e is False)
assert len(SPEC_PROGRAMS) == 100, f"Expected 100, got {len(SPEC_PROGRAMS)}"
assert _satisfy == 60, f"Expected 60 satisfying, got {_satisfy}"
assert _violate == 40, f"Expected 40 violating, got {_violate}"
