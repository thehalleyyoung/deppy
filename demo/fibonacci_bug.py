# fibonacci_bug.py
def fib(n):
    if n <= 1:
        return n
    a, b = 0, 1
    for _ in range(2, n):       # BUG: off-by-one (n instead of n + 1)
        a, b = b, a + b
    return b
