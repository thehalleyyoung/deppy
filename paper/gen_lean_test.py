"""Generate DeppyGenTest.lean from example functions."""
from __future__ import annotations

import sys
sys.path.insert(0, '.')

from deppy.lean.compiler import compile_to_lean, _translate_function_body
from deppy.proofs.sugar import guarantee


@guarantee('result >= 0')
def square(x: int) -> int:
    return x * x


@guarantee('result >= 0')
def abs_val(x: int) -> int:
    if x >= 0:
        return x
    return -x


@guarantee('result >= x')
def plus_one(x: int) -> int:
    return x + 1


@guarantee('result >= 0')
def safe_div(x: int, y: int) -> int:
    try:
        if y == 0:
            return 0
        return x * x
    except Exception:
        return 0


@guarantee('result >= 0')
def double_val(x: int) -> int:
    a = x * x
    return a


@guarantee('result >= 0')
def with_while(n: int) -> int:
    acc = 0
    i = n
    while i > 0:
        acc = acc + i
        i = i - 1
    return acc


@guarantee('result >= 0')
def for_loop(n: int) -> int:
    total = 0
    for i in range(n):
        total += i
    return total


fns = [square, abs_val, plus_one, safe_div, double_val, with_while,
       for_loop]

# Debug body translation
for fn in fns:
    body = _translate_function_body(fn)
    print(f"{fn.__name__}: body={'OK' if body else 'NONE'}")

# Build single combined file
lines = ["import Mathlib.Tactic", "set_option autoImplicit true", ""]
for fn in fns:
    cert = compile_to_lean(fn)
    text = cert.render()
    in_ns = False
    for line in text.split('\n'):
        if line.startswith('namespace'):
            in_ns = True
        if in_ns:
            lines.append(line)
        if line.startswith('end ') and in_ns:
            in_ns = False
            lines.append("")

with open('paper/lean_metatheory/DeppyGenTest.lean', 'w') as f:
    f.write('\n'.join(lines) + '\n')

print(f"\nWrote DeppyGenTest.lean with {len(fns)} functions")
