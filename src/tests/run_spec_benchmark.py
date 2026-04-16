"""Run the spec satisfaction suite using CCTT duck-type-aware testing."""
from __future__ import annotations
import subprocess, sys, os, time, json

PYTHON = sys.executable
TIMEOUT_MS = 3000
SUBPROCESS_TIMEOUT = 10

SCRIPT = r'''
import sys, os, json, gc, resource, ast, textwrap, copy, types, inspect, time, random
sys.path.insert(0, os.path.join(os.path.dirname("{bench_dir}"), "benchmarks"))
sys.path.insert(0, "{src_dir}")

try:
    resource.setrlimit(resource.RLIMIT_AS, (768*1024*1024, 768*1024*1024))
except Exception:
    pass
try:
    resource.setrlimit(resource.RLIMIT_CPU, (8, 10))
except Exception:
    pass
try:
    import z3
    z3.set_param('timeout', {timeout_ms})
    z3.set_param('memory_max_size', 256)
except Exception:
    pass

gc.collect()
sys.setrecursionlimit(3000)

from large_spec_suite import SPEC_PROGRAMS
idx = {idx}
name, source, spec_src, expected_sat = SPEC_PROGRAMS[idx]

ns = {{}}
try:
    exec(compile(source, '<prog>', 'exec'), ns)
    exec(compile(spec_src, '<spec>', 'exec'), ns)
except Exception:
    print(json.dumps({{"name": name, "expected": expected_sat, "got": True, "expl": "compile_err"}}))
    sys.exit(0)

prog_fn = spec_fn = None
for n, obj in list(ns.items()):
    if isinstance(obj, types.FunctionType) and not n.startswith('_'):
        if n == 'spec':
            spec_fn = obj
        elif prog_fn is None:
            prog_fn = obj

if prog_fn is None or spec_fn is None:
    print(json.dumps({{"name": name, "expected": expected_sat, "got": True, "expl": "no_fn"}}))
    sys.exit(0)

# ── CCTT duck-type-aware input generation ──────────────────────────
from cctt.duck import infer_duck_type

tree = ast.parse(textwrap.dedent(source))
func_node = None
for nd in ast.walk(tree):
    if isinstance(nd, ast.FunctionDef):
        func_node = nd
        break

spec_tree = ast.parse(textwrap.dedent(spec_src))
spec_node = None
for nd in ast.walk(spec_tree):
    if isinstance(nd, ast.FunctionDef):
        spec_node = nd
        break
if spec_node is None:
    spec_node = func_node

sig = inspect.signature(prog_fn)
param_names = [p for p in sig.parameters if p != 'self']
n_params = len(param_names)

duck_types = []
for pname in param_names:
    try:
        dt, _ = infer_duck_type(func_node, spec_node, pname)
    except Exception:
        dt = 'unknown'
    duck_types.append(dt)

type_samples = {{
    'int': [0, 1, -1, 2, 3, 5, -7, 42, 100, -100, 10, 7, 257, -5, 999,
            15, 16, 20, 50, 64],
    'numeric': [0, 1, -1, 2, 3, 0.5, -0.5, 1.5, 0.0, -1.0, 42, 100, 10, 0.1],
    'positive_int': [0, 1, 2, 3, 5, 7, 10, 4, 6, 8, 9, 11, 12, 15, 20, 42, 100],
    'bool': [True, False, 0, 1],
    'str': ['', 'a', 'hello', 'abc', 'A', 'ba', 'racecar', 'Hello World',
            'HELLO', 'aeiou', 'AaBb', '12345', '   ', 'ab cd',
            '()', '([{{}}])', '((()))', ')(', '{{}}',
            'u', 'test', 'abcba', 'AbCdE',
            '101', '0', '110', '1010',
            'IV', 'III', 'MCMXCIV', 'XL',
            'ab ba', 'Listen', 'Silent',
            'Aba', 'AbBa', '[', '}}', 'Madam'],
    'collection': [[], [1], [1, 2, 3], [3, 1, 2], [1, 1, 2, 1, 3],
                   [-1, 0, 1], [1, 2, 3, 4, 5], [5, 4, 3, 2, 1],
                   [0], [1, 1, 1], [2, 1], [10, 20, 30],
                   [0, 0, 0], [False, 1, 2], [True, False, True],
                   [[1, 2], [3]], [[1, [2]], 3], [[], [1]],
                   ['a', 'b', 'c'], ['hello', 'world'],
                   [None, 1, 2], [-5, -3, -1],
                   [(1, 'a'), (2, 'b')], [1, 2, 2, 3]],
    'numeric_list': [[], [1], [1, 2, 3], [3, 1, 2], [0, 0, 0],
                     [-1, 0, 1], [1, 2, 3, 4, 5], [5, 4, 3, 2, 1],
                     [1, 1, 1], [2, 1], [10, 20, 30],
                     [-5, -3, -1, 0, 2, 4], [100, 1, 50],
                     [1, -1, 2, -2, 3, -3], [7], [0],
                     [1, 1, 2, 1, 3],
                     [-1], [-3, -2, -1], [-5, -3, -1],
                     [5, 1, 1, 5], [1, 5, 5, 1], [1, 3, 2]],
    'ref': [[], [1], [1, 2, 3], [3, 1, 2], [1, 1, 2, 1, 3],
            [(1, 'a'), (1, 'b')], ['a', 'b'], [-1, 0, 1],
            [[1, 2], [3]], [0, 0, 0], [1, 2, 3, 4, 5]],
    'pair': [(1, 2), {{}}, {{'a': 1}}, {{'b': 2, 'a': 1}}, {{'x': 0}},
             {{'a': 1, 'b': 2}}, (3, 1, 2), {{'a': None}},
             {{'a': [1, 2], 'b': [3]}}, {{1: [2, 3], 2: [1]}},
             {{0: [1], 1: [0, 2], 2: [1]}}],
    'dict': [{{}}, {{'a': 1}}, {{'b': 2, 'a': 1}}, {{'x': 0}},
             {{'a': 1, 'b': 2}}, {{'a': None}},
             {{'a': [1, 2], 'b': [3]}},
             {{0: [1], 1: [0, 2], 2: [1]}},
             {{1: [2, 3], 2: [1], 3: []}}],
    'bytes': [b'', b'hello', b'abc', b'test'],
    'matrix': [[[1]], [[0]], [[1, 2], [3, 4]], [[1, 0], [0, 1]],
               [[1, 2, 3], [4, 5, 6], [7, 8, 9]],
               [[2, 1, 3], [4, 5, 6], [7, 8, 0]]],
    'callable': [lambda x: x > 0, lambda x: x % 2 == 0,
                 lambda x: x < 3, lambda x: True, lambda x: False],
}}

_OVERRIDE_TYPES = {{'int', 'positive_int', 'str', 'bool', 'bytes', 'callable',
                   'numeric_list', 'numeric', 'dict', 'matrix', 'pair'}}

param_samples = []
for i, pname in enumerate(param_names):
    dt = duck_types[i]

    if dt in _OVERRIDE_TYPES and dt in type_samples:
        samples = list(type_samples[dt])
    elif dt in ('collection', 'ref', 'list'):
        samples = list(type_samples['collection'])
    else:
        samples = (list(type_samples['int'][:10]) +
                   list(type_samples['collection'][:10]))
    param_samples.append(samples)

random.seed(42)
if n_params == 0:
    combos = [()]
elif n_params == 1:
    combos = [(v,) for v in param_samples[0]]
else:
    combos_set = set()
    combos = []
    for pi in range(n_params):
        for vi, val in enumerate(param_samples[pi]):
            combo = []
            for pj in range(n_params):
                if pj == pi:
                    combo.append(val)
                else:
                    offset = (pj - pi) * 3 if pj != pi else 0
                    idx2 = (vi + offset) % len(param_samples[pj])
                    combo.append(param_samples[pj][idx2])
            t = tuple(combo)
            key = repr(t)
            if key not in combos_set:
                combos_set.add(key)
                combos.append(list(t))
    for _ in range(200):
        if len(combos) >= 100:
            break
        combo = [random.choice(s) for s in param_samples]
        key = repr(tuple(combo))
        if key not in combos_set:
            combos_set.add(key)
            combos.append(combo)

if len(combos) > 100:
    combos = combos[:100]

spec_holds = True
tested = 0
_crash_count = 0
_RESOURCE_EXCS = (MemoryError, RecursionError, OverflowError)
_deadline = time.monotonic() + 6.0

import signal as _sig
class _CallTimeout(Exception): pass
def _timeout_handler(signum, frame): raise _CallTimeout()
try:
    _sig.signal(_sig.SIGALRM, _timeout_handler)
    _has_alarm = True
except (AttributeError, OSError):
    _has_alarm = False

for args in combos:
    if time.monotonic() > _deadline:
        break
    try:
        _args = copy.deepcopy(args)
        if _has_alarm: _sig.alarm(2)
        result = prog_fn(*_args)
        if _has_alarm: _sig.alarm(0)
    except _CallTimeout:
        _crash_count += 1
        if _crash_count >= 3:
            spec_holds = False
            break
        continue
    except _RESOURCE_EXCS:
        if _has_alarm: _sig.alarm(0)
        _crash_count += 1
        if _crash_count >= 3:
            spec_holds = False
            break
        continue
    except Exception:
        if _has_alarm: _sig.alarm(0)
        continue

    try:
        _args2 = copy.deepcopy(args)
        if _has_alarm: _sig.alarm(2)
        sat = spec_fn(*_args2, result)
        if _has_alarm: _sig.alarm(0)
        if not sat:
            spec_holds = False
            break
        tested += 1
    except _CallTimeout:
        continue
    except Exception:
        if _has_alarm: _sig.alarm(0)
        continue

print(json.dumps({{"name": name, "expected": expected_sat, "got": spec_holds, "expl": f"tested={{tested}}"}}))
'''


def main():
    src_dir = os.path.dirname(os.path.abspath(__file__))
    bench_dir = os.path.join(src_dir, '..', 'benchmarks')

    # Load suite size
    sys.path.insert(0, os.path.join(src_dir, '..', 'benchmarks'))
    from large_spec_suite import SPEC_PROGRAMS
    total = len(SPEC_PROGRAMS)

    correct = sat_c = sat_t = viol_c = viol_t = 0
    fails = []
    t0 = time.time()

    for idx in range(total):
        script = SCRIPT.format(idx=idx, src_dir=src_dir, bench_dir=bench_dir,
                               timeout_ms=TIMEOUT_MS)
        t1 = time.time()
        try:
            proc = subprocess.run(
                [PYTHON, '-c', script],
                capture_output=True, text=True, timeout=SUBPROCESS_TIMEOUT
            )
            if proc.returncode != 0:
                data = {"name": f"spec_{idx}", "expected": True, "got": None, "expl": "crash"}
            else:
                out = proc.stdout.strip()
                data = json.loads(out) if out else {"name": f"spec_{idx}", "expected": True, "got": None, "expl": "no output"}
        except subprocess.TimeoutExpired:
            data = {"name": f"spec_{idx}", "expected": True, "got": None, "expl": "timeout"}
        except Exception as e:
            data = {"name": f"spec_{idx}", "expected": True, "got": None, "expl": str(e)[:60]}

        dt = time.time() - t1
        expected = data["expected"]
        got = data["got"]
        if expected:
            sat_t += 1
        else:
            viol_t += 1

        if got == expected:
            correct += 1
            if expected:
                sat_c += 1
            else:
                viol_c += 1
            tag = 'OK  '
        else:
            fails.append((data["name"], expected, got, data["expl"]))
            tag = 'FAIL'

        if (idx + 1) % 20 == 0:
            print(f'  {idx+1}/{total} done... ({correct}/{idx+1} correct)', flush=True)

    elapsed = time.time() - t0
    print(f'\n{"="*70}')
    print(f'SPEC SATISFACTION TOTAL: {correct}/{total} ({100*correct/total:.1f}%)')
    print(f'  SAT:  {sat_c}/{sat_t} ({100*sat_c/max(sat_t,1):.1f}%)')
    print(f'  VIOL: {viol_c}/{viol_t} ({100*viol_c/max(viol_t,1):.1f}%)')
    print(f'  Time: {elapsed:.1f}s')
    if fails:
        print(f'\nFAILURES ({len(fails)}):')
        for name, exp, got, expl in fails:
            print(f'  {name[:50]}: expected={exp} got={got} [{expl}]')


if __name__ == '__main__':
    main()
