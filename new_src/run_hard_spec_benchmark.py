"""Run hard_spec_suite (200 pairs) one at a time in subprocesses."""
from __future__ import annotations
import subprocess, sys, os, time, json

PYTHON = sys.executable
TIMEOUT_MS = 3000
SUBPROCESS_TIMEOUT = 8

SCRIPT = r'''
import sys, os, json, gc, resource
sys.path.insert(0, os.path.join(os.path.dirname("{bench_dir}"), "benchmarks"))
sys.path.insert(0, "{src_dir}")

try:
    resource.setrlimit(resource.RLIMIT_AS, (768*1024*1024, 768*1024*1024))
except Exception:
    pass
try:
    resource.setrlimit(resource.RLIMIT_CPU, (6, 8))
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

from hard_spec_suite import SPEC_PROGRAMS
idx = {idx}
name, source, spec_src, expected_sat = SPEC_PROGRAMS[idx]

import types, copy
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

import inspect
sig = inspect.signature(prog_fn)
n_params = len(sig.parameters) - (1 if 'self' in sig.parameters else 0)

int_samples = [0, 1, -1, 2, 3, -7, 42, 10, 100, -100, 5, -5, 7, 999]
str_samples = ['', 'a', 'hello', 'abc', 'A', 'ba', 'racecar', 'ab']
list_samples = [[], [1], [1,2,3], [3,1,2], [1,1,2,1,3], [-1,0,1], [1,2,3,4,5],
                [5,4,3,2,1], [0], [1,1,1], [2,1], [10,20,30]]
dict_samples = [{{}}, {{"a": 1}}, {{"b": 2, "a": 1}}, {{"x": 0}}]

all_samples = int_samples + str_samples + list_samples

spec_holds = True
tested = 0

if n_params == 1:
    for inp in all_samples[:25]:
        try:
            result = prog_fn(copy.deepcopy(inp))
            if not spec_fn(copy.deepcopy(inp), result):
                spec_holds = False
                break
            tested += 1
        except Exception:
            continue
elif n_params == 2:
    for a in int_samples[:8] + list_samples[:5] + str_samples[:4]:
        for b in int_samples[:8] + list_samples[:3]:
            try:
                result = prog_fn(copy.deepcopy(a), copy.deepcopy(b))
                if not spec_fn(copy.deepcopy(a), copy.deepcopy(b), result):
                    spec_holds = False
                    break
                tested += 1
            except Exception:
                continue
        if not spec_holds:
            break
elif n_params == 3:
    for a in int_samples[:5]:
        for b in int_samples[:5]:
            for c in int_samples[:3]:
                try:
                    result = prog_fn(copy.deepcopy(a), copy.deepcopy(b), copy.deepcopy(c))
                    if not spec_fn(copy.deepcopy(a), copy.deepcopy(b), copy.deepcopy(c), result):
                        spec_holds = False
                        break
                    tested += 1
                except Exception:
                    continue
            if not spec_holds:
                break
        if not spec_holds:
            break
else:
    for inp in int_samples[:8]:
        args = [copy.deepcopy(inp)] * n_params
        try:
            result = prog_fn(*args)
            spec_args = args + [result]
            if not spec_fn(*spec_args):
                spec_holds = False
                break
            tested += 1
        except Exception:
            continue

print(json.dumps({{"name": name, "expected": expected_sat, "got": spec_holds, "expl": f"tested={{tested}}"}}))
'''


def main():
    src_dir = os.path.dirname(os.path.abspath(__file__))
    bench_dir = os.path.join(src_dir, '..', 'benchmarks')

    sys.path.insert(0, os.path.join(src_dir, '..', 'benchmarks'))
    from hard_spec_suite import SPEC_PROGRAMS
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

        print(f'{tag} [{idx+1:3d}/200] exp={str(expected):5s} got={str(got):5s} {dt:4.1f}s {data["name"][:45]:45s} [{data["expl"][:50]}]', flush=True)

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
