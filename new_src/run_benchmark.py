"""Run the hard_equiv_suite one pair at a time in subprocesses to limit memory."""
from __future__ import annotations
import subprocess, sys, os, time, json

PYTHON = sys.executable       # use current interpreter
TIMEOUT_MS = 5000             # per-problem Z3 timeout (ms) — conservative
SUBPROCESS_TIMEOUT = 12       # per-problem subprocess wall-clock timeout (s)

SCRIPT = r'''
import sys, os, json, gc, resource, signal
sys.path.insert(0, os.path.join(os.path.dirname("{bench_dir}"), "benchmarks"))
sys.path.insert(0, "{src_dir}")

# Hard resource limits to prevent crashing the computer
try:
    # Limit virtual memory to 768MB per subprocess
    resource.setrlimit(resource.RLIMIT_AS, (768*1024*1024, 768*1024*1024))
except Exception:
    pass

# CPU time limit as a safety valve
try:
    resource.setrlimit(resource.RLIMIT_CPU, (10, 12))
except Exception:
    pass

# Global Z3 parameters — constrain memory and timeout
try:
    import z3
    z3.set_param('timeout', {timeout_ms})
    z3.set_param('memory_max_size', 512)  # 512 MB max for Z3 solver
except Exception:
    pass

gc.collect()
sys.setrecursionlimit(3000)

from hard_equiv_suite import EQUIV_PAIRS
idx = {idx}
name, src_a, src_b, expected = EQUIV_PAIRS[idx]
from cctt.checker import check_equivalence
try:
    r = check_equivalence(src_a, src_b, timeout_ms={timeout_ms})
    print(json.dumps({{"name": name, "expected": expected, "got": r.equivalent, "expl": r.explanation[:80]}}))
except Exception as e:
    print(json.dumps({{"name": name, "expected": expected, "got": None, "expl": f"ERR: {{str(e)[:60]}}"}}))
'''

def main():
    src_dir = os.path.dirname(os.path.abspath(__file__))
    bench_dir = os.path.join(src_dir, '..', 'benchmarks')
    correct = eq_c = eq_t = neq_c = neq_t = 0
    fails = []
    t0 = time.time()
    total = 100

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
                err = proc.stderr.strip()[-80:] if proc.stderr else 'unknown'
                data = {"name": f"pair_{idx}", "expected": idx < 50, "got": None, "expl": f"crash: {err}"}
            else:
                out = proc.stdout.strip()
                if out:
                    data = json.loads(out)
                else:
                    data = {"name": f"pair_{idx}", "expected": idx < 50, "got": None, "expl": "no output"}
        except subprocess.TimeoutExpired:
            data = {"name": f"pair_{idx}", "expected": idx < 50, "got": None, "expl": f"subprocess timeout ({SUBPROCESS_TIMEOUT}s)"}
        except Exception as e:
            data = {"name": f"pair_{idx}", "expected": idx < 50, "got": None, "expl": str(e)[:60]}

        dt = time.time() - t1
        expected = data["expected"]
        got = data["got"]
        if expected: eq_t += 1
        else: neq_t += 1

        if got == expected:
            correct += 1
            if expected: eq_c += 1
            else: neq_c += 1
            tag = 'OK  '
        else:
            fails.append((data["name"], expected, got, data["expl"]))
            tag = 'FAIL'

        print(f'{tag} [{idx+1:3d}/100] exp={str(expected):5s} got={str(got):5s} {dt:4.1f}s {data["name"][:45]:45s} [{data["expl"][:50]}]', flush=True)

    elapsed = time.time() - t0
    print(f'\n{"="*70}')
    print(f'TOTAL: {correct}/{total} ({100*correct/total:.1f}%)')
    print(f'  EQ:  {eq_c}/{eq_t} ({100*eq_c/max(eq_t,1):.1f}%)')
    print(f'  NEQ: {neq_c}/{neq_t} ({100*neq_c/max(neq_t,1):.1f}%)')
    print(f'  Time: {elapsed:.1f}s')
    if fails:
        print(f'\nFAILURES ({len(fails)}):')
        for name, exp, got, expl in fails:
            print(f'  {name[:50]}: expected={exp} got={got} [{expl}]')

if __name__ == '__main__':
    main()
