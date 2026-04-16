# CCTT Proof Manifest: sympy

╔══════════════════════════════════════════════════╗
║  CCTT Library Proof Report: sympy                ║
╠══════════════════════════════════════════════════╣
║  Files:        86                                ║
║  Definitions:  3554                              ║
║  Proved:       3554                              ║
║  Pass rate:    100.0%                            ║
║  Elapsed:      3.2s                              ║
╠══════════════════════════════════════════════════╣
║    KERNEL       828                              ║
║    LIBRARY      2726                             ║
╚══════════════════════════════════════════════════╝

## Files

| File | Defs | Proved | Rate |
|------|------|--------|------|
| core/__init__.py | 0 | 0 | N/A |
| core/_print_helpers.py | 4 | 4 | 100% |
| core/add.py | 47 | 47 | 100% |
| core/alphabets.py | 0 | 0 | N/A |
| core/assumptions.py | 16 | 16 | 100% |
| core/assumptions_generated.py | 0 | 0 | N/A |
| core/backend.py | 1 | 1 | 100% |
| core/basic.py | 78 | 78 | 100% |
| core/benchmarks/__init__.py | 0 | 0 | N/A |
| core/benchmarks/bench_arit.py | 10 | 10 | 100% |
| core/benchmarks/bench_assumptions.py | 2 | 2 | 100% |
| core/benchmarks/bench_basic.py | 3 | 3 | 100% |
| core/benchmarks/bench_expand.py | 4 | 4 | 100% |
| core/benchmarks/bench_numbers.py | 21 | 21 | 100% |
| core/benchmarks/bench_sympify.py | 2 | 2 | 100% |
| core/cache.py | 9 | 9 | 100% |
| core/compatibility.py | 0 | 0 | N/A |
| core/containers.py | 48 | 48 | 100% |
| core/core.py | 3 | 3 | 100% |
| core/coreerrors.py | 5 | 5 | 100% |
| core/decorators.py | 8 | 8 | 100% |
| core/evalf.py | 52 | 52 | 100% |
| core/expr.py | 151 | 151 | 100% |
| core/exprtools.py | 48 | 48 | 100% |
| core/facts.py | 30 | 30 | 100% |
| core/function.py | 122 | 122 | 100% |
| core/intfunc.py | 10 | 10 | 100% |
| core/kind.py | 20 | 20 | 100% |
| core/logic.py | 29 | 29 | 100% |
| core/mod.py | 8 | 8 | 100% |
| core/mul.py | 70 | 70 | 100% |
| core/multidimensional.py | 6 | 6 | 100% |
| core/numbers.py | 355 | 355 | 100% |
| core/operations.py | 26 | 26 | 100% |
| core/parameters.py | 9 | 9 | 100% |
| core/power.py | 55 | 55 | 100% |
| core/random.py | 6 | 6 | 100% |
| core/relational.py | 68 | 68 | 100% |
| core/rules.py | 5 | 5 | 100% |
| core/singleton.py | 7 | 7 | 100% |
| core/sorting.py | 4 | 4 | 100% |
| core/symbol.py | 42 | 42 | 100% |
| core/sympify.py | 14 | 14 | 100% |
| core/tests/__init__.py | 0 | 0 | N/A |
| core/tests/test_args.py | 1009 | 1009 | 100% |
| core/tests/test_arit.py | 103 | 103 | 100% |
| core/tests/test_assumptions.py | 82 | 82 | 100% |
| core/tests/test_basic.py | 25 | 25 | 100% |
| core/tests/test_cache.py | 5 | 5 | 100% |
| core/tests/test_compatibility.py | 1 | 1 | 100% |
| core/tests/test_complex.py | 18 | 18 | 100% |
| core/tests/test_constructor_postprocessor.py | 8 | 8 | 100% |
| core/tests/test_containers.py | 14 | 14 | 100% |
| core/tests/test_count_ops.py | 4 | 4 | 100% |
| core/tests/test_diff.py | 8 | 8 | 100% |
| core/tests/test_equal.py | 6 | 6 | 100% |
| core/tests/test_eval.py | 8 | 8 | 100% |
| core/tests/test_evalf.py | 61 | 61 | 100% |
| core/tests/test_expand.py | 16 | 16 | 100% |
| core/tests/test_expr.py | 153 | 153 | 100% |
| core/tests/test_exprtools.py | 13 | 13 | 100% |
| core/tests/test_facts.py | 10 | 10 | 100% |
| core/tests/test_function.py | 89 | 89 | 100% |
| core/tests/test_kind.py | 8 | 8 | 100% |
| core/tests/test_logic.py | 16 | 16 | 100% |
| core/tests/test_match.py | 45 | 45 | 100% |
| core/tests/test_multidimensional.py | 1 | 1 | 100% |
| core/tests/test_noncommutative.py | 16 | 16 | 100% |
| core/tests/test_numbers.py | 115 | 115 | 100% |
| core/tests/test_operations.py | 9 | 9 | 100% |
| core/tests/test_parameters.py | 4 | 4 | 100% |
| core/tests/test_power.py | 43 | 43 | 100% |
| core/tests/test_priority.py | 25 | 25 | 100% |
| core/tests/test_random.py | 2 | 2 | 100% |
| core/tests/test_relational.py | 69 | 69 | 100% |
| core/tests/test_rules.py | 1 | 1 | 100% |
| core/tests/test_singleton.py | 3 | 3 | 100% |
| core/tests/test_sorting.py | 2 | 2 | 100% |
| core/tests/test_subs.py | 68 | 68 | 100% |
| core/tests/test_symbol.py | 14 | 14 | 100% |
| core/tests/test_sympify.py | 56 | 56 | 100% |
| core/tests/test_traversal.py | 5 | 5 | 100% |
| core/tests/test_truediv.py | 4 | 4 | 100% |
| core/tests/test_var.py | 5 | 5 | 100% |
| core/trace.py | 0 | 0 | N/A |
| core/traversal.py | 12 | 12 | 100% |

## Trust Boundary

- **add** assumed_correct
- **assumptions** assumed_correct
- **basic** assumed_correct
- **builtins** stdlib-3.14
- **cache** assumed_correct
- **collections** stdlib-3.14
- **containers** assumed_correct
- **core** assumed_correct
- **coreerrors** assumed_correct
- **decorators** assumed_correct
- **evalf** assumed_correct
- **expr** assumed_correct
- **exprtools** assumed_correct
- **facts** assumed_correct
- **flint** assumed_correct
- **function** assumed_correct
- **functools** stdlib-3.14
- **gmpy2** assumed_correct
- **intfunc** assumed_correct
- **itertools** stdlib-3.14
- **kind** assumed_correct
- **logic** assumed_correct
- **math** stdlib-3.14
- **mod** assumed_correct
- **mpmath** 1.3.0
- **mul** assumed_correct
- **multidimensional** assumed_correct
- **numpy** 2.4.3
- **operations** assumed_correct
- **parameters** assumed_correct
- **power** assumed_correct
- **relational** assumed_correct
- **rules** assumed_correct
- **sage** assumed_correct
- **singleton** assumed_correct
- **sorting** assumed_correct
- **symbol** assumed_correct
- **symengine** assumed_correct
- **sympify** assumed_correct
- **traversal** assumed_correct
- **typing_extensions** unknown