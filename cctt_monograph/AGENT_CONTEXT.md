# Agent Context for Monograph Deepening

## Implementation Files (read to understand what's actually built)
- `new_src/cctt/denotation.py` — OTerm types, 7-phase normalizer, denotational_equiv
- `new_src/cctt/path_search.py` — HIT structural prover, BFS, 16 axiom functions
- `new_src/cctt/checker.py` — Full pipeline: denotation → Z3 → Čech H1
- `new_src/cctt/compiler.py` — Python AST → Z3 presheaf sections
- `new_src/cctt/theory.py` — Z3 PyObj sort, tag system, builtins
- `new_src/cctt/duck.py` — Duck type inference for fiber restriction
- `new_src/cctt/cohomology.py` — Čech H1 computation
- `new_src/cctt/normalizer.py` — Semantic fingerprinting

## LaTeX Rules
- Use \coloneqq NOT \defeq (undefined)
- Use proper theorem environments
- Cross-reference using \ref{} and \label{}
- Compile: cd cctt_monograph && pdflatex -interaction=nonstopmode -halt-on-error main.tex

## Code Proposal Rules
- Write proposals to `new_src/proposals/YOUR_GROUP.py`
- Each proposal is a standalone Python file with functions/classes
- Include test cases as functions named test_*
- Proposals should be importable and testable independently
- Target: improve benchmark from 55/100 (7 EQ + 48 NEQ)

## Current Benchmark: 55/100
- EQ passing (7): eq02, eq05, eq22, eq35, eq37, eq39, eq50
- NEQ failing (2): neq15 (generator exhaustion), neq30 (identical canons)
- 43 EQ pairs fail (22 H1 obstructions, 14 inconclusive, 5 memory, 2 other)
