# DepPy Architecture & Reuse Guide

**Generated from exploration of**: `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src`

**For complete analysis, see**: `/tmp/deppy_mapping.md`

## Quick Navigation

1. **Module Mapping** (40+ modules analyzed) → which existing code to adapt
2. **Foundational vs. Risky** → which modules are safe to reuse directly
3. **Proposed Package Layout** → where to put new code
4. **Minimum Viable Core** → what to implement first (21 weeks)
5. **Reuse Matrix** → effort estimation for each component

## Key Findings

### Tier 1: Safe to Adapt Directly (32 modules)

**Frontend/Predicates**:
- `guard_extractor.py` (multipattern guard extraction)
- `real_analyzer.py` (flow-sensitive type narrowing, 2190 LOC)
- `guard_domain.py` (abstract domain for guards)

**Type System**:
- `types.py` (BaseType hierarchy, TypeVariable, 1843 LOC)
- `types_extended.py` (subtyping checker, 3948 LOC)

**Contracts & Analysis**:
- `interprocedural.py` (call graphs, 940 LOC)
- `assume_guarantee.py` (compositional verification)

**Abstract Domains** (7 modules):
- `domains/base.py` (Galois connections, fixed-point machinery)
- `domains/{intervals,nullity,typetags,strings,product,widening,abstract_domains}`

**Fragment Classification**:
- `decidability.py` (P vs NP-hard classification, 667 LOC)
- `verifiable_fragment.py`
- `theory_combination_analysis.py`

**SMT Backend** (5 modules):
- `smt/{encoder,z3_backend,theory_interface,solver}`
- `proof_certificate.py` (900 LOC, proof witnesses)

**Diagnostics & Export** (7 modules):
- `output/{report,sarif_reporter,pyi_generator}`
- `source_mapped_errors.py` (error tracing)
- CLI infrastructure

### Tier 2: Needs Refactoring (8 modules)

- `guard_domain.py` → separate from solver
- `_experimental/predicates/*` → integrate into core predicates module
- `unsat_core_cegar.py` → integrate with normalization
- Various frontend modules → consolidate

### Tier 3: Inspiration-Only (9 modules)

**Do NOT adapt directly; rethink from scratch:**
- `type_inference_engine.py` (monolithic, 55K LOC)
- `python_ast_analyzer.py` (conflated concerns)
- `_experimental/refinement_lattice.py` (mix solver + logic)
- `shape_cegar.py` (domain-specific, 3176 LOC)
- `cegar_cpa.py`, `denotational_semantics.py`, etc.

## Architecture Overview

```
Parse → Harvest → Infer → Normalize → Solve → Explain
  ↓        ↓        ↓          ↓        ↓        ↓
Parse   Guards   Base Types  Frag    Z3      Reports
AST     ×        ×           Class   Backend  SARIF
Scope   Preds    Candidates  Symbol  Proof   Stubs
        ×        Optimization Elim    Cert    HTML
       IPA       CEGAR       NF
```

**Key invariant**: Every verdict is traceable to a unique pipeline path with explicit artifacts (selected predicates, normalized obligations, fragment classification, proof status).

## Reuse Summary (by effort)

| Component | Reuse Modules | Effort | Risk |
|-----------|---------------|--------|------|
| Types | 3 modules | 1w | **Low** |
| Predicates | 6 modules | 1.5w | Low |
| Harvest | 4 modules | 1.5w | Low |
| Domains | 7 modules | 0.5w | **Very Low** |
| Normalization | 3 modules | 1w | Medium |
| Fragment Classification | 2 modules | 0.5w | Low |
| SMT Solving | 5 modules | 1w | Low |
| Diagnostics | 5 modules | 1w | Low |
| CLI/LSP | 3 modules | 1.5w | Low |
| **NEW**: Core IR, Surface syntax, IPA | — | 4w | Medium |
| **NEW**: Orchestration, Tests | — | 3.5w | Low |
| **TOTAL** | 41 existing + 3 new | **~21w** | — |

## Minimum Viable Core (in order)

1. Type system (types/)
2. Predicate IR (predicates/)
3. Guard extraction (harvest/)
4. Normalization (normalize/)
5. SMT solving (solver/)
6. Diagnostics (explain/)
7. Frontend elaboration (frontend/)
8. CLI (cli/)
9. Interprocedural (optional for MVP)

**Timeline**: ~5 months full-time with 2 engineers, OR ~8 months part-time with 1.

## Next Steps

1. Copy ARCHITECTURE.md into deppy/
2. Create `src/` skeleton with __init__.py stubs
3. Start with Phase 1: types/ module
4. Run guard_extractor on real Python to validate predicates
5. Integrate incrementally; test each component in isolation
