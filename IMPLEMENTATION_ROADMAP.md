# DepPy Implementation Roadmap

**Status**: Foundation design phase (ready for implementation)  
**Last updated**: 2025-03-10  
**Document**: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/`

---

## Executive Summary

Based on comprehensive exploration of 60+ modules in the existing TensorGuard refinement-type implementation, this roadmap outlines how to build DepPy as a serious, production-ready dependent-type system for Python.

**Key findings**:
- **32 foundational modules** are ready for direct reuse
- **8 modules** need light refactoring
- **9 modules** should inspire new implementations, not be copied
- **~21–24 weeks** (5–6 months) to reach MVP with 2 engineers
- **Phase 1 (types + harvest)** takes 4 weeks; low-risk baseline for validating architecture

---

## What Are We Building?

DepPy is a dependent-type system for Python that bridges the spec (chapters 03, 07, 09 of main.tex) with working code:

```
┌─────────────────────────────────────────────────────────────┐
│  Surface Layer (what users see)                             │
│  - Python code with optional type annotations               │
│  - Inferred refinements: {v: τ | φ}                         │
│  - Dependent function types: Π(x:τ₁).τ₂                     │
│  - Contracts & assertions                                   │
└─────────────────────────────────────────────────────────────┘
                          ↓ normalize
┌─────────────────────────────────────────────────────────────┐
│  Core Layer (what the solver sees)                          │
│  - Quantifier-free linear integer arithmetic (QF_LIA)       │
│  - Finite-domain enumerations                               │
│  - Uninterpreted functions                                  │
│  - Fragment classification (P / NP-hard / unknown)          │
└─────────────────────────────────────────────────────────────┘
                          ↓ encode
┌─────────────────────────────────────────────────────────────┐
│  Solver (Z3)                                                │
│  - sat/unsat/unknown decision                               │
│  - Proof certificates & counterexamples                     │
└─────────────────────────────────────────────────────────────┘
                          ↓ explain
┌─────────────────────────────────────────────────────────────┐
│  Output Layer                                               │
│  - Diagnostics (source context, confidence)                 │
│  - SARIF (CI integration)                                   │
│  - Stubs (.pyi files)                                       │
│  - Proof artifacts                                          │
└─────────────────────────────────────────────────────────────┘
```

---

## High-Level Architecture

### Pipeline (from Chapter 09 spec)

```
Parse → Harvest → Infer → Normalize → Solve → Explain
  ↓        ↓        ↓          ↓        ↓        ↓
Python  Guards   Base Types  Frag    Z3      Diagnostics
AST     ×        Candidates  Class   Backend SARIF/Stubs
        Preds    Contracts   Symbol  Proof   HTML/IDE
                 IPA         Elim    Cert
```

### Module Ownership

| Component | Packages | Risk |
|-----------|----------|------|
| **Frontend** | `src/frontend/`, `src/predicates/` | Low (mostly reuse) |
| **Harvesting** | `src/harvest/` | Low (harvester framework proven) |
| **Type inference** | `src/types/`, `src/infer/` | Low (reuse subtyping) |
| **Normalization** | `src/normalize/` | Medium (new integration layer) |
| **Solving** | `src/solver/` | Low (mostly reuse Z3 backend) |
| **Diagnostics** | `src/explain/` | Low (output formatter reuse) |
| **IPA** | `src/interprocedural/` | Medium (contract inference new) |
| **CLI** | `src/cli/`, `src/lsp/` | Low (framework reuse) |

---

## Phase-by-Phase Implementation Plan

### Phase 1: Core Type System (Week 1–2) — **LOW RISK**

**Goal**: Establish type representation and subtyping.

**Modules to implement**:
1. `src/types/base_type.py` – Copy from `/src/types.py`
2. `src/types/variables.py` – Copy `TypeVariable`, `RowVariable`
3. `src/types/subtyping.py` – Copy from `/src/types_extended.py`
4. `src/types/refinement_type.py` – NEW: {v: τ | φ}
5. `src/types/dependent_type.py` – NEW: Π(x:τ₁).τ₂

**Deliverable**:
- Type representation for all surface forms
- Refinement subtyping (sound)
- 30+ unit tests

**Testing strategy**:
- `test_types.py`: Type hierarchy, polymorphism, subtyping queries
- Fixtures: simple.py (5 LOC), medium.py (30 LOC)

**Success criteria**:
- `is_subtype(RefinementType, RefinementType)` works
- VCs generated for subtyping queries
- Tests run in <1s

---

### Phase 2: Frontend & Guard Harvesting (Week 3–4) — **LOW RISK**

**Goal**: Parse Python → Core IR; extract guards.

**Modules to implement**:
1. `src/frontend/ir/core_term.py` – NEW: Core AST (e, λx.e, if/let)
2. `src/frontend/ir/core_type.py` – NEW: Core type AST
3. `src/frontend/parser.py` – NEW: Python AST → Core IR (simple elaboration)
4. `src/harvest/guard_harvester.py` – Copy from `/src/guard_extractor.py`
5. `src/predicates/predicate.py` – Copy from `/src/guard_extractor.py`
6. `src/predicates/kinds.py` – NEW: PredicateKind enum

**Deliverable**:
- Parse 100-line functions
- Extract all guard patterns (if, try, assert, walrus)
- Source location tracking for all predicates

**Testing strategy**:
- `test_frontend.py`: Parser on fixtures
- `test_harvest.py`: Guard extraction accuracy

**Success criteria**:
- Parse & extract guards from simple.py, medium.py
- All predicates have provenance (file, line, column)
- Tests run in <2s

---

### Phase 3: Fragment Classification & Normalization (Week 5–6) — **MEDIUM RISK**

**Goal**: Classify predicates (QF_LIA / finite-domain / unknown); normalize to core.

**Modules to implement**:
1. `src/normalize/normalizer.py` – NEW: Norm: Pred ↝ Core
2. `src/normalize/fragment_classifier.py` – Copy from `/src/decidability.py`
3. `src/normalize/symbol_elimination.py` – NEW: Remove unused vars
4. `src/normalize/arithmetic_classifier.py` – NEW: Classify arithmetic
5. `src/normalize/outside_kernel.py` – NEW: Handle non-decidable

**Deliverable**:
- Classify every predicate (with explanation)
- Normalize to core forms
- Graceful handling of outside-kernel

**Testing strategy**:
- `test_normalize.py`: Classification accuracy
- Fixtures: complex.py (100+ LOC, all predicate types)

**Success criteria**:
- 100% of harvestable predicates classified
- No crashes on outside-kernel predicates
- Tests run in <5s

**Risk mitigation**:
- Start conservative: Only QF_LIA in trusted core initially
- Test against reference `decidability.py`
- Document assumptions for each fragment

---

### Phase 4: SMT Encoding & Solving (Week 7–8) — **LOW RISK**

**Goal**: Encode VCs as Z3 queries; generate proofs.

**Modules to implement**:
1. `src/solver/encoder.py` – Copy from `/src/smt/encoder.py`
2. `src/solver/z3_backend.py` – Copy from `/src/smt/z3_backend.py`
3. `src/solver/query_builder.py` – NEW: Build VC formulas
4. `src/explain/proof_certificate.py` – Copy from `/src/proof_certificate.py`

**Deliverable**:
- Encode refined subtyping queries to Z3
- Report sat/unsat/unknown
- Generate proof certificates

**Testing strategy**:
- `test_solver.py`: Encoding soundness
- Unit tests for each Z3 theory

**Success criteria**:
- All Phase 2 predicates encode without error
- Soundness: if Z3 says unsat, the predicate is unsatisfiable
- Proof certificates validate

---

### Phase 5: Diagnostics & Export (Week 9–10) — **LOW RISK**

**Goal**: Generate user-friendly diagnostics, SARIF, stubs.

**Modules to implement**:
1. `src/explain/diagnostic.py` – Copy from `/src/output/report.py`
2. `src/explain/sarif_exporter.py` – Copy from `/src/output/sarif_reporter.py`
3. `src/explain/html_exporter.py` – Copy from `/src/output/html_report.py`
4. `src/explain/stub_generator.py` – Copy from `/src/output/pyi_generator.py`

**Deliverable**:
- Structured diagnostics with source context
- SARIF output for CI
- Stub generation (.pyi files)

**Testing strategy**:
- `test_integration.py`: End-to-end diagnostics
- Human review of HTML output

**Success criteria**:
- SARIF validates with sarif-sdk
- HTML renders in browser
- Stubs are syntactically valid Python

---

### Phase 6: CLI & IDE Integration (Week 11–12) — **LOW RISK**

**Goal**: Working CLI; LSP server for IDE.

**Modules to implement**:
1. `src/cli/main.py` – Copy from `/src/cli/main.py`
2. `src/cli/commands.py` – NEW: Subcommand impls
3. `src/lsp/server.py` – Copy from `/src/cli/lsp_server.py`

**Deliverable**:
- `deppy check myfile.py` command
- LSP server listening on stdin/stdout
- Basic VS Code integration

**Testing strategy**:
- CLI manual testing on fixtures
- LSP protocol compliance (pyls tests)

**Success criteria**:
- CLI works on simple.py, medium.py, complex.py
- LSP hover & diagnostics work in VS Code
- No crashes on multi-file projects

---

### Phase 7 (Optional): Interprocedural Analysis (Week 13–14)

**Goal**: Cross-function analysis; contract inference.

**Modules to implement**:
1. `src/interprocedural/call_graph.py` – Copy from `/src/interprocedural.py`
2. `src/interprocedural/contract_inference.py` – NEW: Infer function contracts
3. `src/interprocedural/compositional.py` – Copy from `/src/assume_guarantee.py`

**Deliverable**:
- Call graph construction
- Function contract inference
- Compositional verification

**Note**: Can be deferred post-MVP. Adds ~4 weeks.

---

## Tier 1 MVP: Minimum Viable Core

**Scope**: Phases 1–6 (12 weeks)

**Coverage**:
- Single-function Python code ✓
- All predicate types (guards, asserts, comprehensions) ✓
- Refinement type inference ✓
- Diagnostics + stubs ✓
- CLI + basic IDE ✓

**Scope**: Multi-function, IPA deferred

**Effort**: 2 engineers × 12 weeks = **24 engineer-weeks**  
**Timeline**: ~3 months full-time, or ~6 months part-time

**Risk**: Low (heavy reuse, clear phases, incrementally testable)

---

## Tier 2 Extension: Production-Ready

**Scope**: Phase 7 + hardening + optimization

**Additional work**:
- Interprocedural analysis (4 weeks)
- Performance tuning (2 weeks)
- Security audit (1 week)
- Documentation (2 weeks)
- Release engineering (1 week)

**Total**: ~32 engineer-weeks (~8 months full-time)

---

## Resource Requirements

### Minimum Team

| Role | FTE | Responsibilities |
|------|-----|-----------------|
| Lead architect | 1.0 | Design, integration, solver |
| Type system engineer | 1.0 | Types, subtyping, VCs |
| Frontend engineer | 0.5 | Parser, elaborator, harvest |
| Testing & infra | 0.5 | CI/CD, fixtures, performance |

**Total**: ~3 FTE for 12 weeks → Tier 1 MVP

### Optional (for Tier 2)

| Role | FTE | Responsibilities |
|------|-----|-----------------|
| IPA specialist | 1.0 | Call graphs, contracts |
| IDE/LSP engineer | 0.5 | Language server, VS Code |

---

## Key Design Decisions

### 1. Separation of Concerns

- **Predicates** (logic) ≠ **Solver** (Z3)
- **Harvest** (extraction) ≠ **Normalize** (simplification)
- **Types** (data structure) ≠ **Inference** (algorithm)

→ Each module has single responsibility; easy to test, extend, replace.

### 2. Traceable Verdicts

Every diagnostic references:
- Original predicate ID
- Normalized obligation
- Fragment classification
- Proof artifact

→ Auditable results; no "magic" verdicts.

### 3. Fragment-First

Classify predicates *before* solving:
- QF_LIA → Z3 (fast, trusted)
- Finite-domain → enumeration (trivial)
- Outside-kernel → weaken or reject (transparent)

→ No surprising timeouts; explicit about limitations.

### 4. Graceful Degradation

Non-decidable predicates → warnings, not crashes.
Solver timeout → "unknown", not false positive.

→ Usable on partial code; gradual type migration.

---

## Success Metrics (Tier 1)

| Metric | Target | How to Measure |
|--------|--------|---|
| **Correctness** | 100% soundness | Proof certificates for all sat/unsat claims |
| **Completeness** | 95% of decidable predicates | Compare against Z3 in theory |
| **Performance** | <5s per 100-line file | Time each phase on complex.py |
| **Usability** | <5 false positives per 1KLOC | Manual review of diagnostics |
| **Code quality** | >80% test coverage | pytest coverage report |
| **Documentation** | >90% modules documented | docstring coverage |

---

## Risks & Mitigations

| Risk | Probability | Impact | Mitigation |
|------|---|---|---|
| Type inference underconstrained | Medium | Won't find bugs | Use predicates as hard constraints (not heuristics) |
| Solver timeouts | Medium | False negatives | Fragment classify first; set per-theory timeouts |
| IPA complexity explosion | Medium | Slow on large code | Lazy evaluation; cache-first design from day 1 |
| IDE latency | Low | Poor UX | Incremental checking; reuse cache across edits |
| Predicate + solver entanglement | Low | Hard to maintain | Strict module boundaries; separate tests for each |

---

## Dependency Chain

```
Phase 1: types/
    ↓
Phase 2: frontend/ + harvest/
    ↓↓
Phase 3: normalize/
    ↓
Phase 4: solver/
    ↓
Phase 5: explain/
    ↓
Phase 6: cli/ + lsp/
    ↓
Phase 7 (optional): interprocedural/
```

**Critical path**: Phases 1–4 (10 weeks) must be serial.  
**Parallel opportunities**: UI + IPA work can start after Phase 4.

---

## Testing Strategy

### Unit Tests (per-module)

- Each module has `test_<module>.py`
- Tests in `src/tests/test_*.py`
- Target: 80%+ coverage

### Integration Tests

- End-to-end pipeline on fixtures
- `fixtures/simple.py` – 5 LOC (MVP baseline)
- `fixtures/medium.py` – 30 LOC (core functionality)
- `fixtures/complex.py` – 100+ LOC (stress test)

### Regression Tests

- Keep failing cases from exploration
- Add as we discover bugs
- Prevent regressions

### Performance Tests

- Measure each phase (parse, harvest, infer, normalize, solve, explain)
- Target: <5s per 100 LOC

---

## Getting Started

### Week 0: Setup

1. Initialize `/Users/halleyyoung/Documents/div/mathdivergence/deppy/src/` structure (✓ done)
2. Copy foundational modules from `/src/` (types.py, domains/*, smt/*)
3. Set up pytest + CI/CD
4. Create fixtures (simple.py, medium.py, complex.py)

### Week 1: Phase 1 (types/)

1. Implement `types/base_type.py`
2. Implement `types/subtyping.py`
3. Implement `types/refinement_type.py`
4. Write 30+ tests
5. Validate on simple.py

### Ongoing

- Daily standup: blockers, progress, plan for next day
- Weekly review: test coverage, design decisions, risk updates
- Bi-weekly demo: working code on fixtures

---

## Success Criteria for MVP

- [ ] Type system: 100% tests passing
- [ ] Frontend: parse & elaborate 100-line functions
- [ ] Harvest: extract all guard patterns with provenance
- [ ] Normalize: classify 95%+ of predicates
- [ ] Solver: encode & solve refinement queries soundly
- [ ] Explain: generate diagnostics with source context
- [ ] CLI: `deppy check` works on fixtures
- [ ] LSP: basic hover + diagnostics in VS Code

---

## Recommended Reading Order

1. Start: **ARCHITECTURE.md** (this overview)
2. Deep dive: **REUSE_INVENTORY.md** (module-by-module mapping)
3. Structure: **PACKAGE_STRUCTURE.md** (directory layout)
4. Spec: Chapters 03, 07, 09 in deppy/*.tex

---

## References

**Exploration results**:
- Full module analysis: `/tmp/deppy_mapping.md` (60+ modules reviewed)

**Existing TensorGuard artifact**:
- Implementation: `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/`
- Specification: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/` (*.tex)

**Key papers & resources**:
- Refinement types: Dunfield & Pfenning (survey)
- Decidability: Tinelli & Zarba (Nelson-Oppen with finite domains)
- CEGAR: Clarke et al. (predicate abstraction)
- Z3: de Moura & Björner (SMT solver)

---

**Next step**: Begin Week 0 setup. Implement Phase 1 in parallel.

