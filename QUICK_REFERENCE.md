# DepPy Implementation: Quick Reference

**For detailed analysis, see**: ARCHITECTURE.md, REUSE_INVENTORY.md, IMPLEMENTATION_ROADMAP.md

---

## 1. Answer to Each Question

### Q1: Which modules suit each architecture area?

| Architecture Area | Best-Suited Modules | Count |
|---|---|---|
| **Frontend/elaboration** | guard_extractor, real_analyzer, scope_analyzer, ssa_passes, guard_grammar | 5 |
| **Predicate IR + harvesting** | guard_extractor, guard_domain, _exp/predicates/* | 6 |
| **Nominal/dependent types** | types.py, types_extended.py, tensor_shapes.py | 3 |
| **Contracts + IPA** | interprocedural.py, assume_guarantee.py, thread_modular.py | 3 |
| **Domain interfaces** | domains/{base,intervals,nullity,typetags,strings,product,widening} | 7 |
| **Normalization** | decidability.py, verifiable_fragment.py, unsat_core_cegar.py | 3 |
| **Decidability/fragment classification** | decidability.py, theory_combination_analysis.py, verifiable_fragment.py | 3 |
| **SMT solving** | smt/{encoder,z3_backend,theory_interface,solver,theory_combination} | 5 |
| **Diagnostics/export** | output/{report,sarif,html,pyi}, source_mapped_errors.py, proof_certificate.py | 6 |
| **CLI/LSP** | cli/{main,lsp,ci_runner}, integrations/vscode/ | 4 |

**Total: 45 existing modules identified for reuse**

---

### Q2: Foundational vs. Experimental?

#### ✓ Foundational (32 modules — safe to reuse directly)

```
Types:
  ✓ types.py (1843 LOC) — type hierarchy, clean design
  ✓ types_extended.py (3948 LOC) — structural subtyping
  ✓ tensor_shapes.py (1639 LOC) — dimension algebra

Predicates & Harvest:
  ✓ guard_extractor.py (900 LOC) — multi-pattern extraction
  ✓ guard_domain.py — abstract domain for guards
  ✓ guard_grammar.py — predicate taxonomy

Frontend & Flow:
  ✓ real_analyzer.py (2190 LOC) — flow-sensitive narrowing

Analysis & Contracts:
  ✓ interprocedural.py (940 LOC) — call graphs, analysis
  ✓ assume_guarantee.py — compositional verification
  ✓ thread_modular.py — effect typing (pattern)

Domains (7 modules):
  ✓ domains/base.py — Galois connections, **GOLD STANDARD**
  ✓ domains/{intervals,nullity,typetags,strings,product,widening,abstract_domains}

Fragment Classification:
  ✓ decidability.py (667 LOC) — complexity classes, fragment model
  ✓ verifiable_fragment.py — decidable subset definition
  ✓ theory_combination_analysis.py — Nelson-Oppen combination

Solver:
  ✓ smt/{encoder,z3_backend,theory_interface,solver} (5 modules)
  ✓ smt/theory_combination.py
  ✓ proof_certificate.py (900 LOC) — proof witnesses

Diagnostics:
  ✓ output/{report,sarif_reporter,html_report,pyi_generator} (4 modules)
  ✓ source_mapped_errors.py — error tracing
  ✓ cegar_explanation.py — counterexample analysis

CLI/LSP:
  ✓ cli/{main,lsp_server,ci_runner} (3 modules)
  ✓ pipeline.py (952 LOC) — orchestration
```

#### ◐ Solid Base (8 modules — needs refactoring)

```
  ◐ guard_domain.py — separate from solver
  ◐ _experimental/predicates/* — integrate into core
  ◐ scope_analyzer.py — consolidate with frontend
  ◐ ssa_passes.py — add to IR pipeline
  ◐ unsat_core_cegar.py — integrate with normalization
  ◐ cegar_explanation.py — clean up interface
  ◐ thread_modular.py — generalize effect typing
  ◐ assume_guarantee.py — API cleanup only
```

#### ✗ Experimental/Risky (9 modules — inspiration only, rebuild)

```
  ✗ type_inference_engine.py (55K LOC) — monolithic, conflates concerns
  ✗ python_ast_analyzer.py — too many responsibilities
  ✗ _experimental/refinement_lattice.py — solver + logic entangled
  ✗ guard_to_refinement.py — two concerns in one
  ✗ shape_cegar.py (3176 LOC) — domain-specific; generalize principles
  ✗ cegar_cpa.py — weak implementation; rethink
  ✗ denotational_semantics.py — incomplete spec
  ✗ cvc5_backend.py — nascent support
  ✗ parametric.py — polymorphism underdeveloped
```

---

### Q3: Proposed DepPy Package Layout

```
deppy/
├── *.tex (specification documents — keep)
├── ARCHITECTURE.md
├── REUSE_INVENTORY.md
├── IMPLEMENTATION_ROADMAP.md
├── PACKAGE_STRUCTURE.md
│
└── src/
    ├── frontend/              # [REUSE 5 modules + NEW elaborator]
    ├── predicates/            # [REUSE 6 modules]
    ├── harvest/               # [REUSE 1 + NEW 5 harvesters]
    ├── types/                 # [REUSE 3 modules + NEW 5 dep type modules]
    ├── domains/               # [REUSE 7 modules directly]
    ├── infer/                 # [NEW: candidate generation]
    ├── normalize/             # [REUSE 3 modules + NEW normalizers]
    ├── solver/                # [REUSE 5 modules + NEW query builder]
    ├── explain/               # [REUSE 6 modules + NEW counterexample]
    ├── interprocedural/       # [REUSE 3 modules + NEW contract inference]
    ├── cli/                   # [REUSE/ADAPT 4 modules]
    ├── lsp/                   # [NEW LSP handlers + REUSE server]
    ├── pipeline.py            # [REUSE + ADAPT main orchestrator]
    └── tests/                 # [NEW: 50+ test files + fixtures]
```

**Key principle**: Boundaries between modules are strict. Each has single responsibility.

---

### Q4: Minimum Viable Core

**7-phase implementation (12 weeks = ~3 months full-time)**

| Phase | Modules | Weeks | MVP? |
|-------|---------|-------|------|
| 1. **Types** | types/ | 2 | Foundation |
| 2. **Frontend + Harvest** | frontend/ir, harvest/, predicates/ | 2 | Input pipeline |
| 3. **Normalization** | normalize/ | 2 | Surface → core |
| 4. **Solver** | solver/ | 2 | Decision procedure |
| 5. **Diagnostics** | explain/ | 2 | User output |
| 6. **CLI** | cli/, lsp/ | 1 | Usability |
| 7. **IPA** (optional) | interprocedural/ | 2 | Multi-function |

**Tier 1 (Phases 1–6)**: Single-function Python → refinement types + diagnostics ✓  
**Tier 2 (Phase 7)**: Multi-function support (post-MVP)

**Resource**: 2 engineers × 12 weeks = 24 engineer-weeks

---

## 2. Concrete File Paths & Reuse Mapping

### Copy Directly (REUSE)

```
Source → Target
─────────────────────────────────────
/src/types.py → deppy/src/types/base_type.py, variables.py
/src/types_extended.py → deppy/src/types/subtyping.py
/src/guard_extractor.py → deppy/src/harvest/guard_harvester.py
/src/real_analyzer.py → deppy/src/frontend/ (reference)
/src/interprocedural.py → deppy/src/interprocedural/call_graph.py
/src/assume_guarantee.py → deppy/src/interprocedural/compositional.py
/src/domains/* (all 8) → deppy/src/domains/* (direct copy)
/src/decidability.py → deppy/src/normalize/fragment_classifier.py
/src/smt/encoder.py → deppy/src/solver/encoder.py
/src/smt/z3_backend.py → deppy/src/solver/z3_backend.py
/src/proof_certificate.py → deppy/src/explain/proof_certificate.py
/src/output/report.py → deppy/src/explain/diagnostic.py
/src/output/sarif_reporter.py → deppy/src/explain/sarif_exporter.py
/src/cli/main.py → deppy/src/cli/main.py
/src/cli/lsp_server.py → deppy/src/lsp/server.py
/src/pipeline.py → deppy/src/pipeline.py
```

### Adapt (light refactoring)

```
/src/_experimental/python_frontend/scope_analyzer.py
  → deppy/src/frontend/scope_analyzer.py

/src/_experimental/python_frontend/ssa_passes.py
  → deppy/src/frontend/ir/ssa_transforms.py

/src/_experimental/predicates/{templates,matching,lattice}.py
  → deppy/src/predicates/{templates,matching,lattice}.py

/src/unsat_core_cegar.py
  → deppy/src/normalize/minimization.py

/src/cegar_explanation.py
  → deppy/src/explain/counterexample.py
```

### Implement New (core architecture)

```
deppy/src/frontend/ir/core_term.py — Core term AST
deppy/src/frontend/ir/core_type.py — Core type AST
deppy/src/frontend/parser.py — Elaboration
deppy/src/types/refinement_type.py — {v: τ | φ}
deppy/src/types/dependent_type.py — Π types
deppy/src/types/sigma_type.py — Σ types
deppy/src/predicates/provenance.py — Source tracking
deppy/src/predicates/normalization.py — Simplification
deppy/src/harvest/{exception,comprehension,default,walrus,callsite}_harvester.py
deppy/src/infer/{candidate_generator,optimizer,constraint_generator}.py
deppy/src/normalize/{normalizer,symbol_elimination,arithmetic_classifier}.py
deppy/src/solver/{query_builder,result}.py
deppy/src/explain/{counterexample,contract_exporter}.py
deppy/src/interprocedural/{contract_inference,summary_cache}.py
deppy/src/cli/{commands,config_loader,project_runner}.py
deppy/src/lsp/{handlers,diagnostics}.py
```

---

## 3. Implementation Sequence (Recommended Order)

### Week 1–2: Phase 1 (Type System)

```bash
# Start here
1. deppy/src/types/base_type.py — Copy from /src/types.py
2. deppy/src/types/variables.py — Copy TypeVariable, RowVariable
3. deppy/src/types/subtyping.py — Copy from /src/types_extended.py
4. deppy/src/types/refinement_type.py — Implement {v: τ | φ}
5. deppy/src/types/dependent_type.py — Implement Π types
→ Write 30+ unit tests
→ Validate: is_subtype() works; VC generation works
```

### Week 3–4: Phase 2 (Frontend + Harvest)

```bash
6. deppy/src/frontend/ir/core_term.py — Core AST
7. deppy/src/frontend/parser.py — Parse + elaborate
8. deppy/src/harvest/guard_harvester.py — Copy from /src/guard_extractor.py
9. deppy/src/predicates/predicate.py — Copy predicates + add provenance
10. deppy/src/predicates/kinds.py — PredicateKind enum
→ Test: Parse simple.py, extract all guards
```

### Week 5–6: Phase 3 (Normalization)

```bash
11. deppy/src/normalize/fragment_classifier.py — Copy from /src/decidability.py
12. deppy/src/normalize/normalizer.py — Implement Norm: Pred ↝ Core
13. deppy/src/normalize/symbol_elimination.py — Remove unused vars
→ Test: Classify 95%+ of predicates; normalize to core forms
```

### Week 7–8: Phase 4 (Solver)

```bash
14. deppy/src/solver/encoder.py — Copy from /src/smt/encoder.py
15. deppy/src/solver/z3_backend.py — Copy from /src/smt/z3_backend.py
16. deppy/src/solver/query_builder.py — Build VC formulas
17. deppy/src/explain/proof_certificate.py — Copy from /src/proof_certificate.py
→ Test: Encode & solve refinement queries soundly
```

### Week 9–10: Phase 5 (Diagnostics)

```bash
18. deppy/src/explain/diagnostic.py — Copy from /src/output/report.py
19. deppy/src/explain/sarif_exporter.py — Copy from /src/output/sarif_reporter.py
20. deppy/src/explain/html_exporter.py — Copy from /src/output/html_report.py
21. deppy/src/explain/stub_generator.py — Copy from /src/output/pyi_generator.py
→ Test: Generate diagnostics; export SARIF; generate stubs
```

### Week 11–12: Phase 6 (CLI)

```bash
22. deppy/src/cli/main.py — Copy from /src/cli/main.py
23. deppy/src/cli/commands.py — Implement subcommands
24. deppy/src/lsp/server.py — Copy from /src/cli/lsp_server.py
→ Test: CLI works; LSP basic functionality
```

**Then**: Phase 7 (IPA) optional; integration testing; release prep.

---

## 4. File Path Quick Lookup

### Source (TensorGuard)

```
/Users/halleyyoung/Documents/div/mathdivergence/best2/
  refinement-type-inference-dynamic-lang/implementation/src/
```

### Specification

```
/Users/halleyyoung/Documents/div/mathdivergence/deppy/
  chapter03-dependent-python-core.tex
  chapter07-z3-decidable-core.tex
  chapter09-implementation-architecture.tex
```

### DepPy Target

```
/Users/halleyyoung/Documents/div/mathdivergence/deppy/src/
```

### Documentation

```
ARCHITECTURE.md (overview) ← START HERE
REUSE_INVENTORY.md (module-by-module mapping)
IMPLEMENTATION_ROADMAP.md (7 phases, detailed plan)
PACKAGE_STRUCTURE.md (directory layout + design)
QUICK_REFERENCE.md (this file)
```

---

## 5. Risk Summary & Mitigations

| Risk | Severity | Mitigation |
|------|----------|-----------|
| Predicate logic + solver entanglement | **HIGH** | Enforce strict module boundaries; separate tests |
| Type inference goes wrong | **HIGH** | Use predicates as hard constraints; no guessing |
| Normalization loses expressivity | **HIGH** | Start with QF_LIA only; test fragment classifier vs. reference |
| IPA complexity explosion | **MEDIUM** | Cache-first design; lazy evaluation from day 1 |
| IDE latency | **MEDIUM** | Incremental checking; reuse cache across edits |

---

## 6. Success Criteria (Tier 1 MVP)

- [ ] Phase 1: `is_subtype()` passes 30+ tests
- [ ] Phase 2: Parse & harvest on simple.py, medium.py
- [ ] Phase 3: Classify 95%+ of predicates without crash
- [ ] Phase 4: Z3 encoding soundness validated
- [ ] Phase 5: SARIF + HTML exports syntactically valid
- [ ] Phase 6: `deppy check myfile.py` works end-to-end
- [ ] Overall: **Zero false positives on fixtures**; **100% soundness**

---

## 7. Next Immediate Actions

1. ✓ Read: ARCHITECTURE.md (5 min)
2. ✓ Read: REUSE_INVENTORY.md for your assigned modules (10 min)
3. → Copy foundational modules to deppy/src/ (2 hours)
4. → Write Phase 1 tests (4 hours)
5. → Implement Phase 1 (2 weeks)

**Go!**

