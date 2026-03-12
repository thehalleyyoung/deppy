# DepPy Package Structure

Created: 2025-03-10

## Directory Layout

```
/Users/halleyyoung/Documents/div/mathdivergence/deppy/
├── *.tex                              # Specification documents (LaTeX)
├── main.pdf                           # Compiled specification
├── ARCHITECTURE.md                    # This architecture guide
├── PACKAGE_STRUCTURE.md               # This file
├── REUSE_INVENTORY.md                 # Detailed module inventory
├── README.md                          # Getting started
├── setup.py                           # Package metadata
│
└── src/
    ├── __init__.py
    ├── config.py                      # Global configuration & constants
    ├── version.py                     # Version info
    │
    ├── frontend/                      # Parsing, elaboration, IR construction
    │   ├── __init__.py
    │   ├── parser.py                  # Python AST → Core IR [NEW]
    │   ├── cfg.py                     # Control-flow graph [NEW]
    │   ├── elaborator.py              # Surface → Core elaboration [NEW]
    │   ├── scope_analyzer.py          # [ADAPT: @exp/python_frontend]
    │   ├── ir/
    │   │   ├── __init__.py
    │   │   ├── core_term.py           # Core term AST (e, λx.e, if/let) [NEW]
    │   │   ├── core_type.py           # Core type AST (τ ::= int | list | ...) [NEW]
    │   │   └── visitors.py            # IR traversal & pattern matching [NEW]
    │
    ├── predicates/                    # Canonical predicate representation
    │   ├── __init__.py
    │   ├── predicate.py               # [ADAPT: guard_extractor.py Predicate]
    │   ├── kinds.py                   # PredicateKind enum
    │   ├── provenance.py              # Source tracking [NEW]
    │   ├── templates.py               # [ADAPT: @exp/predicates/templates]
    │   ├── matching.py                # [ADAPT: @exp/predicates/matching]
    │   ├── lattice.py                 # [ADAPT: @exp/predicates/lattice]
    │   └── normalization.py           # Simplify & normalize predicates [NEW]
    │
    ├── harvest/                       # Multi-source predicate extraction
    │   ├── __init__.py
    │   ├── multi_source.py            # Orchestrate all harvesters [NEW]
    │   ├── guard_harvester.py         # [ADAPT: guard_extractor.py]
    │   ├── exception_harvester.py     # Extract from except/finally [NEW]
    │   ├── comprehension_harvester.py # Extract from comprehension filters [NEW]
    │   ├── default_harvester.py       # Extract from default values [NEW]
    │   ├── walrus_harvester.py        # Extract from := (walrus) [NEW]
    │   └── callsite_harvester.py      # Extract from call sites [NEW]
    │
    ├── types/                         # Nominal and dependent types
    │   ├── __init__.py
    │   ├── base_type.py               # [ADAPT: types.py BaseType hierarchy]
    │   ├── variables.py               # [ADAPT: types.py TypeVariable, RowVariable]
    │   ├── refinement_type.py         # {v: τ | φ} [NEW]
    │   ├── dependent_type.py          # Π(x:τ₁).τ₂ [NEW]
    │   ├── sigma_type.py              # Σ(x:τ₁).τ₂ [NEW]
    │   ├── contract.py                # Pre/post conditions [NEW]
    │   ├── object_protocol.py         # Obj{φ} structural types [NEW]
    │   ├── subtyping.py               # [ADAPT: types_extended.py is_subtype]
    │   ├── unification.py             # Type unification [NEW]
    │   └── environment.py             # Type environment (Γ) [NEW]
    │
    ├── domains/                       # Abstract domains (reused directly)
    │   ├── __init__.py
    │   ├── base.py                    # [REUSE: @src/domains/base.py]
    │   ├── intervals.py               # [REUSE]
    │   ├── nullity.py                 # [REUSE]
    │   ├── typetags.py                # [REUSE]
    │   ├── strings.py                 # [REUSE]
    │   ├── product.py                 # [REUSE]
    │   ├── widening.py                # [REUSE]
    │   ├── abstract_domains.py        # [REUSE]
    │   └── interface.py               # Domain registry [NEW]
    │
    ├── infer/                         # Candidate generation & optimization
    │   ├── __init__.py
    │   ├── candidate_generator.py     # Generate refinement candidates [NEW]
    │   ├── optimizer.py               # Select best candidate set [NEW]
    │   ├── constraint_generator.py    # Generate verification conditions [NEW]
    │   └── refinement_loop.py         # CEGAR-style refinement [NEW]
    │
    ├── normalize/                     # Source → Core lowering
    │   ├── __init__.py
    │   ├── normalizer.py              # Norm: Pred ↝ Core [NEW]
    │   ├── fragment_classifier.py     # [ADAPT: decidability.py patterns]
    │   ├── symbol_elimination.py      # Variable elimination [NEW]
    │   ├── arithmetic_classifier.py   # Classify arithmetic [NEW]
    │   ├── finite_domain_encoder.py   # Encode finite domains [NEW]
    │   └── outside_kernel.py          # Handle non-decidable [NEW]
    │
    ├── solver/                        # SMT encoding & solving
    │   ├── __init__.py
    │   ├── encoder.py                 # [ADAPT: smt/encoder.py]
    │   ├── z3_backend.py              # [REUSE: smt/z3_backend.py]
    │   ├── theory_interface.py        # [REUSE: smt/theory_interface.py]
    │   ├── solver.py                  # [REUSE: smt/solver.py]
    │   ├── theory_combination.py      # [REUSE: smt/theory_combination.py]
    │   ├── query_builder.py           # Build VC formulas [NEW]
    │   └── result.py                  # Solver result types [NEW]
    │
    ├── explain/                       # Diagnostics & proof artifacts
    │   ├── __init__.py
    │   ├── diagnostic.py              # [ADAPT: output/report.py Diagnostic]
    │   ├── proof_certificate.py       # [ADAPT: proof_certificate.py]
    │   ├── counterexample.py          # Analyze counterexamples [NEW]
    │   ├── source_mapper.py           # [ADAPT: source_mapped_errors.py]
    │   ├── sarif_exporter.py          # [ADAPT: output/sarif_reporter.py]
    │   ├── html_exporter.py           # [ADAPT: output/html_report.py]
    │   ├── stub_generator.py          # [ADAPT: output/pyi_generator.py]
    │   └── contract_exporter.py       # Export contracts [NEW]
    │
    ├── interprocedural/               # Cross-function analysis
    │   ├── __init__.py
    │   ├── call_graph.py              # [ADAPT: interprocedural.py CallGraph]
    │   ├── contract_inference.py      # Infer function contracts [NEW]
    │   ├── summary_cache.py           # Cache summaries [NEW]
    │   └── effect_analysis.py         # Purity, taint, escapes [NEW]
    │
    ├── cli/                           # Command-line interface
    │   ├── __init__.py
    │   ├── main.py                    # [ADAPT: cli/main.py]
    │   ├── commands.py                # Subcommands [NEW]
    │   ├── config_loader.py           # Load .deppy.yaml [NEW]
    │   └── project_runner.py          # Batch analysis [NEW]
    │
    ├── lsp/                           # Language Server Protocol
    │   ├── __init__.py
    │   ├── server.py                  # [ADAPT: cli/lsp_server.py]
    │   ├── handlers.py                # LSP handlers [NEW]
    │   └── diagnostics.py             # Convert to LSP format [NEW]
    │
    ├── pipeline.py                    # [ADAPT: pipeline.py] Main orchestrator
    │
    └── tests/
        ├── __init__.py
        ├── conftest.py                # pytest fixtures
        ├── test_types.py              # Type system tests
        ├── test_predicates.py         # Predicate IR tests
        ├── test_harvest.py            # Guard extraction tests
        ├── test_normalize.py          # Normalization tests
        ├── test_solver.py             # SMT solving tests
        ├── test_frontend.py           # Parser/elaborator tests
        ├── test_integration.py        # End-to-end tests
        └── fixtures/                  # Test code samples
            ├── simple.py              # 5–10 LOC programs
            ├── medium.py              # 30–50 LOC
            └── complex.py             # 100+ LOC, multi-function
```

## Legend

| Prefix | Meaning |
|--------|---------|
| `[REUSE: ...]` | Copy code directly (no changes) |
| `[ADAPT: ...]` | Copy + light refactoring (method rename, interface cleanup) |
| `[NEW]` | Implement from scratch (inspired by spec + adjacent modules) |

## Phase Mapping

### Phase 1: Core Type System (Week 1–2)
- `frontend/ir/{core_term, core_type, visitors}`
- `types/{base_type, variables, refinement_type, dependent_type, subtyping}`

### Phase 2: Frontend + Harvest (Week 3–4)
- `frontend/{parser, cfg, elaborator, scope_analyzer}`
- `harvest/{multi_source, guard_harvester, ...}`
- `predicates/{predicate, kinds, provenance}`

### Phase 3: Normalization (Week 5–6)
- `normalize/{normalizer, fragment_classifier, symbol_elimination, ...}`

### Phase 4: Solving (Week 7–8)
- `solver/{encoder, z3_backend, query_builder}`
- `explain/{diagnostic, proof_certificate}`

### Phase 5: Diagnostics + CLI (Week 9–10)
- `explain/{sarif_exporter, html_exporter, stub_generator}`
- `cli/{main, commands}`

### Phase 6: IPA (Week 11+, optional)
- `interprocedural/{call_graph, contract_inference, summary_cache}`

## Key Design Principles

1. **Separation of concerns**: Predicates (logic) ≠ Solver (Z3). Harvest (extraction) ≠ Normalize (simplification).

2. **Traceable verdicts**: Every diagnostic references a pipeline artifact (predicate ID, normalized obligation, fragment class, proof).

3. **Composable domains**: Each domain in `domains/` is independent. Product domain combines them cleanly.

4. **Sound encoding**: Every solver query is traceable to a VC in `normalize/` output.

5. **Graceful degradation**: Non-decidable predicates → outside-kernel classification, not crashes.

## Configuration

Global settings in `src/config.py`:
- SMT solver timeouts
- Verbosity levels
- Fragment classifier thresholds
- Cache directories
- Trust boundaries (what solver to use for each fragment)

## Testing Strategy

- **Unit tests**: Each module tests in isolation (e.g., `test_types.py` → `types/`)
- **Integration tests**: Full pipeline on fixtures (simple.py → complex.py)
- **Regression tests**: Known bugs from artifact stay fixed
- **Performance tests**: Scalability on 1K–10K LOC codebases

