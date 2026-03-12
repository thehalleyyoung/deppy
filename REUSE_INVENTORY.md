# DepPy Reuse Inventory

**Last updated**: 2025-03-10

Mapping of existing TensorGuard modules to DepPy target packages, with recommended adaptation strategy for each.

---

## 1. Frontend / Elaboration

### ✓ REUSE: `guard_extractor.py`

- **Source**: `/src/guard_extractor.py` (900 LOC)
- **Target**: `deppy/src/harvest/guard_harvester.py`
- **Strategy**: Copy most of it. Rename `extract_guards()` → `harvest_guards()` for consistency.
- **Rationale**: Multi-pattern guard extraction is production-ready.
- **Dependencies**: Python AST, basic type hierarchy
- **Integration**: Feed output to `predicates/normalization.py`

### ✓ REUSE: `real_analyzer.py`

- **Source**: `/src/real_analyzer.py` (2190 LOC)
- **Target**: `deppy/src/frontend/` (as reference for flow-sensitive state)
- **Strategy**: Extract flow-sensitive type narrowing logic; integrate with elaborator.
- **Rationale**: Handles type tag narrowing, nullity refinement. Good prior art.
- **Dependencies**: Type environment, guard predicates
- **Integration**: Output feeds to `infer/candidate_generator.py`

### ◐ ADAPT: `scope_analyzer.py`

- **Source**: `/src/_experimental/python_frontend/scope_analyzer.py`
- **Target**: `deppy/src/frontend/scope_analyzer.py`
- **Strategy**: Copy + rename methods for consistency with DepPy naming.
- **Rationale**: Builds symbol tables, scopes, definitions. Essential for elaboration.
- **Dependencies**: Python AST
- **Integration**: Feeds into parser/elaborator

### ◐ ADAPT: `ssa_passes.py`

- **Source**: `/src/_experimental/python_frontend/ssa_passes.py`
- **Target**: `deppy/src/frontend/ir/ssa_transforms.py`
- **Strategy**: Integrate into IR transformation pipeline.
- **Rationale**: Normalizes control flow to SSA form. Useful for path-sensitive analysis.
- **Dependencies**: IR core term representation
- **Integration**: Applied after elaboration

### ✓ REUSE: `guard_grammar.py`

- **Source**: `/src/guard_grammar.py` (500 LOC)
- **Target**: `deppy/src/predicates/kinds.py` + `deppy/src/harvest/`
- **Strategy**: Copy guard pattern definitions directly.
- **Rationale**: Guard taxonomy is stable and comprehensive.
- **Integration**: Used by all harvesters

---

## 2. Predicates & Predicate IR

### ✓ REUSE: `guard_extractor.py` (Predicate data structures)

- **Components**: `Predicate`, `PredicateKind` classes
- **Target**: `deppy/src/predicates/predicate.py`
- **Strategy**: Copy classes; add provenance metadata.
- **Rationale**: Clean AST design; well-tested.

### ◐ ADAPT: `_experimental/predicates/templates.py`

- **Source**: `/src/_experimental/predicates/templates.py`
- **Target**: `deppy/src/predicates/templates.py`
- **Strategy**: Copy; may need cleanup for consistency.
- **Rationale**: Predicate template matching already formalized.
- **Risk**: Partial implementation; ensure completeness.

### ◐ ADAPT: `_experimental/predicates/matching.py`

- **Source**: `/src/_experimental/predicates/matching.py`
- **Target**: `deppy/src/predicates/matching.py`
- **Strategy**: Copy + integrate with `templates.py`.
- **Rationale**: Pattern-based extraction mechanism.

### ◐ ADAPT: `_experimental/predicates/lattice.py`

- **Source**: `/src/_experimental/predicates/lattice.py`
- **Target**: `deppy/src/predicates/lattice.py`
- **Strategy**: Copy + separate from Z3 encoding.
- **Rationale**: Boolean lattice operations (join, meet, widening).
- **Risk**: May be entangled with solver. Refactor carefully.

### [NEW] `predicates/provenance.py`

- **Target**: `deppy/src/predicates/provenance.py`
- **Design**: Add source tracking to all predicates:
  ```python
  @dataclass
  class Provenance:
      source: str  # "guard" | "assert" | "comprehension" | ...
      file: str
      line: int
      col: int
      confidence: float  # 0.0–1.0
  ```
- **Rationale**: Every diagnostic must be traceable.

### [NEW] `predicates/normalization.py`

- **Target**: `deppy/src/predicates/normalization.py`
- **Design**: Simplify predicates before sending to solver:
  - Flatten nested boolean ops
  - Eliminate tautologies/contradictions
  - Rename variables to canonical form
- **Integration**: Called before `normalize/fragment_classifier.py`

---

## 3. Nominal & Dependent Types

### ✓ REUSE: `types.py`

- **Source**: `/src/types.py` (1843 LOC)
- **Target**: `deppy/src/types/base_type.py` + `variables.py`
- **Strategy**: Copy class hierarchy: `BaseType`, `IntType`, `StrType`, etc.
- **Rationale**: Clean, tested design. Minimal changes needed.
- **Components to reuse**:
  - `TypeVariable`, `RowVariable` → `types/variables.py`
  - `BaseType` hierarchy (Int, Str, Bool, None, List, Dict, Set, Tuple, Function, Union, Object)
  - Basic subtyping check (move to `types/subtyping.py`)

### ✓ REUSE: `types_extended.py`

- **Source**: `/src/types_extended.py` (3948 LOC)
- **Target**: `deppy/src/types/subtyping.py`
- **Strategy**: Copy `is_subtype()` and related checkers.
- **Rationale**: Robust structural subtyping; handles unions, generics, callable types.
- **Key methods**:
  - `is_subtype(ty1, ty2)`
  - `_callable_subtype()`
  - `_structural_subtype()`
  - `_class_subtype()`

### [NEW] `types/refinement_type.py`

- **Target**: `deppy/src/types/refinement_type.py`
- **Design**: Refinement type {v: τ | φ}
  ```python
  @dataclass
  class RefinementType:
      var: str  # bound variable
      base_type: BaseType
      predicate: Predicate
  ```
- **Operations**:
  - Refinement subtyping (VC generation)
  - Predicate substitution
  - Meet / join

### [NEW] `types/dependent_type.py`

- **Target**: `deppy/src/types/dependent_type.py`
- **Design**: Dependent function type Π(x:τ₁).τ₂
  ```python
  @dataclass
  class DependentFunctionType:
      param_name: str
      param_type: Type  # Can be refinement
      return_type: Type  # Can mention param
  ```
- **Operations**:
  - Type application / instantiation
  - Dependency checking

### [NEW] `types/sigma_type.py`

- **Target**: `deppy/src/types/sigma_type.py`
- **Design**: Dependent pair / witness type Σ(x:τ₁).τ₂
- **Operations**: Projection, construction

### [NEW] `types/contract.py`

- **Target**: `deppy/src/types/contract.py`
- **Design**: Pre/post conditions
  ```python
  @dataclass
  class Contract:
      precondition: Optional[Predicate]
      postcondition: Optional[Predicate]
      effect_type: Optional[Effect]  # IO, mutation, exceptions
  ```

### [NEW] `types/environment.py`

- **Target**: `deppy/src/types/environment.py`
- **Design**: Type environment Γ (bindings of vars to types)
  ```python
  class TypeEnvironment:
      bindings: Dict[str, Type]
      parent: Optional[TypeEnvironment]
      def lookup(var: str) -> Type
  ```

### ✓ REUSE: `tensor_shapes.py`

- **Source**: `/src/tensor_shapes.py` (1639 LOC)
- **Target**: `deppy/src/types/` (reference for shape predicates)
- **Strategy**: Extract tensor-specific logic; make domain-agnostic.
- **Rationale**: Dimension algebra is a good example of specialized predicate language.
- **Integration**: Domain-specific; use as template for other domains.

---

## 4. Abstract Domains

### ✓ REUSE: All domain modules in `/src/domains/`

Copy these modules directly with minimal changes:

| Module | LOC | Target | Strategy |
|--------|-----|--------|----------|
| `base.py` | 600 | `deppy/src/domains/base.py` | **REUSE** – Gold standard |
| `intervals.py` | 400 | `deppy/src/domains/intervals.py` | REUSE |
| `nullity.py` | 300 | `deppy/src/domains/nullity.py` | REUSE |
| `typetags.py` | 350 | `deppy/src/domains/typetags.py` | REUSE |
| `strings.py` | 250 | `deppy/src/domains/strings.py` | REUSE |
| `product.py` | 200 | `deppy/src/domains/product.py` | REUSE |
| `widening.py` | 150 | `deppy/src/domains/widening.py` | REUSE |
| `abstract_domains.py` | 400 | `deppy/src/domains/abstract_domains.py` | REUSE |

**Rationale**: These modules embody the Galois connection formalism. They are production-ready.

### [NEW] `domains/interface.py`

- **Target**: `deppy/src/domains/interface.py`
- **Design**: Domain registry and lookup
  ```python
  DOMAINS: Dict[str, Type[AbstractDomain]] = {
      "intervals": IntervalDomain,
      "nullity": NullityDomain,
      "typetags": TypeTagDomain,
      ...
  }
  ```
- **Integration**: Used by `infer/candidate_generator.py` to pick domains

---

## 5. Interprocedural Analysis & Contracts

### ✓ REUSE: `interprocedural.py`

- **Source**: `/src/interprocedural.py` (940 LOC)
- **Target**: `deppy/src/interprocedural/call_graph.py`
- **Strategy**: Copy `CallGraph`, `nullity_analysis()` classes.
- **Rationale**: Call graph construction is solid.
- **Components**:
  - `CallGraph` class
  - `CallSite` data structure
  - Transitive closure methods

### ✓ REUSE: `assume_guarantee.py`

- **Source**: `/src/assume_guarantee.py` (large)
- **Target**: `deppy/src/interprocedural/compositional.py`
- **Strategy**: Copy compositional verification logic.
- **Rationale**: Assume-guarantee framework is elegant and sound.
- **Integration**: Called from `pipeline.py` for multi-function code

### ◐ ADAPT: `thread_modular.py`

- **Source**: `/src/thread_modular.py` (940 LOC)
- **Target**: `deppy/src/interprocedural/effect_analysis.py` (for inspiration)
- **Strategy**: Extract thread-safety reasoning; generalize to other effects.
- **Rationale**: Demonstrates effect typing (IO, mutation, exceptions).
- **Risk**: Domain-specific (threading). Extract principles, not code.

---

## 6. Fragment Classification & Normalization

### ✓ REUSE: `decidability.py`

- **Source**: `/src/decidability.py` (667 LOC)
- **Target**: `deppy/src/normalize/fragment_classifier.py`
- **Strategy**: Copy `ComplexityClass`, `TheoryFragment` enums; adapt predicates to general Python.
- **Rationale**: Fragment classification model is mathematically sound.
- **Key components**:
  - `ComplexityClass` enum (P, NP_HARD)
  - `TheoryFragment` enum
  - Fragment detection logic
- **Adaptation**: Generalize from shape/device/phase to all predicate types.

### ✓ REUSE: `verifiable_fragment.py`

- **Source**: `/src/verifiable_fragment.py` (667 LOC)
- **Target**: `deppy/src/normalize/` (reference)
- **Strategy**: Use as specification; implement custom for general predicates.
- **Rationale**: Defines which fragments are safe for solver.

### ◐ ADAPT: `unsat_core_cegar.py`

- **Source**: `/src/unsat_core_cegar.py` (1036 LOC)
- **Target**: `deppy/src/normalize/minimization.py`
- **Strategy**: Extract unsat-core extraction; use for predicate minimization.
- **Rationale**: Minimal predicates → smaller VCs → faster solving.
- **Integration**: Post-processing in normalization pipeline.

### ✓ REUSE: `theory_combination_analysis.py`

- **Source**: `/src/theory_combination_analysis.py` (878 LOC)
- **Target**: `deppy/src/normalize/` (reference)
- **Strategy**: Reference for Nelson-Oppen combination.
- **Rationale**: Multi-domain theories require careful combination.

### [NEW] `normalize/normalizer.py`

- **Target**: `deppy/src/normalize/normalizer.py`
- **Design**: Main normalization pass
  ```python
  def normalize(pred: Predicate) -> Union[Predicate, OutsideKernel]:
      # 1. Simplify (flatten, tautology elimination)
      # 2. Fragment classify
      # 3. If decidable: return
      # 4. If undecidable: return OutsideKernel
  ```

### [NEW] `normalize/symbol_elimination.py`

- **Target**: `deppy/src/normalize/symbol_elimination.py`
- **Design**: Remove variables that don't appear in conclusion
  ```python
  def eliminate_symbols(vc: VerificationCondition) -> VerificationCondition
  ```

---

## 7. SMT Solving

### ✓ REUSE: `smt/encoder.py`

- **Source**: `/src/smt/encoder.py` (large)
- **Target**: `deppy/src/solver/encoder.py`
- **Strategy**: Copy predicate-to-Z3 translation.
- **Rationale**: Sound encoding of refinement predicates.
- **Key methods**:
  - `encode_predicate(pred: Predicate) -> z3.ExprRef`
  - `encode_subtyping(s: RefinementType, t: RefinementType) -> z3.BoolRef`

### ✓ REUSE: `smt/z3_backend.py`

- **Source**: `/src/smt/z3_backend.py`
- **Target**: `deppy/src/solver/z3_backend.py`
- **Strategy**: Copy Z3 API wrapper.
- **Rationale**: Stable interface to Z3.

### ✓ REUSE: `smt/theory_interface.py`

- **Source**: `/src/smt/theory_interface.py`
- **Target**: `deppy/src/solver/theory_interface.py`
- **Strategy**: Copy abstract solver interface.
- **Rationale**: Allows swapping solvers (Z3, CVC5, dReal) later.

### ✓ REUSE: `smt/solver.py`

- **Source**: `/src/smt/solver.py` (large)
- **Target**: `deppy/src/solver/solver.py`
- **Strategy**: Copy top-level solver entry point.
- **Rationale**: Query formatting, result handling.

### ✓ REUSE: `smt/theory_combination.py`

- **Source**: `/src/smt/theory_combination.py`
- **Target**: `deppy/src/solver/theory_combination.py`
- **Strategy**: Copy Nelson-Oppen combination.
- **Rationale**: Multi-theory queries.

### ✓ REUSE: `smt/distinctness_axioms.py`

- **Source**: `/src/smt/distinctness_axioms.py`
- **Target**: `deppy/src/solver/` (reference)
- **Strategy**: Use as example of custom axioms.
- **Rationale**: Tag distinctness is important for type reasoning.

### [NEW] `solver/query_builder.py`

- **Target**: `deppy/src/solver/query_builder.py`
- **Design**: Build verification condition formulas
  ```python
  def build_vc(obligations: List[Obligation]) -> z3.BoolRef:
      # Combine predicates + type constraints
  ```

### [NEW] `solver/result.py`

- **Target**: `deppy/src/solver/result.py`
- **Design**: Solver result types
  ```python
  @dataclass
  class SolverResult:
      status: Literal["sat", "unsat", "unknown"]
      model: Optional[z3.ModelRef]
      proof: Optional[str]
      time_ms: float
  ```

---

## 8. Diagnostics & Output

### ✓ REUSE: `output/report.py`

- **Source**: `/src/output/report.py` (large)
- **Target**: `deppy/src/explain/diagnostic.py`
- **Strategy**: Copy `Diagnostic`, `Severity`, `BugCategory` classes.
- **Rationale**: LSP-compatible diagnostic format.

### ✓ REUSE: `output/sarif_reporter.py`

- **Source**: `/src/output/sarif_reporter.py`
- **Target**: `deppy/src/explain/sarif_exporter.py`
- **Strategy**: Copy SARIF export logic.
- **Rationale**: CI integration (GitHub, GitLab, etc.).

### ✓ REUSE: `output/html_report.py`

- **Source**: `/src/output/html_report.py`
- **Target**: `deppy/src/explain/html_exporter.py`
- **Strategy**: Copy HTML generation.
- **Rationale**: Human-readable output.

### ✓ REUSE: `output/pyi_generator.py`

- **Source**: `/src/output/pyi_generator.py`
- **Target**: `deppy/src/explain/stub_generator.py`
- **Strategy**: Copy stub generation logic.
- **Rationale**: Export inferred types as `.pyi` stubs.

### ✓ REUSE: `proof_certificate.py`

- **Source**: `/src/proof_certificate.py` (900 LOC)
- **Target**: `deppy/src/explain/proof_certificate.py`
- **Strategy**: Copy proof witness structure.
- **Rationale**: Auditable verification results.
- **Key components**:
  - `ProofCertificate` dataclass
  - Proof artifact generation
  - Certificate serialization

### ✓ REUSE: `source_mapped_errors.py`

- **Source**: `/src/source_mapped_errors.py` (484 LOC)
- **Target**: `deppy/src/explain/source_mapper.py`
- **Strategy**: Copy source location tracking.
- **Rationale**: Diagnostic → source position mapping.

### ◐ ADAPT: `cegar_explanation.py`

- **Source**: `/src/cegar_explanation.py` (large)
- **Target**: `deppy/src/explain/counterexample.py`
- **Strategy**: Copy counterexample analysis logic; adapt to general predicates.
- **Rationale**: Explain why refinement was needed.

### [NEW] `explain/contract_exporter.py`

- **Target**: `deppy/src/explain/contract_exporter.py`
- **Design**: Export inferred contracts
  ```python
  def export_contracts(functions: List[Function]) -> str:
      # Export as Python type comments or .deppy files
  ```

---

## 9. CLI & Language Server

### ✓ REUSE: `cli/main.py`

- **Source**: `/src/cli/main.py` (1000+ LOC)
- **Target**: `deppy/src/cli/main.py`
- **Strategy**: Copy CLI skeleton; adapt subcommands.
- **Rationale**: Argparse-based CLI is solid.
- **Subcommands**:
  - `check` – analyze files
  - `export` – generate stubs / contracts
  - `explain` – show proof certificates

### ✓ REUSE: `cli/lsp_server.py`

- **Source**: `/src/cli/lsp_server.py` (large)
- **Target**: `deppy/src/lsp/server.py`
- **Strategy**: Copy LSP server implementation.
- **Rationale**: VS Code integration ready.

### ✓ REUSE: `cli/ci_runner.py`

- **Source**: `/src/cli/ci_runner.py`
- **Target**: `deppy/src/cli/project_runner.py`
- **Strategy**: Copy batch analysis + caching.
- **Rationale**: Efficient project-wide checking.

### [NEW] `cli/commands.py`

- **Target**: `deppy/src/cli/commands.py`
- **Design**: Subcommand implementations
  ```python
  def cmd_check(files: List[str], config: Config) -> Results
  def cmd_export(files: List[str], format: str) -> None
  def cmd_explain(file: str, line: int) -> None
  ```

### [NEW] `cli/config_loader.py`

- **Target**: `deppy/src/cli/config_loader.py`
- **Design**: Load `.deppy.yaml` configuration
  ```yaml
  # .deppy.yaml
  solver: z3
  timeout_ms: 5000
  trust_outside_kernel: false
  domains: [intervals, nullity, typetags]
  ```

---

## 10. Orchestration

### ✓ REUSE: `pipeline.py`

- **Source**: `/src/pipeline.py` (952 LOC)
- **Target**: `deppy/src/pipeline.py`
- **Strategy**: Copy main orchestrator logic.
- **Rationale**: Already implements parse → harvest → infer → solve → explain.
- **Adaptation**: Ensure it calls new DepPy modules (types, normalize, etc.).

---

## Summary: Module Reuse by Target

| DepPy Target | Source Modules | Count | Effort |
|--------------|---|---|---|
| `frontend/` | guard_extractor, real_analyzer, scope_analyzer, ssa_passes, guard_grammar | 5 | 2w |
| `predicates/` | guard_extractor, _exp/predicates/{templates,matching,lattice} | 4 | 1.5w |
| `harvest/` | guard_extractor | 1 | 0.5w |
| `types/` | types, types_extended, tensor_shapes | 3 | 1w |
| `domains/` | domains/* (8 modules) | 8 | 0.5w |
| `normalize/` | decidability, verifiable_fragment, unsat_core_cegar, theory_combination_analysis | 4 | 1.5w |
| `solver/` | smt/{encoder,z3_backend,theory_interface,solver,theory_combination,distinctness_axioms}, proof_certificate | 7 | 1w |
| `explain/` | output/{report,sarif,html,pyi}, source_mapped_errors, proof_certificate, cegar_explanation | 7 | 1.5w |
| `interprocedural/` | interprocedural, assume_guarantee, thread_modular | 3 | 1w |
| `cli/` + `lsp/` | cli/{main,lsp,ci}, integrations/vscode | 4 | 1.5w |
| `pipeline.py` | pipeline | 1 | 0.5w |
| **Total Reuse** | 47 existing modules | **47** | **~13w** |
| **New Components** | (core IR, frontend IR, new normalizers, ...) | — | **~8w** |
| **Testing + Integration** | — | — | **~3w** |
| **GRAND TOTAL** | | | **~24w** |

---

## Risk Assessment

| Risk | Mitigation |
|------|-----------|
| Predicate + Solver entanglement | Start with predicates in isolation; solver added later. |
| Fragment classifier too strict | Test with reference `decidability.py`. Document assumptions. |
| Missing harvesters | Implement one at a time; test each against guard taxonomy. |
| Type inference divergence | Use predicates as hard constraints; don't guess. |
| IPA scalability | Cache-first design. Lazy evaluation. |

