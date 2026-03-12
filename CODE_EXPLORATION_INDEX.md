# Dependent Type Core: Code Exploration Index

**Date:** March 10, 2025
**Objective:** Map reusable code from existing implementation to formal dependent type specification
**Status:** ✓ COMPLETE

---

## 📋 Documentation Files

### 1. **REUSABLE_CODE_SUMMARY.md** ⭐ START HERE
   - **Best for:** Quick orientation, high-level overview
   - **Contents:**
     - Quick-reference table (source files → target modules)
     - 5 implementation phases with estimated effort
     - Critical gaps and fixes
     - File locations
   - **Length:** ~7.6 KB (quick read)

### 2. **REUSABLE_CODE_MAPPING.md** 📚 DETAILED REFERENCE
   - **Best for:** Developers implementing each module
   - **Contents:**
     - Part 1: Type Representations (5 sections)
     - Part 2: Predicate/Formula Representations (3 sections)
     - Part 3: Subtyping, Entailment, Environments (6 sections)
     - Part 4: Z3 Solver Integration (4 sections)
     - Part 5: Summary & Package Layout
     - Part 6: Critical Mismatches & Gaps
     - Part 7: Implementation Checklist
   - **Length:** ~26 KB (comprehensive reference)
   - **Key feature:** Each section maps LaTeX formal spec → source code → target module

### 3. **MODULE_ARCHITECTURE.txt** 🏗️ VISUAL REFERENCE
   - **Best for:** Understanding system design, data flow
   - **Contents:**
     - ASCII-art module hierarchy
     - Detailed class/function listings per module
     - Data flow diagram (AST → Type Checking → SMT)
     - Week-by-week implementation roadmap
   - **Length:** ~36 KB (visual reference)
     
---

## 🗂️ Organization

### Package Structure (Proposed)
```
deppy/src/deppy/
├── types/              (Type representations)
├── predicates/         (Formula/predicate language)
├── core/               (Subtyping, environments, type checking)
└── smt/                (Z3 solver integration)
```

### Source Code Locations
| Component | File | Size | Key Classes |
|-----------|------|------|-------------|
| **Types** | `//.../types.py` | 1,843 LOC | BaseType, RefinementType, DependentFunctionType |
| **Extended Types** | `//.../types_extended.py` | 3,948 LOC | TypeEnvironment, Guard, narrowing |
| **Path Sensitivity** | `//.../path_sensitive.py` | — | PathConstraint, PathContext |
| **Decidability** | `//.../decidability.py` | — | ComplexityClass, TheoryFragment |
| **SMT Backend** | `//.../smt/` | 350 KB | Z3Encoder, z3_backend |

### LaTeX Specification
| Chapter | File | Focus |
|---------|------|-------|
| **Chapter 3** | `chapter03-dependent-python-core.tex` | Type forms, judgments, rules |
| **Chapter 7** | `chapter07-z3-decidable-core.tex` | Fragment classification, normalization |

---

## 🎯 Quick Navigation

### For Implementation
1. **Week 1 (Types & Predicates):**
   - Go to REUSABLE_CODE_MAPPING.md → Part 1 (Type Representations)
   - Go to REUSABLE_CODE_MAPPING.md → Part 2 (Predicates)
   - Follow line numbers to source code

2. **Week 2 (Core Machinery):**
   - Go to REUSABLE_CODE_MAPPING.md → Part 3 (Subtyping & Environments)
   - Reference MODULE_ARCHITECTURE.txt for module interactions

3. **Week 3 (SMT Integration):**
   - Go to REUSABLE_CODE_MAPPING.md → Part 4 (Z3 Integration)
   - Check Part 6 for gaps (quantifiers, tensor type, mutation)

### For Understanding Gaps
- See REUSABLE_CODE_SUMMARY.md → "Critical Implementation Gaps"
- See REUSABLE_CODE_MAPPING.md → Part 6 → "Critical Mismatches & Gaps"
- Detailed action items for each gap

### For Architecture
- See MODULE_ARCHITECTURE.txt for ASCII-art module hierarchy
- See data flow diagram for type checking pipeline
- See implementation roadmap for parallelization opportunities

---

## 📊 Key Statistics

### Code Reusability
| Category | LOC | Status |
|----------|-----|--------|
| Directly reusable | ~2,500 | ✓ Ready (copy-paste) |
| Requires adaptation | ~800 | ⚠ Minor changes |
| New implementation | ~400 | 🆕 Missing in source |
| **Total effort** | **2-3 weeks** | ✅ Feasible |

### Coverage
- **Type representations:** ✓ 100% (with new TensorType)
- **Predicates:** ✓ 95% (missing quantifiers)
- **Subtyping & environment:** ✓ 100%
- **Path sensitivity:** ✓ 100%
- **SMT integration:** ✓ 80% (needs adaptation)
- **Type checking judgment:** 🆕 0% (needs implementation)

---

## ⚙️ Implementation Phases

### Phase 1: Core Types (Week 1)
**Effort:** ~200 LOC
- Copy base types (IntType, ListType, etc.)
- Copy RefinementType with α-equivalence
- Copy DependentFunctionType
- **[NEW]** Add TensorType, TypeScheme

### Phase 2: Predicates (Week 1)
**Effort:** ~150 LOC
- Copy LinearExpr hierarchy
- Copy Predicate hierarchy
- **[NEW]** Add ExistsExpr, ForallExpr for ∃/∀

### Phase 3: Core Machinery (Week 2)
**Effort:** ~250 LOC
- Copy subtyping functions
- Copy TypeEnvironment
- Copy PathContext
- Copy Guard machinery
- **[NEW]** Stub typing.py

### Phase 4: Type Checking (Week 2)
**Effort:** ~100 LOC (spec)
- Implement Γ;Φ ⊢ e:τ judgment
- Implement guard-refinement rule
- Implement dependent application

### Phase 5: SMT Integration (Week 3)
**Effort:** ~300 LOC
- Extend fragment classification
- **[NEW]** Source → core normalization
- Adapt Z3 encoding
- **[NEW]** Z3-backed entailment

---

## 🔍 Finding Specific Code

### "Where is RefinementType?"
1. Source: `types.py:1150-1232`
2. Target module: `types/refinement.py`
3. Details: REUSABLE_CODE_MAPPING.md → Part 1.2

### "Where is PathContext?"
1. Source: `path_sensitive.py:56-100`
2. Target module: `core/path_environment.py`
3. Details: REUSABLE_CODE_MAPPING.md → Part 3.4

### "What about quantified predicates?"
1. Status: 🆕 Missing from source
2. Action: Add ExistsExpr, ForallExpr to `predicates/formula.py`
3. Details: REUSABLE_CODE_MAPPING.md → Part 6 → Mismatch 1

### "Where is Z3 integration?"
1. Source: `smt/encoder.py` (53 KB), `smt/z3_backend.py` (55 KB)
2. Target modules: `smt/encoding.py`, `smt/entailment.py`
3. Details: REUSABLE_CODE_MAPPING.md → Part 4

---

## 📝 Implementation Checklist

Use REUSABLE_CODE_MAPPING.md → Part 7 for detailed checklist including:
- [ ] Week 1 tasks (types, predicates)
- [ ] Week 2 tasks (core machinery, type checking)
- [ ] Week 3 tasks (SMT integration)
- Unit tests for each phase
- Integration tests

---

## 🎓 Learning Path

**For someone new to the codebase:**

1. **Start:** REUSABLE_CODE_SUMMARY.md (5 min read)
2. **Understand:** MODULE_ARCHITECTURE.txt diagrams (10 min study)
3. **Deep dive:** REUSABLE_CODE_MAPPING.md Part 1 (types)
4. **Hands-on:** Copy types.py → deppy/src/deppy/types/base.py

**For implementation:**

1. **Reference:** MODULE_ARCHITECTURE.txt for module structure
2. **Map:** REUSABLE_CODE_MAPPING.md for each module
3. **Source:** Follow line numbers to types.py, types_extended.py, etc.
4. **Adapt:** Check Part 6 (gaps) for required changes
5. **Test:** Unit tests for each phase

---

## 🐛 Troubleshooting

### "Type XYZ doesn't match the LaTeX spec"
→ Check REUSABLE_CODE_MAPPING.md Part 6 for known mismatches

### "How do I implement the type checking judgment?"
→ See REUSABLE_CODE_MAPPING.md Part 3 → core/typing.py (stub)
→ See MODULE_ARCHITECTURE.txt → data flow diagram

### "What's the relationship between Γ and Φ?"
→ REUSABLE_CODE_MAPPING.md Part 3 → TypeEnvironment vs PathContext
→ MODULE_ARCHITECTURE.txt → core/ section

### "How does Z3 entailment work?"
→ REUSABLE_CODE_MAPPING.md Part 4.4 → EntailmentChecker
→ smt/entailment.py: Callback pattern in is_refinement_subtype

---

## ✅ Verification

All documents created and verified:
```
✓ REUSABLE_CODE_MAPPING.md (26 KB)
✓ REUSABLE_CODE_SUMMARY.md (7.6 KB)
✓ MODULE_ARCHITECTURE.txt (36 KB)
✓ CODE_EXPLORATION_INDEX.md (this file)
```

**Location:** `/Users/halleyyoung/Documents/div/mathdivergence/deppy/`

---

## 📞 Reference

**LaTeX formal spec sources:**
- `/Users/halleyyoung/Documents/div/mathdivergence/deppy/chapter03-dependent-python-core.tex`
- `/Users/halleyyoung/Documents/div/mathdivergence/deppy/chapter07-z3-decidable-core.tex`

**Implementation source:**
- `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/`

**Target package:**
- `/Users/halleyyoung/Documents/div/mathdivergence/deppy/src/deppy/`

---

Generated: March 10, 2025 | Status: ✅ Ready for implementation
