# Dependent Type Core: Reusable Code Summary

## Quick Reference: Source Files → Target Modules

### TYPES (Type representations)
| Source File | Lines | Target Module | Key Classes |
|---|---|---|---|
| types.py | 111-583 | `types/base.py` | BaseType, IntType, ListType, ObjectType, UnionType |
| types.py | 57-104 | `types/base.py` | TypeVariable, RowVariable |
| types.py | 1150-1232 | `types/refinement.py` | RefinementType (α-equivalence) |
| types.py | 1243-1314 | `types/dependent.py` | DependentParam, DependentFunctionType |
| types.py | 1322-1391 | `types/schemes.py` | TypeScheme (polymorphism) |

**ACTION:** Add TensorType as explicit base type

### PREDICATES (Formula representations)
| Source File | Lines | Target Module | Key Classes |
|---|---|---|---|
| types.py | 589-743 | `predicates/linear.py` | LinearExpr, VarExpr, LenExpr, BinOpExpr |
| types.py | 750-1096 | `predicates/formula.py` | Predicate, TruePred, ComparisonPred, AndPred, OrPred |
| types.py | 1520-1585 | `predicates/simplify.py` | normalize_type, normalize_refinement, _simplify_pred |

**ACTION:** Add ExistsExpr, ForallExpr for full ∃/∀ coverage

### CORE (Subtyping, entailment, environments)
| Source File | Lines | Target Module | Key Classes |
|---|---|---|---|
| types.py | 1592-1668 | `core/subtyping.py` | is_subtype(t1, t2) → bool |
| types.py | 1671-1696 | `core/subtyping.py` | is_refinement_subtype(rt1, rt2, entailment_checker) |
| types.py | 1398-1486 | `core/substitution.py` | Substitution (type/row/expr variables) |
| types_extended.py | 1333-1451 | `core/environments.py` | TypeEnvironment (join/meet/widen) |
| types_extended.py | 1459-1570 | `core/guards.py` | Guard, GuardKind (type narrowing) |
| path_sensitive.py | 23-100 | `core/path_environment.py` | PathConstraint, PathContext (Φ) |

### SMT (Solver integration)
| Source File | Lines | Target Module | Key Classes |
|---|---|---|---|
| decidability.py | 67-150 | `smt/decidability.py` | ComplexityClass, TheoryFragment, identify_fragments |
| smt/encoder.py | ~53KB | `smt/encoding.py` | Z3Encoder (predicate → Z3 terms) |
| smt/z3_backend.py | ~55KB | `smt/solver.py` | Z3Backend (solver interface) |

---

## Proposed Package Structure

```
deppy/src/deppy/
├── types/
│   ├── __init__.py
│   ├── base.py                    # BaseType hierarchy, TypeVariable, RowVariable
│   ├── refinement.py              # RefinementType (α-equivalence support)
│   ├── dependent.py               # DependentParam, DependentFunctionType
│   ├── schemes.py                 # TypeScheme, polymorphism
│   └── constructors.py            # Factories and type builders
│
├── predicates/
│   ├── __init__.py
│   ├── linear.py                  # LinearExpr hierarchy
│   ├── formula.py                 # Predicate, atomic + boolean combinations
│   ├── simplify.py                # Normalization, simplification
│   └── substitution.py            # Predicate variable renaming
│
├── core/
│   ├── __init__.py
│   ├── subtyping.py               # is_subtype, is_refinement_subtype
│   ├── environments.py            # TypeEnvironment (Γ)
│   ├── path_environment.py        # PathContext (Φ)
│   ├── guards.py                  # Guard, type narrowing rules
│   ├── substitution.py            # Full substitution machinery
│   ├── typing.py                  # Judgment Γ;Φ ⊢ e:τ (stub)
│   └── normalization.py           # Type/predicate normalization
│
├── smt/
│   ├── __init__.py
│   ├── decidability.py            # Fragment classification
│   ├── normalization.py           # Source → core predicate pipeline
│   ├── encoding.py                # Predicate → Z3 terms
│   ├── entailment.py              # φ₁ ⊨ φ₂ via Z3
│   └── solver.py                  # SMT solver interface
│
└── __init__.py
```

---

## Implementation Phases

### Phase 1: Core Types (Week 1)
**Effort:** ~200 LOC (mostly copy-paste)
```
✓ types/base.py        (copy IntType, StrType, ObjectType, etc. from types.py)
✓ types/refinement.py  (copy RefinementType from types.py:1150-1232)
✓ types/dependent.py   (copy DependentParam, DependentFunctionType)
✓ Add TensorType       (NEW: explicit base type)
✓ Add TypeScheme       (copy from types.py:1322-1391)
```

### Phase 2: Predicates (Week 1)
**Effort:** ~150 LOC
```
✓ predicates/linear.py   (copy LinearExpr hierarchy from types.py:589-743)
✓ predicates/formula.py  (copy Predicate hierarchy from types.py:750-1096)
✓ Add ExistsExpr, ForallExpr (NEW: quantifier support)
✓ predicates/simplify.py (copy normalize_* from types.py:1520-1585)
```

### Phase 3: Core Machinery (Week 2)
**Effort:** ~250 LOC
```
✓ core/subtyping.py          (copy is_subtype, is_refinement_subtype)
✓ core/environments.py       (copy TypeEnvironment from types_extended.py)
✓ core/path_environment.py   (copy PathContext from path_sensitive.py)
✓ core/guards.py            (copy Guard, GuardKind, narrowing logic)
✓ core/substitution.py      (copy Substitution class)
```

### Phase 4: Verification Core (Week 2)
**Effort:** ~100 LOC (spec)
```
✓ core/typing.py            (stub typing judgments with signatures)
✓ Guard-refinement rule     (NEW: implement if-then-else type checking)
✓ Dependent application     (NEW: Π-elimination rule)
```

### Phase 5: SMT Integration (Week 3)
**Effort:** ~300 LOC
```
✓ smt/decidability.py     (extend from decidability.py)
✓ smt/normalization.py    (NEW: general predicate normalization)
✓ smt/encoding.py         (adapt from smt/encoder.py)
✓ smt/entailment.py       (NEW: Z3-backed entailment)
✓ smt/solver.py           (wrap smt/z3_backend.py)
```

---

## Critical Implementation Gaps

### Gap 1: Quantified Predicates
**LaTeX:** ∃x.φ, ∀x.φ
**Fix:** Add ExistsExpr, ForallExpr to predicates/formula.py

### Gap 2: Tensor as Base Type
**LaTeX:** τ ::= Tensor (line 38)
**Fix:** Add TensorType to types/base.py

### Gap 3: Object Type Predicates
**LaTeX:** Obj{φ}
**Fix:** Consider RefinedObjectType or extend ObjectType

### Gap 4: Mutation Safety
**LaTeX:** stab(φ) ∈ {stable, ephemeral, borrowed}
**Fix:** Add Stability(Enum) to Predicate

### Gap 5: Type Checking Judgment
**LaTeX:** Γ;Φ ⊢ e:τ
**Fix:** Implement core/typing.py with full rule set

---

## File Locations

**Source (reusable code):**
- `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
- `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types_extended.py`
- `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/path_sensitive.py`
- `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/decidability.py`
- `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/smt/*.py`

**Target:**
- `/Users/halleyyoung/Documents/div/mathdivergence/deppy/src/deppy/`

**Formal Spec (LaTeX):**
- `/Users/halleyyoung/Documents/div/mathdivergence/deppy/chapter03-dependent-python-core.tex`
- `/Users/halleyyoung/Documents/div/mathdivergence/deppy/chapter07-z3-decidable-core.tex`

---

## Total Reusable Code

- **types.py**: ~1,800 LOC
- **types_extended.py**: ~3,950 LOC (mostly type checking, not all useful)
- **Directly reusable**: ~2,500 LOC
- **Requires adaptation**: ~800 LOC
- **Requires new implementation**: ~400 LOC (predicates, quantifiers, mutation)

**Estimated effort:** 2-3 weeks for full core implementation
