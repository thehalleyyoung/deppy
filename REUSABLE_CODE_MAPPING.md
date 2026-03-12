# Dependent Type Core: Reusable Code Mapping

## Executive Summary
This document maps reusable components from `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src` 
to the formal dependent type system described in the LaTeX monograph in `deppy/*.tex`. The mapping aligns with the proposed package structure:
```
deppy/src/deppy/
├── types/          # Type representations
├── predicates/     # Formula/predicate language
├── core/           # Core machinery (subtyping, entailment, environments)
└── smt/            # Z3 solver integration
```

---

## Part 1: TYPE REPRESENTATIONS
### Formal Specification
**LaTeX Source:** `deppy/chapter03-dependent-python-core.tex` (lines 31-45)

Type forms:
```
τ ::= α | int | bool | str | float | None | Tensor
    | list[τ] | dict[τ,τ] | tuple[τ₁,…,τₙ]
    | {v:τ | φ}                       (refinement)
    | Π(x:τ₁).τ₂                      (dependent function)
    | Σ(x:τ₁).τ₂                      (dependent pair)
    | τ₁ + τ₂                         (union)
    | Obj{φ}                          (structural object)
```

### Reusable Code Mapping

#### 1.1 Base Type Hierarchy
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 111-583

**Classes to reuse:**
- `BaseType` (ABC, lines 111-154) – abstract root
- `IntType`, `StrType`, `BoolType`, `NoneType_` (lines 159-254) – base types
- `ListType` (lines 258-281) – generic container
- `TupleType` (lines 285-310)
- `DictType` (lines 314-339)
- `SetType` (lines 343-365)
- `FunctionType` (lines 369-415) – simple function type
- `ObjectType` (lines 450-503) – structural types with row variables
- `UnionType` (lines 419-446) – τ₁ + τ₂
- `TypeVariable`, `RowVariable` (lines 57-104) – polymorphic type variables
- `AnyType`, `NeverType` (lines 534-582) – lattice top/bottom

**Recommended first-pass module:**
```
deppy/src/deppy/types/base.py
├── BaseType (ABC)
├── Primitive types (Int, Str, Bool, None)
├── Container types (List, Dict, Set, Tuple)
├── FunctionType
├── ObjectType (with row variable support for structural types)
├── UnionType
├── TypeVariable, RowVariable
├── Factories: int_type(), str_type(), object_type(fields, open=False)
```

**Mismatch with LaTeX:** 
- Formal chapter03 mentions `Tensor` as a base type but current implementation treats it as an `ObjectType` with special attributes
- **ACTION:** Add `TensorType` as explicit base type in deppy/types/base.py

#### 1.2 Refinement Types {v : τ | φ}
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 1150-1232

**Class to reuse:**
```python
class RefinementType:
    binder: str              # ν (binder variable)
    base: BaseType           # τ (base type)
    pred: Predicate          # φ (predicate over binder)
```

**Key methods:**
- `free_pred_vars()` – free variables in predicate excluding binder
- `substitute_pred_var(old, new)` – variable renaming
- `alpha_rename(new_binder)` – α-equivalence canonicalization
- `is_trivial()` – check if predicate is ⊤

**Recommended first-pass module:**
```
deppy/src/deppy/types/refinement.py
├── RefinementType (with α-equivalence support)
├── trivial_refinement(base, binder="ν")
└── _fresh_binder(avoid, prefix="ν")
```

**Status:** Ready to reuse directly. Supports exact LaTeX semantics.

#### 1.3 Dependent Function Types Π(x:τ₁).τ₂
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 1243-1314

**Classes to reuse:**
```python
@dataclass(frozen=True)
class DependentParam:
    name: str
    type: RefinementType   # {v:τ|φ}

@dataclass(frozen=True)
class DependentFunctionType:
    params: Tuple[DependentParam, ...]
    ret: RefinementType    # May mention parameter names
```

**Key methods:**
- `param_names()` – extract parameter names for substitution
- `to_simple_function_type()` – erase refinements
- `free_type_vars()`, `free_row_vars()` – free variable analysis

**Recommended first-pass module:**
```
deppy/src/deppy/types/dependent.py
├── DependentParam
├── DependentFunctionType
└── dependent_func(params: Sequence[(str, RefinementType)], ret: RefinementType)
```

**Status:** Ready to reuse. Supports dependent application rule from chapter03 line 160-165.

#### 1.4 Type Schemes (Polymorphism)
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 1322-1391

**Class to reuse:**
```python
@dataclass(frozen=True)
class TypeScheme:
    type_vars: FrozenSet[TypeVariable]
    row_vars: FrozenSet[RowVariable]
    body: RefinementType
```

**Key methods:**
- `instantiate_fresh()` – generate fresh instances
- `generalize_over(env_tvs, env_rvs)` – rank-1 polymorphism
- `is_monomorphic` property

**Recommended module:**
```
deppy/src/deppy/types/schemes.py
├── TypeScheme
├── mono_scheme(rt: RefinementType)
└── instantiation machinery
```

---

## Part 2: PREDICATE/FORMULA REPRESENTATIONS
### Formal Specification
**LaTeX Source:** `deppy/chapter03-dependent-python-core.tex` (lines 74-84)

Predicate grammar:
```
φ ::= ⊤ | ⊥ | t₁ = t₂ | t₁ ≤ t₂ | t₁ < t₂
    | len(x) = t | tag(x) = T | hasattr(x, a)
    | shape(x) = d̄ | device(x) = δ | phase(x) = π
    | φ ∧ φ | φ ∨ φ | ¬φ | ∃x.φ | ∀x.φ
```

### Reusable Code Mapping

#### 2.1 Linear Expressions (Arithmetic Terms)
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 589-743

**Classes to reuse:**
```python
class LinearExpr(ABC):  # e ::= x | c | len(x) | e+e | e-e | e*c
    
@dataclass(frozen=True)
class VarExpr(LinearExpr):           # x
class ConstExpr(LinearExpr):         # c
class LenExpr(LinearExpr):           # len(x)
class BinOpExpr(LinearExpr):         # e + e | e - e
class ScaleExpr(LinearExpr):         # e * c | e // c | e % c
```

**Recommended module:**
```
deppy/src/deppy/predicates/linear.py
├── LinearExpr (ABC)
├── VarExpr, ConstExpr, LenExpr
├── BinOpExpr (for +, -)
└── ScaleExpr (for *, //, %)
```

**Status:** Ready to reuse. Supports QF_LIA fragment.

#### 2.2 Predicate Hierarchy
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 750-1096

**Classes to reuse:**
```python
class Predicate(ABC):
    @abstractmethod
    def free_vars(self) -> FrozenSet[str]
    @abstractmethod
    def negate(self) -> Predicate
    
# Atomic predicates:
@dataclass(frozen=True)
class TruePred(AtomicPredicate):      # ⊤
class FalsePred(AtomicPredicate):     # ⊥
class ComparisonPred(AtomicPredicate): # t₁ ⊕ t₂ (==, !=, <, <=, >, >=)
class TypeTagPred(AtomicPredicate):   # tag(x) = T
class NullityPred(AtomicPredicate):   # x is None | x is not None
class HasAttrPred(AtomicPredicate):   # hasattr(x, "k")

# Boolean combinations:
@dataclass(frozen=True)
class AndPred(Predicate):             # φ₁ ∧ φ₂ ∧ …
class OrPred(Predicate):              # φ₁ ∨ φ₂ ∨ …
class NotPred(Predicate):             # ¬φ
```

**Key features:**
- Frozen dataclasses → structural equality, hashable
- Free variable analysis
- Substitution machinery
- Negation normal form conversions

**Recommended module:**
```
deppy/src/deppy/predicates/formula.py
├── Predicate (ABC)
├── TruePred, FalsePred
├── ComparisonPred
├── TypeTagPred, NullityPred
├── HasAttrPred
├── AndPred, OrPred, NotPred
└── Constants: TRUE_PRED, FALSE_PRED
```

**Missing from LaTeX but in code:**
- `TruthinessPred` (truthy/falsy) – useful for Python semantics
- `LenPred` variants – covered in types_extended

**Mismatch:** 
- Formal spec allows ∃x.φ, ∀x.φ but current code has no explicit quantifier nodes
- **ACTION:** Add `ExistsExpr`, `ForallExpr` to deppy/predicates/formula.py for full coverage

#### 2.3 Extended Predicates (types_extended)
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types_extended.py`
**Lines:** 38-328

**Class to reuse:**
```python
class PredicateKind(Enum):
    # Comparison
    EQ, NEQ, LT, LE, GT, GE
    # Collections
    LEN_EQ, LEN_GT, LEN_GE, LEN_LT, LEN_LE
    # Typing
    IS_NONE, IS_NOT_NONE, ISINSTANCE, HASATTR
    # Membership
    IN, NOT_IN
    # Boolean
    TRUE, FALSE, AND, OR, NOT, IMPLIES
    # Truthiness
    TRUTHY, FALSY
    # Custom
    CUSTOM
```

**Note:** This is an alternative predicate encoding (more compact than the types.py hierarchy).

**Recommendation:** 
- Use types.py Predicate hierarchy for core (more extensible)
- Provide conversion utilities to types_extended encoding for SMT

---

## Part 3: SUBTYPING, ENTAILMENT, AND TYPE-ENVIRONMENT MACHINERY
### Formal Specification
**LaTeX Source:** 
- `chapter03-dependent-python-core.tex` (lines 121-160): Judgments Γ;Φ ⊢ e:τ
- Line 130-135: Dependent subtyping as implication

Subtyping judgment:
```
Γ;Φ ⊢ {v:τ₁|φ₁} ⪯ {v:τ₂|φ₂}  iff  τ₁ <: τ₂  and  Γ;Φ ⊨ φ₁ ⟹ φ₂
```

### Reusable Code Mapping

#### 3.1 Structural (Width) Subtyping
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 1592-1668

**Function to reuse:**
```python
def is_subtype(t1: BaseType, t2: BaseType) -> bool:
    """Structural subtyping: t1 <: t2."""
    # Rules:
    # - Never <: τ for all τ
    # - τ <: Any for all τ
    # - τ <: τ (reflexive)
    # - Object width subtyping (more fields = finer type)
    # - List covariance
    # - Function contravariance on params, covariance on return
    # - Union handling
```

**Recommended module:**
```
deppy/src/deppy/core/subtyping.py
├── is_subtype(t1: BaseType, t2: BaseType) -> bool
└── Structural subtyping rules (no predicate entailment)
```

**Status:** Ready to reuse directly.

#### 3.2 Refinement Subtyping
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 1671-1696

**Function to reuse:**
```python
def is_refinement_subtype(
    rt1: RefinementType,
    rt2: RefinementType,
    entailment_checker: Optional[Callable[[Predicate, Predicate], bool]] = None
) -> bool:
    """Check {x:τ₁|φ₁} <: {x:τ₂|φ₂}.
    
    Requires:
    1. τ₁ <: τ₂ (structural subtyping)
    2. Γ;Φ ⊨ φ₁ ⟹ φ₂ (predicate entailment via callback)
    """
```

**Key design:**
- Binder α-renaming for comparison
- Optional entailment checker callback
- Trivial predicate optimization

**Recommended module:**
```
deppy/src/deppy/core/subtyping.py
├── is_refinement_subtype(
│     rt1, rt2,
│     entailment_checker: Callable[[Predicate, Predicate], bool]
│   ) -> bool
```

**Status:** Ready to reuse. Callback pattern enables SMT integration.

#### 3.3 Type Environments (Γ)
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types_extended.py`
**Lines:** 1333-1451

**Class to reuse:**
```python
class TypeEnvironment:
    """Maps x ↦ τ; supports join/meet/widen at merge points."""
    
    def bind(self, var: str, ty: BaseType) -> TypeEnvironment
    def lookup(self, var: str) -> Optional[BaseType]
    def extend(self, bindings: Dict[str, BaseType]) -> TypeEnvironment
    def restrict(self, vars_: Set[str]) -> TypeEnvironment
    
    # Lattice operations for join points:
    def join(self, other: TypeEnvironment) -> TypeEnvironment
    def meet(self, other: TypeEnvironment) -> TypeEnvironment
    def widen(self, other: TypeEnvironment) -> TypeEnvironment
    
    # Guard application (for path sensitivity):
    def apply_guard(self, guard: Guard) -> TypeEnvironment
```

**Recommended module:**
```
deppy/src/deppy/core/environments.py
├── TypeEnvironment
│   ├── Binding operations (bind, lookup, extend, restrict)
│   ├── Lattice operations (join, meet, widen)
│   └── Guard application (apply_guard)
```

**Status:** Ready to reuse. Supports join/meet lattice operations needed for control-flow merges.

#### 3.4 Path-Sensitive Predicate Environments (Φ)
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/path_sensitive.py`
**Lines:** 23-100

**Classes to reuse:**
```python
@dataclass(frozen=True)
class PathConstraint:
    """Single constraint active on path (e.g., isinstance guard)."""
    variable: str
    predicate: str           # e.g., "isinstance_Tensor"
    negated: bool = False    # True in else-branch

@dataclass
class PathContext:
    """Stack of active path constraints (Φ as conjunction)."""
    constraints: List[PathConstraint]
    
    def push(self, constraint: PathConstraint) -> None
    def active_predicates_for(self, variable: str) -> Set[str]
    def has_type_constraint(self, variable: str) -> Optional[str]
    def variable_is_none(self, variable: str) -> Optional[bool]
```

**Recommended module:**
```
deppy/src/deppy/core/path_environment.py
├── PathConstraint
├── PathContext
└── Utilities for tracking conjunctive guard facts
```

**Status:** Ready to reuse. Critical for guard-refinement rule (chapter03, line 168-175).

#### 3.5 Substitution Machinery
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 1398-1486

**Class to reuse:**
```python
@dataclass
class Substitution:
    """Combined substitution for type/row/predicate variables."""
    type_map: Dict[TypeVariable, BaseType] = field(default_factory=dict)
    row_map: Dict[RowVariable, Tuple[Dict[str, BaseType], Optional[RowVariable]]] = ...
    expr_map: Dict[str, LinearExpr] = field(default_factory=dict)
    
    def apply_base(self, t: BaseType) -> BaseType
    def apply_pred(self, p: Predicate) -> Predicate
    def apply_refinement(self, rt: RefinementType) -> RefinementType
    def compose(self, other: Substitution) -> Substitution
```

**Recommended module:**
```
deppy/src/deppy/core/substitution.py
├── Substitution
│   ├── apply_base, apply_pred, apply_refinement
│   ├── compose (for chained substitutions)
│   └── Support for dependent application rule
```

**Status:** Ready to reuse. Supports dependent function application.

#### 3.6 Guard-Based Type Narrowing
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types_extended.py`
**Lines:** 1459-1570

**Class to reuse:**
```python
class GuardKind(Enum):
    ISINSTANCE, IS_NONE, IS_NOT_NONE, HASATTR, COMPARISON, ...

@dataclass(frozen=True)
class Guard:
    """Represents a boolean guard condition (if test)."""
    kind: GuardKind
    variable: str
    args: Tuple[Any, ...]
    children: Tuple[Guard, ...]  # For AND/OR/NOT
```

**Recommended module:**
```
deppy/src/deppy/core/guards.py
├── GuardKind (enum)
├── Guard (guard condition AST)
└── Guard narrowing utilities
```

**Status:** Ready to reuse. Supports guard-refinement rule (chapter03, line 168-175).

---

## Part 4: Z3 SOLVER INTEGRATION & NORMALIZATION
### Formal Specification
**LaTeX Source:** `deppy/chapter07-z3-decidable-core.tex` (lines 1-170)

Core concept: Two-phase normalization
```
φ_source ──→ φ_canonical ──→ φ_core ──→ fragment_label
```

Decidable fragments:
1. **QF_LIA** – quantifier-free linear integer arithmetic (P-complete)
2. **Finite-domain** – enums, state tags, device labels (O(1) per constraint)
3. **Uninterpreted functions** – library behavior summaries
4. **Arrays (controlled)** – only in tight schemas

### Reusable Code Mapping

#### 4.1 Decidability Classification
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/decidability.py`
**Lines:** 67-150

**Enum to reuse:**
```python
class ComplexityClass(Enum):
    P = "P"
    NP_HARD = "NP-hard"

class TheoryFragment(Enum):
    T_SHAPE_LINEAR     # QF_LIA
    T_SHAPE_BROADCAST  # max of dims
    T_SHAPE_MATMUL     # inner-dim equality
    T_SHAPE_RESHAPE    # product-equality (NP-hard)
    T_DEVICE           # finite domain (5 elements)
    T_PHASE            # finite domain (2 elements)
```

**Recommended module:**
```
deppy/src/deppy/smt/decidability.py
├── ComplexityClass
├── TheoryFragment
├── identify_fragments(query: VerificationQuery) -> Set[TheoryFragment]
└── Fragment classification logic
```

**Status:** Ready to reuse. Extends beyond tensor shapes to general predicates.

#### 4.2 Predicate Normalization
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types.py`
**Lines:** 1520-1585

**Functions to reuse:**
```python
def normalize_type(t: BaseType) -> BaseType:
    """Canonicalize type: flatten unions, sort fields."""

def normalize_refinement(rt: RefinementType) -> RefinementType:
    """Normalize base type and simplify predicates."""

def _simplify_pred(p: Predicate) -> Predicate:
    """Predicate simplification (flatten nested And/Or)."""
```

**Recommended module:**
```
deppy/src/deppy/smt/normalization.py
├── normalize_type(t: BaseType) -> BaseType
├── normalize_refinement(rt: RefinementType) -> RefinementType
├── normalize_predicate(p: Predicate) -> Predicate
└── Fragment classification of normalized predicates
```

**Status:** Partial reuse. Need to extend with:
- Fragment detection for general predicates (not just shapes)
- Weakening for out-of-kernel predicates
- Bounded-arithmetic approximations

#### 4.3 Z3 Encoding
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/smt/encoder.py`
**Lines:** 1-100 (large file, 53KB)

**Classes to reuse:**
```python
class Z3Encoder:
    """Encodes normalized predicates to Z3."""
    
    def encode_predicate(self, pred: Predicate, ...) -> z3.ExprRef
    def encode_refinement(self, rt: RefinementType, ...) -> z3.ExprRef
```

**SMT backend details:**
- File `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/smt/z3_backend.py` (55KB)
- Solver interface with CVC5, Z3 support
- Theory combination (shape + device + phase)

**Recommended module:**
```
deppy/src/deppy/smt/encoding.py
├── Fragment-aware encoder
├── QF_LIA encoding (primary)
├── Finite-domain encoding
├── Uninterpreted function stubs
└── Theory combination (Nelson-Oppen)
```

**Status:** Large reuse candidate. Skip advanced features for MVP.

#### 4.4 Entailment Checker (using SMT)
**File:** `/Users/halleyyoung/Documents/div/mathdivergence/best2/refinement-type-inference-dynamic-lang/implementation/src/types_extended.py`
**Lines:** 1830-1877

**Function pattern to adapt:**
```python
def _check_predicate_implication(self, p1: Predicate, p2: Predicate) -> bool:
    """Approximate predicate implication check without SMT."""
    # Fallback: syntactic pattern matching
    # For full implementation: encode to Z3, check unsat(p1 ∧ ¬p2)
```

**Recommended module:**
```
deppy/src/deppy/smt/entailment.py
├── entail_predicate(assumption: Predicate, goal: Predicate) -> bool
│   ├── Syntactic fast path (equality, tautologies)
│   └── Z3-backed full check
└── EntailmentChecker (stateful, caches Z3 contexts)
```

**Status:** Partial reuse. Need full SMT integration.

---

## Part 5: SUMMARY & PROPOSED PACKAGE LAYOUT

### Directory Structure
```
deppy/src/deppy/
├── types/
│   ├── __init__.py
│   ├── base.py           # Base types, TypeVariable, RowVariable
│   ├── refinement.py     # RefinementType, α-equivalence
│   ├── dependent.py      # DependentParam, DependentFunctionType
│   ├── schemes.py        # TypeScheme, polymorphism
│   └── constructors.py   # Factories and helpers
│
├── predicates/
│   ├── __init__.py
│   ├── linear.py         # LinearExpr hierarchy
│   ├── formula.py        # Predicate hierarchy (Atomic, And, Or, Not)
│   ├── simplify.py       # Predicate simplification
│   └── substitution.py   # Predicate variable renaming
│
├── core/
│   ├── __init__.py
│   ├── subtyping.py      # is_subtype, is_refinement_subtype
│   ├── environments.py   # TypeEnvironment, lattice operations
│   ├── path_environment.py # PathConstraint, PathContext (Φ)
│   ├── guards.py         # Guard, type narrowing
│   ├── substitution.py   # Substitution (type/row/expr variables)
│   ├── typing.py         # Main judgment Γ;Φ ⊢ e:τ (to implement)
│   └── normalization.py  # Type/predicate normalization
│
├── smt/
│   ├── __init__.py
│   ├── decidability.py   # Fragment classification
│   ├── encoding.py       # Predicate → Z3 terms
│   ├── entailment.py     # φ₁ ⊨ φ₂ via Z3
│   └── solver.py         # SMT solver interface (thin wrapper)
│
└── __init__.py           # Package exports
```

### First-Pass Module Implementation Priority

**Phase 1 (Core Type System):**
1. `types/base.py` – all base types
2. `types/refinement.py` – RefinementType
3. `types/dependent.py` – DependentFunctionType
4. `predicates/linear.py` – LinearExpr
5. `predicates/formula.py` – Predicate hierarchy

**Phase 2 (Judgment & Environment):**
6. `core/environments.py` – TypeEnvironment
7. `core/path_environment.py` – PathContext
8. `core/subtyping.py` – is_subtype, is_refinement_subtype
9. `core/guards.py` – Guard-based narrowing

**Phase 3 (Verification):**
10. `core/typing.py` – Main type-checking judgment
11. `smt/decidability.py` – Fragment classification
12. `smt/normalization.py` – Predicate normalization

**Phase 4 (Solver):**
13. `smt/encoding.py` – Z3 encoding
14. `smt/entailment.py` – Entailment checking

---

## Part 6: CRITICAL MISMATCHES & GAPS

### Mismatch 1: Quantified Predicates (∃, ∀)
**LaTeX:** Chapter 3, line 83: `φ ::= … | ∃x.φ | ∀x.φ`
**Current Code:** No explicit quantifier nodes in types.py

**ACTION:**
- Add `ExistsExpr(var: str, inner: Predicate)` to predicates/formula.py
- Add `ForallExpr(var: str, inner: Predicate)` to predicates/formula.py
- Update free variable analysis

### Mismatch 2: Tensor Type
**LaTeX:** Chapter 3, line 38: `τ ::= … | Tensor`
**Current Code:** Tensor is an ObjectType with special attributes

**ACTION:**
- Add explicit `TensorType` to types/base.py
- Support shape/device/phase as TensorType attributes in refinements

### Mismatch 3: Object Type Predicates
**LaTeX:** Chapter 3, line 44: `Obj{φ}` – structural object with predicates
**Current Code:** ObjectType only has field types, no predicate payload

**ACTION:**
- Consider `RefinedObjectType(fields, row_var, predicate)` variant
- Or allow objects with object-level predicates in refinement wrapper

### Mismatch 4: Guarded Control Flow
**LaTeX:** Chapter 3, line 168-175: Guard-refinement rule
**Current Code:** Types.py has PathContext but no type-checking rule

**ACTION:**
- Implement in core/typing.py:
  ```python
  def check_if_then_else(
      guard: Predicate,
      env_true: TypeEnvironment,
      env_false: TypeEnvironment,
      expr_then, expr_else
  ) -> RefinementType
  ```

### Mismatch 5: Mutation Safety
**LaTeX:** Chapter 3, line 197-214: Stability modes (stable/ephemeral/borrowed)
**Current Code:** No explicit stability tracking

**ACTION:**
- Add `Stability(Enum)` to predicates/formula.py
- Extend Predicate dataclass with `stability: Stability` field

### Mismatch 6: SMT Fragment Detection
**LaTeX:** Chapter 7, line 61-92: QF_LIA, finite-domain, UF, arrays
**Current Code:** Only shape/device/phase fragments in decidability.py

**ACTION:**
- Generalize fragment detector in smt/decidability.py
- Support arbitrary predicate fragment classification

---

## Part 7: IMPLEMENTATION CHECKLIST

### Week 1: Types Foundation
- [ ] Copy types.py classes to deppy/src/deppy/types/base.py
- [ ] Add TensorType, fix imports
- [ ] Create types/refinement.py, types/dependent.py
- [ ] Add quantifier support to predicates/formula.py
- [ ] Unit tests: α-equivalence, substitution

### Week 2: Predicates & Environment
- [ ] Copy predicate hierarchy to deppy/src/deppy/predicates/formula.py
- [ ] Implement predicate simplification
- [ ] Copy TypeEnvironment to deppy/src/deppy/core/environments.py
- [ ] Copy PathContext to deppy/src/deppy/core/path_environment.py
- [ ] Unit tests: narrowing, lattice ops

### Week 3: Subtyping & Core Rules
- [ ] Implement core/subtyping.py (is_subtype, is_refinement_subtype)
- [ ] Implement core/guards.py (Guard-based narrowing)
- [ ] Stub core/typing.py with judgment signatures
- [ ] Implement guard-refinement rule
- [ ] Integration tests

### Week 4: SMT & Verification
- [ ] Extend smt/decidability.py for general predicates
- [ ] Implement smt/normalization.py
- [ ] Implement smt/encoding.py (QF_LIA focus)
- [ ] Implement smt/entailment.py
- [ ] End-to-end verification test

---

## CONCLUSION

**Total lines of reusable code:** ~6,500 LOC from types.py + types_extended.py
**Estimated adaptation effort:** 2-3 weeks (modular, well-structured)
**Risk factors:**
- Quantifier handling (not in original types.py)
- Mutation/stability tracking (needs extension)
- Full SMT integration (already exists in smt/ but needs adaptation)

**Recommendation:** Start with types/ and predicates/ modules (lowest risk), then build core/ and smt/ with callbacks to allow staged solver integration.

