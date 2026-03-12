# SSA Value-Lineage Metadata Implementation Guide

**Goal:** Enable semantic fact survival through local aliasing and nested expressions by enriching SSA with value lineage metadata.

---

## Problem Diagnosis

### Current Limitation

The DepPy pipeline recognizes **direct-return wrappers only**:
```python
# ✓ WORKS: Direct return
def serving_rank(scores):
    return direct_rank(scores)

# ✗ FAILS: Local aliasing
def local_rank(scores):
    ranked = rank_scores(scores)   # <- Additional statement
    return ranked

# ✗ FAILS: Nested expression
def flatten_nested(scores):
    return serving_rank(scores).view(-1)  # <- Method chain
```

**Root cause** (`frontier_propagation.py:180-196`):
- Line 183: `if len(function.node.body) != 1: continue` — rejects multi-statement bodies
- Line 193: `if isinstance(argument, ast.Name): arg_map[...] = argument.id` — only matches bare names, not chained calls

**Result:** Local aliasing and nested expressions lose semantic facts (atoms, theories) during interprocedural propagation.

---

## Solution: Value Lineage Metadata

### Core Insight

Attach immutable metadata to each SSA value tracking:
1. **Direct predecessors** in the SSA graph (which versions feed into this value)
2. **Call sites** in the value's expression (which callees are invoked)
3. **Wrapper indicator** (whether this is an alias to a call result)

This enables wrapper detection to recognize local aliasing and extract calls from nested expressions.

---

## Implementation: File-by-File Guidance

### 1. `src/deppy/surface/python_ssa.py`

#### A. Add Three New Dataclasses (after imports, before `PhiNode`)

```python
@dataclass(frozen=True)
class CallSiteRecord:
    """A function call found in an SSA value's expression."""
    call_target: str                         # e.g., "rank_scores"
    args_versioned: Dict[str, str] = field(default_factory=dict)

@dataclass(frozen=True)
class ValueLineageEdge:
    """Direct predecessor link in SSA lineage graph."""
    source_version: str                      # e.g., "ranked@1", "scores@0"

@dataclass(frozen=True)
class SSAValueLineage:
    """Complete lineage for an SSA value."""
    versioned_name: str
    direct_sources: Tuple[ValueLineageEdge, ...] = ()
    call_sites: Tuple[CallSiteRecord, ...] = ()  # ← KEY for wrapper detection
    wrapper_indicator: bool = False              # ← True if Name alias to call
```

#### B. Modify Existing Dataclasses (add field)

```python
@dataclass(frozen=True)
class SSABinding:
    # ... existing fields ...
    lineage: SSAValueLineage | None = None

@dataclass(frozen=True)
class SSAReturn:
    # ... existing fields ...
    lineage: SSAValueLineage | None = None

@dataclass(frozen=True)
class PhiNode:
    # ... existing fields ...
    lineage: SSAValueLineage | None = None
```

#### C. Add New Builder Class

```python
class PythonSSALineageBuilder:
    """Post-processes FunctionSSA to compute value lineage metadata."""
    
    def build(self, ssa: FunctionSSA) -> FunctionSSA:
        """Returns new FunctionSSA with lineage attached."""
        version_map = self._index_versions(ssa)       # Pass 1
        call_index = self._extract_call_sites(ssa)    # Pass 2
        
        assignment_lineage = {
            binding.versioned_name: self._compute_lineage(
                binding.versioned_name,
                binding.value_text,
                binding.inputs,
                version_map,
                call_index,
            )
            for binding in ssa.assignments
        }
        
        return_lineage = {
            ret.versioned_name: self._compute_lineage(
                ret.versioned_name,
                ret.value_text,
                ret.inputs,
                version_map,
                call_index,
            )
            for ret in ssa.returns
        }
        
        phi_lineage = self._compute_phi_lineage(
            ssa.phi_nodes,
            assignment_lineage,
        )
        
        return self._attach_lineage(
            ssa,
            assignment_lineage,
            return_lineage,
            phi_lineage,
        )
    
    def _index_versions(self, ssa: FunctionSSA) -> Dict[str, str]:
        """Map versioned_name → source type."""
        version_map = {}
        for param_name, param_version in ssa.parameters.items():
            version_map[param_version] = f"param:{param_name}"
        for binding in ssa.assignments:
            version_map[binding.versioned_name] = f"binding:{binding.variable}"
        for ret in ssa.returns:
            version_map[ret.versioned_name] = "return"
        for phi in ssa.phi_nodes:
            version_map[phi.versioned_name] = f"phi:{phi.variable}"
        return version_map
    
    def _extract_call_sites(self, ssa: FunctionSSA) -> Dict[str, List[CallSiteRecord]]:
        """Index all Call nodes in value expressions."""
        call_index = {}
        for binding in ssa.assignments:
            call_index[binding.versioned_name] = self._calls_in_expr(binding.value_text)
        for ret in ssa.returns:
            call_index[ret.versioned_name] = self._calls_in_expr(ret.value_text)
        return call_index
    
    def _calls_in_expr(self, expr_text: str) -> List[CallSiteRecord]:
        """Walk AST to find all Call nodes."""
        try:
            node = ast.parse(expr_text, mode='eval').body
        except SyntaxError:
            return []
        
        calls = []
        for call_node in ast.walk(node):
            if isinstance(call_node, ast.Call):
                target = self._call_target(call_node.func)
                if target:
                    calls.append(CallSiteRecord(call_target=target))
        return calls
    
    def _call_target(self, node: ast.expr) -> str | None:
        """Extract function name from Call target."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            return ast.unparse(node)
        return None
    
    def _compute_lineage(
        self,
        versioned_name: str,
        value_text: str,
        inputs: Dict[str, str],
        version_map: Dict[str, str],
        call_index: Dict[str, List[CallSiteRecord]],
    ) -> SSAValueLineage:
        """Compute lineage chain for a value."""
        direct_sources = tuple(
            ValueLineageEdge(source_version=version)
            for version in inputs.values()
        )
        
        call_sites = tuple(call_index.get(versioned_name, []))
        
        wrapper_indicator = False
        try:
            node = ast.parse(value_text, mode='eval').body
            if isinstance(node, ast.Name):
                wrapper_indicator = True
        except SyntaxError:
            pass
        
        return SSAValueLineage(
            versioned_name=versioned_name,
            direct_sources=direct_sources,
            call_sites=call_sites,
            wrapper_indicator=wrapper_indicator,
        )
    
    def _compute_phi_lineage(
        self,
        phi_nodes: List[PhiNode],
        assignment_lineage: Dict[str, SSAValueLineage],
    ) -> Dict[str, SSAValueLineage]:
        """Phi lineage = union of input lineages."""
        phi_lineage = {}
        for phi in phi_nodes:
            all_sources = []
            all_calls = set()
            
            for pred, version in phi.inputs:
                if version and version in assignment_lineage:
                    pred_lineage = assignment_lineage[version]
                    all_sources.extend(pred_lineage.direct_sources)
                    all_calls.update(pred_lineage.call_sites)
            
            phi_lineage[phi.versioned_name] = SSAValueLineage(
                versioned_name=phi.versioned_name,
                direct_sources=tuple(all_sources),
                call_sites=tuple(all_calls),
                wrapper_indicator=False,
            )
        return phi_lineage
    
    def _attach_lineage(
        self,
        ssa: FunctionSSA,
        assignment_lineage: Dict[str, SSAValueLineage],
        return_lineage: Dict[str, SSAValueLineage],
        phi_lineage: Dict[str, SSAValueLineage],
    ) -> FunctionSSA:
        """Create new FunctionSSA with lineage attached."""
        from dataclasses import replace
        
        assignments = [
            replace(binding, lineage=assignment_lineage.get(binding.versioned_name))
            for binding in ssa.assignments
        ]
        returns = [
            replace(ret, lineage=return_lineage.get(ret.versioned_name))
            for ret in ssa.returns
        ]
        phi_nodes = [
            replace(phi, lineage=phi_lineage.get(phi.versioned_name))
            for phi in ssa.phi_nodes
        ]
        
        return replace(ssa, assignments=assignments, returns=returns, phi_nodes=phi_nodes)
```

#### D. Update `PythonSSABuilder.build()`

At the end of the existing `build()` method (after line 75), add:

```python
def build(self, function: FunctionModel, cfg: FunctionCFG) -> FunctionSSA:
    # ... existing code (lines 59-75) ...
    summary = FunctionSSA(function=function.qualname)
    # ... populate summary ...
    summary.final_names = dict(summary.block_outputs.get(cfg.exit_block, {}))
    summary.final_return = summary.final_names.get("return")
    
    # NEW: Enrich with lineage metadata
    summary = PythonSSALineageBuilder().build(summary)
    
    return summary
```

---

### 2. `src/deppy/surface/__init__.py`

#### Update Imports (line 14)

```python
from .python_ssa import (
    FunctionSSA,
    PhiNode,
    PythonSSABuilder,
    SSABinding,
    SSAReturn,
    SSAValueLineage,           # NEW
    ValueLineageEdge,          # NEW
    CallSiteRecord,            # NEW
    PythonSSALineageBuilder,   # NEW
)
```

#### Update `__all__` (lines 59-84)

Add before the closing bracket:

```python
__all__ = [
    # ... existing exports ...
    "SSAValueLineage",
    "ValueLineageEdge",
    "CallSiteRecord",
    "PythonSSALineageBuilder",
]
```

---

### 3. `src/deppy/interprocedural/frontier_propagation.py`

#### A. Update `_wrapper_call_sites` Signature

Change line 180:

```python
# OLD
def _wrapper_call_sites(module: ModuleModel) -> Dict[str, Tuple[str, Dict[str, str]]]:

# NEW
def _wrapper_call_sites(
    module: ModuleModel,
    ssa_map: Dict[str, FunctionSSA] | None = None,
) -> Dict[str, Tuple[str, Dict[str, str]]]:
```

#### B. Update `_wrapper_call_sites` Body

Replace the loop (lines 182-195):

```python
def _wrapper_call_sites(
    module: ModuleModel,
    ssa_map: Dict[str, FunctionSSA] | None = None,
) -> Dict[str, Tuple[str, Dict[str, str]]]:
    """Detect wrappers using SSA lineage; supports local aliasing & nested exprs."""
    wrappers: Dict[str, Tuple[str, Dict[str, str]]] = {}
    
    for qualname, function in module.functions.items():
        if len(function.node.body) != 1:
            continue
        statement = function.node.body[0]
        if not isinstance(statement, ast.Return) or not isinstance(statement.value, ast.Call):
            continue
        
        # NEW: Try lineage-based extraction first
        if ssa_map and qualname in ssa_map:
            ssa = ssa_map[qualname]
            if ssa.returns:
                ret = ssa.returns[0]
                if ret.lineage and ret.lineage.call_sites:
                    callee, arg_map = self._wrapper_from_lineage(function, ret, ssa)
                    if callee and arg_map:
                        wrappers[qualname] = (callee, arg_map)
                        continue
        
        # EXISTING: Fall back to syntax-based extraction
        raw_callee = _raw_callee_name(statement.value.func)
        if raw_callee is None:
            continue
        arg_map = {}
        for parameter, argument in zip(function.parameters, statement.value.args):
            if isinstance(argument, ast.Name):
                arg_map[parameter.name] = argument.id
        if raw_callee and arg_map:
            wrappers[qualname] = (raw_callee, arg_map)
    
    return wrappers
```

#### C. Add `_wrapper_from_lineage` Method

Add as a new method of `InterproceduralFrontierPropagator` class:

```python
def _wrapper_from_lineage(
    self,
    function: FunctionModel,
    ret: SSAReturn,
    ssa: FunctionSSA,
) -> Tuple[str | None, Dict[str, str]]:
    """Extract wrapper callee + arg mapping from return lineage.
    
    Handles:
    - return serving_rank(scores).view(-1)  (nested call)
    - ranked = rank_scores(...); return ranked  (local alias)
    """
    if not ret.lineage or len(ret.lineage.call_sites) != 1:
        return None, {}
    
    call_site = ret.lineage.call_sites[0]
    
    arg_map = {}
    try:
        node = ast.parse(ret.value_text, mode='eval').body
        # Find first Call node in the expression tree
        first_call = None
        for child in ast.walk(node):
            if isinstance(child, ast.Call):
                first_call = child
                break
        
        if first_call:
            # Extract arguments from the first call
            for param, arg in zip(function.parameters, first_call.args):
                if isinstance(arg, ast.Name):
                    arg_map[param.name] = arg.id
            
            return call_site.call_target, arg_map
    except SyntaxError:
        pass
    
    return None, {}
```

#### D. Update Call Site (in `propagate_frontiers` or equivalent)

Find where `_wrapper_call_sites` is called. Update to pass SSA map:

```python
# Before propagation, ensure SSA is available
# (This depends on how the analysis pipeline is structured)
wrappers = _wrapper_call_sites(module, ssa_map=surface_summary.ssa)
```

---

### 4. `tests/test_python_cfg_ssa.py`

Add three new test functions after existing tests:

```python
def test_ssa_lineage_local_alias_wrapper() -> None:
    """Lineage enables wrapper recognition for local assignments (local_rank pattern)."""
    source = '''
def local_rank(scores):
    ranked = rank_scores(scores)
    return ranked
'''
    module = parse_module(source, 'test_wrapper.py')
    summary = PythonSurfaceLowerer().build(module)
    
    ssa = summary.ssa['test_wrapper.local_rank']
    
    # Check binding has lineage
    assert len(ssa.assignments) == 1
    binding = ssa.assignments[0]
    assert binding.lineage is not None
    assert binding.lineage.wrapper_indicator is True
    assert len(binding.lineage.call_sites) == 1
    assert binding.lineage.call_sites[0].call_target == 'rank_scores'
    
    # Check return lineage chains through binding
    ret = ssa.returns[0]
    assert ret.lineage is not None
    assert len(ret.lineage.call_sites) >= 1
    call_targets = {c.call_target for c in ret.lineage.call_sites}
    assert 'rank_scores' in call_targets


def test_ssa_lineage_nested_call_extraction() -> None:
    """Lineage extracts call sites from nested expressions (flatten_nested)."""
    source = '''
def flatten_nested(scores):
    return serving_rank(scores).view(-1)
'''
    module = parse_module(source, 'test_nested.py')
    summary = PythonSurfaceLowerer().build(module)
    
    ssa = summary.ssa['test_nested.flatten_nested']
    ret = ssa.returns[0]
    
    assert ret.lineage is not None
    call_targets = {c.call_target for c in ret.lineage.call_sites}
    assert 'serving_rank' in call_targets


def test_ssa_lineage_phi_merge() -> None:
    """Phi node lineage merges call sites from multiple branches."""
    source = '''
def branch_with_calls(flag: bool, x: int):
    if flag:
        y = rank_scores(x)
    else:
        y = rank_indices(x)
    return y
'''
    module = parse_module(source, 'test_branch.py')
    summary = PythonSurfaceLowerer().build(module)
    
    ssa = summary.ssa['test_branch.branch_with_calls']
    
    # Phi should have lineage from both branches
    assert len(ssa.phi_nodes) == 1
    phi = ssa.phi_nodes[0]
    assert phi.lineage is not None
    call_targets = {c.call_target for c in phi.lineage.call_sites}
    assert call_targets == {'rank_scores', 'rank_indices'}
```

---

### 5. `tests/test_long_capability_audit.py`

Update lines 82-87 (replace failing assertions):

```python
# BEFORE (lines 82-87) — these fail
# assert not analysis.signatures[local_rank_name].atoms
# assert not analysis.signatures[local_rank_indices_name].atoms
# assert analysis.signatures[local_rank_name].active_theories == ()
# assert analysis.signatures[local_rank_indices_name].active_theories == ()
# assert not analysis.signatures[flatten_nested_name].atoms
# assert analysis.signatures[flatten_nested_name].active_theories == ()

# AFTER — should pass with lineage
assert {"sorted(result)", "perm(result, scores)"} <= _atom_set(analysis, local_rank_name)
assert analysis.signatures[local_rank_name].active_theories == ("pytorch-sort",)

assert {"argsort(result, scores)"} <= _atom_set(analysis, local_rank_indices_name)
assert analysis.signatures[local_rank_indices_name].active_theories == ("pytorch-sort",)

assert {"view_of(result, ranked)", "shape_transform(result, ranked)"} <= _atom_set(
    analysis, flatten_nested_name
)
assert analysis.signatures[flatten_nested_name].active_theories == ("pytorch-shapes",)
```

---

## Implementation Sequence

1. ✓ `python_ssa.py`: Add dataclasses (CallSiteRecord, ValueLineageEdge, SSAValueLineage)
2. ✓ `python_ssa.py`: Update SSABinding, SSAReturn, PhiNode with lineage field
3. ✓ `python_ssa.py`: Implement PythonSSALineageBuilder
4. ✓ `python_ssa.py`: Update PythonSSABuilder.build() to invoke lineage builder
5. ✓ `__init__.py`: Export new types
6. ✓ `test_python_cfg_ssa.py`: Add three test functions
7. ✓ `frontier_propagation.py`: Update _wrapper_call_sites signature
8. ✓ `frontier_propagation.py`: Implement _wrapper_from_lineage
9. ✓ `frontier_propagation.py`: Integrate lineage check in _wrapper_call_sites
10. ✓ `test_long_capability_audit.py`: Update assertions

---

## Expected Outcomes

| Pattern | Before | After |
|---------|--------|-------|
| `return direct_call(...)` | ✓ Works | ✓ Works |
| `x = direct_call(...); return x` | ✗ Fails | ✓ Works (local aliasing) |
| `return nested_call(...).method()` | ✗ Fails | ✓ Works (nested extraction) |
| Multi-branch phi with calls | ✗ Loses calls | ✓ Merges all call sites |

---

## Key Design Decisions

| Decision | Reasoning |
|----------|-----------|
| **Frozen dataclasses** | SSA values are immutable; lineage is derived metadata |
| **Optional lineage field** | Lazy enrichment; backward compatible |
| **Post-processing pass** | Separates SSA construction from enrichment |
| **Call site keying by name** | Matches `_rename_atom` logic in interprocedural module |
| **Phi union semantics** | Preserves all reachable calls across branches |

---

## Future Work

- **Argument versioning**: Track which versioned values were passed to which calls
- **Transitive aliasing**: Chain through multiple local assignments
- **Dynamic calls**: Handle `getattr(obj, name)()` patterns
- **Method chains**: Normalize `.view()`, `.reshape()`, etc. as data-preserving transforms
- **Performance**: Cache AST nodes in CFG/SSA construction

