# Quick Reference: SSA Value-Lineage Implementation

## At a Glance

**What**: Attach value lineage metadata to SSA values to track call sites and predecessors  
**Why**: Enable semantic fact propagation through local aliasing (`x = call(); return x`) and nested calls (`return call().method()`)  
**Where**: 5 files across surface and interprocedural modules  
**How Much**: ~375 lines total (250 new + 50 modifications + 75 tests)

---

## Core Data Structures

```python
# NEW in python_ssa.py
@dataclass(frozen=True)
class CallSiteRecord:
    call_target: str                         # "rank_scores"
    args_versioned: Dict[str, str] = field(default_factory=dict)

@dataclass(frozen=True)
class ValueLineageEdge:
    source_version: str                      # "ranked@1"

@dataclass(frozen=True)
class SSAValueLineage:
    versioned_name: str                      # "ranked@1"
    direct_sources: Tuple[ValueLineageEdge, ...]   # Predecessors
    call_sites: Tuple[CallSiteRecord, ...]         # ← KEY: calls in expr
    wrapper_indicator: bool = False                # True if Name -> call

# MODIFIED in python_ssa.py
SSABinding.lineage: SSAValueLineage | None = None
SSAReturn.lineage: SSAValueLineage | None = None
PhiNode.lineage: SSAValueLineage | None = None
```

---

## PythonSSALineageBuilder: 7 Key Methods

| Method | Input | Output | Purpose |
|--------|-------|--------|---------|
| `build()` | FunctionSSA | FunctionSSA | Orchestrator: runs 5-pass algorithm |
| `_index_versions()` | FunctionSSA | Dict[str, str] | Map version → source type |
| `_extract_call_sites()` | FunctionSSA | Dict[str, List[CallSiteRecord]] | Parse all value_text for Call nodes |
| `_calls_in_expr()` | str (expr_text) | List[CallSiteRecord] | AST walk to find Call nodes |
| `_call_target()` | ast.expr | str \| None | Extract function name from call |
| `_compute_lineage()` | value_text + inputs | SSAValueLineage | Compute lineage for binding/return |
| `_compute_phi_lineage()` | phi_nodes + lineages | Dict[str, SSAValueLineage] | Merge input lineages for phi |

---

## Integration: 2 Points

### Point 1: python_ssa.py

At end of `PythonSSABuilder.build()`:
```python
summary = PythonSSALineageBuilder().build(summary)
return summary
```

### Point 2: frontier_propagation.py

In `_wrapper_call_sites()` before falling back to syntax:
```python
if ssa_map and qualname in ssa_map:
    ssa = ssa_map[qualname]
    if ssa.returns:
        ret = ssa.returns[0]
        if ret.lineage and ret.lineage.call_sites:
            callee, arg_map = self._wrapper_from_lineage(function, ret, ssa)
            if callee and arg_map:
                wrappers[qualname] = (callee, arg_map)
                continue
```

---

## Test Coverage: 3 New Tests

| Test | Validates |
|------|-----------|
| `test_ssa_lineage_local_alias_wrapper()` | `x = call(...); return x` pattern |
| `test_ssa_lineage_nested_call_extraction()` | `return call(...).method()` pattern |
| `test_ssa_lineage_phi_merge()` | Phi union of call sites across branches |

---

## File-by-File Checklist

### `src/deppy/surface/python_ssa.py`
- [ ] Add `CallSiteRecord` dataclass
- [ ] Add `ValueLineageEdge` dataclass
- [ ] Add `SSAValueLineage` dataclass
- [ ] Add `lineage` field to `SSABinding`
- [ ] Add `lineage` field to `SSAReturn`
- [ ] Add `lineage` field to `PhiNode`
- [ ] Implement `PythonSSALineageBuilder` class (7 methods, ~200 lines)
- [ ] Update `PythonSSABuilder.build()` to call lineage builder

### `src/deppy/surface/__init__.py`
- [ ] Import 4 new types
- [ ] Export 4 new types in `__all__`

### `src/deppy/interprocedural/frontier_propagation.py`
- [ ] Add `ssa_map` parameter to `_wrapper_call_sites`
- [ ] Add lineage check before syntax fallback
- [ ] Implement `_wrapper_from_lineage()` method (~30 lines)

### `tests/test_python_cfg_ssa.py`
- [ ] Add `test_ssa_lineage_local_alias_wrapper()`
- [ ] Add `test_ssa_lineage_nested_call_extraction()`
- [ ] Add `test_ssa_lineage_phi_merge()`

### `tests/test_long_capability_audit.py`
- [ ] Update assertions for `local_rank_name` (lines 82-84)
- [ ] Update assertions for `local_rank_indices_name` (lines 85-87)
- [ ] Update assertions for `flatten_nested_name` (lines 88-92)

---

## Expected Test Results

| Test | Before | After |
|------|--------|-------|
| `test_ssa_lineage_local_alias_wrapper` | N/A | ✓ PASS |
| `test_ssa_lineage_nested_call_extraction` | N/A | ✓ PASS |
| `test_ssa_lineage_phi_merge` | N/A | ✓ PASS |
| `test_long_capability_audit` (local_rank) | ✗ FAIL | ✓ PASS |
| `test_long_capability_audit` (flatten_nested) | ✗ FAIL | ✓ PASS |

---

## Example: How It Works

### Input Code
```python
def local_rank(scores):
    ranked = rank_scores(scores)
    return ranked
```

### SSA (Before Lineage)
```
parameters:
  scores → scores@0

assignments:
  ranked@1 ← rank_scores(scores@0)
    value_text: "rank_scores(scores)"
    inputs: {"scores": "scores@0"}

returns:
  return@1 ← ranked@1
    value_text: "ranked"
    inputs: {"ranked": "ranked@1"}
```

### SSA (After Lineage)
```
assignments:
  ranked@1 ← rank_scores(scores@0)
    lineage.call_sites: [CallSiteRecord("rank_scores", {})]
    lineage.wrapper_indicator: True
    lineage.direct_sources: [ValueLineageEdge("scores@0")]

returns:
  return@1 ← ranked@1
    lineage.call_sites: [CallSiteRecord("rank_scores", {})]
    lineage.direct_sources: [ValueLineageEdge("ranked@1")]
```

### Wrapper Detection
Old logic: `len(body) == 1` ✗ (2 statements)  
New logic: `ret.lineage.call_sites` ✓ → Extract "rank_scores" wrapper

---

## Debugging Tips

1. **Lineage is None**: Check `PythonSSABuilder.build()` calls lineage builder
2. **Call sites empty**: Debug `_calls_in_expr()` — check if AST parsing works
3. **Wrapper not detected**: Check `_wrapper_from_lineage()` is called with `ssa_map`
4. **Wrong call target**: Verify `_call_target()` handles ast.Name and ast.Attribute

---

## Full Documentation

See: `SSA_LINEAGE_IMPLEMENTATION_GUIDE.md` (586 lines, comprehensive reference)
