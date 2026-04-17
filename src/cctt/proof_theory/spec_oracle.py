"""Spec Oracle — LLM and template-based spec generation.

The static spec analyzer extracts what it can from AST structure.
But for `simplify(expr)`, the AST only tells us it returns `Expr`.
The real spec — `simplify(simplify(e)) == simplify(e)` — requires
SEMANTIC understanding of what the function does.

This module provides oracles that generate richer specs:

1. **SpecOracle** — ABC for spec generation
2. **TemplateOracle** — pattern-matching on common function shapes
3. **MockLLMOracle** — deterministic specs for testing
4. **LLMSpecOracle** — wraps an actual LLM call (requires API key)

All specs are in C4 language (Python boolean expressions, not English).
The oracle's output is always a CANDIDATE spec — it must still be verified
by the C4 compiler before becoming PROVED.

Usage::

    oracle = TemplateOracle()
    upgraded = oracle.generate_spec(
        source="def abs(x): return x if x >= 0 else -x",
        name="abs",
        params=["x"],
        static_spec=static_analyzer_result,
    )
    # upgraded.ensures now includes: ["result >= 0", "result == x or result == -x"]
    # upgraded.source == SpecSource.TEMPLATE
"""
from __future__ import annotations

import ast
import hashlib
import json
import logging
import os
import re
import subprocess
import textwrap
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from cctt.proof_theory.spec_inference import (
    C4Spec, SpecSource, SpecStrength, FiberClause,
    build_llm_spec_prompt, parse_llm_spec_response,
)

logger = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════
# Abstract oracle
# ═══════════════════════════════════════════════════════════════════

class SpecOracle(ABC):
    """Abstract base for spec generators.

    All oracles take a function's source + static spec and produce
    a richer spec. The oracle's output is a CANDIDATE — not yet proved.
    """

    @abstractmethod
    def generate_spec(
        self,
        source: str,
        name: str,
        params: List[str],
        static_spec: C4Spec,
        qualname: str = "",
        docstring: str = "",
    ) -> C4Spec:
        """Generate or upgrade a spec for a function.

        Args:
            source: Function source code
            name: Function name
            params: Parameter names
            static_spec: What the static analyzer already found
            qualname: Fully qualified name
            docstring: Docstring (semantic hint)

        Returns:
            Upgraded C4Spec (may be same as static_spec if no upgrade possible)
        """
        ...

    @property
    @abstractmethod
    def source_label(self) -> SpecSource:
        """What SpecSource to label the output with."""
        ...


# ═══════════════════════════════════════════════════════════════════
# Template Oracle — pattern-based spec generation
# ═══════════════════════════════════════════════════════════════════

class TemplateOracle(SpecOracle):
    """Generate specs by matching common function patterns.

    NOT an LLM — this is deterministic pattern matching.
    Labeled as TEMPLATE (not LLM) to be honest about provenance.

    Patterns recognized:
      - Identity: `return x` → returns_expr="x"
      - Absolute value: `return x if x >= 0 else -x` → result >= 0, result == x or result == -x
      - Max/min: `return a if a > b else b` → result >= a and result >= b
      - Length-preserving: `return [f(x) for x in lst]` → len(result) == len(lst)
      - Boolean predicate: `return all(...)`  → isinstance(result, bool)
      - Container wrap: `return list(x)` → isinstance(result, list)
      - Monotone: `def f(x): return g(x) + k` where k > 0 → result > g(x)
      - Idempotent: function calls itself internally → f(f(x)) == f(x) hint
      - Comparison: `return a == b` → isinstance(result, bool)
      - Default value: `return x if x is not None else default` → result is not None
    """

    @property
    def source_label(self) -> SpecSource:
        return SpecSource.STATIC  # Honest: template is static, not LLM

    def generate_spec(
        self,
        source: str,
        name: str,
        params: List[str],
        static_spec: C4Spec,
        qualname: str = "",
        docstring: str = "",
    ) -> C4Spec:
        # Only upgrade if static spec is insufficient
        if static_spec.is_formal:
            return static_spec

        try:
            tree = ast.parse(textwrap.dedent(source))
        except SyntaxError:
            return static_spec

        fn_node = self._find_function(tree, name)
        if fn_node is None:
            return static_spec

        new_ensures = list(static_spec.ensures)
        new_requires = list(static_spec.requires)
        new_returns = static_spec.returns_expr
        new_fibers = list(static_spec.fibers)
        upgraded = False

        actual_params = params or [a.arg for a in fn_node.args.args]

        # Try each pattern
        for pattern_fn in [
            self._pattern_identity,
            self._pattern_none_default,
            self._pattern_container_wrap,
            self._pattern_boolean_predicate,
            self._pattern_length_preserving,
            self._pattern_comparison,
            self._pattern_idempotent_hint,
            self._pattern_constructor,
            self._pattern_getter,
            self._pattern_delegation,
        ]:
            result = pattern_fn(fn_node, name, actual_params, docstring)
            if result:
                for e in result.get("ensures", []):
                    if e not in new_ensures:
                        new_ensures.append(e)
                        upgraded = True
                for r in result.get("requires", []):
                    if r not in new_requires:
                        new_requires.append(r)
                        upgraded = True
                if result.get("returns_expr") and not new_returns:
                    new_returns = result["returns_expr"]
                    upgraded = True

        if not upgraded:
            return static_spec

        spec = C4Spec(
            requires=new_requires,
            ensures=new_ensures,
            returns_expr=new_returns,
            fibers=new_fibers,
            purity=static_spec.purity,
            source=self.source_label,
            effects=static_spec.effects,
            state_contract=static_spec.state_contract,
        )
        spec.strength = spec.classify_strength()
        return spec

    # ── Patterns ──────────────────────────────────────────────────

    def _pattern_identity(self, fn: ast.FunctionDef, name: str,
                          params: List[str], doc: str) -> Optional[Dict]:
        """Return param directly."""
        ret = self._single_return(fn)
        if ret and isinstance(ret, ast.Name) and ret.id in params:
            return {"returns_expr": ret.id, "ensures": [f"result == {ret.id}"]}
        return None

    def _pattern_none_default(self, fn: ast.FunctionDef, name: str,
                              params: List[str], doc: str) -> Optional[Dict]:
        """return x if x is not None else default."""
        ret = self._single_return(fn)
        if isinstance(ret, ast.IfExp):
            # Check for `is not None` test
            test = ret.test
            if isinstance(test, ast.Compare) and len(test.ops) == 1:
                if isinstance(test.ops[0], ast.IsNot):
                    if isinstance(test.comparators[0], ast.Constant) and test.comparators[0].value is None:
                        return {"ensures": ["result is not None"]}
        return None

    def _pattern_container_wrap(self, fn: ast.FunctionDef, name: str,
                                params: List[str], doc: str) -> Optional[Dict]:
        """return list(x), dict(x), set(x), tuple(x)."""
        ret = self._single_return(fn)
        if isinstance(ret, ast.Call) and isinstance(ret.func, ast.Name):
            if ret.func.id in ("list", "dict", "set", "tuple", "frozenset"):
                return {"ensures": [f"isinstance(result, {ret.func.id})"]}
        return None

    def _pattern_boolean_predicate(self, fn: ast.FunctionDef, name: str,
                                   params: List[str], doc: str) -> Optional[Dict]:
        """return all(...), any(...), isinstance(...), bool(...)."""
        ret = self._single_return(fn)
        if isinstance(ret, ast.Call) and isinstance(ret.func, ast.Name):
            if ret.func.id in ("all", "any", "isinstance", "bool", "callable",
                               "hasattr"):
                return {"ensures": ["isinstance(result, bool)"]}
        if isinstance(ret, ast.Compare):
            return {"ensures": ["isinstance(result, bool)"]}
        if isinstance(ret, ast.BoolOp):
            return {"ensures": ["isinstance(result, bool)"]}
        return None

    def _pattern_length_preserving(self, fn: ast.FunctionDef, name: str,
                                   params: List[str], doc: str) -> Optional[Dict]:
        """return [f(x) for x in lst] — preserves length."""
        ret = self._single_return(fn)
        if isinstance(ret, ast.ListComp):
            for gen in ret.generators:
                if isinstance(gen.iter, ast.Name) and gen.iter.id in params:
                    return {
                        "ensures": [
                            "isinstance(result, list)",
                            f"len(result) == len({gen.iter.id})",
                        ],
                    }
        return None

    def _pattern_comparison(self, fn: ast.FunctionDef, name: str,
                            params: List[str], doc: str) -> Optional[Dict]:
        """return a == b → bool result."""
        ret = self._single_return(fn)
        if isinstance(ret, ast.Compare):
            return {"ensures": ["isinstance(result, bool)", "result == True or result == False"]}
        return None

    def _pattern_idempotent_hint(self, fn: ast.FunctionDef, name: str,
                                 params: List[str], doc: str) -> Optional[Dict]:
        """If function calls itself → hint at idempotence."""
        for node in ast.walk(fn):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                if node.func.id == name and node != fn:
                    # Self-recursive call — might be idempotent
                    return {"ensures": [f"# HINT: {name} may be idempotent: {name}({name}(x)) == {name}(x)"]}
        return None

    def _pattern_constructor(self, fn: ast.FunctionDef, name: str,
                             params: List[str], doc: str) -> Optional[Dict]:
        """__init__ → sets attributes from params."""
        if name != "__init__":
            return None
        ensures = []
        for node in ast.walk(fn):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Attribute):
                        if (isinstance(target.value, ast.Name)
                                and target.value.id == "self"):
                            if isinstance(node.value, ast.Name) and node.value.id in params:
                                ensures.append(
                                    f"self.{target.attr} == {node.value.id}"
                                )
        return {"ensures": ensures} if ensures else None

    def _pattern_getter(self, fn: ast.FunctionDef, name: str,
                        params: List[str], doc: str) -> Optional[Dict]:
        """return self.attr → result == self.attr."""
        ret = self._single_return(fn)
        if isinstance(ret, ast.Attribute):
            if isinstance(ret.value, ast.Name) and ret.value.id == "self":
                return {"returns_expr": f"self.{ret.attr}",
                        "ensures": [f"result == self.{ret.attr}"]}
        return None

    def _pattern_delegation(self, fn: ast.FunctionDef, name: str,
                            params: List[str], doc: str) -> Optional[Dict]:
        """return other_func(args) → result == other_func(args)."""
        ret = self._single_return(fn)
        if isinstance(ret, ast.Call) and isinstance(ret.func, ast.Name):
            func_name = ret.func.id
            if func_name not in ("list", "dict", "set", "tuple", "frozenset",
                                 "all", "any", "isinstance", "bool", "callable",
                                 "hasattr", "len", "str", "int", "float",
                                 "sorted", "reversed", "range", "enumerate",
                                 "zip", "map", "filter", "type", "super"):
                args_str = ", ".join(ast.unparse(a) for a in ret.args)
                return {"returns_expr": f"{func_name}({args_str})"}
        return None

    # ── Helpers ───────────────────────────────────────────────────

    def _find_function(self, tree: ast.Module, name: str) -> Optional[ast.FunctionDef]:
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name == name:
                    return node
        return None

    def _single_return(self, fn: ast.FunctionDef) -> Optional[ast.expr]:
        """Extract the return expression if there's exactly one return."""
        returns = []
        for node in ast.walk(fn):
            if isinstance(node, ast.Return) and node.value is not None:
                returns.append(node.value)
        if len(returns) == 1:
            return returns[0]
        return None


# ═══════════════════════════════════════════════════════════════════
# Mock LLM Oracle — deterministic specs for testing
# ═══════════════════════════════════════════════════════════════════

class MockLLMOracle(SpecOracle):
    """Deterministic mock oracle with hardcoded specs for common functions.

    Used in tests. The "LLM" is a lookup table.
    """

    KNOWN_SPECS: Dict[str, Dict[str, Any]] = {
        "abs": {
            "ensures": ["result >= 0", "result == x or result == -x"],
            "requires": [],
            "returns_expr": "x if x >= 0 else -x",
        },
        "max": {
            "ensures": ["result >= a", "result >= b", "result == a or result == b"],
            "requires": [],
        },
        "min": {
            "ensures": ["result <= a", "result <= b", "result == a or result == b"],
            "requires": [],
        },
        "len": {
            "ensures": ["result >= 0", "isinstance(result, int)"],
            "requires": [],
        },
        "sorted": {
            "ensures": [
                "isinstance(result, list)",
                "len(result) == len(iterable)",
                "all(result[i] <= result[i+1] for i in range(len(result)-1))",
            ],
        },
        "reversed": {
            "ensures": ["len(list(result)) == len(seq)"],
        },
        "sum": {
            "ensures": ["isinstance(result, (int, float))"],
        },
        "simplify": {
            "ensures": [
                "isinstance(result, Expr)",
                "simplify(result) == result",  # idempotent
            ],
        },
        "expand": {
            "ensures": [
                "isinstance(result, Expr)",
                "expand(result) == result",  # idempotent
            ],
        },
        "sqrt": {
            "ensures": ["result >= 0", "result * result == x"],
            "requires": ["x >= 0"],
        },
        "factorial": {
            "ensures": ["result >= 1", "isinstance(result, int)"],
            "requires": ["isinstance(n, int)", "n >= 0"],
        },
        "gcd": {
            "ensures": [
                "result >= 0",
                "a % result == 0",
                "b % result == 0",
            ],
            "requires": ["isinstance(a, int)", "isinstance(b, int)"],
        },
    }

    @property
    def source_label(self) -> SpecSource:
        return SpecSource.LLM

    def generate_spec(
        self,
        source: str,
        name: str,
        params: List[str],
        static_spec: C4Spec,
        qualname: str = "",
        docstring: str = "",
    ) -> C4Spec:
        # Look up by function name (case-insensitive suffix match)
        lookup_name = name.lower()
        known = self.KNOWN_SPECS.get(lookup_name)
        if known is None:
            # Try suffix of qualname
            if qualname:
                for suffix in qualname.split(".")[::-1]:
                    known = self.KNOWN_SPECS.get(suffix.lower())
                    if known:
                        break

        if known is None:
            return static_spec

        # Merge known spec with static spec
        new_ensures = list(static_spec.ensures)
        for e in known.get("ensures", []):
            if e not in new_ensures:
                new_ensures.append(e)

        new_requires = list(static_spec.requires)
        for r in known.get("requires", []):
            if r not in new_requires:
                new_requires.append(r)

        return C4Spec(
            requires=new_requires,
            ensures=new_ensures,
            returns_expr=known.get("returns_expr", static_spec.returns_expr),
            fibers=static_spec.fibers,
            purity=static_spec.purity,
            source=self.source_label,
            effects=static_spec.effects,
            state_contract=static_spec.state_contract,
        )


# ═══════════════════════════════════════════════════════════════════
# LLM Spec Oracle — wraps actual LLM call
# ═══════════════════════════════════════════════════════════════════

class LLMSpecOracle(SpecOracle):
    """Oracle that calls an LLM to generate specs.

    Uses the prompt template from spec_inference.build_llm_spec_prompt()
    and parses the response with parse_llm_spec_response().

    Requires a callback function that takes a prompt string and returns
    the LLM's response string.
    """

    def __init__(self, llm_call: Any = None):
        """
        Args:
            llm_call: Callable[[str], str] — takes prompt, returns response.
                      If None, falls back to static spec.
        """
        self._llm_call = llm_call

    @property
    def source_label(self) -> SpecSource:
        return SpecSource.LLM

    def generate_spec(
        self,
        source: str,
        name: str,
        params: List[str],
        static_spec: C4Spec,
        qualname: str = "",
        docstring: str = "",
    ) -> C4Spec:
        if self._llm_call is None:
            return static_spec

        prompt = build_llm_spec_prompt(source, qualname or name, name, docstring)
        try:
            response = self._llm_call(prompt)
        except Exception:
            return static_spec

        # Parse LLM response using existing parser
        llm_spec = parse_llm_spec_response(response)
        if llm_spec and not llm_spec.is_trivial:
            llm_spec.source = self.source_label
            return llm_spec

        return static_spec


# ═══════════════════════════════════════════════════════════════════
# Copilot Spec Oracle — uses copilot CLI to generate intent specs
# ═══════════════════════════════════════════════════════════════════

_SPEC_SYSTEM = """\
You are a formal specification generator for Python functions.
Your job is to describe the INTENT of each function — what it SHOULD do,
not merely restating what the code does.

For each function, output a JSON object with these keys:
- "requires": list of preconditions as Python boolean expressions over the parameters
- "ensures": list of postconditions as Python boolean expressions over "result"
- "returns_expr": the exact return expression if determinable, else null
- "fibers": list of case-analysis objects, each with:
    - "name": a short label for the case
    - "guard": Python boolean expression for when this case applies
    - "ensures": list of postconditions specific to this case

Rules:
1. Specs must be PYTHON BOOLEAN EXPRESSIONS, not English. E.g. "result >= 0", not "returns a non-negative number".
2. Postconditions use the variable name "result" for the return value.
3. Preconditions use the actual parameter names from the function signature.
4. For mathematical functions, state mathematical properties (idempotence, commutativity, monotonicity, etc.)
5. For data structure operations, state structural invariants (length preservation, containment, ordering, etc.)
6. For predicates (is_*, has_*), ensure "isinstance(result, bool)".
7. For constructors (__init__), state what attributes are set.
8. Distinguish INTENT from IMPLEMENTATION: e.g. for sort(), the intent spec is
   "all(result[i] <= result[i+1] for i in range(len(result)-1))" and
   "set(result) == set(lst)", NOT the sorting algorithm's steps.
9. Do NOT just restate the code. If a function says "return x + 1", saying
   "result == x + 1" is an IMPLEMENTATION spec. The INTENT spec is the
   mathematical property that justifies WHY x+1 is correct.
10. For library functions (sympy, numpy, etc.), use domain knowledge about
    what the function mathematically should do.

Output ONLY valid JSON. No markdown fences, no explanation.\
"""


def _sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()[:12]


class CopilotSpecOracle(SpecOracle):
    """Oracle that calls copilot CLI to generate intent specs.

    Uses `copilot -p {prompt} --autopilot --allow-all-tools` as the LLM backend.
    Supports batching: multiple functions per copilot call to reduce overhead.
    Caches results to disk to avoid re-calling for the same function.
    """

    def __init__(
        self,
        binary: str = "copilot",
        model: str = "",
        effort: str = "low",
        timeout: int = 90,
        batch_size: int = 10,
        cache_dir: Optional[str] = None,
    ):
        self.binary = binary
        self.model = model
        self.effort = effort
        self.timeout = timeout
        self.batch_size = batch_size
        self._cache: Dict[str, C4Spec] = {}
        self._cache_dir = Path(cache_dir) if cache_dir else None
        self._call_count = 0
        self._hit_count = 0
        if self._cache_dir:
            self._cache_dir.mkdir(parents=True, exist_ok=True)
            self._load_disk_cache()

    def _load_disk_cache(self) -> None:
        if not self._cache_dir:
            return
        cache_file = self._cache_dir / "spec_cache.json"
        if cache_file.exists():
            try:
                data = json.loads(cache_file.read_text())
                for key, spec_dict in data.items():
                    self._cache[key] = C4Spec.from_json(spec_dict)
                logger.info("Loaded %d cached specs from %s", len(self._cache), cache_file)
            except Exception as e:
                logger.warning("Failed to load spec cache: %s", e)

    def save_cache(self) -> None:
        if not self._cache_dir:
            return
        cache_file = self._cache_dir / "spec_cache.json"
        data = {k: v.to_json() for k, v in self._cache.items()}
        cache_file.write_text(json.dumps(data, indent=2))

    def _cache_key(self, source: str, name: str) -> str:
        return f"{name}:{_sha(source)}"

    @property
    def source_label(self) -> SpecSource:
        return SpecSource.LLM

    def _call_copilot(self, prompt: str) -> Optional[str]:
        """Call copilot CLI and return stdout."""
        cmd = [self.binary, "-p", prompt, "--autopilot", "--allow-all-tools",
               "--no-custom-instructions", "--disable-builtin-mcps", "--no-ask-user"]
        if self.model:
            cmd.extend(["--model", self.model])
        if self.effort:
            cmd.extend(["--effort", self.effort])
        try:
            r = subprocess.run(
                cmd, capture_output=True, text=True,
                timeout=self.timeout,
                env={**os.environ, "NO_COLOR": "1"},
            )
            if r.returncode == 0 and r.stdout.strip():
                return r.stdout.strip()
            elif r.stderr:
                logger.warning("copilot stderr: %s", r.stderr[:200])
        except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as e:
            logger.warning("copilot call failed: %s", e)
        return None

    def _parse_json_from_response(self, raw: str) -> Optional[Any]:
        """Extract JSON from copilot response, handling markdown fences."""
        # Try direct parse
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            pass
        # Strip markdown fences
        stripped = re.sub(r'```(?:json)?\s*', '', raw).strip().rstrip('`').strip()
        try:
            return json.loads(stripped)
        except json.JSONDecodeError:
            pass
        # Find first { ... } block
        depth = 0
        start = -1
        for i, ch in enumerate(raw):
            if ch == '{':
                if depth == 0:
                    start = i
                depth += 1
            elif ch == '}':
                depth -= 1
                if depth == 0 and start >= 0:
                    try:
                        return json.loads(raw[start:i+1])
                    except json.JSONDecodeError:
                        break
        # Find first [ ... ] block (for batch responses)
        depth = 0
        start = -1
        for i, ch in enumerate(raw):
            if ch == '[':
                if depth == 0:
                    start = i
                depth += 1
            elif ch == ']':
                depth -= 1
                if depth == 0 and start >= 0:
                    try:
                        return json.loads(raw[start:i+1])
                    except json.JSONDecodeError:
                        break
        return None

    def _spec_from_dict(self, d: Dict[str, Any]) -> C4Spec:
        """Convert a parsed JSON dict to a C4Spec."""
        fibers = []
        for fb in d.get("fibers", []):
            if isinstance(fb, dict):
                fibers.append(FiberClause(
                    name=fb.get("name", ""),
                    guard=fb.get("guard", "True"),
                    ensures=fb.get("ensures", []),
                    returns_expr=fb.get("returns_expr"),
                ))
        spec = C4Spec(
            requires=d.get("requires", []),
            ensures=d.get("ensures", []),
            returns_expr=d.get("returns_expr"),
            fibers=fibers,
            source=SpecSource.LLM,
        )
        spec.strength = spec.classify_strength()
        return spec

    def generate_spec(
        self,
        source: str,
        name: str,
        params: List[str],
        static_spec: C4Spec,
        qualname: str = "",
        docstring: str = "",
    ) -> C4Spec:
        """Generate a single spec via copilot CLI."""
        key = self._cache_key(source, qualname or name)
        if key in self._cache:
            self._hit_count += 1
            return self._cache[key]

        self._call_count += 1
        prompt = f"""{_SPEC_SYSTEM}

Function to specify:
```python
{source.strip()[:3000]}
```

Qualified name: {qualname or name}
Parameter names: {', '.join(params)}
{"Docstring: " + docstring[:500] if docstring else ""}

Output the JSON spec object:"""

        raw = self._call_copilot(prompt)
        if not raw:
            return static_spec

        parsed = self._parse_json_from_response(raw)
        if isinstance(parsed, dict):
            spec = self._spec_from_dict(parsed)
            if not spec.is_trivial:
                self._cache[key] = spec
                return spec

        return static_spec

    def generate_specs_batch(
        self,
        functions: List[Dict[str, Any]],
    ) -> Dict[str, C4Spec]:
        """Generate specs for multiple functions in one copilot call.

        Args:
            functions: List of dicts with keys: name, qualname, source, params, docstring

        Returns:
            Dict mapping qualname -> C4Spec for successfully generated specs
        """
        results: Dict[str, C4Spec] = {}
        uncached: List[Dict[str, Any]] = []

        for fn in functions:
            key = self._cache_key(fn["source"], fn.get("qualname", fn["name"]))
            if key in self._cache:
                results[fn.get("qualname", fn["name"])] = self._cache[key]
                self._hit_count += 1
            else:
                uncached.append(fn)

        if not uncached:
            return results

        # Process in batches
        for i in range(0, len(uncached), self.batch_size):
            batch = uncached[i:i + self.batch_size]
            batch_results = self._call_batch(batch)
            results.update(batch_results)
            # Save cache periodically
            if self._cache_dir and (i + self.batch_size) % 50 == 0:
                self.save_cache()

        return results

    def _call_batch(self, batch: List[Dict[str, Any]]) -> Dict[str, C4Spec]:
        """Call copilot once for a batch of functions, fallback to individual calls."""
        results: Dict[str, C4Spec] = {}

        if len(batch) == 1:
            fn = batch[0]
            spec = self.generate_spec(
                fn["source"], fn["name"],
                fn.get("params", []),
                C4Spec(),
                fn.get("qualname", fn["name"]),
                fn.get("docstring", ""),
            )
            if not spec.is_trivial:
                results[fn.get("qualname", fn["name"])] = spec
            return results

        # Build batch prompt
        fn_blocks = []
        for idx, fn in enumerate(batch):
            src = fn["source"].strip()[:1500]
            doc = fn.get("docstring", "")
            doc_line = f"\nDocstring: {doc[:200]}" if doc else ""
            fn_blocks.append(
                f'### Function {idx + 1}: {fn.get("qualname", fn["name"])}\n'
                f'Parameters: {", ".join(fn.get("params", []))}{doc_line}\n'
                f'```python\n{src}\n```\n'
            )

        prompt = f"""{_SPEC_SYSTEM}

Generate specs for ALL {len(batch)} functions below.
Output a JSON ARRAY of {len(batch)} objects, one per function, in the same order.
Each object has keys: "name", "requires", "ensures", "returns_expr", "fibers".

{"".join(fn_blocks)}

Output ONLY the JSON array:"""

        self._call_count += 1
        raw = self._call_copilot(prompt)
        if not raw:
            # Fallback: try each individually
            for fn in batch:
                spec = self.generate_spec(
                    fn["source"], fn["name"], fn.get("params", []),
                    C4Spec(), fn.get("qualname", fn["name"]), fn.get("docstring", ""),
                )
                if not spec.is_trivial:
                    results[fn.get("qualname", fn["name"])] = spec
            return results

        parsed = self._parse_json_from_response(raw)

        if isinstance(parsed, list):
            for idx, item in enumerate(parsed):
                if idx < len(batch) and isinstance(item, dict):
                    fn = batch[idx]
                    spec = self._spec_from_dict(item)
                    if not spec.is_trivial:
                        qn = fn.get("qualname", fn["name"])
                        key = self._cache_key(fn["source"], qn)
                        self._cache[key] = spec
                        results[qn] = spec
        elif isinstance(parsed, dict):
            # LLM returned a single object — try to match to first function
            fn = batch[0]
            spec = self._spec_from_dict(parsed)
            if not spec.is_trivial:
                qn = fn.get("qualname", fn["name"])
                key = self._cache_key(fn["source"], qn)
                self._cache[key] = spec
                results[qn] = spec

        # Fallback: individually call for any functions not in results
        covered = set(results.keys())
        for fn in batch:
            qn = fn.get("qualname", fn["name"])
            if qn not in covered:
                spec = self.generate_spec(
                    fn["source"], fn["name"], fn.get("params", []),
                    C4Spec(), qn, fn.get("docstring", ""),
                )
                if not spec.is_trivial:
                    results[qn] = spec

        return results

    @property
    def stats(self) -> Dict[str, int]:
        return {
            "calls": self._call_count,
            "cache_hits": self._hit_count,
            "cached_specs": len(self._cache),
        }


# ═══════════════════════════════════════════════════════════════════
# Upgrade function — try oracle when static spec is insufficient
# ═══════════════════════════════════════════════════════════════════

def upgrade_spec(
    source: str,
    name: str,
    params: List[str],
    static_spec: C4Spec,
    oracle: Optional[SpecOracle] = None,
    qualname: str = "",
    docstring: str = "",
) -> C4Spec:
    """Try to upgrade a static spec using an oracle.

    If static spec is already FORMAL, returns it unchanged.
    If oracle produces a richer spec, returns the upgrade.
    Otherwise returns the original static spec.
    """
    if static_spec.is_formal:
        return static_spec

    if oracle is None:
        oracle = TemplateOracle()

    upgraded = oracle.generate_spec(
        source, name, params, static_spec, qualname, docstring,
    )

    # Only use upgrade if it's actually richer
    if upgraded.classify_strength().value != "trivial":
        return upgraded

    return static_spec
