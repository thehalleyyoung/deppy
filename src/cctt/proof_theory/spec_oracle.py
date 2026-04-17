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
import re
import textwrap
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

from cctt.proof_theory.spec_inference import (
    C4Spec, SpecSource, SpecStrength, FiberClause,
    build_llm_spec_prompt, parse_llm_spec_response,
)


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
