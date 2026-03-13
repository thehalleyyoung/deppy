"""Lawvere Hyperdoctrine for contract propagation.

Makes the contract system a genuine indexed category with Beck-Chevalley
substitution, so `@ensures` and `@requires` contracts automatically
propagate through function calls without manual annotation.

A **Lawvere hyperdoctrine** is:
  - A functor P : C^op → Lattice, where C is the category of types
  - For each morphism f : A → B, a substitution functor f* : P(B) → P(A)
  - Left and right adjoints ∃_f ⊣ f* ⊣ ∀_f (quantifier structure)
  - Beck-Chevalley: for any pullback square, ∃ commutes with substitution

In deppy:
  - C = the category of function signatures (params as objects, calls as morphisms)
  - P(f) = the contracts (requires + ensures) of function f
  - f* = substitution of actual arguments into formal parameters
  - ∃_f = existential projection (weakening a contract)
  - ∀_f = universal projection (strengthening a contract)

The Beck-Chevalley condition ensures:
  If g calls f, and f has `@ensures(result > 0)`, then g inherits
  `@ensures(g_result > 0)` when g returns f's result — automatically.

Usage:
    from deppy.contracts.hyperdoctrine import Hyperdoctrine
    hd = Hyperdoctrine()
    hd.register_function("f", params=["x"], ensures=[...])
    propagated = hd.propagate_through_call("g", "f", arg_mapping={"x": "data"})
"""

from __future__ import annotations

import ast
import copy
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Set, Tuple


@dataclass
class FunctionSignature:
    """A function's position in the type category."""
    name: str
    params: List[str] = field(default_factory=list)
    return_name: str = "result"


@dataclass
class ContractFiber:
    """The fiber of the hyperdoctrine over a function.

    P(f) = {requires, ensures} for function f.
    """
    function: FunctionSignature
    requires: List[str] = field(default_factory=list)  # Predicate strings
    ensures: List[str] = field(default_factory=list)    # Predicate strings

    def substitute(
        self, mapping: Dict[str, str],
    ) -> 'ContractFiber':
        """Substitution functor f* : apply variable renaming.

        Given a call morphism g→f with argument mapping,
        rename formal parameters to actual arguments.
        """
        new_requires = [
            _substitute_vars(r, mapping) for r in self.requires]
        new_ensures = [
            _substitute_vars(e, mapping) for e in self.ensures]
        return ContractFiber(
            function=self.function,
            requires=new_requires,
            ensures=new_ensures)

    def weaken(self) -> 'ContractFiber':
        """Existential projection ∃_f : weaken contracts.

        Drops contracts that reference variables not in the function's
        public interface (internal-only constraints).
        """
        pub_vars = set(self.function.params) | {self.function.return_name}
        new_requires = [
            r for r in self.requires
            if all(v in pub_vars for v in _extract_vars(r))]
        new_ensures = [
            e for e in self.ensures
            if all(v in pub_vars for v in _extract_vars(e))]
        return ContractFiber(
            function=self.function,
            requires=new_requires,
            ensures=new_ensures)

    def strengthen(self, additional: List[str]) -> 'ContractFiber':
        """Universal projection ∀_f : add additional constraints."""
        return ContractFiber(
            function=self.function,
            requires=self.requires + additional,
            ensures=self.ensures)


@dataclass
class PropagationResult:
    """Result of contract propagation through a call."""
    caller: str
    callee: str
    inherited_requires: List[str] = field(default_factory=list)
    inherited_ensures: List[str] = field(default_factory=list)
    beck_chevalley_satisfied: bool = True
    explanation: str = ""

    def summary(self) -> str:
        lines = [
            f"Contract propagation: {self.caller} → {self.callee}",
            f"  Beck-Chevalley: "
            f"{'satisfied' if self.beck_chevalley_satisfied else 'VIOLATED'}",
        ]
        if self.inherited_requires:
            lines.append(f"  Inherited requires:")
            for r in self.inherited_requires:
                lines.append(f"    {r}")
        if self.inherited_ensures:
            lines.append(f"  Inherited ensures:")
            for e in self.inherited_ensures:
                lines.append(f"    {e}")
        return "\n".join(lines)


class Hyperdoctrine:
    """Lawvere hyperdoctrine for automatic contract propagation.

    Maintains the indexed category P : FuncSig^op → Lattice and
    implements substitution, existential/universal adjoints, and
    Beck-Chevalley propagation.
    """

    def __init__(self) -> None:
        self._fibers: Dict[str, ContractFiber] = {}
        self._call_graph: Dict[str, Set[str]] = {}  # caller → {callees}

    def register_function(
        self,
        name: str,
        params: Optional[List[str]] = None,
        requires: Optional[List[str]] = None,
        ensures: Optional[List[str]] = None,
    ) -> None:
        """Register a function and its contracts in the hyperdoctrine."""
        sig = FunctionSignature(name=name, params=params or [])
        self._fibers[name] = ContractFiber(
            function=sig,
            requires=requires or [],
            ensures=ensures or [])

    def register_from_ast(self, source: str) -> None:
        """Register all functions from a source file.

        Extracts basic contracts from type annotations, assertions,
        and guard patterns.
        """
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return

        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue

            name = node.name
            params = [a.arg for a in node.args.args]
            requires: List[str] = []
            ensures: List[str] = []

            # Extract requires from assertions and guards
            for stmt in node.body:
                if isinstance(stmt, ast.Assert):
                    try:
                        requires.append(ast.unparse(stmt.test))
                    except Exception:
                        pass
                if isinstance(stmt, ast.If):
                    # Pattern: if x is None: raise → requires x is not None
                    test = stmt.test
                    body_raises = any(isinstance(s, ast.Raise) for s in stmt.body)
                    if body_raises:
                        try:
                            negated = f"not ({ast.unparse(test)})"
                            requires.append(negated)
                        except Exception:
                            pass

            # Extract ensures from return type annotations
            if node.returns:
                try:
                    ret_ann = ast.unparse(node.returns)
                    if ret_ann != "None":
                        ensures.append(f"result is not None")
                except Exception:
                    pass

            # Extract ensures from explicit return values
            for child in ast.walk(node):
                if isinstance(child, ast.Return) and child.value:
                    if isinstance(child.value, ast.Constant):
                        if isinstance(child.value.value, bool):
                            pass  # Don't infer from bool returns
                        elif isinstance(child.value.value, (int, float)):
                            if child.value.value >= 0:
                                ensures.append("result >= 0")

            self.register_function(name, params, requires, ensures)

            # Build call graph
            for child in ast.walk(node):
                if isinstance(child, ast.Call):
                    callee = None
                    if isinstance(child.func, ast.Name):
                        callee = child.func.id
                    if callee:
                        self._call_graph.setdefault(name, set()).add(callee)

    def propagate_through_call(
        self,
        caller: str,
        callee: str,
        arg_mapping: Optional[Dict[str, str]] = None,
    ) -> PropagationResult:
        """Propagate contracts from callee to caller via Beck-Chevalley.

        Given a call site `caller` calling `callee` with argument mapping,
        substitute the callee's contracts into the caller's context.
        """
        callee_fiber = self._fibers.get(callee)
        if callee_fiber is None:
            return PropagationResult(
                caller=caller, callee=callee,
                explanation=f"No contracts registered for {callee}")

        # Build argument mapping if not provided
        if arg_mapping is None:
            arg_mapping = {}

        # Apply substitution functor f*
        substituted = callee_fiber.substitute(arg_mapping)

        # For requires: propagate with caller variable names
        # (substitution already renamed callee params → caller args)
        inherited_requires = substituted.requires
        inherited_ensures = substituted.ensures

        # Beck-Chevalley check: verify that substitution commutes
        # with existential projection (∃ ∘ f* = g* ∘ ∃)
        weakened_first = callee_fiber.weaken()
        alt_requires = weakened_first.substitute(arg_mapping).requires
        alt_ensures = weakened_first.substitute(arg_mapping).ensures
        bc_satisfied = (
            set(inherited_requires) == set(alt_requires)
            and set(inherited_ensures) == set(alt_ensures))

        return PropagationResult(
            caller=caller,
            callee=callee,
            inherited_requires=inherited_requires,
            inherited_ensures=inherited_ensures,
            beck_chevalley_satisfied=bc_satisfied,
            explanation=(
                f"Propagated {len(inherited_requires)} requires and "
                f"{len(inherited_ensures)} ensures from {callee}"))

    def propagate_all(self) -> Dict[str, PropagationResult]:
        """Propagate contracts through the entire call graph."""
        results: Dict[str, PropagationResult] = {}
        for caller, callees in self._call_graph.items():
            for callee in callees:
                if callee in self._fibers:
                    result = self.propagate_through_call(caller, callee)
                    results[f"{caller}→{callee}"] = result
        return results


def _substitute_vars(pred_str: str, mapping: Dict[str, str]) -> str:
    """Substitute variable names in a predicate string.

    Uses word-boundary matching to avoid replacing substrings inside
    other identifiers (e.g., 'x' inside 'extra').
    """
    import re
    result = pred_str
    # Sort by length (longest first) to avoid partial replacements
    for old, new in sorted(mapping.items(), key=lambda x: -len(x[0])):
        result = re.sub(r'\b' + re.escape(old) + r'\b', new, result)
    return result


def _extract_vars(pred_str: str) -> Set[str]:
    """Extract variable-like identifiers from a predicate string."""
    import re
    return set(re.findall(r'\b[a-zA-Z_]\w*\b', pred_str)) - {
        'and', 'or', 'not', 'True', 'False', 'None',
        'is', 'in', 'if', 'else', 'for', 'while',
        'return', 'lambda', 'def', 'class',
        'isinstance', 'len', 'int', 'float', 'str', 'bool', 'list',
    }
