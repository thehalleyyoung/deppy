"""Cosheaf homology for root-cause analysis of bugs.

The **dual** of the presheaf bug detection pipeline.  While the presheaf
(contravariant functor) propagates type requirements *backward* through
restriction maps, the cosheaf (covariant functor) propagates
*witnesses and counterexamples forward* through data flow.

Given a gluing obstruction (bug) at site U, the cosheaf traces the
obstruction backward through the data-flow graph to find the
*originating site* — the root cause.

Mathematically:
  - A **cosheaf** F_! : Sites → Set is a covariant functor.
  - The **extension map** F_!(r : U → V) pushes witnesses forward.
  - **Cosheaf homology** H_0(F_!) = sections that agree on overlaps
    = the equivalence classes of root causes.
  - **H_1(F_!)** = obstructions to *separating* independent root causes.

The root-cause chain for an obstruction at line L is the maximal
backward path through the cosheaf, terminating at either:
  (a) a function parameter (external root cause), or
  (b) a literal/constructor (internal root cause), or
  (c) a call return (interprocedural root cause).
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple


class RootCauseKind(Enum):
    """Classification of root-cause sites."""
    PARAMETER = "parameter"        # Function argument (external)
    LITERAL = "literal"            # Constant literal (internal)
    CONSTRUCTOR = "constructor"    # Object/collection constructor (internal)
    CALL_RETURN = "call_return"    # Function call return (interprocedural)
    DEFAULT_ARG = "default_arg"    # Default parameter value
    GLOBAL = "global"              # Module-level variable
    UNKNOWN = "unknown"            # Could not trace further


@dataclass
class RootCauseSite:
    """A site in the cosheaf where an obstruction originates."""
    kind: RootCauseKind
    line: int
    col: int = 0
    variable: str = ""
    expression: str = ""
    explanation: str = ""


@dataclass
class CosheafChain:
    """A chain in the cosheaf homology: backward trace from bug to root cause.

    The chain records each intermediate site visited during backward
    propagation.  The first element is the bug site; the last is the root.
    """
    bug_line: int
    bug_type: str
    bug_variable: str
    chain: List[Tuple[int, str, str]] = field(default_factory=list)
    root_cause: Optional[RootCauseSite] = None
    confidence: float = 1.0

    @property
    def depth(self) -> int:
        return len(self.chain)

    @property
    def root_line(self) -> Optional[int]:
        return self.root_cause.line if self.root_cause else None


@dataclass
class CosheafHomologyResult:
    """Result of cosheaf homology computation.

    H_0 = equivalence classes of root causes (independent origins).
    H_1 rank = number of root causes that interact (share data flow).
    """
    chains: List[CosheafChain] = field(default_factory=list)
    root_cause_classes: List[List[CosheafChain]] = field(default_factory=list)
    h0_rank: int = 0  # Number of independent root-cause classes
    h1_rank: int = 0  # Number of interacting root-cause pairs

    def summary(self) -> str:
        lines = [f"Cosheaf root-cause analysis: {len(self.chains)} chains"]
        lines.append(f"  H_0 = {self.h0_rank} independent root-cause classes")
        if self.h1_rank > 0:
            lines.append(f"  H_1 = {self.h1_rank} interacting root-cause pairs")
        for i, cls in enumerate(self.root_cause_classes):
            rc = cls[0].root_cause
            if rc:
                lines.append(
                    f"  Class {i}: {rc.kind.value} at line {rc.line} "
                    f"({rc.variable}) → {len(cls)} bug(s)")
        return "\n".join(lines)


class CosheafRootCauseTracer:
    """Trace bugs backward through data flow to find root causes.

    Implements cosheaf propagation: given a bug at a use site,
    follow the data-flow edges backward (covariant push-forward
    in the cosheaf) to find where the problematic value originated.
    """

    def __init__(self, tree: ast.AST) -> None:
        self._tree = tree
        # Build def-use chains: variable → list of (line, assignment_rhs)
        self._defs: Dict[str, List[Tuple[int, ast.expr]]] = {}
        # Build parameter set
        self._params: Set[str] = set()
        self._build_def_use_chains()

    def _build_def_use_chains(self) -> None:
        """Walk AST to build definition sites for each variable."""
        for node in ast.walk(self._tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                for arg in node.args.args:
                    self._params.add(arg.arg)
                    if arg.annotation:
                        self._defs.setdefault(arg.arg, []).append(
                            (node.lineno, arg.annotation))
                # Default args
                for default in node.args.defaults:
                    pass  # Tracked via parameter

            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        self._defs.setdefault(target.id, []).append(
                            (getattr(node, 'lineno', 0), node.value))
                    elif isinstance(target, ast.Tuple):
                        for elt in target.elts:
                            if isinstance(elt, ast.Name):
                                self._defs.setdefault(elt.id, []).append(
                                    (getattr(node, 'lineno', 0), node.value))

            if isinstance(node, ast.AugAssign):
                if isinstance(node.target, ast.Name):
                    self._defs.setdefault(node.target.id, []).append(
                        (getattr(node, 'lineno', 0), node.value))

            if isinstance(node, ast.For):
                if isinstance(node.target, ast.Name):
                    self._defs.setdefault(node.target.id, []).append(
                        (getattr(node, 'lineno', 0), node.iter))

    def trace_obstruction(
        self, bug_line: int, bug_type: str, variable: str,
    ) -> CosheafChain:
        """Trace a single obstruction backward to its root cause.

        The cosheaf extension map F_!(r) pushes the obstruction witness
        backward through each assignment in the def-use chain.
        """
        chain = CosheafChain(
            bug_line=bug_line, bug_type=bug_type, bug_variable=variable)

        visited: Set[Tuple[str, int]] = set()
        self._trace_backward(variable, bug_line, chain, visited)

        return chain

    def _trace_backward(
        self,
        var: str,
        use_line: int,
        chain: CosheafChain,
        visited: Set[Tuple[str, int]],
    ) -> None:
        """Recursive backward trace through the cosheaf."""
        if (var, use_line) in visited:
            return
        visited.add((var, use_line))

        # Check if this is a parameter (external root cause)
        if var in self._params:
            chain.chain.append(
                (use_line, var, f"parameter '{var}'"))
            chain.root_cause = RootCauseSite(
                kind=RootCauseKind.PARAMETER,
                line=use_line, variable=var,
                explanation=f"Value flows in via parameter '{var}'")
            return

        # Find the most recent definition before use_line
        defs = self._defs.get(var, [])
        # Filter to definitions before or at the use line
        candidates = [(ln, rhs) for ln, rhs in defs if ln <= use_line]
        if not candidates:
            # Also check definitions after (for loop variables etc.)
            candidates = defs

        if not candidates:
            chain.root_cause = RootCauseSite(
                kind=RootCauseKind.UNKNOWN,
                line=use_line, variable=var,
                explanation=f"No definition found for '{var}'")
            return

        # Take the closest definition
        candidates.sort(key=lambda x: abs(x[0] - use_line))
        def_line, rhs = candidates[0]

        try:
            expr_str = ast.unparse(rhs)
        except Exception:
            expr_str = "?"

        chain.chain.append((def_line, var, expr_str))

        # Classify the RHS
        root = self._classify_rhs(rhs, def_line, var)
        if root is not None:
            chain.root_cause = root
            return

        # If RHS is a variable reference, continue backward
        if isinstance(rhs, ast.Name):
            self._trace_backward(rhs.id, def_line, chain, visited)
        elif isinstance(rhs, ast.Attribute) and isinstance(rhs.value, ast.Name):
            self._trace_backward(rhs.value.id, def_line, chain, visited)
        elif isinstance(rhs, ast.Subscript) and isinstance(rhs.value, ast.Name):
            self._trace_backward(rhs.value.id, def_line, chain, visited)
        elif isinstance(rhs, ast.BinOp):
            # Trace both sides of binary operations
            traced_any = False
            if isinstance(rhs.left, ast.Name):
                self._trace_backward(rhs.left.id, def_line, chain, visited)
                traced_any = True
            if isinstance(rhs.right, ast.Name):
                self._trace_backward(rhs.right.id, def_line, chain, visited)
                traced_any = True
            if not traced_any:
                chain.root_cause = RootCauseSite(
                    kind=RootCauseKind.UNKNOWN, line=def_line,
                    variable=var, expression=expr_str,
                    explanation=f"Complex expression: {expr_str}")
        else:
            chain.root_cause = RootCauseSite(
                kind=RootCauseKind.UNKNOWN, line=def_line,
                variable=var, expression=expr_str,
                explanation=f"Could not trace through: {expr_str}")

    def _classify_rhs(
        self, rhs: ast.expr, line: int, var: str,
    ) -> Optional[RootCauseSite]:
        """Classify an RHS expression as a root-cause site."""
        try:
            expr_str = ast.unparse(rhs)
        except Exception:
            expr_str = "?"

        if isinstance(rhs, ast.Constant):
            return RootCauseSite(
                kind=RootCauseKind.LITERAL, line=line,
                variable=var, expression=expr_str,
                explanation=f"Literal value: {rhs.value!r}")

        if isinstance(rhs, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
            return RootCauseSite(
                kind=RootCauseKind.CONSTRUCTOR, line=line,
                variable=var, expression=expr_str,
                explanation=f"Collection constructor at line {line}")

        if isinstance(rhs, ast.Call):
            if isinstance(rhs.func, ast.Name):
                fn = rhs.func.id
                if fn[0:1].isupper():
                    return RootCauseSite(
                        kind=RootCauseKind.CONSTRUCTOR, line=line,
                        variable=var, expression=expr_str,
                        explanation=f"Constructor call: {fn}()")
                return RootCauseSite(
                    kind=RootCauseKind.CALL_RETURN, line=line,
                    variable=var, expression=expr_str,
                    explanation=f"Return value from {fn}()")
            if isinstance(rhs.func, ast.Attribute):
                method = rhs.func.attr
                return RootCauseSite(
                    kind=RootCauseKind.CALL_RETURN, line=line,
                    variable=var, expression=expr_str,
                    explanation=f"Return value from .{method}()")

        return None

    def trace_all_obstructions(
        self, obstructions: list,
    ) -> CosheafHomologyResult:
        """Trace all obstructions and compute cosheaf homology.

        Groups chains by root-cause equivalence class (H_0) and
        computes the interaction rank (H_1).
        """
        chains: List[CosheafChain] = []
        for obs in obstructions:
            if obs.resolved_by_guard or obs.confidence <= 0:
                continue
            var = self._extract_variable(obs)
            if var:
                chain = self.trace_obstruction(
                    obs.line, obs.bug_type, var)
                chains.append(chain)

        # Compute H_0: group by root-cause site
        root_groups: Dict[Tuple[str, int], List[CosheafChain]] = {}
        no_root: List[CosheafChain] = []
        for chain in chains:
            if chain.root_cause and chain.root_cause.kind != RootCauseKind.UNKNOWN:
                key = (chain.root_cause.variable, chain.root_cause.line)
                root_groups.setdefault(key, []).append(chain)
            else:
                no_root.append(chain)

        classes = list(root_groups.values())
        if no_root:
            classes.append(no_root)

        # H_1: count interacting pairs (shared variables in chains)
        h1 = 0
        for i in range(len(classes)):
            vars_i = {c.bug_variable for c in classes[i]}
            for j in range(i + 1, len(classes)):
                vars_j = {c.bug_variable for c in classes[j]}
                if vars_i & vars_j:
                    h1 += 1

        return CosheafHomologyResult(
            chains=chains,
            root_cause_classes=classes,
            h0_rank=len(classes),
            h1_rank=h1,
        )

    @staticmethod
    def _extract_variable(obs) -> Optional[str]:
        """Extract the primary variable from an obstruction."""
        desc = obs.requirement.description if obs.requirement else ""
        # Common patterns: "variable 'x' may be ...", "'x' used before ..."
        import re
        m = re.search(r"['\"](\w+)['\"]", desc)
        if m:
            return m.group(1)
        # Try the AST node
        if obs.requirement and obs.requirement.ast_node:
            node = obs.requirement.ast_node
            if isinstance(node, ast.Name):
                return node.id
            if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
                return node.value.id
        # Fallback: if description is a single identifier, use it directly
        if desc and re.fullmatch(r"\w+", desc):
            return desc
        return None
