"""Call graph construction and analysis from Python AST.

Builds a call graph from module-level AST, tracking which functions call which
other functions.  Provides topological ordering, strongly-connected-component
detection (for mutual recursion), and callee/caller lookups.

In the sheaf-descent view, the call graph determines which function covers
need interprocedural section transport: for every call edge F -> G, sections
from G's output boundary must be imported into F's call-result sites, and
F's actual-argument sections must be transported to G's input boundary.
"""

from __future__ import annotations

import ast
from collections import defaultdict, deque
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from deppy.core._protocols import SiteId, SiteKind


# ---------------------------------------------------------------------------
# Call edge
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CallEdge:
    """A directed edge in the call graph from caller to callee.

    Attributes:
        _caller: Fully qualified name of the calling function.
        _callee: Fully qualified name of the called function.
        _call_site_id: The observation site id for the call expression.
        _arguments: Positional argument names at the call site.
        _keyword_arguments: Keyword argument names at the call site.
        _line: Source line number of the call expression.
        _col: Source column offset of the call expression.
        _is_method_call: Whether this is a method call (obj.method()).
        _receiver: The receiver variable name for method calls.
    """

    _caller: str
    _callee: str
    _call_site_id: Optional[SiteId] = None
    _arguments: Tuple[str, ...] = ()
    _keyword_arguments: Tuple[Tuple[str, str], ...] = ()
    _line: int = 0
    _col: int = 0
    _is_method_call: bool = False
    _receiver: Optional[str] = None

    @property
    def caller(self) -> str:
        """Name of the calling function."""
        return self._caller

    @property
    def callee(self) -> str:
        """Name of the called function."""
        return self._callee

    @property
    def call_site_id(self) -> Optional[SiteId]:
        """Observation site id at the call expression."""
        return self._call_site_id

    @property
    def arguments(self) -> Tuple[str, ...]:
        """Positional argument names."""
        return self._arguments

    @property
    def keyword_arguments(self) -> Tuple[Tuple[str, str], ...]:
        """Keyword argument (name, value_name) pairs."""
        return self._keyword_arguments

    @property
    def line(self) -> int:
        """Source line number."""
        return self._line

    @property
    def col(self) -> int:
        """Source column offset."""
        return self._col

    @property
    def is_method_call(self) -> bool:
        """Whether this is a method call."""
        return self._is_method_call

    @property
    def receiver(self) -> Optional[str]:
        """Receiver variable for method calls."""
        return self._receiver

    def __repr__(self) -> str:
        args_str = ", ".join(self._arguments)
        return f"CallEdge({self._caller} -> {self._callee}({args_str}))"


# ---------------------------------------------------------------------------
# Call target resolution
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CallTarget:
    """Resolved target of a call expression.

    Attributes:
        _name: Resolved function name.
        _is_builtin: Whether this is a Python builtin.
        _is_method: Whether this is a method call.
        _class_name: Enclosing class name for methods.
        _module_name: Module where the target is defined.
        _is_indirect: Whether the call target could not be resolved statically.
    """

    _name: str
    _is_builtin: bool = False
    _is_method: bool = False
    _class_name: Optional[str] = None
    _module_name: Optional[str] = None
    _is_indirect: bool = False

    @property
    def name(self) -> str:
        return self._name

    @property
    def is_builtin(self) -> bool:
        return self._is_builtin

    @property
    def is_method(self) -> bool:
        return self._is_method

    @property
    def class_name(self) -> Optional[str]:
        return self._class_name

    @property
    def module_name(self) -> Optional[str]:
        return self._module_name

    @property
    def is_indirect(self) -> bool:
        return self._is_indirect

    @property
    def qualified_name(self) -> str:
        """Fully qualified name for the call target."""
        parts: List[str] = []
        if self._module_name:
            parts.append(self._module_name)
        if self._class_name:
            parts.append(self._class_name)
        parts.append(self._name)
        return ".".join(parts)


# ---------------------------------------------------------------------------
# Built-in function registry
# ---------------------------------------------------------------------------

_BUILTINS: FrozenSet[str] = frozenset({
    "abs", "all", "any", "ascii", "bin", "bool", "breakpoint", "bytearray",
    "bytes", "callable", "chr", "classmethod", "compile", "complex",
    "delattr", "dict", "dir", "divmod", "enumerate", "eval", "exec",
    "filter", "float", "format", "frozenset", "getattr", "globals",
    "hasattr", "hash", "help", "hex", "id", "input", "int", "isinstance",
    "issubclass", "iter", "len", "list", "locals", "map", "max",
    "memoryview", "min", "next", "object", "oct", "open", "ord", "pow",
    "print", "property", "range", "repr", "reversed", "round", "set",
    "setattr", "slice", "sorted", "staticmethod", "str", "sum", "super",
    "tuple", "type", "vars", "zip",
})


def _is_builtin(name: str) -> bool:
    """Check whether a name refers to a Python builtin."""
    return name in _BUILTINS


# ---------------------------------------------------------------------------
# AST call visitor
# ---------------------------------------------------------------------------

class _CallVisitor(ast.NodeVisitor):
    """Walk an AST and collect call edges for a single function."""

    def __init__(
        self,
        caller_name: str,
        module_functions: FrozenSet[str],
        class_methods: Dict[str, Set[str]],
        file_path: str,
    ) -> None:
        self._caller = caller_name
        self._module_functions = module_functions
        self._class_methods = class_methods
        self._file_path = file_path
        self._edges: List[CallEdge] = []
        self._call_counter = 0

    @property
    def edges(self) -> List[CallEdge]:
        return list(self._edges)

    def _resolve_call_target(self, node: ast.Call) -> Optional[CallTarget]:
        """Resolve the target of a Call node."""
        func = node.func

        # Simple name call: foo()
        if isinstance(func, ast.Name):
            name = func.id
            if _is_builtin(name):
                return CallTarget(_name=name, _is_builtin=True)
            if name in self._module_functions:
                return CallTarget(_name=name)
            # Could be a class constructor or imported name
            return CallTarget(_name=name, _is_indirect=True)

        # Attribute call: obj.method() or module.func()
        if isinstance(func, ast.Attribute):
            method_name = func.attr
            receiver_name: Optional[str] = None

            if isinstance(func.value, ast.Name):
                receiver_name = func.value.id

                # Check if receiver is a known class
                if receiver_name in self._class_methods:
                    if method_name in self._class_methods[receiver_name]:
                        return CallTarget(
                            _name=method_name,
                            _is_method=True,
                            _class_name=receiver_name,
                        )

                # self.method() calls within a class
                if receiver_name == "self":
                    # Find the enclosing class
                    parts = self._caller.split(".")
                    if len(parts) >= 2:
                        class_name = parts[-2]
                        return CallTarget(
                            _name=method_name,
                            _is_method=True,
                            _class_name=class_name,
                        )

            return CallTarget(
                _name=method_name,
                _is_method=True,
                _is_indirect=True,
            )

        # Subscript call, nested call, etc. -- indirect
        return CallTarget(_name="<indirect>", _is_indirect=True)

    def _extract_arg_names(self, node: ast.Call) -> Tuple[str, ...]:
        """Extract argument names from a Call node."""
        names: List[str] = []
        for arg in node.args:
            if isinstance(arg, ast.Name):
                names.append(arg.id)
            elif isinstance(arg, ast.Constant):
                names.append(repr(arg.value))
            elif isinstance(arg, ast.Starred):
                if isinstance(arg.value, ast.Name):
                    names.append(f"*{arg.value.id}")
                else:
                    names.append("*<expr>")
            else:
                names.append("<expr>")
        return tuple(names)

    def _extract_kwarg_names(
        self, node: ast.Call
    ) -> Tuple[Tuple[str, str], ...]:
        """Extract keyword argument (name, value) pairs."""
        pairs: List[Tuple[str, str]] = []
        for kw in node.keywords:
            key = kw.arg if kw.arg else "**"
            if isinstance(kw.value, ast.Name):
                val = kw.value.id
            elif isinstance(kw.value, ast.Constant):
                val = repr(kw.value.value)
            else:
                val = "<expr>"
            pairs.append((key, val))
        return tuple(pairs)

    def visit_Call(self, node: ast.Call) -> None:
        """Process a Call node and potentially add an edge."""
        target = self._resolve_call_target(node)
        if target is None:
            self.generic_visit(node)
            return

        # Skip builtins and indirect calls for edge creation
        callee_name = target.qualified_name
        if target.is_builtin:
            self.generic_visit(node)
            return

        line = getattr(node, "lineno", 0)
        col = getattr(node, "col_offset", 0)

        call_site_id = SiteId(
            kind=SiteKind.CALL_RESULT,
            name=f"{self._caller}.call_{self._call_counter}",
            source_location=(self._file_path, line, col),
        )

        arg_names = self._extract_arg_names(node)
        kwarg_names = self._extract_kwarg_names(node)

        receiver: Optional[str] = None
        if isinstance(node.func, ast.Attribute) and isinstance(
            node.func.value, ast.Name
        ):
            receiver = node.func.value.id

        edge = CallEdge(
            _caller=self._caller,
            _callee=callee_name,
            _call_site_id=call_site_id,
            _arguments=arg_names,
            _keyword_arguments=kwarg_names,
            _line=line,
            _col=col,
            _is_method_call=target.is_method,
            _receiver=receiver,
        )
        self._edges.append(edge)
        self._call_counter += 1

        self.generic_visit(node)


# ---------------------------------------------------------------------------
# Function definition collector
# ---------------------------------------------------------------------------

class _FunctionCollector(ast.NodeVisitor):
    """Collect all function and method definitions from a module AST."""

    def __init__(self) -> None:
        self._functions: Dict[str, ast.FunctionDef] = {}
        self._class_methods: Dict[str, Set[str]] = {}
        self._current_class: Optional[str] = None

    @property
    def functions(self) -> Dict[str, ast.FunctionDef]:
        return dict(self._functions)

    @property
    def class_methods(self) -> Dict[str, Set[str]]:
        return {k: set(v) for k, v in self._class_methods.items()}

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        prev_class = self._current_class
        self._current_class = node.name
        if node.name not in self._class_methods:
            self._class_methods[node.name] = set()
        self.generic_visit(node)
        self._current_class = prev_class

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        if self._current_class:
            qualified = f"{self._current_class}.{node.name}"
            self._class_methods[self._current_class].add(node.name)
        else:
            qualified = node.name
        self._functions[qualified] = node
        # Visit nested definitions
        prev_class = self._current_class
        self._current_class = None
        self.generic_visit(node)
        self._current_class = prev_class

    visit_AsyncFunctionDef = visit_FunctionDef


# ---------------------------------------------------------------------------
# Call graph
# ---------------------------------------------------------------------------

class CallGraph:
    """Call graph with topological ordering and SCC detection.

    The call graph is a directed graph where nodes are function names and
    edges are CallEdge instances representing call sites.  It supports:

    - Building from a Python module AST
    - Adding edges incrementally
    - Querying callees and callers
    - Topological ordering (for bottom-up summary propagation)
    - Strongly connected component detection (for recursive functions)
    - Recursion detection
    """

    def __init__(self) -> None:
        self._edges: List[CallEdge] = []
        self._outgoing: Dict[str, List[CallEdge]] = defaultdict(list)
        self._incoming: Dict[str, List[CallEdge]] = defaultdict(list)
        self._functions: Dict[str, ast.FunctionDef] = {}
        self._nodes: Set[str] = set()

    # -- Construction -------------------------------------------------------

    @classmethod
    def build_from_module(
        cls,
        module_ast: ast.Module,
        *,
        file_path: str = "<module>",
    ) -> CallGraph:
        """Build a call graph from a module AST.

        Collects all function/method definitions, then walks each function
        body to discover call edges.
        """
        graph = cls()

        # Phase 1: Collect all function definitions
        collector = _FunctionCollector()
        collector.visit(module_ast)
        graph._functions = collector.functions

        module_func_names = frozenset(collector.functions.keys())
        class_methods = collector.class_methods

        # Register all functions as nodes
        for name in module_func_names:
            graph._nodes.add(name)

        # Phase 2: Walk each function body to find calls
        for func_name, func_node in collector.functions.items():
            visitor = _CallVisitor(
                caller_name=func_name,
                module_functions=module_func_names,
                class_methods=class_methods,
                file_path=file_path,
            )
            visitor.visit(func_node)
            for edge in visitor.edges:
                graph.add_edge(edge)

        return graph

    @classmethod
    def build_from_source(
        cls,
        source: str,
        *,
        file_path: str = "<module>",
    ) -> CallGraph:
        """Build a call graph from Python source code."""
        tree = ast.parse(source, filename=file_path)
        return cls.build_from_module(tree, file_path=file_path)

    def add_edge(self, edge: CallEdge) -> None:
        """Add a call edge to the graph."""
        self._edges.append(edge)
        self._outgoing[edge.caller].append(edge)
        self._incoming[edge.callee].append(edge)
        self._nodes.add(edge.caller)
        self._nodes.add(edge.callee)

    def add_node(self, name: str) -> None:
        """Register a function as a node without any edges."""
        self._nodes.add(name)

    # -- Queries ------------------------------------------------------------

    @property
    def nodes(self) -> FrozenSet[str]:
        """All function names in the graph."""
        return frozenset(self._nodes)

    @property
    def edges(self) -> List[CallEdge]:
        """All call edges."""
        return list(self._edges)

    @property
    def functions(self) -> Dict[str, ast.FunctionDef]:
        """Mapping from function name to AST node."""
        return dict(self._functions)

    def get_callees(self, func: str) -> List[CallEdge]:
        """Return all edges from func to its callees."""
        return list(self._outgoing.get(func, []))

    def get_callers(self, func: str) -> List[CallEdge]:
        """Return all edges from callers to func."""
        return list(self._incoming.get(func, []))

    def callee_names(self, func: str) -> FrozenSet[str]:
        """Return the set of callee names for a function."""
        return frozenset(e.callee for e in self._outgoing.get(func, []))

    def caller_names(self, func: str) -> FrozenSet[str]:
        """Return the set of caller names for a function."""
        return frozenset(e.caller for e in self._incoming.get(func, []))

    def edges_between(self, caller: str, callee: str) -> List[CallEdge]:
        """Return all edges from caller to callee."""
        return [
            e for e in self._outgoing.get(caller, [])
            if e.callee == callee
        ]

    def has_edge(self, caller: str, callee: str) -> bool:
        """Check whether there is a call edge from caller to callee."""
        return any(
            e.callee == callee for e in self._outgoing.get(caller, [])
        )

    def get_function_ast(self, name: str) -> Optional[ast.FunctionDef]:
        """Look up the AST node for a function."""
        return self._functions.get(name)

    # -- Topological ordering -----------------------------------------------

    def topological_order(self) -> List[str]:
        """Return a topological ordering of functions (leaves first).

        Functions that are called but never call others come first.
        If the graph has cycles (mutual recursion), nodes in SCCs are
        grouped together and ordered arbitrarily within each SCC.

        This ordering is used for bottom-up summary propagation:
        process callees before callers.
        """
        # Kahn's algorithm with SCC collapsing
        sccs = self.strongly_connected_components()

        # Map each node to its SCC index
        node_to_scc: Dict[str, int] = {}
        for idx, scc in enumerate(sccs):
            for node in scc:
                node_to_scc[idx] = idx
                node_to_scc[node] = idx  # type: ignore[assignment]

        # Build DAG of SCCs
        scc_count = len(sccs)
        scc_adj: Dict[int, Set[int]] = defaultdict(set)
        scc_in_degree: Dict[int, int] = {i: 0 for i in range(scc_count)}

        for edge in self._edges:
            caller_scc = node_to_scc.get(edge.caller)
            callee_scc = node_to_scc.get(edge.callee)
            if (
                caller_scc is not None
                and callee_scc is not None
                and caller_scc != callee_scc
            ):
                if callee_scc not in scc_adj[caller_scc]:
                    scc_adj[caller_scc].add(callee_scc)
                    scc_in_degree[callee_scc] = (
                        scc_in_degree.get(callee_scc, 0) + 1
                    )

        # Topological sort of the SCC DAG (callees first)
        queue: deque[int] = deque()
        for i in range(scc_count):
            if scc_in_degree.get(i, 0) == 0:
                queue.append(i)

        scc_order: List[int] = []
        while queue:
            scc_idx = queue.popleft()
            scc_order.append(scc_idx)
            for neighbor in scc_adj.get(scc_idx, set()):
                scc_in_degree[neighbor] -= 1
                if scc_in_degree[neighbor] == 0:
                    queue.append(neighbor)

        # If some SCCs were not reached (shouldn't happen), add them
        visited_sccs = set(scc_order)
        for i in range(scc_count):
            if i not in visited_sccs:
                scc_order.append(i)

        # Reverse: we want callees (leaf SCCs) first
        scc_order.reverse()

        # Flatten SCCs to produce the final order
        result: List[str] = []
        for scc_idx in scc_order:
            if scc_idx < len(sccs):
                for node in sorted(sccs[scc_idx]):
                    result.append(node)

        return result

    # -- Strongly connected components --------------------------------------

    def strongly_connected_components(self) -> List[FrozenSet[str]]:
        """Find strongly connected components using Tarjan's algorithm.

        Returns a list of frozensets, each containing the function names
        in one SCC.  SCCs with more than one member indicate mutual recursion.
        """
        index_counter = [0]
        stack: List[str] = []
        on_stack: Set[str] = set()
        index_map: Dict[str, int] = {}
        lowlink_map: Dict[str, int] = {}
        result: List[FrozenSet[str]] = []

        def strongconnect(v: str) -> None:
            index_map[v] = index_counter[0]
            lowlink_map[v] = index_counter[0]
            index_counter[0] += 1
            stack.append(v)
            on_stack.add(v)

            for edge in self._outgoing.get(v, []):
                w = edge.callee
                if w not in self._nodes:
                    continue
                if w not in index_map:
                    strongconnect(w)
                    lowlink_map[v] = min(lowlink_map[v], lowlink_map[w])
                elif w in on_stack:
                    lowlink_map[v] = min(lowlink_map[v], index_map[w])

            if lowlink_map[v] == index_map[v]:
                scc_members: Set[str] = set()
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    scc_members.add(w)
                    if w == v:
                        break
                result.append(frozenset(scc_members))

        for node in sorted(self._nodes):
            if node not in index_map:
                strongconnect(node)

        return result

    # -- Recursion detection ------------------------------------------------

    def is_recursive(self, func: str) -> bool:
        """Check whether a function is directly or mutually recursive.

        A function is recursive if it appears in an SCC of size > 1,
        or if it has a self-edge.
        """
        # Direct self-recursion
        if any(e.callee == func for e in self._outgoing.get(func, [])):
            return True

        # Mutual recursion: check if func is in an SCC with other functions
        for scc in self.strongly_connected_components():
            if func in scc and len(scc) > 1:
                return True

        return False

    def recursive_functions(self) -> FrozenSet[str]:
        """Return the set of all recursive functions."""
        result: Set[str] = set()
        # Direct self-recursion
        for func in self._nodes:
            if any(e.callee == func for e in self._outgoing.get(func, [])):
                result.add(func)

        # Mutual recursion
        for scc in self.strongly_connected_components():
            if len(scc) > 1:
                result.update(scc)

        return frozenset(result)

    # -- Subgraph extraction ------------------------------------------------

    def reachable_from(self, func: str) -> FrozenSet[str]:
        """Return all functions reachable from func (transitive callees)."""
        visited: Set[str] = set()
        queue: deque[str] = deque([func])
        while queue:
            current = queue.popleft()
            if current in visited:
                continue
            visited.add(current)
            for edge in self._outgoing.get(current, []):
                if edge.callee not in visited:
                    queue.append(edge.callee)
        return frozenset(visited)

    def reaching(self, func: str) -> FrozenSet[str]:
        """Return all functions that can reach func (transitive callers)."""
        visited: Set[str] = set()
        queue: deque[str] = deque([func])
        while queue:
            current = queue.popleft()
            if current in visited:
                continue
            visited.add(current)
            for edge in self._incoming.get(current, []):
                if edge.caller not in visited:
                    queue.append(edge.caller)
        return frozenset(visited)

    def leaf_functions(self) -> FrozenSet[str]:
        """Return functions that make no calls to other module functions."""
        return frozenset(
            n for n in self._nodes
            if not self._outgoing.get(n, [])
        )

    def root_functions(self) -> FrozenSet[str]:
        """Return functions that are not called by any other module function."""
        return frozenset(
            n for n in self._nodes
            if not self._incoming.get(n, [])
        )

    # -- Statistics ---------------------------------------------------------

    def edge_count(self) -> int:
        """Total number of call edges."""
        return len(self._edges)

    def node_count(self) -> int:
        """Total number of functions."""
        return len(self._nodes)

    def max_fan_out(self) -> int:
        """Maximum number of distinct callees from any single function."""
        if not self._nodes:
            return 0
        return max(
            len(set(e.callee for e in self._outgoing.get(n, [])))
            for n in self._nodes
        )

    def max_fan_in(self) -> int:
        """Maximum number of distinct callers for any single function."""
        if not self._nodes:
            return 0
        return max(
            len(set(e.caller for e in self._incoming.get(n, [])))
            for n in self._nodes
        )

    def call_depth(self, func: str) -> int:
        """Compute the maximum call depth from a function.

        Returns 0 for leaf functions, -1 for recursive functions
        (infinite depth).
        """
        if self.is_recursive(func):
            return -1

        memo: Dict[str, int] = {}

        def _depth(f: str, visited: Set[str]) -> int:
            if f in memo:
                return memo[f]
            if f in visited:
                return -1  # Cycle detected
            visited.add(f)

            callees = self._outgoing.get(f, [])
            if not callees:
                memo[f] = 0
                return 0

            max_d = 0
            for edge in callees:
                if edge.callee in self._nodes:
                    d = _depth(edge.callee, visited)
                    if d == -1:
                        memo[f] = -1
                        return -1
                    max_d = max(max_d, d + 1)

            memo[f] = max_d
            visited.discard(f)
            return max_d

        return _depth(func, set())

    def __repr__(self) -> str:
        return (
            f"CallGraph(nodes={self.node_count()}, "
            f"edges={self.edge_count()})"
        )
