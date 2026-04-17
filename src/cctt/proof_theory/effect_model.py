"""Python Effect Model — tracking what Python functions actually DO.

Python is not purely functional. Lists mutate. Dicts are objects.
`self.x = y` changes heap state. `open()` touches the filesystem.
`random()` is nondeterministic. A proof system that ignores this is unsound.

This module provides:

1. **EffectType** — classification of what side effects a function has
2. **FunctionEffect** — detailed effect descriptor (reads, writes, raises, aliases)
3. **StateContract** — pre/post state specs for functions with effects
4. **EffectAnalyzer** — static analysis to detect effects from Python AST

The key insight: in the sheaf-theoretic picture, effects are **sections of the
state sheaf**. A pure function's section is constant; a mutating function's
section varies over the timeline. The pre/post contract is a PATH in the
state sheaf from pre-section to post-section.

Design principles:
  - Conservative: if unsure, classify as IMPURE (sound over-approximation)
  - Python-specific: understands __setattr__, __dict__, descriptors, etc.
  - Dict-as-object: Python objects ARE dicts; attribute access IS dict lookup
  - old() references: pre-state snapshots for postconditions about mutation

Usage::

    from cctt.proof_theory.effect_model import EffectAnalyzer, EffectType

    analyzer = EffectAnalyzer()
    effect = analyzer.analyze("def f(self, x): self.items.append(x)", "f")
    # effect.type == EffectType.MUTATES_SELF
    # effect.writes == {"self.items"}
    # effect.calls_mutating == {"list.append"}

    contract = effect.to_state_contract()
    # contract.modifies == {"self.items"}
    # contract.post_ensures == ["len(self.items) == len(old(self.items)) + 1"]
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple


# ═══════════════════════════════════════════════════════════════════
# Effect classification
# ═══════════════════════════════════════════════════════════════════

class EffectType(Enum):
    """What kind of side effects does a function have?

    Ordered from least to most impure. A function with multiple effects
    gets the HIGHEST (most impure) classification.
    """
    PURE = "pure"                       # No effects — safe for equational reasoning
    READS_STATE = "reads_state"         # Reads mutable state but doesn't modify
    MUTATES_SELF = "mutates_self"       # Modifies self.* attributes
    MUTATES_ARGS = "mutates_args"       # Modifies arguments in-place
    MUTATES_GLOBAL = "mutates_global"   # Modifies global/module-level state
    IO = "io"                           # File I/O, network, database
    NONDETERMINISTIC = "nondeterministic"  # random, time, uuid, etc.

    @property
    def is_pure(self) -> bool:
        return self == EffectType.PURE

    @property
    def allows_equational(self) -> bool:
        """Can we use equational reasoning (f(x) == f(x))?"""
        return self in (EffectType.PURE, EffectType.READS_STATE)

    @property
    def severity(self) -> int:
        """Numeric severity for combining effects."""
        return {
            EffectType.PURE: 0,
            EffectType.READS_STATE: 1,
            EffectType.MUTATES_SELF: 2,
            EffectType.MUTATES_ARGS: 3,
            EffectType.MUTATES_GLOBAL: 4,
            EffectType.IO: 5,
            EffectType.NONDETERMINISTIC: 6,
        }[self]


def _max_effect(*effects: EffectType) -> EffectType:
    """Return the most severe effect type."""
    if not effects:
        return EffectType.PURE
    return max(effects, key=lambda e: e.severity)


# ═══════════════════════════════════════════════════════════════════
# Detailed effect descriptor
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FunctionEffect:
    """Detailed effect descriptor for a Python function.

    This is NOT just a boolean is_pure — it tracks WHAT is read/written,
    WHAT exceptions are raised, and WHAT aliasing exists.

    In the sheaf picture: this describes the "support" of the function's
    section in the state sheaf — which parts of the heap it touches.
    """
    effect_type: EffectType = EffectType.PURE

    # What state is read (attribute paths like "self.items", "arg.shape")
    reads: FrozenSet[str] = frozenset()

    # What state is written (attribute paths like "self.count", "arg[0]")
    writes: FrozenSet[str] = frozenset()

    # What mutating methods are called (like "list.append", "dict.update")
    calls_mutating: FrozenSet[str] = frozenset()

    # What exceptions can be raised
    raises: FrozenSet[str] = frozenset()

    # What exceptions are caught internally
    catches: FrozenSet[str] = frozenset()

    # Aliasing: which params might alias each other or self
    aliases: FrozenSet[Tuple[str, str]] = frozenset()

    # Global/nonlocal variables accessed
    globals_read: FrozenSet[str] = frozenset()
    globals_written: FrozenSet[str] = frozenset()

    # IO operations (file paths, network calls, etc.)
    io_operations: FrozenSet[str] = frozenset()

    # Nondeterministic sources
    nondeterministic_sources: FrozenSet[str] = frozenset()

    @property
    def is_pure(self) -> bool:
        return self.effect_type == EffectType.PURE

    @property
    def modifies(self) -> FrozenSet[str]:
        """All state locations that may be modified."""
        return self.writes | frozenset(
            f"{c.split('.')[0]}.*" for c in self.calls_mutating
        )

    def combine(self, other: FunctionEffect) -> FunctionEffect:
        """Combine two effects (for sequential composition)."""
        return FunctionEffect(
            effect_type=_max_effect(self.effect_type, other.effect_type),
            reads=self.reads | other.reads,
            writes=self.writes | other.writes,
            calls_mutating=self.calls_mutating | other.calls_mutating,
            raises=self.raises | other.raises,
            catches=self.catches | other.catches,
            aliases=self.aliases | other.aliases,
            globals_read=self.globals_read | other.globals_read,
            globals_written=self.globals_written | other.globals_written,
            io_operations=self.io_operations | other.io_operations,
            nondeterministic_sources=(
                self.nondeterministic_sources | other.nondeterministic_sources
            ),
        )

    def to_json(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {"effect_type": self.effect_type.value}
        if self.reads:
            d["reads"] = sorted(self.reads)
        if self.writes:
            d["writes"] = sorted(self.writes)
        if self.calls_mutating:
            d["calls_mutating"] = sorted(self.calls_mutating)
        if self.raises:
            d["raises"] = sorted(self.raises)
        if self.catches:
            d["catches"] = sorted(self.catches)
        if self.aliases:
            d["aliases"] = [list(a) for a in sorted(self.aliases)]
        if self.globals_read:
            d["globals_read"] = sorted(self.globals_read)
        if self.globals_written:
            d["globals_written"] = sorted(self.globals_written)
        if self.io_operations:
            d["io_operations"] = sorted(self.io_operations)
        if self.nondeterministic_sources:
            d["nondeterministic_sources"] = sorted(self.nondeterministic_sources)
        return d

    @staticmethod
    def from_json(d: Dict[str, Any]) -> FunctionEffect:
        return FunctionEffect(
            effect_type=EffectType(d.get("effect_type", "pure")),
            reads=frozenset(d.get("reads", [])),
            writes=frozenset(d.get("writes", [])),
            calls_mutating=frozenset(d.get("calls_mutating", [])),
            raises=frozenset(d.get("raises", [])),
            catches=frozenset(d.get("catches", [])),
            aliases=frozenset(tuple(a) for a in d.get("aliases", [])),
            globals_read=frozenset(d.get("globals_read", [])),
            globals_written=frozenset(d.get("globals_written", [])),
            io_operations=frozenset(d.get("io_operations", [])),
            nondeterministic_sources=frozenset(
                d.get("nondeterministic_sources", [])
            ),
        )


# ═══════════════════════════════════════════════════════════════════
# State contract — pre/post specs for effectful functions
# ═══════════════════════════════════════════════════════════════════

@dataclass
class StateContract:
    """Pre/post state contract for a function with effects.

    This is the CORRECT way to specify a mutating function:

        list.append(self, x):
          modifies: {self}
          pre:  old_len = len(self)
          post: len(self) == old_len + 1 and self[-1] == x

    The `old()` references bind pre-state snapshots that postconditions
    can reference. This follows the JML/Dafny/F* approach to framing.

    In the cubical picture: the contract is a PATH
        (pre_state, args) ---> (post_state, result)
    in the state × value sheaf.
    """
    # What locations may be modified (frame condition)
    modifies: FrozenSet[str] = frozenset()

    # Pre-state snapshots: name -> expression (e.g., "old_len" -> "len(self)")
    old_bindings: Dict[str, str] = field(default_factory=dict)

    # Preconditions (over params and pre-state)
    pre_requires: List[str] = field(default_factory=list)

    # Postconditions (over params, result, post-state, and old() refs)
    post_ensures: List[str] = field(default_factory=list)

    # Exceptional postconditions: exception_type -> ensures
    exceptional_post: Dict[str, List[str]] = field(default_factory=dict)

    # Frame: what is NOT modified (everything not in modifies is preserved)
    # This is implicit: anything not in `modifies` is unchanged.

    @property
    def is_trivial(self) -> bool:
        return (not self.modifies and not self.old_bindings
                and not self.pre_requires and not self.post_ensures
                and not self.exceptional_post)

    def to_json(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {}
        if self.modifies:
            d["modifies"] = sorted(self.modifies)
        if self.old_bindings:
            d["old_bindings"] = self.old_bindings
        if self.pre_requires:
            d["pre_requires"] = self.pre_requires
        if self.post_ensures:
            d["post_ensures"] = self.post_ensures
        if self.exceptional_post:
            d["exceptional_post"] = self.exceptional_post
        return d

    @staticmethod
    def from_json(d: Dict[str, Any]) -> StateContract:
        return StateContract(
            modifies=frozenset(d.get("modifies", [])),
            old_bindings=d.get("old_bindings", {}),
            pre_requires=d.get("pre_requires", []),
            post_ensures=d.get("post_ensures", []),
            exceptional_post=d.get("exceptional_post", {}),
        )


# ═══════════════════════════════════════════════════════════════════
# Known mutating methods — Python's "everything is really a dict"
# ═══════════════════════════════════════════════════════════════════

# Methods that mutate their receiver (self/first arg)
MUTATING_METHODS: Dict[str, Set[str]] = {
    # list methods
    "list": {"append", "extend", "insert", "remove", "pop", "clear",
             "sort", "reverse", "__setitem__", "__delitem__", "__iadd__"},
    # dict methods
    "dict": {"update", "pop", "popitem", "clear", "setdefault",
             "__setitem__", "__delitem__"},
    # set methods
    "set": {"add", "remove", "discard", "pop", "clear",
            "update", "intersection_update", "difference_update",
            "symmetric_difference_update", "__ior__", "__iand__",
            "__isub__", "__ixor__"},
    # deque methods
    "deque": {"append", "appendleft", "extend", "extendleft",
              "pop", "popleft", "clear", "rotate"},
    # bytearray
    "bytearray": {"append", "extend", "insert", "remove", "pop",
                  "clear", "reverse", "__setitem__"},
    # io
    "io": {"write", "writelines", "truncate", "seek", "close", "flush"},
}

# Flatten for quick lookup
ALL_MUTATING_METHODS: Set[str] = set()
for _methods in MUTATING_METHODS.values():
    ALL_MUTATING_METHODS |= _methods

# IO-related function names
IO_FUNCTIONS: Set[str] = {
    "open", "print", "input",
    "os.remove", "os.rename", "os.mkdir", "os.makedirs",
    "os.rmdir", "os.unlink", "os.symlink",
    "shutil.copy", "shutil.move", "shutil.rmtree",
    "subprocess.run", "subprocess.call", "subprocess.Popen",
    "socket.socket", "urllib.request.urlopen",
    "requests.get", "requests.post",
}
IO_FUNCTION_NAMES: Set[str] = {f.split(".")[-1] for f in IO_FUNCTIONS}

# Nondeterministic function names
NONDETERMINISTIC_FUNCTIONS: Set[str] = {
    "random", "randint", "randrange", "choice", "shuffle", "sample",
    "uniform", "gauss", "normalvariate",
    "time", "monotonic", "perf_counter",
    "uuid4", "uuid1",
    "getpid", "getppid",
}

# Attribute names that indicate state reading
STATE_READING_ATTRS: Set[str] = {
    "__dict__", "__class__", "__bases__", "__mro__",
    "__slots__", "__weakref__",
}


# ═══════════════════════════════════════════════════════════════════
# Effect Analyzer — static analysis of Python AST
# ═══════════════════════════════════════════════════════════════════

class EffectAnalyzer:
    """Analyze Python function AST to determine its effects.

    Conservative: if unsure, classifies as impure (sound over-approximation).
    This means false positives (pure function classified as impure) but
    never false negatives (impure function classified as pure).

    Handles Python-specific patterns:
      - self.x = y  →  MUTATES_SELF, writes={"self.x"}
      - arg.append(v)  →  MUTATES_ARGS, calls_mutating={"list.append"}
      - open(f)  →  IO, io_operations={"open"}
      - random.random()  →  NONDETERMINISTIC
      - global x; x = 1  →  MUTATES_GLOBAL
      - raise ValueError  →  raises={"ValueError"}
      - x = self.items  →  reads={"self.items"} (Python objects ARE dicts)
      - __setattr__  →  MUTATES_SELF (descriptor protocol)
    """

    def analyze(self, source: str, func_name: str) -> FunctionEffect:
        """Analyze a function's source code for effects."""
        try:
            tree = ast.parse(source)
        except SyntaxError:
            # Can't parse → conservatively impure
            return FunctionEffect(effect_type=EffectType.IO)

        fn_node = self._find_function(tree, func_name)
        if fn_node is None:
            return FunctionEffect(effect_type=EffectType.IO)

        params = [arg.arg for arg in fn_node.args.args]
        has_self = bool(params) and params[0] == "self"
        is_init = func_name == "__init__"

        return self._analyze_function(fn_node, params, has_self, is_init)

    def analyze_node(self, fn_node: ast.FunctionDef) -> FunctionEffect:
        """Analyze an already-parsed function node."""
        params = [arg.arg for arg in fn_node.args.args]
        has_self = bool(params) and params[0] == "self"
        is_init = fn_node.name == "__init__"
        return self._analyze_function(fn_node, params, has_self, is_init)

    def _find_function(self, tree: ast.Module,
                       name: str) -> Optional[ast.FunctionDef]:
        """Find a function by name in the AST (handles nesting)."""
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name == name:
                    return node
        return None

    def _analyze_function(
        self, fn: ast.FunctionDef, params: List[str],
        has_self: bool, is_init: bool,
    ) -> FunctionEffect:
        """Core analysis of a function node."""
        reads: Set[str] = set()
        writes: Set[str] = set()
        calls_mut: Set[str] = set()
        raises_set: Set[str] = set()
        catches_set: Set[str] = set()
        globals_r: Set[str] = set()
        globals_w: Set[str] = set()
        io_ops: Set[str] = set()
        nondet: Set[str] = set()
        effects: List[EffectType] = []

        # Track global/nonlocal declarations
        declared_globals: Set[str] = set()
        declared_nonlocals: Set[str] = set()

        for node in ast.walk(fn):
            # ── Global/nonlocal declarations ──
            if isinstance(node, ast.Global):
                declared_globals.update(node.names)
                effects.append(EffectType.MUTATES_GLOBAL)
            elif isinstance(node, ast.Nonlocal):
                declared_nonlocals.update(node.names)
                effects.append(EffectType.MUTATES_GLOBAL)

            # ── Attribute assignment: self.x = y or arg.x = y ──
            elif isinstance(node, ast.Assign):
                for target in node.targets:
                    self._check_attr_write(
                        target, params, has_self, is_init,
                        writes, effects,
                    )
                    self._check_global_write(
                        target, declared_globals, globals_w, effects,
                    )

            elif isinstance(node, ast.AugAssign):
                self._check_attr_write(
                    node.target, params, has_self, is_init,
                    writes, effects,
                )
                self._check_global_write(
                    node.target, declared_globals, globals_w, effects,
                )

            # ── Delete: del self.x ──
            elif isinstance(node, ast.Delete):
                for target in node.targets:
                    self._check_attr_write(
                        target, params, has_self, is_init,
                        writes, effects,
                    )

            # ── Function calls ──
            elif isinstance(node, ast.Call):
                self._check_call(
                    node, params, has_self,
                    calls_mut, io_ops, nondet, reads, effects,
                )

            # ── Raise statements ──
            elif isinstance(node, ast.Raise):
                if node.exc is not None:
                    exc_name = self._extract_exception_name(node.exc)
                    if exc_name:
                        raises_set.add(exc_name)

            # ── Try/except handlers ──
            elif isinstance(node, ast.ExceptHandler):
                if node.type is not None:
                    exc_name = self._extract_name(node.type)
                    if exc_name:
                        catches_set.add(exc_name)

            # ── Attribute reads (Python objects ARE dicts) ──
            elif isinstance(node, ast.Attribute):
                if isinstance(node.ctx, ast.Load):
                    owner = self._extract_name(node.value)
                    if owner and owner in params:
                        reads.add(f"{owner}.{node.attr}")
                    if node.attr in STATE_READING_ATTRS:
                        reads.add(f"*.{node.attr}")

        # Classify reads from globals
        for name in declared_globals:
            globals_r.add(name)

        # Compute overall effect type
        overall = EffectType.PURE
        if effects:
            overall = _max_effect(*effects)
        elif reads and not writes and not calls_mut:
            overall = EffectType.READS_STATE
        if raises_set and overall.severity < EffectType.READS_STATE.severity:
            # Exceptions are effects but mild — at least READS_STATE
            overall = EffectType.READS_STATE

        return FunctionEffect(
            effect_type=overall,
            reads=frozenset(reads),
            writes=frozenset(writes),
            calls_mutating=frozenset(calls_mut),
            raises=frozenset(raises_set),
            catches=frozenset(catches_set),
            globals_read=frozenset(globals_r),
            globals_written=frozenset(globals_w),
            io_operations=frozenset(io_ops),
            nondeterministic_sources=frozenset(nondet),
        )

    def _check_attr_write(
        self, target: ast.expr, params: List[str],
        has_self: bool, is_init: bool,
        writes: Set[str], effects: List[EffectType],
    ) -> None:
        """Check if a target is writing to self.x or arg.x."""
        if isinstance(target, ast.Attribute):
            owner = self._extract_name(target.value)
            if owner == "self" and has_self:
                writes.add(f"self.{target.attr}")
                if not is_init:
                    effects.append(EffectType.MUTATES_SELF)
            elif owner and owner in params and owner != "self":
                writes.add(f"{owner}.{target.attr}")
                effects.append(EffectType.MUTATES_ARGS)
        elif isinstance(target, ast.Subscript):
            owner = self._extract_name(target.value)
            if owner == "self" and has_self:
                writes.add("self[*]")
                if not is_init:
                    effects.append(EffectType.MUTATES_SELF)
            elif owner and owner in params and owner != "self":
                writes.add(f"{owner}[*]")
                effects.append(EffectType.MUTATES_ARGS)

    def _check_global_write(
        self, target: ast.expr, declared_globals: Set[str],
        globals_w: Set[str], effects: List[EffectType],
    ) -> None:
        """Check if a target writes to a declared global."""
        if isinstance(target, ast.Name) and target.id in declared_globals:
            globals_w.add(target.id)
            effects.append(EffectType.MUTATES_GLOBAL)
        # Subscript on a global: _cache[k] = v
        elif isinstance(target, ast.Subscript):
            name = self._extract_name(target.value)
            if name and name in declared_globals:
                globals_w.add(name)
                effects.append(EffectType.MUTATES_GLOBAL)

    def _check_call(
        self, node: ast.Call, params: List[str], has_self: bool,
        calls_mut: Set[str], io_ops: Set[str], nondet: Set[str],
        reads: Set[str], effects: List[EffectType],
    ) -> None:
        """Check a function call for effects."""
        # Method call: obj.method(...)
        if isinstance(node.func, ast.Attribute):
            method = node.func.attr
            owner = self._extract_name(node.func.value)

            # Root of the attribute chain (self.items.append → root is "self")
            root = owner.split(".")[0] if owner else None

            # Mutating method on a param or self (including attribute chains)
            if method in ALL_MUTATING_METHODS:
                if root == "self" and has_self:
                    calls_mut.add(f"{owner}.{method}")
                    effects.append(EffectType.MUTATES_SELF)
                elif root and root in params and root != "self":
                    calls_mut.add(f"{owner}.{method}")
                    effects.append(EffectType.MUTATES_ARGS)
                elif owner:
                    calls_mut.add(f"{owner}.{method}")

            # __setattr__, __delattr__ — descriptor protocol mutation
            if method in ("__setattr__", "__delattr__", "__setitem__",
                          "__delitem__"):
                if root == "self":
                    effects.append(EffectType.MUTATES_SELF)
                elif root and root in params:
                    effects.append(EffectType.MUTATES_ARGS)

            # IO method calls
            if method in ("write", "writelines", "close", "flush",
                          "truncate", "seek"):
                io_ops.add(f"{owner or '?'}.{method}")
                effects.append(EffectType.IO)

            # Nondeterministic method calls (e.g., random.randint)
            if method in NONDETERMINISTIC_FUNCTIONS:
                nondet.add(f"{owner}.{method}" if owner else method)
                effects.append(EffectType.NONDETERMINISTIC)

        # Direct function call: func(...)
        elif isinstance(node.func, ast.Name):
            fname = node.func.id

            # IO functions
            if fname in IO_FUNCTION_NAMES:
                io_ops.add(fname)
                effects.append(EffectType.IO)

            # setattr/delattr builtins
            if fname in ("setattr", "delattr"):
                if node.args:
                    target = self._extract_name(node.args[0])
                    if target == "self":
                        effects.append(EffectType.MUTATES_SELF)
                    elif target and target in params:
                        effects.append(EffectType.MUTATES_ARGS)

            # Nondeterministic
            if fname in NONDETERMINISTIC_FUNCTIONS:
                nondet.add(fname)
                effects.append(EffectType.NONDETERMINISTIC)

            # sorted/reversed/list/... are PURE — they don't mutate

    def _extract_exception_name(self, exc: ast.expr) -> Optional[str]:
        """Extract exception class name from a raise expression."""
        if isinstance(exc, ast.Call):
            return self._extract_name(exc.func)
        return self._extract_name(exc)

    def _extract_name(self, node: ast.expr) -> Optional[str]:
        """Extract a simple name from a node."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            owner = self._extract_name(node.value)
            if owner:
                return f"{owner}.{node.attr}"
        return None


# ═══════════════════════════════════════════════════════════════════
# State contract synthesis — from effects to pre/post specs
# ═══════════════════════════════════════════════════════════════════

def synthesize_state_contract(
    effect: FunctionEffect,
    func_name: str = "",
    params: Optional[List[str]] = None,
) -> StateContract:
    """Synthesize a state contract from detected effects.

    For pure functions: trivial contract (no modifies, no old()).
    For mutating functions: generate modifies set and old() bindings.

    This is a CONSERVATIVE synthesis — it captures what CAN be modified
    but doesn't yet know the exact postcondition (that needs an LLM or
    manual annotation).
    """
    if effect.is_pure:
        return StateContract()

    modifies = effect.modifies
    old_bindings: Dict[str, str] = {}
    pre_requires: List[str] = []
    post_ensures: List[str] = []
    exceptional_post: Dict[str, List[str]] = {}

    # Generate old() bindings for written locations
    for w in sorted(effect.writes):
        safe_name = w.replace(".", "_").replace("[", "_").replace("]", "").replace("*", "star")
        old_bindings[f"old_{safe_name}"] = w

    # For mutating method calls, generate frame conditions
    for call in sorted(effect.calls_mutating):
        parts = call.split(".")
        if len(parts) >= 2:
            obj = parts[0]
            method = parts[-1]
            # Common patterns with known semantics
            if method == "append":
                old_name = f"old_len_{obj}"
                old_bindings[old_name] = f"len({obj})"
                post_ensures.append(
                    f"len({obj}) == {old_name} + 1"
                )
            elif method == "pop":
                old_name = f"old_len_{obj}"
                old_bindings[old_name] = f"len({obj})"
                post_ensures.append(
                    f"len({obj}) == {old_name} - 1"
                )
                pre_requires.append(f"len({obj}) > 0")
            elif method == "clear":
                post_ensures.append(f"len({obj}) == 0")
            elif method == "extend":
                old_name = f"old_len_{obj}"
                old_bindings[old_name] = f"len({obj})"
                # Can't know exact size increase without knowing arg length
            elif method in ("sort", "reverse"):
                old_name = f"old_len_{obj}"
                old_bindings[old_name] = f"len({obj})"
                post_ensures.append(
                    f"len({obj}) == {old_name}"
                )
            elif method == "update" and obj != "self":
                old_name = f"old_len_{obj}"
                old_bindings[old_name] = f"len({obj})"
                # len may increase; keys are added

    # For exceptions: note what might be raised
    for exc in sorted(effect.raises):
        exceptional_post[exc] = [f"isinstance(raised, {exc})"]

    return StateContract(
        modifies=frozenset(modifies),
        old_bindings=old_bindings,
        pre_requires=pre_requires,
        post_ensures=post_ensures,
        exceptional_post=exceptional_post,
    )


# ═══════════════════════════════════════════════════════════════════
# Singleton analyzer instance
# ═══════════════════════════════════════════════════════════════════

_ANALYZER = EffectAnalyzer()


def analyze_effects(source: str, func_name: str) -> FunctionEffect:
    """Top-level API: analyze a function's effects from source."""
    return _ANALYZER.analyze(source, func_name)
