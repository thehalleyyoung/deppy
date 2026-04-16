"""Library Axioms — assume-and-use properties of external Python libraries.

Python's power comes from its ecosystem: numpy, sympy, pandas, scipy,
requests, etc. We can't re-verify these libraries from scratch, but we
CAN state what they promise and use those promises in proofs.

This module provides:

1. **Library contracts**: per-function pre/post conditions
2. **Library axioms**: assumed equational properties (trusted)
3. **Trust provenance**: unified tracking of where trust comes from
4. **Version-aware specs**: contracts tied to library versions

Architecture
============

The trust model has ONE unified provenance system (not scattered across
AxiomApp, MathlibTheorem, MathLibAxiom, Assume, and now LibraryAxiom).
Every piece of trusted evidence flows through TrustProvenance:

    source: z3 | structural | mathlib | library | user_assumption | cech
    name: human-readable name
    library: which library (if applicable)
    version: which version (if applicable)
    confidence: float 0..1

Usage::

    # Declare a library's contracts
    sympy_axioms = LibraryTheory("sympy", version=">=1.12")

    sympy_axioms.function("expand",
        takes=[("expr", "Expr")],
        returns="Expr",
        ensures=["expand(a + b) == expand(a) + expand(b)",
                 "expand(a * b) == expand(a) * expand(b) for polynomial a,b"],
    )

    sympy_axioms.function("simplify",
        takes=[("expr", "Expr")],
        returns="Expr",
        ensures=["simplify(simplify(e)) == simplify(e)"],  # idempotent
    )

    sympy_axioms.axiom("factor_expand_inverse",
        statement="factor(expand(e)) == e",
        when="e is a polynomial over ZZ",
    )

    # Use in proofs
    @c4_proof
    def polynomial_roundtrip(pb):
        pb.use_library("sympy", "factor_expand_inverse", e=poly)
"""
from __future__ import annotations

import json
import os
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple

from cctt.denotation import OTerm, OVar, OLit, OOp, OAbstract

from cctt.proof_theory.terms import (
    ProofTerm, Assume,
)


# ═══════════════════════════════════════════════════════════════════
# Trust provenance — ONE unified model for all trusted evidence
# ═══════════════════════════════════════════════════════════════════

class TrustSource(Enum):
    """Where does this trust come from?"""
    STRUCTURAL = "structural"         # Checked by proof term structure
    Z3_PROVEN = "z3"                  # Proved by Z3 solver
    LEAN_VERIFIED = "lean"            # Machine-checked by Lean kernel
    MATHLIB = "mathlib"               # From Mathlib theorem catalog
    LIBRARY_ASSUMED = "library"       # Assumed property of a Python library
    USER_ASSUMPTION = "user"          # User-asserted (axiom/hypothesis)
    CECH_DESCENT = "cech"             # Glued from local proofs via H¹=0
    ORACLE_JUDGED = "oracle"          # LLM oracle judgment

    @property
    def trust_rank(self) -> int:
        """Numeric trust ranking (higher = more trusted)."""
        _ranks = {
            TrustSource.LEAN_VERIFIED: 100,
            TrustSource.Z3_PROVEN: 90,
            TrustSource.MATHLIB: 85,
            TrustSource.STRUCTURAL: 80,
            TrustSource.CECH_DESCENT: 75,
            TrustSource.LIBRARY_ASSUMED: 50,
            TrustSource.ORACLE_JUDGED: 30,
            TrustSource.USER_ASSUMPTION: 10,
        }
        return _ranks.get(self, 0)


@dataclass(frozen=True)
class TrustProvenance:
    """Complete provenance record for a piece of trusted evidence.

    This replaces the scattered trust mechanisms (AxiomApp, MathlibTheorem,
    MathLibAxiom, Assume) with ONE unified model.
    """
    source: TrustSource
    name: str                           # human-readable name
    library: str = ''                   # e.g., 'sympy', 'numpy'
    version: str = ''                   # e.g., '>=1.12,<2.0'
    module_path: str = ''               # e.g., 'sympy.core.expand'
    statement: str = ''                 # the asserted proposition
    confidence: float = 1.0             # 1.0 for proved, <1.0 for oracles
    assumptions: Tuple[str, ...] = ()   # what this depends on

    @property
    def trust_level(self) -> str:
        """Human-readable trust level."""
        if self.source == TrustSource.LEAN_VERIFIED:
            return '🟢 LEAN_VERIFIED'
        if self.source == TrustSource.Z3_PROVEN:
            return '🟡 Z3_PROVEN'
        if self.source == TrustSource.MATHLIB:
            return '🟢 MATHLIB'
        if self.source == TrustSource.STRUCTURAL:
            return '🟢 STRUCTURAL'
        if self.source == TrustSource.CECH_DESCENT:
            return '🟡 CECH_DESCENT'
        if self.source == TrustSource.LIBRARY_ASSUMED:
            return '🟠 LIBRARY_ASSUMED'
        if self.source == TrustSource.ORACLE_JUDGED:
            return '🟠 ORACLE_JUDGED'
        return '🔴 USER_ASSUMPTION'

    def pretty(self) -> str:
        parts = [f'{self.trust_level} {self.name}']
        if self.library:
            parts.append(f'  library: {self.library}')
            if self.version:
                parts.append(f'  version: {self.version}')
        if self.statement:
            parts.append(f'  states: {self.statement}')
        if self.assumptions:
            parts.append(f'  assumes: {", ".join(self.assumptions)}')
        return '\n'.join(parts)


# ═══════════════════════════════════════════════════════════════════
# Library function contract
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FunctionContract:
    """Pre/postcondition contract for a library function.

    Models Python-specific concerns:
    - Dynamic typing: parameter types are advisory, not enforced
    - Exceptions: functions may raise on precondition violation
    - Mutation: some args may be mutated in-place
    - None returns: many functions return None for in-place ops
    - Versioned behavior: API changes across versions
    """
    name: str                    # e.g., 'expand', 'solve', 'dot'
    module: str                  # e.g., 'sympy', 'numpy.linalg'
    parameters: List[Tuple[str, str]] = field(default_factory=list)  # (name, type_desc)
    return_type: str = 'Any'
    preconditions: List[str] = field(default_factory=list)
    postconditions: List[str] = field(default_factory=list)
    raises: List[str] = field(default_factory=list)
    mutates_args: List[int] = field(default_factory=list)
    is_pure: bool = True         # does it have side effects?
    is_deterministic: bool = True # same inputs → same outputs?
    version_range: str = ''

    @property
    def qualname(self) -> str:
        return f'{self.module}.{self.name}'

    def to_provenance(self) -> TrustProvenance:
        """Convert to a TrustProvenance for tracking."""
        conditions = '; '.join(self.postconditions[:3])
        return TrustProvenance(
            source=TrustSource.LIBRARY_ASSUMED,
            name=f'{self.qualname}_contract',
            library=self.module.split('.')[0],
            module_path=self.module,
            statement=conditions,
        )


@dataclass
class LibraryAxiomEntry:
    """An equational axiom about a library — assumed true, not proved.

    Examples:
        expand(a + b) = expand(a) + expand(b)
        np.dot(A, np.eye(n)) = A when A.shape[1] == n
        sorted(xs) is a permutation of xs
        len(list(filter(p, xs))) <= len(xs)
    """
    name: str                    # e.g., 'expand_distributes'
    library: str                 # e.g., 'sympy'
    statement: str               # the equational assertion
    lhs_pattern: str = ''        # e.g., 'expand(a + b)'
    rhs_pattern: str = ''        # e.g., 'expand(a) + expand(b)'
    conditions: List[str] = field(default_factory=list)  # when does this hold?
    version_range: str = ''

    def to_provenance(self) -> TrustProvenance:
        return TrustProvenance(
            source=TrustSource.LIBRARY_ASSUMED,
            name=self.name,
            library=self.library,
            statement=self.statement,
            assumptions=tuple(self.conditions),
        )


# ═══════════════════════════════════════════════════════════════════
# Library theory — a collection of contracts and axioms for a library
# ═══════════════════════════════════════════════════════════════════

class LibraryTheory:
    """A theory about a Python library — its contracts and axioms.

    This is the Pythonic analog of a Lean/Coq module: it collects
    all the assumed properties of a library into one place, with
    explicit versioning and trust tracking.

    Usage::

        sympy = LibraryTheory("sympy", version=">=1.12")

        sympy.function("expand",
            takes=[("expr", "Expr")],
            returns="Expr",
            ensures=["expand distributes over addition"],
        )

        sympy.axiom("simplify_idem",
            statement="simplify(simplify(e)) == simplify(e)",
        )

        # Use the theory
        axiom = sympy.get_axiom("simplify_idem")
        contract = sympy.get_contract("expand")
    """

    def __init__(self, library: str, version: str = ''):
        self.library = library
        self.version = version
        self._contracts: Dict[str, FunctionContract] = {}
        self._axioms: Dict[str, LibraryAxiomEntry] = {}

    def function(self, name: str, *,
                 takes: Optional[List[Tuple[str, str]]] = None,
                 returns: str = 'Any',
                 requires: Optional[List[str]] = None,
                 ensures: Optional[List[str]] = None,
                 raises: Optional[List[str]] = None,
                 mutates: Optional[List[int]] = None,
                 pure: bool = True,
                 deterministic: bool = True) -> FunctionContract:
        """Declare a function contract."""
        contract = FunctionContract(
            name=name,
            module=self.library,
            parameters=takes or [],
            return_type=returns,
            preconditions=requires or [],
            postconditions=ensures or [],
            raises=raises or [],
            mutates_args=mutates or [],
            is_pure=pure,
            is_deterministic=deterministic,
            version_range=self.version,
        )
        self._contracts[name] = contract
        return contract

    def axiom(self, name: str, *,
              statement: str,
              lhs: str = '',
              rhs: str = '',
              when: Optional[List[str]] = None) -> LibraryAxiomEntry:
        """Declare an equational axiom."""
        entry = LibraryAxiomEntry(
            name=name,
            library=self.library,
            statement=statement,
            lhs_pattern=lhs,
            rhs_pattern=rhs,
            conditions=when or [],
            version_range=self.version,
        )
        self._axioms[name] = entry
        return entry

    def get_contract(self, name: str) -> Optional[FunctionContract]:
        return self._contracts.get(name)

    def get_axiom(self, name: str) -> Optional[LibraryAxiomEntry]:
        return self._axioms.get(name)

    def all_contracts(self) -> Dict[str, FunctionContract]:
        return dict(self._contracts)

    def all_axioms(self) -> Dict[str, LibraryAxiomEntry]:
        return dict(self._axioms)

    def all_provenances(self) -> List[TrustProvenance]:
        """Get all trust provenances from this theory."""
        result = []
        for c in self._contracts.values():
            result.append(c.to_provenance())
        for a in self._axioms.values():
            result.append(a.to_provenance())
        return result

    def summary(self) -> str:
        return (f'LibraryTheory({self.library} {self.version}): '
                f'{len(self._contracts)} contracts, {len(self._axioms)} axioms')


# ═══════════════════════════════════════════════════════════════════
# Proof term: LibraryAxiom — use a library property in a proof
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class LibraryAxiom(ProofTerm):
    """Apply an assumed property of a Python library as a proof step.

    This is EXPLICITLY TRUSTED — not machine-checked.
    The trust_provenance records exactly what is being assumed.

    Unlike MathlibTheorem (which trusts Lean's kernel), this trusts
    the human who wrote the library contract.
    """
    library: str                        # 'sympy', 'numpy', etc.
    axiom_name: str                     # name in the LibraryTheory
    instantiation: Dict[str, OTerm] = field(default_factory=dict)
    statement: str = ''                 # the assertion being used
    version: str = ''                   # library version constraint

    def children(self) -> List[ProofTerm]:
        return []

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        binds = ', '.join(f'{k}={v.canon()}' for k, v in self.instantiation.items())
        trust = '🟠 LIBRARY_ASSUMED'
        return f'{pad}{trust} {self.library}.{self.axiom_name}({binds})'

    def provenance(self) -> TrustProvenance:
        return TrustProvenance(
            source=TrustSource.LIBRARY_ASSUMED,
            name=self.axiom_name,
            library=self.library,
            version=self.version,
            statement=self.statement,
        )


@dataclass(frozen=True)
class LibraryContract(ProofTerm):
    """Apply a library function's postcondition as a proof step.

    Given that preconditions hold, the postconditions are assumed true.

    Example:
        # If A is square and invertible, then np.linalg.solve(A, b)
        # returns x such that A @ x ≈ b
        LibraryContract("numpy", "linalg.solve",
            precondition_proofs={"A_square": ..., "A_invertible": ...},
            postcondition="A @ result ≈ b",
        )
    """
    library: str
    function_name: str
    precondition_proofs: Dict[str, ProofTerm] = field(default_factory=dict)
    postcondition: str = ''
    instantiation: Dict[str, OTerm] = field(default_factory=dict)

    def children(self) -> List[ProofTerm]:
        return list(self.precondition_proofs.values())

    def pretty(self, indent: int = 0) -> str:
        pad = '  ' * indent
        parts = [f'{pad}🟠 contract {self.library}.{self.function_name}:']
        for name, proof in self.precondition_proofs.items():
            parts.append(f'{pad}  pre[{name}]:')
            parts.append(proof.pretty(indent + 2))
        parts.append(f'{pad}  ⊢ {self.postcondition}')
        return '\n'.join(parts)


# ═══════════════════════════════════════════════════════════════════
# Global library registry
# ═══════════════════════════════════════════════════════════════════

_LIBRARY_REGISTRY: Dict[str, LibraryTheory] = {}


def register_library(theory: LibraryTheory) -> None:
    """Register a library theory globally."""
    _LIBRARY_REGISTRY[theory.library] = theory


def get_library(name: str) -> Optional[LibraryTheory]:
    """Look up a registered library theory."""
    return _LIBRARY_REGISTRY.get(name)


def all_libraries() -> Dict[str, LibraryTheory]:
    """Get all registered library theories."""
    return dict(_LIBRARY_REGISTRY)


# ═══════════════════════════════════════════════════════════════════
# Built-in library theories for common Python libraries
# ═══════════════════════════════════════════════════════════════════

def _build_builtins_theory() -> LibraryTheory:
    """Theory for Python builtins — sorted, len, range, etc."""
    t = LibraryTheory("builtins")

    t.function("sorted",
        takes=[("iterable", "Iterable")],
        returns="list",
        ensures=[
            "result is a permutation of list(iterable)",
            "result is sorted in ascending order",
            "len(result) == len(list(iterable))",
        ],
        pure=True,
    )

    t.function("len",
        takes=[("obj", "Sized")],
        returns="int",
        ensures=["result >= 0"],
        pure=True,
    )

    t.function("range",
        takes=[("start", "int"), ("stop", "int"), ("step", "int")],
        returns="range",
        ensures=["len(result) == max(0, ceil((stop - start) / step))"],
        pure=True,
    )

    t.function("reversed",
        takes=[("seq", "Sequence")],
        returns="iterator",
        ensures=["list(result) == list(seq)[::-1]"],
        pure=True,
    )

    t.function("enumerate",
        takes=[("iterable", "Iterable"), ("start", "int")],
        returns="iterator",
        ensures=["result yields (start+i, x) for i, x in iteration"],
        pure=True,
    )

    t.function("zip",
        takes=[("*iterables", "Iterable")],
        returns="iterator",
        ensures=["len(list(result)) == min(len(it) for it in iterables)"],
        pure=True,
    )

    t.function("map",
        takes=[("func", "Callable"), ("iterable", "Iterable")],
        returns="iterator",
        ensures=["list(result) == [func(x) for x in iterable]"],
        pure=True,
    )

    t.function("filter",
        takes=[("func", "Callable"), ("iterable", "Iterable")],
        returns="iterator",
        ensures=["list(result) == [x for x in iterable if func(x)]"],
        pure=True,
    )

    # Equational axioms
    t.axiom("sorted_idempotent",
        statement="sorted(sorted(xs)) == sorted(xs)",
    )
    t.axiom("sorted_preserves_length",
        statement="len(sorted(xs)) == len(xs)",
    )
    t.axiom("len_nonneg",
        statement="len(xs) >= 0",
    )
    t.axiom("reversed_involution",
        statement="list(reversed(list(reversed(xs)))) == list(xs)",
    )
    t.axiom("map_compose",
        statement="list(map(f, map(g, xs))) == list(map(lambda x: f(g(x)), xs))",
    )
    t.axiom("filter_map_commute",
        statement="list(map(f, filter(p, xs))) == list(filter(p, map(f, xs)))",
        when=["p(x) == p(f(x)) for all x"],
    )

    return t


def _build_sympy_theory() -> LibraryTheory:
    """Theory for sympy — symbolic mathematics."""
    t = LibraryTheory("sympy", version=">=1.12")

    t.function("expand",
        takes=[("expr", "Expr")],
        returns="Expr",
        ensures=[
            "result is algebraically equivalent to expr",
            "result is in expanded polynomial form",
        ],
        pure=True,
    )

    t.function("simplify",
        takes=[("expr", "Expr")],
        returns="Expr",
        ensures=["result is algebraically equivalent to expr"],
        pure=True,
    )

    t.function("factor",
        takes=[("expr", "Expr")],
        returns="Expr",
        ensures=["result is algebraically equivalent to expr"],
        pure=True,
    )

    t.function("solve",
        takes=[("eq", "Expr"), ("symbol", "Symbol")],
        returns="list[Expr]",
        ensures=["for each s in result: eq.subs(symbol, s) == 0"],
        pure=True,
    )

    t.function("diff",
        takes=[("expr", "Expr"), ("symbol", "Symbol")],
        returns="Expr",
        ensures=["result is the symbolic derivative of expr w.r.t. symbol"],
        pure=True,
    )

    t.function("integrate",
        takes=[("expr", "Expr"), ("symbol", "Symbol")],
        returns="Expr",
        ensures=["diff(result, symbol) == expr (up to constants)"],
        pure=True,
    )

    # Equational axioms
    t.axiom("expand_distributes_add",
        statement="expand(a + b) == expand(a) + expand(b)",
        lhs="expand(a + b)",
        rhs="expand(a) + expand(b)",
    )
    t.axiom("simplify_idempotent",
        statement="simplify(simplify(e)) == simplify(e)",
        lhs="simplify(simplify(e))",
        rhs="simplify(e)",
    )
    t.axiom("factor_expand_inverse",
        statement="factor(expand(e)) == e",
        when=["e is a polynomial over integers"],
    )
    t.axiom("diff_linearity",
        statement="diff(a*f + b*g, x) == a*diff(f, x) + b*diff(g, x)",
        when=["a, b are constants w.r.t. x"],
    )
    t.axiom("diff_product_rule",
        statement="diff(f*g, x) == f*diff(g, x) + g*diff(f, x)",
    )
    t.axiom("diff_chain_rule",
        statement="diff(f(g(x)), x) == diff(f, g(x)) * diff(g, x)",
    )
    t.axiom("integrate_diff_inverse",
        statement="diff(integrate(f, x), x) == f",
    )

    return t


def _build_numpy_theory() -> LibraryTheory:
    """Theory for numpy — numerical computing."""
    t = LibraryTheory("numpy", version=">=1.20")

    t.function("dot",
        takes=[("a", "ndarray"), ("b", "ndarray")],
        returns="ndarray",
        requires=["a.shape[-1] == b.shape[0]"],
        ensures=[
            "result.shape == (*a.shape[:-1], *b.shape[1:])",
            "result is the matrix product of a and b",
        ],
        pure=True,
    )

    t.function("linalg.solve",
        takes=[("a", "ndarray"), ("b", "ndarray")],
        returns="ndarray",
        requires=["a is square", "a is non-singular"],
        ensures=["np.allclose(a @ result, b)"],
        raises=["LinAlgError"],
        pure=True,
    )

    t.function("linalg.inv",
        takes=[("a", "ndarray")],
        returns="ndarray",
        requires=["a is square", "a is non-singular"],
        ensures=["np.allclose(a @ result, np.eye(a.shape[0]))"],
        raises=["LinAlgError"],
        pure=True,
    )

    t.function("sort",
        takes=[("a", "ndarray")],
        returns="ndarray",
        ensures=[
            "result contains same elements as a",
            "result is sorted along last axis",
        ],
        pure=True,
    )

    t.function("zeros",
        takes=[("shape", "tuple[int, ...]")],
        returns="ndarray",
        ensures=["result.shape == shape", "all elements are 0.0"],
        pure=True,
    )

    t.function("ones",
        takes=[("shape", "tuple[int, ...]")],
        returns="ndarray",
        ensures=["result.shape == shape", "all elements are 1.0"],
        pure=True,
    )

    # Equational axioms
    t.axiom("dot_associative",
        statement="np.dot(np.dot(A, B), C) == np.dot(A, np.dot(B, C))",
        when=["shapes are compatible"],
    )
    t.axiom("dot_identity",
        statement="np.dot(A, np.eye(n)) == A",
        when=["A.shape[1] == n"],
    )
    t.axiom("inv_correct",
        statement="np.dot(A, np.linalg.inv(A)) == np.eye(n)",
        when=["A is n×n and non-singular"],
    )
    t.axiom("sort_idempotent",
        statement="np.sort(np.sort(a)) == np.sort(a)",
    )
    t.axiom("transpose_involution",
        statement="a.T.T == a",
    )

    return t


def _build_collections_theory() -> LibraryTheory:
    """Theory for collections — Python's data structure library."""
    t = LibraryTheory("collections")

    t.function("Counter",
        takes=[("iterable", "Iterable")],
        returns="Counter",
        ensures=["result[x] == count of x in iterable for all x"],
        pure=True,
    )

    t.function("defaultdict",
        takes=[("default_factory", "Callable")],
        returns="defaultdict",
        ensures=["result[missing_key] == default_factory()"],
        pure=True,
    )

    t.function("OrderedDict",
        takes=[],
        returns="OrderedDict",
        ensures=["iteration order matches insertion order"],
        pure=True,
    )

    t.function("deque",
        takes=[("iterable", "Iterable"), ("maxlen", "Optional[int]")],
        returns="deque",
        ensures=[
            "list(result) == list(iterable)[-maxlen:] if maxlen else list(iterable)",
        ],
        pure=True,
    )

    t.axiom("counter_add_commutes",
        statement="Counter(a) + Counter(b) == Counter(b) + Counter(a)",
    )
    t.axiom("counter_from_list",
        statement="sum(Counter(xs).values()) == len(xs)",
    )
    t.axiom("deque_appendleft_popleft",
        statement="d.popleft() after d.appendleft(x) returns x",
        when=["d is not empty or x was just appended"],
    )

    return t


def _build_itertools_theory() -> LibraryTheory:
    """Theory for itertools — functional iteration patterns."""
    t = LibraryTheory("itertools")

    t.function("chain",
        takes=[("*iterables", "Iterable")],
        returns="iterator",
        ensures=["list(result) == [x for it in iterables for x in it]"],
        pure=True,
    )

    t.function("product",
        takes=[("*iterables", "Iterable")],
        returns="iterator",
        ensures=["len(list(result)) == product of lengths of iterables"],
        pure=True,
    )

    t.function("combinations",
        takes=[("iterable", "Iterable"), ("r", "int")],
        returns="iterator",
        ensures=["len(list(result)) == C(n, r) where n = len(list(iterable))"],
        pure=True,
    )

    t.function("permutations",
        takes=[("iterable", "Iterable"), ("r", "Optional[int]")],
        returns="iterator",
        ensures=["len(list(result)) == P(n, r) where n = len(list(iterable))"],
        pure=True,
    )

    t.axiom("chain_associative",
        statement="list(chain(chain(a, b), c)) == list(chain(a, chain(b, c)))",
    )
    t.axiom("chain_empty_identity",
        statement="list(chain(a, [])) == list(a)",
    )
    t.axiom("product_length",
        statement="len(list(product(a, b))) == len(list(a)) * len(list(b))",
    )

    return t


# ═══════════════════════════════════════════════════════════════════
# Initialize built-in theories
# ═══════════════════════════════════════════════════════════════════

def _init_builtin_theories() -> None:
    """Register all built-in library theories."""
    for builder in [_build_builtins_theory, _build_sympy_theory,
                    _build_numpy_theory, _build_collections_theory,
                    _build_itertools_theory]:
        register_library(builder())


# Auto-register on import
_init_builtin_theories()
