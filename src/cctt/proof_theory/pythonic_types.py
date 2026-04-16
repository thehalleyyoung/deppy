"""Pythonic Dependent Types — a type system designed for Python's reality.

Python is not Haskell. Everything is a dict. Types are duck-shaped.
Functions are first-class but loosely typed. Mutation is everywhere.
Exception handling is control flow. `None` is a billion-dollar mistake
that every Python program lives with.

This module provides dependent types that EMBRACE these Pythonic realities
rather than fighting them:

    DuckType         — types defined by what operations they support
    DictShape        — structural types for dict-as-object patterns
    Optional/Nullable — explicit None-tracking (the biggest Python bug source)
    PyUnion          — Python's ubiquitous Union[X, Y] as a proper coproduct
    Refinement       — {x : A | φ(x)} where φ is Z3-decidable or oracle-judged
    DependentDict    — Dict[K, V(k)] where values depend on keys
    Protocol         — structural subtyping (PEP 544)
    MutableRef       — explicit mutation tracking (Python's hidden state)
    ExceptionEffect  — what a function might raise (try/except as effect)
    GeneratorType    — yield-based lazy sequences
    Sigma            — Σ(x:A).B(x) for proof-carrying code
    Pi               — Π(x:A).B(x) for dependent functions
    PyLibType        — opaque library function with contract

Every type carries its "fiber" — the duck-type decomposition that the
Čech cohomology engine uses.  This makes the type system and the
verification engine speak the same language.

Design Principle: types should be INFERRED from Python code, not
imposed by annotations.  The bidirectional engine (bidirectional.py)
synthesizes types from usage patterns, then checks them against specs.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, FrozenSet, List, Optional, Set, Tuple, Union

from cctt.proof_theory.predicates import (
    Pred, PTrue, PVar, PLit, PCompare, PIsNone, PNot, PIsInstance,
    PAttr, PCall, PLibCall, PAnd, POr, PContains, PHasAttr,
    RefinementFiber, RefinementCover, Decidability,
    parse_predicate,
)


# ═══════════════════════════════════════════════════════════════════
# Universe levels — keeps the type theory consistent
# ═══════════════════════════════════════════════════════════════════

class Level(Enum):
    """Universe levels for the type hierarchy.

    In Python terms:
      VALUE  = runtime values (ints, strings, objects)
      TYPE   = type objects (int, str, list)
      KIND   = metatypes (type, ABCMeta)
      SORT   = the universe of kinds (rarely needed)
    """
    VALUE = 0
    TYPE = 1
    KIND = 2
    SORT = 3


# ═══════════════════════════════════════════════════════════════════
# Base type
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class CType:
    """Base class for all C⁴ types.

    Every type knows its universe level and can compute the duck-type
    fiber it lives in.  This connects the type system to the Čech
    cohomology engine.
    """
    def level(self) -> Level:
        return Level.TYPE

    def fiber(self) -> FrozenSet[str]:
        """The duck-type operations this type supports.

        Used by the Čech engine to decompose verification into
        *capability fibers* — which operations a value supports.
        This is a structural/syntactic notion, NOT a logical one.
        """
        return frozenset()

    def refinement_cover(self, var: str = 'x') -> Optional[RefinementCover]:
        """The default refinement cover for this type.

        Returns a cover whose fibers are refinement types —
        predicates like {x : T | φ(x)}.  This is the LOGICAL
        decomposition used by the proof checker for Čech descent.

        Returns None if no non-trivial cover is available.
        Subclasses override to provide meaningful covers.
        """
        return None

    def is_inhabited(self) -> Optional[bool]:
        """Can this type have any values? None = unknown."""
        return None

    def pretty(self) -> str:
        return type(self).__name__


# ═══════════════════════════════════════════════════════════════════
# Python's actual type zoo — what programs really use
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class PyAtom(CType):
    """Atomic Python types: int, float, str, bytes, bool, NoneType.

    These are the leaves of the type tree — irreducible.
    """
    name: str  # 'int', 'float', 'str', 'bytes', 'bool', 'NoneType'

    def fiber(self) -> FrozenSet[str]:
        _fibers = {
            'int': frozenset({'add', 'sub', 'mul', 'floordiv', 'mod', 'lt', 'eq', 'hash'}),
            'float': frozenset({'add', 'sub', 'mul', 'truediv', 'lt', 'eq'}),
            'str': frozenset({'add', 'getitem', 'len', 'iter', 'contains', 'eq', 'hash',
                              'split', 'join', 'strip', 'replace', 'startswith', 'endswith'}),
            'bytes': frozenset({'add', 'getitem', 'len', 'iter', 'contains', 'eq', 'hash'}),
            'bool': frozenset({'and', 'or', 'not', 'eq', 'hash'}),
            'NoneType': frozenset(),
        }
        return _fibers.get(self.name, frozenset())

    def is_inhabited(self) -> Optional[bool]:
        return True

    def pretty(self) -> str:
        return self.name


# Singleton atoms
INT = PyAtom('int')
FLOAT = PyAtom('float')
STR = PyAtom('str')
BYTES = PyAtom('bytes')
BOOL = PyAtom('bool')
NONE_TYPE = PyAtom('NoneType')


@dataclass(frozen=True)
class DuckType(CType):
    """Type defined by supported operations — Python's true type system.

    In Python, "if it walks like a duck and quacks like a duck, it's a duck."
    A DuckType is a set of operation signatures that a value must support.

    This is the C⁴ site category: each fiber in the Čech cover corresponds
    to a subset of duck operations.

    Example:
        Iterable = DuckType({'__iter__', '__next__'})
        Sized = DuckType({'__len__'})
        Mapping = DuckType({'__getitem__', '__contains__', 'keys', 'values', 'items'})
    """
    ops: FrozenSet[str]
    name: str = ''

    def fiber(self) -> FrozenSet[str]:
        return self.ops

    def subsumes(self, other: 'DuckType') -> bool:
        """Does this duck type support everything `other` requires?"""
        return self.ops >= other.ops

    def pretty(self) -> str:
        if self.name:
            return self.name
        ops_str = ', '.join(sorted(self.ops)[:5])
        if len(self.ops) > 5:
            ops_str += ', ...'
        return f'Duck({ops_str})'


# Common duck types
ITERABLE = DuckType(frozenset({'__iter__'}), 'Iterable')
ITERATOR = DuckType(frozenset({'__iter__', '__next__'}), 'Iterator')
SIZED = DuckType(frozenset({'__len__'}), 'Sized')
CONTAINER = DuckType(frozenset({'__contains__'}), 'Container')
HASHABLE = DuckType(frozenset({'__hash__', '__eq__'}), 'Hashable')
COMPARABLE = DuckType(frozenset({'__lt__', '__le__', '__gt__', '__ge__', '__eq__'}), 'Comparable')
SEQUENCE = DuckType(frozenset({'__getitem__', '__len__', '__iter__', '__contains__'}), 'Sequence')
MAPPING = DuckType(frozenset({'__getitem__', '__contains__', 'keys', 'values', 'items', '__len__'}), 'Mapping')
CALLABLE_DUCK = DuckType(frozenset({'__call__'}), 'Callable')
NUMERIC = DuckType(frozenset({'__add__', '__sub__', '__mul__', '__truediv__',
                               '__neg__', '__abs__'}), 'Numeric')


@dataclass(frozen=True)
class DictShape(CType):
    """Structural type for Python's dict-as-object pattern.

    Python uses dicts EVERYWHERE as lightweight objects:
        config = {'host': 'localhost', 'port': 8080, 'debug': True}
        point = {'x': 1.0, 'y': 2.0}

    A DictShape specifies which keys exist and what types their values have.
    Keys may be required or optional.

    This is a *dependent record type* in disguise: each field's type can
    depend on the values of earlier fields (via refinements).
    """
    required: Dict[str, CType] = field(default_factory=dict)
    optional: Dict[str, CType] = field(default_factory=dict)
    allow_extra: bool = True  # Python dicts are open by default

    def fiber(self) -> FrozenSet[str]:
        return MAPPING.ops | frozenset(f'key:{k}' for k in self.required)

    def pretty(self) -> str:
        parts = []
        for k, v in self.required.items():
            parts.append(f'{k}: {v.pretty()}')
        for k, v in self.optional.items():
            parts.append(f'{k}?: {v.pretty()}')
        if self.allow_extra:
            parts.append('...')
        return '{' + ', '.join(parts) + '}'


@dataclass(frozen=True)
class PyList(CType):
    """List[T] — Python's workhorse container."""
    element: CType

    def fiber(self) -> FrozenSet[str]:
        return SEQUENCE.ops | frozenset({'append', 'extend', 'insert', 'pop', 'sort', 'reverse'})

    def pretty(self) -> str:
        return f'list[{self.element.pretty()}]'


@dataclass(frozen=True)
class PyDict(CType):
    """Dict[K, V] — Python's universal data structure."""
    key: CType
    value: CType

    def fiber(self) -> FrozenSet[str]:
        return MAPPING.ops

    def pretty(self) -> str:
        return f'dict[{self.key.pretty()}, {self.value.pretty()}]'


@dataclass(frozen=True)
class PySet(CType):
    """Set[T] — unordered, unique elements."""
    element: CType

    def fiber(self) -> FrozenSet[str]:
        return frozenset({'__contains__', '__len__', '__iter__', 'add', 'discard',
                          'union', 'intersection', 'difference'})

    def pretty(self) -> str:
        return f'set[{self.element.pretty()}]'


@dataclass(frozen=True)
class PyTuple(CType):
    """Tuple[T1, T2, ...] — fixed-length heterogeneous container."""
    elements: Tuple[CType, ...]

    def fiber(self) -> FrozenSet[str]:
        return frozenset({'__getitem__', '__len__', '__iter__', '__hash__', '__eq__'})

    def pretty(self) -> str:
        inner = ', '.join(e.pretty() for e in self.elements)
        return f'tuple[{inner}]'


# ═══════════════════════════════════════════════════════════════════
# Python-specific type formers — handling Python's quirks
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Nullable(CType):
    """Optional[T] = T | None — Python's billion-dollar problem.

    Almost every Python function can return None. This type makes it
    explicit and forces proofs to handle the None case.

    In the Čech decomposition, this creates two fibers:
      fiber_some: T operations
      fiber_none: NoneType (empty fiber)
    The proof obligation is: the code handles both fibers.
    """
    inner: CType

    def fiber(self) -> FrozenSet[str]:
        return self.inner.fiber()  # The None fiber is special-cased

    def refinement_cover(self, var: str = 'x') -> Optional[RefinementCover]:
        """Nullable decomposes into Some/None refinement fibers."""
        return RefinementCover.from_predicates(
            f'Optional[{self.inner.pretty()}]', var,
            [('some', f'{var} is not None'),
             ('none', f'{var} is None')],
            var_sorts={var: 'Int'},
        )

    def pretty(self) -> str:
        return f'Optional[{self.inner.pretty()}]'


@dataclass(frozen=True)
class PyUnion(CType):
    """Union[T1, T2, ...] — Python's ubiquitous sum type.

    Python functions often return different types depending on input:
        def parse(s): return int(s) if s.isdigit() else s

    Each variant creates a fiber in the Čech cover.
    """
    variants: Tuple[CType, ...]

    def fiber(self) -> FrozenSet[str]:
        result: Set[str] = set()
        for v in self.variants:
            result |= v.fiber()
        return frozenset(result)

    def refinement_cover(self, var: str = 'x') -> Optional[RefinementCover]:
        """Union decomposes into per-variant isinstance fibers."""
        specs = []
        for v in self.variants:
            name = v.pretty()
            specs.append((name, f'isinstance({var}, {name})'))
        if specs:
            return RefinementCover.from_predicates(
                self.pretty(), var, specs, var_sorts={var: 'Int'})
        return None

    def pretty(self) -> str:
        inner = ' | '.join(v.pretty() for v in self.variants)
        return inner


@dataclass(frozen=True)
class MutableRef(CType):
    """Explicit mutation tracking — Python's hidden state.

    Python is not purely functional. Lists, dicts, and objects are
    mutable by default. This type tracks what can be mutated and
    when, connecting to the sheaf-theoretic story:

    A mutable reference is a SECTION of the state sheaf that varies
    over the timeline of execution.

    pre_type:  type before mutation
    post_type: type after mutation (may differ!)
    mutates:   set of operations that modify the value
    """
    content: CType
    mutates: FrozenSet[str] = frozenset()  # e.g., {'append', 'sort', '__setitem__'}

    def fiber(self) -> FrozenSet[str]:
        return self.content.fiber() | self.mutates

    def pretty(self) -> str:
        if self.mutates:
            muts = ', '.join(sorted(self.mutates))
            return f'Mut[{self.content.pretty()}, mutates={{{muts}}}]'
        return f'Mut[{self.content.pretty()}]'


@dataclass(frozen=True)
class ExceptionEffect(CType):
    """What exceptions a function might raise — try/except as effect type.

    Python uses exceptions for control flow (StopIteration, KeyError, etc.).
    This type tracks what effects a function has, connecting to the D22
    dichotomy (exception as algebraic effect vs. error value).

    In the cubical model: exceptions create a fiber where the function's
    output is ⊥ (bottom), and the catch handler provides the alternative path.
    """
    return_type: CType
    raises: FrozenSet[str] = frozenset()  # e.g., {'ValueError', 'KeyError'}
    catches: FrozenSet[str] = frozenset()  # what it handles internally

    def fiber(self) -> FrozenSet[str]:
        return self.return_type.fiber() | frozenset(f'raises:{e}' for e in self.raises)

    def refinement_cover(self, var: str = 'x') -> Optional[RefinementCover]:
        """Exception effects decompose into normal + per-exception fibers."""
        specs: List[Tuple[str, str]] = [('normal', 'True')]
        for exc in sorted(self.raises):
            specs.append((f'except_{exc}', f'isinstance({var}, {exc})'))
        if len(specs) > 1:
            return RefinementCover.from_predicates(
                self.pretty(), var, specs, var_sorts={var: 'Int'})
        return None

    def pretty(self) -> str:
        base = self.return_type.pretty()
        if self.raises:
            excs = ', '.join(sorted(self.raises))
            return f'{base} raises {{{excs}}}'
        return base


@dataclass(frozen=True)
class GeneratorType(CType):
    """Generator[YieldT, SendT, ReturnT] — Python's lazy sequence protocol.

    Generators are coroutines that yield values lazily. They're a special
    case of a dependent type: the type of the next yielded value can
    depend on what was sent in.
    """
    yield_type: CType
    send_type: CType = field(default_factory=lambda: NONE_TYPE)
    return_type: CType = field(default_factory=lambda: NONE_TYPE)

    def fiber(self) -> FrozenSet[str]:
        return frozenset({'__iter__', '__next__', 'send', 'throw', 'close'})

    def pretty(self) -> str:
        return f'Generator[{self.yield_type.pretty()}, {self.send_type.pretty()}, {self.return_type.pretty()}]'


@dataclass(frozen=True)
class Protocol(CType):
    """Structural subtyping (PEP 544) — Python's formalized duck typing.

    A Protocol defines a set of method signatures that a type must implement.
    Unlike DuckType (which tracks operations used), Protocol tracks the
    full method signatures including argument and return types.
    """
    name: str
    methods: Dict[str, Tuple[Tuple[CType, ...], CType]] = field(default_factory=dict)

    def fiber(self) -> FrozenSet[str]:
        return frozenset(self.methods.keys())

    def pretty(self) -> str:
        return f'Protocol[{self.name}]'


# ═══════════════════════════════════════════════════════════════════
# Dependent type formers — the proof-theoretic core
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Refinement(CType):
    """Refinement type: {x : A | φ(x)} — the bridge between specs and types.

    This is where Python meets dependent types. A Refinement attaches
    a logical predicate to a base type:

        {xs : list[int] | sorted(xs) == xs and len(xs) > 0}
        {x : torch.Tensor | x.mean() == 0}
        {e : sympy.Expr | sympy.expand(e) == e}

    The predicate is a full Pred AST that can express arbitrary
    conditions including library operations.  Its decidability level
    determines what proof strategy is needed:

      - Z3: checked by the solver (arithmetic, boolean)
      - STRUCTURAL: isinstance, is None, hasattr
      - LIBRARY: involves library calls — needs library axioms
      - ORACLE: complex semantic — needs LLM judgment

    In the Čech decomposition, multiple refinements of the same base
    type form a RefinementCover whose fibers are the refinement
    predicates.
    """
    base: CType
    predicate: Pred                  # typed predicate AST
    predicate_str: str = ''          # human-readable (for display)
    variables: Dict[str, str] = field(default_factory=dict)

    def __post_init__(self):
        if not self.predicate_str and self.predicate:
            object.__setattr__(self, 'predicate_str', self.predicate.pretty())

    def fiber(self) -> FrozenSet[str]:
        return self.base.fiber() | frozenset({f'refine:{self.predicate_str[:30]}'})

    @property
    def decidability(self) -> Decidability:
        return self.predicate.decidability()

    @property
    def is_z3_decidable(self) -> bool:
        return self.decidability == Decidability.Z3

    def is_inhabited(self) -> Optional[bool]:
        if self.is_z3_decidable:
            return None  # Z3 can answer this
        return None

    def refinement_cover(self, var: str = 'x') -> Optional[RefinementCover]:
        """A single-fiber cover: this refinement IS the one fiber."""
        fiber = RefinementFiber(
            name='refined',
            base_type_name=self.base.pretty(),
            predicate=self.predicate,
            variables=self.variables,
        )
        cover = RefinementCover(
            base_type_name=self.base.pretty(),
            bound_var=var,
            fibers={'refined': fiber},
            exhaustiveness_status='assumed',
        )
        return cover

    def pretty(self) -> str:
        return f'{{{self.base.pretty()} | {self.predicate_str}}}'


@dataclass(frozen=True)
class Sigma(CType):
    """Dependent pair: Σ(x:A).B(x) — proof-carrying values.

    This is the type of proof-carrying code:
        Σ(result : list[int]). sorted(result) ∧ permutation(result, input)

    The first component is the value; the second is the proof/witness.

    In Python terms, this is like returning a tuple (value, certificate)
    where the certificate depends on the value.
    """
    var_name: str
    fst_type: CType           # type of the value
    snd_type_desc: str         # description of the proof type (depends on var)

    def fiber(self) -> FrozenSet[str]:
        return self.fst_type.fiber()

    def pretty(self) -> str:
        return f'Σ({self.var_name} : {self.fst_type.pretty()}). {self.snd_type_desc}'


@dataclass(frozen=True)
class Pi(CType):
    """Dependent function: Π(x:A).B(x) — functions whose return type
    depends on the input.

    This models Python's common pattern where the return type depends
    on the argument:
        def get(d: dict, key: str, default: T) -> T | V
        def zeros(shape: tuple[int, ...]) -> ndarray[shape]

    In the fiber decomposition, each input fiber gets its own return type.
    """
    var_name: str
    domain: CType
    codomain_desc: str  # description of B(x), depends on var_name

    def fiber(self) -> FrozenSet[str]:
        return frozenset({'__call__'}) | self.domain.fiber()

    def pretty(self) -> str:
        return f'Π({self.var_name} : {self.domain.pretty()}). {self.codomain_desc}'


@dataclass(frozen=True)
class DependentDict(CType):
    """Dict[K, V(k)] — dictionary where value type depends on key.

    This is INCREDIBLY common in Python:
        config['port']  → int
        config['host']  → str
        config['debug'] → bool

    DataFrame columns:
        df['age']   → Series[int]
        df['name']  → Series[str]

    JSON responses:
        resp['data']   → list
        resp['status'] → int

    Each key fiber gets its own value type — this IS the sheaf structure.
    The presheaf assigns to each open set (key subset) a value type.
    """
    key_type: CType
    value_map: Dict[str, CType] = field(default_factory=dict)
    default_value_type: Optional[CType] = None

    def fiber(self) -> FrozenSet[str]:
        return MAPPING.ops | frozenset(f'key:{k}' for k in self.value_map)

    def refinement_cover(self, var: str = 'x') -> Optional[RefinementCover]:
        """Per-key refinement cover: each key gets its own fiber."""
        if not self.value_map:
            return None
        specs = []
        for k in self.value_map:
            specs.append((f'key_{k}', f"'{k}' in {var}"))
        return RefinementCover.from_predicates(
            self.pretty(), var, specs, var_sorts={var: 'Int'})

    def pretty(self) -> str:
        if self.value_map:
            entries = ', '.join(f'{k}: {v.pretty()}' for k, v in
                                list(self.value_map.items())[:3])
            if len(self.value_map) > 3:
                entries += ', ...'
            return f'DDict[{self.key_type.pretty()}, {{{entries}}}]'
        return f'DDict[{self.key_type.pretty()}, {self.default_value_type.pretty() if self.default_value_type else "?"}]'


# ═══════════════════════════════════════════════════════════════════
# Library type — opaque external function with contract
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class PyLibType(CType):
    """Type of an external library function — opaque with contract.

    We can't look inside numpy.linalg.solve or sympy.expand, but we
    CAN state what they promise (pre/postconditions).

    This is NOT a rich type former — it's an opaque operation with:
      - input contract (preconditions)
      - output contract (postconditions)
      - effect declaration (may raise, may mutate)
      - version bound (which versions this contract holds for)

    The rubber-duck critique was right: the hard part isn't the type;
    it's shape, dtype, domain assumptions, exceptions, aliasing, and
    versioned semantics.
    """
    module: str            # 'numpy', 'sympy', 'pandas'
    qualname: str          # 'linalg.solve', 'expand', 'DataFrame.groupby'
    input_types: Tuple[CType, ...] = ()
    output_type: Optional[CType] = None
    preconditions: Tuple[str, ...] = ()
    postconditions: Tuple[str, ...] = ()
    raises: FrozenSet[str] = frozenset()
    mutates_args: FrozenSet[int] = frozenset()  # indices of args it mutates
    version_range: str = ''  # e.g., '>=1.20,<2.0'

    def fiber(self) -> FrozenSet[str]:
        return frozenset({f'lib:{self.module}.{self.qualname}'})

    def refinement_cover(self, var: str = 'x') -> Optional[RefinementCover]:
        """Library type cover: fibers from preconditions."""
        if not self.preconditions:
            return None
        specs = []
        for i, pre in enumerate(self.preconditions):
            specs.append((f'pre_{i}', pre))
        return RefinementCover.from_predicates(
            self.pretty(), var, specs, var_sorts={var: 'Int'})

    def pretty(self) -> str:
        return f'{self.module}.{self.qualname}'


# ═══════════════════════════════════════════════════════════════════
# Type inference from duck-type operations
# ═══════════════════════════════════════════════════════════════════

def infer_type_from_ops(ops: FrozenSet[str]) -> CType:
    """Infer a CType from a set of duck-type operations.

    This bridges the duck-type inference engine (duck.py) and the
    type system. Given the operations observed on a variable, produce
    the most precise type.
    """
    # Check for specific patterns
    if ops >= MAPPING.ops:
        return PyDict(key=CType(), value=CType())
    if ops >= SEQUENCE.ops:
        return PyList(element=CType())
    if {'add', 'sub', 'mul', 'floordiv', 'mod'} <= ops:
        return INT
    if {'add', 'sub', 'mul', 'truediv'} <= ops:
        return FLOAT
    if {'split', 'join', 'strip', 'replace'} & ops:
        return STR
    if {'append', 'extend', 'pop', 'sort'} & ops:
        return PyList(element=CType())
    if {'keys', 'values', 'items'} & ops:
        return PyDict(key=CType(), value=CType())
    if ops <= {'__call__'}:
        return CALLABLE_DUCK
    if ops:
        return DuckType(ops)
    return CType()  # Top type — no constraints


def fiber_decompose_type(ty: CType) -> Dict[str, CType]:
    """Decompose a type into its *capability* fiber components.

    This is the STRUCTURAL decomposition (by type variant, not by predicate).
    For refinement-predicate decomposition, use ty.refinement_cover() instead.
    """
    fibers: Dict[str, CType] = {}

    if isinstance(ty, PyUnion):
        for i, v in enumerate(ty.variants):
            fibers[f'variant_{i}_{v.pretty()}'] = v
    elif isinstance(ty, Nullable):
        fibers['some'] = ty.inner
        fibers['none'] = NONE_TYPE
    elif isinstance(ty, DependentDict):
        for k, v in ty.value_map.items():
            fibers[f'key_{k}'] = v
        if ty.default_value_type:
            fibers['default'] = ty.default_value_type
    elif isinstance(ty, ExceptionEffect):
        fibers['normal'] = ty.return_type
        for exc in ty.raises:
            fibers[f'except_{exc}'] = CType()
    elif isinstance(ty, PyList):
        fibers['list'] = ty
    elif isinstance(ty, PyDict):
        fibers['dict'] = ty
    else:
        fibers['single'] = ty

    return fibers


def refine(base: CType, predicate_str: str,
           var: str = 'x', var_sorts: Optional[Dict[str, str]] = None,
           ) -> Refinement:
    """Convenience: create a refinement type from a predicate string.

    Examples:
        positive_int = refine(INT, "x > 0")
        zero_mean_tensor = refine(PyLibType("torch", "Tensor"), "x.mean() == 0")
        expanded_expr = refine(PyLibType("sympy", "Expr"), "sympy.expand(x) == x")
        square_matrix = refine(PyLibType("numpy", "ndarray"),
                               "x.shape[0] == x.shape[1]")
    """
    pred = parse_predicate(predicate_str)
    return Refinement(
        base=base,
        predicate=pred,
        predicate_str=predicate_str,
        variables=var_sorts or {var: 'Int'},
    )


def cover_from_predicates(base: CType, var: str,
                          specs: List[Tuple[str, str]],
                          var_sorts: Optional[Dict[str, str]] = None,
                          ) -> RefinementCover:
    """Convenience: build a RefinementCover over a CType.

    Examples:
        # Integer sign cover — Z3-decidable, exhaustive
        sign_cover = cover_from_predicates(INT, "x", [
            ("positive", "x > 0"),
            ("zero", "x == 0"),
            ("negative", "x < 0"),
        ])

        # Tensor shape cover — library-level
        shape_cover = cover_from_predicates(
            PyLibType("torch", "Tensor"), "t", [
                ("scalar", "len(t.shape) == 0"),
                ("vector", "len(t.shape) == 1"),
                ("matrix", "len(t.shape) == 2"),
                ("higher", "len(t.shape) > 2"),
            ])

        # SymPy canonical form cover — library-level
        form_cover = cover_from_predicates(
            PyLibType("sympy", "Expr"), "e", [
                ("expanded", "sympy.expand(e) == e"),
                ("factored", "sympy.factor(e) == e"),
                ("other", "sympy.expand(e) != e and sympy.factor(e) != e"),
            ])
    """
    return RefinementCover.from_predicates(
        base.pretty(), var, specs, var_sorts or {var: 'Int'})


# ═══════════════════════════════════════════════════════════════════
# Python-specific type formers: Callable, Any, TypeVar
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class PyCallable(CType):
    """Callable[[P1, P2, ...], R] — Python's first-class function type.

    In the cubical model, a callable is a SECTION of the function sheaf:
    for each input fiber (refinement region of the domain), there is
    a local return type.  The sheaf condition says these local return
    types glue into a coherent global return type.

    This enables refinement-type descent over function arguments:
    different argument predicates yield different return predicates.
    """
    param_types: Tuple[CType, ...] = ()
    return_type: CType = field(default_factory=CType)
    param_names: Tuple[str, ...] = ()
    is_pure: bool = True
    raises: FrozenSet[str] = frozenset()

    def fiber(self) -> FrozenSet[str]:
        return frozenset({'__call__'})

    def refinement_cover(self, var: str = 'f') -> Optional[RefinementCover]:
        """Callable decomposes into fibers by return-type predicate."""
        ret_cover = self.return_type.refinement_cover('result')
        if ret_cover and ret_cover.fibers:
            specs = []
            for name, fib in ret_cover.fibers.items():
                pred_str = fib.predicate.pretty() if fib.predicate else 'True'
                specs.append((f'returns_{name}', pred_str))
            return RefinementCover.from_predicates(
                self.pretty(), var, specs, {var: 'Int'})
        return None

    def pretty(self) -> str:
        params = ', '.join(t.pretty() for t in self.param_types)
        ret = self.return_type.pretty()
        return f'Callable[[{params}], {ret}]'


@dataclass(frozen=True)
class PyAny(CType):
    """Python's Any — the top type / dynamic universe.

    In the cubical model, Any is the TOTAL SPACE: every type is a fiber
    of Any.  A value of type Any can be restricted to any concrete type
    via isinstance checks, which are refinement predicates.

    Cubically: Any is contractible — it carries all paths.
    Sheaf-theoretically: Any is the terminal object.
    """

    def fiber(self) -> FrozenSet[str]:
        return frozenset({'__call__', '__getitem__', '__iter__', '__len__',
                          '__contains__', '__hash__', '__eq__', '__add__',
                          '__sub__', '__mul__', '__truediv__'})

    def refinement_cover(self, var: str = 'x') -> Optional[RefinementCover]:
        """Any decomposes into Python's built-in type hierarchy."""
        return RefinementCover.from_predicates(
            'Any', var, [
                ('int', f'isinstance({var}, int)'),
                ('float', f'isinstance({var}, float)'),
                ('str', f'isinstance({var}, str)'),
                ('bool', f'isinstance({var}, bool)'),
                ('list', f'isinstance({var}, list)'),
                ('dict', f'isinstance({var}, dict)'),
                ('none', f'{var} is None'),
                ('callable', f'callable({var})'),
                ('other', f'True'),
            ],
            var_sorts={var: 'Int'},
        )

    def is_inhabited(self) -> Optional[bool]:
        return True

    def level(self) -> Level:
        return Level.TYPE

    def pretty(self) -> str:
        return 'Any'


ANY = PyAny()


@dataclass(frozen=True)
class PyTypeVar(CType):
    """TypeVar — parametric polymorphism with variance and bounds.

    In the cubical model, a TypeVar is a FIBRATION: the type varies
    over a base space of possible instantiations.  The bound constrains
    which fibers exist.  Variance determines how paths (subtype relations)
    lift.

    Covariant:     T <: S  ⟹  F[T] <: F[S]     (paths lift covariantly)
    Contravariant: T <: S  ⟹  F[S] <: F[T]     (paths reverse)
    Invariant:     T <: S  ⟹  nothing           (no path lifting)
    """
    name: str = 'T'
    bound: Optional[CType] = None
    constraints: Tuple[CType, ...] = ()
    variance: str = 'invariant'

    def fiber(self) -> FrozenSet[str]:
        if self.bound:
            return self.bound.fiber()
        if self.constraints:
            result: Set[str] = set()
            for c in self.constraints:
                result |= c.fiber()
            return frozenset(result)
        return frozenset()

    def refinement_cover(self, var: str = 'x') -> Optional[RefinementCover]:
        """TypeVar with constraints → per-constraint fibers."""
        if self.constraints:
            specs = []
            for c in self.constraints:
                cname = c.pretty()
                specs.append((cname, f'isinstance({var}, {cname})'))
            return RefinementCover.from_predicates(
                self.pretty(), var, specs, var_sorts={var: 'Int'})
        return None

    def is_inhabited(self) -> Optional[bool]:
        if self.constraints:
            return any(c.is_inhabited() for c in self.constraints)
        return None

    def pretty(self) -> str:
        parts = [self.name]
        if self.bound:
            parts.append(f' <: {self.bound.pretty()}')
        if self.constraints:
            constrs = ', '.join(c.pretty() for c in self.constraints)
            parts.append(f' ∈ {{{constrs}}}')
        if self.variance != 'invariant':
            parts.append(f' ({self.variance})')
        return ''.join(parts)
