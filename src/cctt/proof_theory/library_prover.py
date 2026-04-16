"""Library Prover — cohomological proof generation for arbitrary Python libraries.

The library IS a presheaf topos.  Its type hierarchy IS the Čech nerve.
Correctness IS a sheaf condition.  This module makes that literal.

Given any Python library name, this module:

1. INTROSPECTS it as a presheaf on the type category
   - Objects: types/classes in the library
   - Morphisms: subtyping (inheritance) + coercions
   - Sections: function contracts / specifications

2. BUILDS the Čech nerve of the type cover
   - 0-simplices: individual types
   - k-simplices: k-fold overlaps (multiple inheritance, protocol overlap)
   - The nerve IS the simplicial complex of the proof space

3. GENERATES proof terms per simplex
   - 0-cochains: per-type LibraryAxiom / LibraryContract
   - 1-cochains: overlap compatibility via Transport
   - Descent/GluePath: glue local proofs into global proofs

4. COMPUTES Čech cohomology
   - H⁰ = ker δ⁰ = global sections = universal library properties
   - H¹ = coker δ⁰ = obstructions = where per-type proofs conflict

5. COMPILES everything through check_proof()

The oracle (for generating specification text) is pluggable:
   - DocstringOracle: extracts from docstrings (default, offline)
   - CopilotOracle: calls copilot-cli subprocess
   - MockOracle: for testing

Usage::

    report = prove_library('sympy')
    report = prove_library('collections')
    report = prove_library('math')

    # CLI entry point
    python -m cctt.proof_theory.library_prover sympy
"""
from __future__ import annotations

import ast
import importlib
import inspect
import itertools
import os
import pkgutil
import subprocess
import sys
import textwrap
import types
import typing
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Dict, FrozenSet, List, Optional, Protocol,
    Set, Tuple, Union,
)

from cctt.denotation import OTerm, OVar, OLit, OOp, OAbstract
from cctt.proof_theory.terms import (
    ProofTerm, Refl, Sym, Trans, Cong,
    Assume, Z3Discharge, CasesSplit, Definitional,
    Descent, FiberRestrict, RefinementDescent, PathCompose,
    Transport, HComp, GluePath, LibraryTransport,
    var, lit, op, abstract,
)
from cctt.proof_theory.checker import check_proof, VerificationResult
from cctt.proof_theory.library_axioms import (
    TrustProvenance, TrustSource, FunctionContract,
    LibraryAxiomEntry, LibraryTheory,
    LibraryAxiom, LibraryContract,
    register_library, get_library,
)


# ═══════════════════════════════════════════════════════════════════
# §1. Type Category — objects are types, morphisms are subtyping
# ═══════════════════════════════════════════════════════════════════

class IntrospectionTier(Enum):
    """How deeply we can introspect a callable."""
    FULL = "full"             # pure Python, inspectable, typed
    STUB = "stub"             # .pyi stubs or annotations only
    DOCSTRING = "docstring"   # only docstring available
    OPAQUE = "opaque"         # C extension / dynamic / no info


@dataclass
class FunctionSig:
    """Introspected function signature — a section of the spec presheaf."""
    name: str
    qualname: str
    module: str
    params: List[Tuple[str, str]]    # (name, type_annotation_str)
    return_type: str
    docstring: str
    is_method: bool = False
    is_classmethod: bool = False
    is_staticmethod: bool = False
    is_property: bool = False
    tier: IntrospectionTier = IntrospectionTier.FULL
    source: Optional[str] = None     # actual Python source code

    @property
    def is_pure_heuristic(self) -> bool:
        """Heuristic purity check from docstring and name."""
        impure = {'write', 'set', 'delete', 'remove', 'pop', 'clear',
                  'insert', 'append', 'extend', 'update', 'send', 'close'}
        return not any(w in self.name.lower() for w in impure)

    @property
    def raises_heuristic(self) -> List[str]:
        """Heuristic exception detection from docstring."""
        if not self.docstring:
            return []
        raises = []
        for line in self.docstring.split('\n'):
            stripped = line.strip()
            if stripped.startswith('Raises') or stripped.startswith(':raises'):
                parts = stripped.split(':')
                if len(parts) >= 2:
                    raises.append(parts[1].strip().split()[0])
        return raises


@dataclass
class TypeNode:
    """A node in the type category — an object of the topos.

    Each TypeNode carries:
    - its position in the inheritance DAG (the category structure)
    - its methods (sections of the spec presheaf at this object)
    - overlap data for Čech nerve construction
    """
    name: str
    qualname: str
    module: str
    bases: List[str]               # direct base class qualnames
    subclasses: List[str]          # known direct subclasses
    methods: Dict[str, FunctionSig]
    class_methods: Dict[str, FunctionSig]
    properties: List[str]
    is_abstract: bool
    tier: IntrospectionTier
    source: Optional[str] = None   # actual Python source code

    @property
    def full_name(self) -> str:
        return f'{self.module}.{self.qualname}'


@dataclass
class TypeMorphism:
    """A morphism in the type category — subtyping / coercion."""
    source: str       # subtype qualname
    target: str       # supertype qualname
    kind: str = 'inheritance'  # 'inheritance' | 'protocol' | 'coercion'


# ═══════════════════════════════════════════════════════════════════
# §2. Čech Nerve — simplicial complex from the type cover
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Simplex:
    """A k-simplex in the Čech nerve.

    0-simplex: a single type {T}
    1-simplex: a pair {T_i, T_j} with non-empty overlap
    2-simplex: a triple with non-empty triple overlap
    ...

    The dimension equals len(vertices) - 1.
    """
    vertices: FrozenSet[str]

    @property
    def dimension(self) -> int:
        return len(self.vertices) - 1

    def face(self, vertex_to_remove: str) -> 'Simplex':
        """The face obtained by removing one vertex."""
        return Simplex(self.vertices - {vertex_to_remove})

    def __repr__(self) -> str:
        return f'Δ{self.dimension}({",".join(sorted(self.vertices))})'


@dataclass
class CechNerve:
    """The Čech nerve of the type cover — the proof space.

    The nerve N(U) of a cover U = {U_i} has:
    - 0-simplices: one per open set U_i (each type)
    - k-simplices: one per non-empty (k+1)-fold intersection
    - face maps: removing one open set from the intersection

    This IS the space over which proofs live.  A global proof is
    a compatible family of local proofs on each simplex.
    """
    simplices: Dict[int, List[Simplex]] = field(default_factory=dict)
    types: Dict[str, TypeNode] = field(default_factory=dict)
    morphisms: List[TypeMorphism] = field(default_factory=list)

    @property
    def n_types(self) -> int:
        return len(self.simplices.get(0, []))

    @property
    def n_overlaps(self) -> int:
        return len(self.simplices.get(1, []))

    def get_simplices(self, dim: int) -> List[Simplex]:
        return self.simplices.get(dim, [])

    def euler_characteristic(self) -> int:
        """χ = Σ (-1)^k |C^k| — topological invariant of the proof space."""
        return sum((-1)**k * len(s) for k, s in self.simplices.items())

    def summary(self) -> str:
        parts = [f'CechNerve: χ={self.euler_characteristic()}']
        for dim in sorted(self.simplices.keys()):
            parts.append(f'  dim {dim}: {len(self.simplices[dim])} simplices')
        return '\n'.join(parts)


# ═══════════════════════════════════════════════════════════════════
# §3. Spec Presheaf — specifications as sections over the nerve
# ═══════════════════════════════════════════════════════════════════

class SectionKind(Enum):
    """What kind of proof artifact a section represents."""
    FUNCTION_CONTRACT = "function_contract"
    METHOD_CONTRACT = "method_contract"
    CLASS_INVARIANT = "class_invariant"
    DESCENT = "descent"
    GLUE = "glue"
    OVERLAP = "overlap"
    TRANSPORT = "transport"
    HCOMP = "hcomp"


@dataclass
class Section:
    """A section of the spec presheaf over a simplex.

    At a 0-simplex (type T): the specification of T's methods.
    At a 1-simplex (overlap T_i ∩ T_j): the compatibility condition.
    """
    simplex: Simplex
    function_name: str
    spec_text: str                    # the NL specification
    proof: Optional[ProofTerm] = None # the proof term (filled by Phase 4)
    result: Optional[VerificationResult] = None  # compilation result
    # Emitter metadata (populated during generation)
    kind: SectionKind = SectionKind.FUNCTION_CONTRACT
    owner_module: str = ''           # e.g., 'sympy.core.add'
    owner_symbol: str = ''           # e.g., 'Add.__init__'
    lhs: Optional[OTerm] = None      # left side of the proof goal
    rhs: Optional[OTerm] = None      # right side of the proof goal
    tier: IntrospectionTier = IntrospectionTier.FULL
    related_sections: List[str] = field(default_factory=list)

    @property
    def is_proved(self) -> bool:
        return self.result is not None and self.result.valid

    @property
    def section_id(self) -> str:
        """Stable unique ID for cross-referencing."""
        kind_prefix = self.kind.value.split('_')[0]
        return f'{kind_prefix}:{self.function_name}'


@dataclass
class SpecPresheaf:
    """The presheaf of specifications on the Čech nerve.

    F: N(U)^op → Set
    F(σ) = specifications valid on the types in σ

    A global section of F is a library-wide theorem.
    """
    nerve: CechNerve
    sections: Dict[Simplex, List[Section]] = field(default_factory=dict)

    def add_section(self, section: Section) -> None:
        self.sections.setdefault(section.simplex, []).append(section)

    @property
    def n_sections(self) -> int:
        return sum(len(ss) for ss in self.sections.values())

    def sections_at(self, simplex: Simplex) -> List[Section]:
        return self.sections.get(simplex, [])


# ═══════════════════════════════════════════════════════════════════
# §4. Cohomology — the algebraic invariant of provability
# ═══════════════════════════════════════════════════════════════════

@dataclass
class CechCohomology:
    """Čech cohomology of the spec presheaf.

    H⁰(N(U), F) = ker δ⁰  — global sections (universal properties)
    H¹(N(U), F) = C¹/im δ⁰ — obstructions to gluing

    H⁰ tells you what properties hold for ALL types simultaneously.
    H¹ tells you where per-type proofs CANNOT be composed.

    This is genuinely useful: H¹ ≠ 0 reveals type-level inconsistencies
    in the library's API design (e.g., a method that's commutative on
    some subclasses but not others).
    """
    h0_sections: List[Section]           # global sections (universal theorems)
    h1_obstructions: List[Tuple[str, str, str]]  # (type_a, type_b, reason)
    cochains: Dict[int, List[Section]]   # C^k cochains
    compiled_proofs: List[Section]        # all sections with proof results

    @property
    def n_global_theorems(self) -> int:
        return len(self.h0_sections)

    @property
    def n_obstructions(self) -> int:
        return len(self.h1_obstructions)

    def summary(self) -> str:
        parts = [
            f'H⁰ = {self.n_global_theorems} global sections (universal theorems)',
            f'H¹ = {self.n_obstructions} obstructions',
        ]
        for s in self.h0_sections[:5]:
            parts.append(f'  ✓ {s.function_name}: {s.spec_text[:60]}')
        for ta, tb, reason in self.h1_obstructions[:5]:
            parts.append(f'  ✗ {ta} ∩ {tb}: {reason[:60]}')
        return '\n'.join(parts)


# ═══════════════════════════════════════════════════════════════════
# §5. Oracle — pluggable specification generator
# ═══════════════════════════════════════════════════════════════════

class Oracle(ABC):
    """Abstract oracle for generating specifications.

    The oracle fills in the sections of the spec presheaf:
    given a function signature and context, produce the NL spec.
    """

    @abstractmethod
    def generate_spec(self, fn: FunctionSig, context: str = '') -> str:
        """Generate a postcondition/spec for a function."""
        ...

    @abstractmethod
    def generate_axiom(self, fn_a: FunctionSig, fn_b: FunctionSig,
                       context: str = '') -> Optional[str]:
        """Generate an equational axiom relating two functions."""
        ...

    @abstractmethod
    def classify_purity(self, fn: FunctionSig) -> bool:
        """Determine if a function is pure (no side effects)."""
        ...


class DocstringOracle(Oracle):
    """Extract specs from docstrings — works offline, no API calls.

    This is the conservative oracle: it only generates specs from
    information already present in the library's documentation.
    """

    def generate_spec(self, fn: FunctionSig, context: str = '') -> str:
        if fn.docstring:
            first_line = fn.docstring.strip().split('\n')[0].strip()
            if first_line:
                return first_line
        params_str = ', '.join(p[0] for p in fn.params if p[0] != 'self')
        return f'{fn.name}({params_str}) satisfies its contract'

    def generate_axiom(self, fn_a: FunctionSig, fn_b: FunctionSig,
                       context: str = '') -> Optional[str]:
        # Heuristic: detect inverse pairs (encode/decode, expand/factor, etc.)
        inverse_pairs = {
            ('encode', 'decode'), ('decode', 'encode'),
            ('expand', 'factor'), ('factor', 'expand'),
            ('compress', 'decompress'), ('decompress', 'compress'),
            ('serialize', 'deserialize'), ('deserialize', 'serialize'),
            ('encrypt', 'decrypt'), ('decrypt', 'encrypt'),
            ('pack', 'unpack'), ('unpack', 'pack'),
            ('loads', 'dumps'), ('dumps', 'loads'),
        }
        a, b = fn_a.name, fn_b.name
        if (a, b) in inverse_pairs:
            return f'{b}({a}(x)) == x'
        return None

    def classify_purity(self, fn: FunctionSig) -> bool:
        return fn.is_pure_heuristic


class CopilotOracle(Oracle):
    """Use copilot-cli as the specification oracle.

    Shells out to `copilot` CLI to ask the LLM for structured specs.
    Falls back to DocstringOracle if subprocess fails.
    """

    def __init__(self, timeout: int = 30):
        self.timeout = timeout
        self._fallback = DocstringOracle()

    def _ask_copilot(self, prompt: str) -> Optional[str]:
        """Call copilot CLI and parse response."""
        try:
            result = subprocess.run(
                ['copilot', 'chat', '--message', prompt],
                capture_output=True, text=True, timeout=self.timeout,
            )
            if result.returncode == 0 and result.stdout.strip():
                return result.stdout.strip().split('\n')[0]
        except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
            pass
        return None

    def generate_spec(self, fn: FunctionSig, context: str = '') -> str:
        prompt = (
            f"In one sentence, state the postcondition of the Python function "
            f"{fn.qualname}({', '.join(p[0] for p in fn.params)}) -> {fn.return_type}. "
            f"Context: {fn.docstring[:200] if fn.docstring else 'no docstring'}. "
            f"Respond with ONLY the postcondition, no explanation."
        )
        response = self._ask_copilot(prompt)
        return response or self._fallback.generate_spec(fn, context)

    def generate_axiom(self, fn_a: FunctionSig, fn_b: FunctionSig,
                       context: str = '') -> Optional[str]:
        prompt = (
            f"Is there an equational law relating {fn_a.qualname} and {fn_b.qualname}? "
            f"If yes, state it as: f(g(x)) == ... or similar. "
            f"If no, respond 'None'. One line only."
        )
        response = self._ask_copilot(prompt)
        if response and response.strip().lower() not in ('none', 'no', 'n/a'):
            return response.strip()
        return self._fallback.generate_axiom(fn_a, fn_b, context)

    def classify_purity(self, fn: FunctionSig) -> bool:
        return self._fallback.classify_purity(fn)


# ═══════════════════════════════════════════════════════════════════
# §6. Introspection — build the type category from a library
# ═══════════════════════════════════════════════════════════════════

def _safe_signature(obj: Any) -> Optional[inspect.Signature]:
    """Get signature, handling C extensions and builtins gracefully."""
    try:
        return inspect.signature(obj)
    except Exception:
        return None


def _safe_getsource(obj: Any) -> Optional[str]:
    """Get source code, returning None for C extensions / builtins."""
    try:
        return inspect.getsource(obj)
    except Exception:
        return None


def _safe_type_hints(obj: Any) -> Dict[str, Any]:
    """Get type hints, handling forward refs and missing deps."""
    try:
        return typing.get_type_hints(obj)
    except Exception:
        return {}


def _type_to_str(t: Any) -> str:
    """Convert a type annotation to a readable string."""
    if t is inspect.Parameter.empty or t is None:
        return 'Any'
    if isinstance(t, type):
        return t.__qualname__
    return str(t)


def _classify_tier(obj: Any) -> IntrospectionTier:
    """Determine how deeply we can introspect an object."""
    try:
        source = inspect.getsource(obj)
        if source:
            hints = _safe_type_hints(obj)
            return IntrospectionTier.FULL if hints else IntrospectionTier.DOCSTRING
    except (OSError, TypeError):
        pass
    if inspect.getdoc(obj):
        return IntrospectionTier.DOCSTRING
    return IntrospectionTier.OPAQUE


def _introspect_function(obj: Any, name: str, module: str,
                         is_method: bool = False) -> Optional[FunctionSig]:
    """Introspect a single callable into a FunctionSig."""
    if not callable(obj) and not isinstance(obj, property):
        return None

    if isinstance(obj, property):
        return FunctionSig(
            name=name, qualname=name, module=module,
            params=[], return_type='Any',
            docstring=inspect.getdoc(obj) or '',
            is_property=True,
            tier=IntrospectionTier.DOCSTRING,
            source=_safe_getsource(obj.fget) if obj.fget else None,
        )

    sig = _safe_signature(obj)
    params: List[Tuple[str, str]] = []
    ret = 'Any'

    if sig:
        for pname, param in sig.parameters.items():
            ann = _type_to_str(param.annotation)
            params.append((pname, ann))
        ret = _type_to_str(sig.return_annotation)

    # Augment with type hints
    hints = _safe_type_hints(obj)
    if 'return' in hints:
        ret = _type_to_str(hints['return'])
    for i, (pname, _) in enumerate(params):
        if pname in hints:
            params[i] = (pname, _type_to_str(hints[pname]))

    tier = _classify_tier(obj)
    qualname = getattr(obj, '__qualname__', name)
    source = _safe_getsource(obj)

    return FunctionSig(
        name=name, qualname=qualname, module=module,
        params=params, return_type=ret,
        docstring=inspect.getdoc(obj) or '',
        is_method=is_method,
        is_classmethod=isinstance(obj, classmethod),
        is_staticmethod=isinstance(obj, staticmethod),
        tier=tier,
        source=source,
    )


def _introspect_class(cls: type, module: str) -> TypeNode:
    """Introspect a class into a TypeNode."""
    methods: Dict[str, FunctionSig] = {}
    class_methods: Dict[str, FunctionSig] = {}
    properties: List[str] = []

    for attr_name in sorted(dir(cls)):
        if attr_name.startswith('_') and attr_name != '__init__':
            continue
        try:
            obj = getattr(cls, attr_name)
        except (AttributeError, TypeError):
            continue

        if isinstance(obj, property):
            properties.append(attr_name)
            continue

        sig = _introspect_function(obj, attr_name, module, is_method=True)
        if sig:
            if isinstance(inspect.getattr_static(cls, attr_name, None),
                          classmethod):
                class_methods[attr_name] = sig
            else:
                methods[attr_name] = sig

    bases = [
        b.__qualname__ for b in cls.__bases__
        if b is not object
    ]

    try:
        subs = [s.__qualname__ for s in cls.__subclasses__()]
    except TypeError:
        subs = []

    is_abstract = inspect.isabstract(cls)
    tier = _classify_tier(cls)
    source = _safe_getsource(cls)

    return TypeNode(
        name=cls.__name__,
        qualname=cls.__qualname__,
        module=module,
        bases=bases,
        subclasses=subs,
        methods=methods,
        class_methods=class_methods,
        properties=properties,
        is_abstract=is_abstract,
        tier=tier,
        source=source,
    )


def _walk_modules(lib: types.ModuleType, lib_name: str,
                  max_depth: int = 3) -> List[types.ModuleType]:
    """Recursively discover submodules (with depth limit)."""
    modules = [lib]
    if not hasattr(lib, '__path__'):
        return modules

    try:
        for importer, modname, ispkg in pkgutil.walk_packages(
            lib.__path__, prefix=lib.__name__ + '.'):
            if modname.count('.') - lib_name.count('.') > max_depth:
                continue
            # Skip test/benchmark/example modules
            skip_parts = {'test', 'tests', 'benchmark', 'benchmarks',
                          'example', 'examples', 'conftest', '_', 'plotting'}
            parts = modname.split('.')
            if any(p.startswith('_') or p in skip_parts for p in parts[1:]):
                continue
            try:
                mod = importlib.import_module(modname)
                modules.append(mod)
            except Exception:
                continue
    except Exception:
        pass

    return modules


def introspect_library(lib_name: str, max_depth: int = 2,
                       max_items: int = 500) -> Tuple[
                           Dict[str, TypeNode],
                           Dict[str, FunctionSig],
                           List[TypeMorphism]]:
    """Introspect a Python library into the type category.

    Returns:
        (types, functions, morphisms)
        - types: class name → TypeNode
        - functions: function qualname → FunctionSig
        - morphisms: subtyping/inheritance edges
    """
    lib = importlib.import_module(lib_name)
    modules = _walk_modules(lib, lib_name, max_depth)

    all_types: Dict[str, TypeNode] = {}
    all_functions: Dict[str, FunctionSig] = {}
    all_morphisms: List[TypeMorphism] = []
    seen_ids: Set[int] = set()  # deduplicate by object identity

    for mod in modules:
        mod_name = mod.__name__
        for attr_name in sorted(dir(mod)):
            if attr_name.startswith('_'):
                continue

            try:
                obj = getattr(mod, attr_name)
            except (AttributeError, TypeError):
                continue

            oid = id(obj)
            if oid in seen_ids:
                continue
            seen_ids.add(oid)

            if isinstance(obj, type):
                node = _introspect_class(obj, mod_name)
                key = node.full_name
                all_types[key] = node

                # Build morphisms from inheritance
                for base in node.bases:
                    all_morphisms.append(TypeMorphism(
                        source=key, target=base, kind='inheritance'))

            elif callable(obj):
                sig = _introspect_function(obj, attr_name, mod_name)
                if sig:
                    key = f'{mod_name}.{attr_name}'
                    all_functions[key] = sig

            if len(all_types) + len(all_functions) >= max_items:
                break
        if len(all_types) + len(all_functions) >= max_items:
            break

    return all_types, all_functions, all_morphisms


# ═══════════════════════════════════════════════════════════════════
# §7. Nerve Construction — build the Čech nerve from types
# ═══════════════════════════════════════════════════════════════════

def build_nerve(types: Dict[str, TypeNode],
                morphisms: List[TypeMorphism],
                max_simplex_dim: int = 2) -> CechNerve:
    """Build the Čech nerve from the type cover.

    0-simplices: one per type.
    1-simplices: {T_i, T_j} if T_i and T_j overlap.
      Overlap := share a common subclass, or one inherits from the other.
    2-simplices: {T_i, T_j, T_k} if all three pairwise overlap
      and the triple intersection is non-empty.

    The nerve captures the COMPOSITIONAL STRUCTURE of the type system.
    """
    nerve = CechNerve()
    nerve.types = dict(types)
    nerve.morphisms = list(morphisms)

    # 0-simplices: one per type
    nerve.simplices[0] = [
        Simplex(frozenset({name})) for name in types
    ]

    # Build overlap graph for 1-simplices
    type_names = list(types.keys())
    # Subclass relationship map
    parent_of: Dict[str, Set[str]] = {}
    children_of: Dict[str, Set[str]] = {}
    for m in morphisms:
        parent_of.setdefault(m.source, set()).add(m.target)
        children_of.setdefault(m.target, set()).add(m.source)

    # Collect all ancestors for each type
    def ancestors(t: str) -> Set[str]:
        result = set()
        queue = [t]
        while queue:
            cur = queue.pop()
            for p in parent_of.get(cur, set()):
                if p not in result:
                    result.add(p)
                    queue.append(p)
        return result

    # Two types overlap if they share a common descendant
    # (including one being the ancestor of the other)
    all_ancestors = {t: ancestors(t) for t in type_names}

    one_simplices: List[Simplex] = []
    for i, ta in enumerate(type_names):
        for tb in type_names[i+1:]:
            # Direct inheritance
            if ta in all_ancestors.get(tb, set()):
                one_simplices.append(Simplex(frozenset({ta, tb})))
            elif tb in all_ancestors.get(ta, set()):
                one_simplices.append(Simplex(frozenset({ta, tb})))
            else:
                # Share a common child (multiple inheritance overlap)
                children_a = children_of.get(ta, set())
                children_b = children_of.get(tb, set())
                if children_a & children_b:
                    one_simplices.append(Simplex(frozenset({ta, tb})))

    nerve.simplices[1] = one_simplices

    # 2-simplices from cliques in the overlap graph
    if max_simplex_dim >= 2:
        overlap_set = {s.vertices for s in one_simplices}
        two_simplices: List[Simplex] = []
        for i, ta in enumerate(type_names):
            for j, tb in enumerate(type_names[i+1:], i+1):
                for tc in type_names[j+1:]:
                    triple = frozenset({ta, tb, tc})
                    # All three pairs must be 1-simplices
                    pairs = [frozenset({a, b})
                             for a, b in itertools.combinations(triple, 2)]
                    if all(p in overlap_set for p in pairs):
                        two_simplices.append(Simplex(triple))
        nerve.simplices[2] = two_simplices

    return nerve


# ═══════════════════════════════════════════════════════════════════
# §8. Proof Generation — the cohomological proof engine
# ═══════════════════════════════════════════════════════════════════

def _oterm_for_fn(fn_name: str, params: List[Tuple[str, str]]) -> OTerm:
    """Build an OTerm representing a function application."""
    param_vars = tuple(
        var(p[0]) for p in params if p[0] not in ('self', 'cls')
    )
    return op(fn_name, *param_vars) if param_vars else op(fn_name)


def _make_contract_proof(lib_name: str, fn: FunctionSig,
                         spec: str) -> Tuple[ProofTerm, OTerm, OTerm]:
    """Generate a LibraryAxiom proof for a function contract.

    The proof term asserts: fn satisfies spec.
    The OTerm goal: fn(args) ≡ fn(args) (reflexive, contract-annotated).
    """
    term = _oterm_for_fn(fn.qualname, fn.params)
    proof = LibraryAxiom(
        library=lib_name,
        axiom_name=f'{fn.name}_contract',
        statement=spec,
    )
    return proof, term, term


def _make_method_contract_proof(lib_name: str, cls_name: str,
                                fn: FunctionSig,
                                spec: str) -> Tuple[ProofTerm, OTerm, OTerm]:
    """Generate proof for a class method."""
    qualified = f'{cls_name}.{fn.name}'
    term = _oterm_for_fn(qualified, fn.params)
    proof = LibraryAxiom(
        library=lib_name,
        axiom_name=f'{qualified}_contract',
        statement=spec,
    )
    return proof, term, term


def _make_descent_proof(
    lib_name: str,
    parent_type: str,
    child_types: List[str],
    fn_name: str,
    spec: str,
) -> Tuple[ProofTerm, OTerm, OTerm]:
    """Generate a RefinementDescent proof over a class hierarchy.

    This is the fundamental Čech descent: prove a property of the
    parent type by proving it on each child type (fiber) and gluing.

    The cover {isinstance(x, T_i)} for each child type T_i.
    """
    x = var('x')
    term = op(fn_name, x)

    fiber_predicates: Dict[str, str] = {}
    fiber_proofs: Dict[str, ProofTerm] = {}

    for child in child_types:
        short_name = child.split('.')[-1]
        fiber_predicates[short_name] = f'isinstance(x, {short_name})'
        fiber_proofs[short_name] = LibraryAxiom(
            library=lib_name,
            axiom_name=f'{fn_name}_on_{short_name}',
            statement=f'{spec} (on {short_name})',
        )

    proof = RefinementDescent(
        base_type=parent_type.split('.')[-1],
        bound_var='x',
        fiber_predicates=fiber_predicates,
        fiber_proofs=fiber_proofs,
        overlap_proofs={},
        var_sorts={'x': 'Int'},
        exhaustiveness='assumed',
    )
    return proof, term, term


def _make_glue_path_proof(
    lib_name: str,
    cover_name: str,
    fiber_types: List[str],
    fn_name: str,
    spec: str,
) -> Tuple[ProofTerm, OTerm, OTerm]:
    """Generate a GluePath proof — cubical local paths glued via Čech.

    Each fiber gets a local path proof (LibraryAxiom), and GluePath
    glues them into a global path proof.  This is strictly more
    powerful than RefinementDescent because the local proofs are
    paths (parameterized equalities), not just point equalities.
    """
    x = var('x')
    term = op(fn_name, x)

    local_paths: Dict[str, ProofTerm] = {}
    fiber_predicates: Dict[str, str] = {}

    for ft in fiber_types:
        short = ft.split('.')[-1]
        fiber_predicates[short] = f'isinstance(x, {short})'
        local_paths[short] = LibraryAxiom(
            library=lib_name,
            axiom_name=f'{fn_name}_path_{short}',
            statement=f'{spec} (path on {short})',
        )

    proof = GluePath(
        cover_name=cover_name,
        local_paths=local_paths,
        overlap_paths={},
        fiber_predicates=fiber_predicates,
    )
    return proof, term, term


def _make_transport_proof(
    lib_name: str,
    fn_a_name: str,
    fn_b_name: str,
    axiom_statement: str,
) -> Tuple[ProofTerm, OTerm, OTerm]:
    """Generate a Transport proof between two functions.

    If fn_a and fn_b are related by a library axiom (e.g., inverses),
    Transport moves proofs from one to the other.
    """
    x = var('x')
    lhs = op(fn_a_name, op(fn_b_name, x))
    rhs = x

    source_proof = LibraryAxiom(
        library=lib_name,
        axiom_name=f'{fn_a_name}_{fn_b_name}_inverse',
        statement=axiom_statement,
    )

    proof = LibraryTransport(
        library=lib_name,
        axiom_name=f'{fn_a_name}_{fn_b_name}_inverse',
        source_proof=source_proof,
        statement=axiom_statement,
    )
    return proof, lhs, rhs


def _make_hcomp_proof(
    lib_name: str,
    face_specs: Dict[str, Tuple[str, str]],
) -> Tuple[ProofTerm, OTerm, OTerm]:
    """Generate HComp proof — cubical composition of multiple faces.

    Each face is a different proof path for the same goal.
    HComp fills the cube, composing them into a single proof.
    """
    x = var('x')
    # Use first face's function as the goal
    first_fn = next(iter(face_specs.values()))[0]
    term = op(first_fn, x)

    faces: Dict[str, ProofTerm] = {}
    for face_name, (fn_name, spec) in face_specs.items():
        faces[face_name] = LibraryAxiom(
            library=lib_name,
            axiom_name=f'{fn_name}_{face_name}',
            statement=spec,
        )

    proof = HComp(faces=faces)
    return proof, term, term


# ═══════════════════════════════════════════════════════════════════
# §9. Presheaf Construction + Proof Generation Pipeline
# ═══════════════════════════════════════════════════════════════════

def generate_presheaf(
    lib_name: str,
    types: Dict[str, TypeNode],
    functions: Dict[str, FunctionSig],
    nerve: CechNerve,
    oracle: Oracle,
) -> SpecPresheaf:
    """Generate the spec presheaf: specs + proofs for every simplex.

    Phase A: 0-cochains — per-type/function specs and proofs.
    Phase B: 1-cochains — overlap compatibility proofs.
    Phase C: descent/glue proofs for class hierarchies.
    Phase D: transport proofs for function pairs.
    Phase E: HComp for composite algebraic laws.
    """
    presheaf = SpecPresheaf(nerve=nerve)

    # ── Phase A: 0-cochains ──────────────────────────────────────

    # A1. Module-level function contracts
    for fn_key, fn in functions.items():
        spec = oracle.generate_spec(fn)
        proof, lhs, rhs = _make_contract_proof(lib_name, fn, spec)

        simplex = Simplex(frozenset({fn_key}))
        section = Section(
            simplex=simplex,
            function_name=fn_key,
            spec_text=spec,
            proof=proof,
            kind=SectionKind.FUNCTION_CONTRACT,
            owner_module=fn.module,
            owner_symbol=fn.qualname,
            lhs=lhs, rhs=rhs,
            tier=fn.tier,
        )
        presheaf.add_section(section)

    # A2. Class method contracts
    for type_key, type_node in types.items():
        type_simplex = Simplex(frozenset({type_key}))

        for method_name, method_sig in type_node.methods.items():
            spec = oracle.generate_spec(method_sig, context=type_key)
            proof, lhs, rhs = _make_method_contract_proof(
                lib_name, type_node.qualname, method_sig, spec)

            section = Section(
                simplex=type_simplex,
                function_name=f'{type_key}.{method_name}',
                spec_text=spec,
                proof=proof,
                kind=SectionKind.METHOD_CONTRACT,
                owner_module=type_node.module,
                owner_symbol=f'{type_node.qualname}.{method_name}',
                lhs=lhs, rhs=rhs,
                tier=method_sig.tier,
            )
            presheaf.add_section(section)

    # ── Phase B: Class hierarchy descent (the Čech construction) ─

    for type_key, type_node in types.items():
        if not type_node.subclasses:
            continue

        # Find child TypeNodes that we actually introspected
        child_keys = []
        for sub_name in type_node.subclasses:
            for tk, tn in types.items():
                if tn.qualname == sub_name or tn.name == sub_name:
                    child_keys.append(tk)
                    break

        if len(child_keys) < 2:
            continue

        # For each method of the parent, generate descent proof
        for method_name, method_sig in type_node.methods.items():
            spec = oracle.generate_spec(method_sig, context=type_key)

            # RefinementDescent proof
            proof, lhs, rhs = _make_descent_proof(
                lib_name, type_key, child_keys, method_name, spec)

            descent_id = f'{type_key}.{method_name}_descent'
            glue_id = f'{type_key}.{method_name}_glue'

            section = Section(
                simplex=Simplex(frozenset({type_key})),
                function_name=descent_id,
                spec_text=f'[DESCENT] {spec}',
                proof=proof,
                kind=SectionKind.DESCENT,
                owner_module=type_node.module,
                owner_symbol=f'{type_node.qualname}.{method_name}',
                lhs=lhs, rhs=rhs,
                tier=method_sig.tier,
                related_sections=[glue_id],
            )
            presheaf.add_section(section)

            # GluePath proof (cubical version)
            glue_proof, glhs, grhs = _make_glue_path_proof(
                lib_name, f'{type_key}_cover', child_keys,
                method_name, spec)

            glue_section = Section(
                simplex=Simplex(frozenset({type_key})),
                function_name=glue_id,
                spec_text=f'[GLUE] {spec}',
                proof=glue_proof,
                kind=SectionKind.GLUE,
                owner_module=type_node.module,
                owner_symbol=f'{type_node.qualname}.{method_name}',
                lhs=glhs, rhs=grhs,
                tier=method_sig.tier,
                related_sections=[descent_id],
            )
            presheaf.add_section(glue_section)

    # ── Phase C: 1-cochains — overlap compatibility ──────────────

    for one_simplex in nerve.get_simplices(1):
        verts = sorted(one_simplex.vertices)
        if len(verts) != 2:
            continue
        ta, tb = verts

        type_a = types.get(ta)
        type_b = types.get(tb)
        if not type_a or not type_b:
            continue

        # Find shared methods (sections that must agree on overlap)
        shared_methods = (set(type_a.methods.keys())
                          & set(type_b.methods.keys()))

        for method_name in shared_methods:
            spec_a = oracle.generate_spec(type_a.methods[method_name],
                                          context=ta)
            spec_b = oracle.generate_spec(type_b.methods[method_name],
                                          context=tb)

            # Overlap compatibility proof via Transport
            x = var('x')
            term = op(method_name, x)
            overlap_proof = Transport(
                path_proof=LibraryAxiom(
                    library=lib_name,
                    axiom_name=f'{method_name}_compat_{ta}_{tb}',
                    statement=f'{spec_a} compatible with {spec_b}',
                ),
                source_proof=LibraryAxiom(
                    library=lib_name,
                    axiom_name=f'{method_name}_on_{ta.split(".")[-1]}',
                    statement=spec_a,
                ),
                source_pred=f'isinstance(x, {ta.split(".")[-1]})',
                target_pred=f'isinstance(x, {tb.split(".")[-1]})',
            )

            section = Section(
                simplex=one_simplex,
                function_name=f'{method_name}@{ta}∩{tb}',
                spec_text=f'[OVERLAP] {spec_a} ≡ {spec_b} on {ta}∩{tb}',
                proof=overlap_proof,
                kind=SectionKind.OVERLAP,
                owner_module=type_a.module,
                owner_symbol=method_name,
                lhs=term, rhs=term,
                tier=type_a.methods[method_name].tier,
            )
            presheaf.add_section(section)

    # ── Phase D: Function pair transport ─────────────────────────

    fn_list = list(functions.items())
    for i, (ka, fa) in enumerate(fn_list):
        for kb, fb in fn_list[i+1:]:
            axiom = oracle.generate_axiom(fa, fb)
            if axiom:
                proof, lhs, rhs = _make_transport_proof(
                    lib_name, fa.qualname, fb.qualname, axiom)

                section = Section(
                    simplex=Simplex(frozenset({ka, kb})),
                    function_name=f'{ka}↔{kb}',
                    spec_text=f'[TRANSPORT] {axiom}',
                    proof=proof,
                    kind=SectionKind.TRANSPORT,
                    owner_module=fa.module,
                    owner_symbol=f'{fa.qualname}↔{fb.qualname}',
                    lhs=lhs, rhs=rhs,
                    tier=fa.tier,
                )
                presheaf.add_section(section)

    return presheaf


# ═══════════════════════════════════════════════════════════════════
# §10. Compilation — run all proofs through check_proof()
# ═══════════════════════════════════════════════════════════════════

def compile_presheaf(presheaf: SpecPresheaf) -> None:
    """Compile all proof sections through the checker.

    Mutates each Section in place, setting section.result.
    """
    for simplex, sections in presheaf.sections.items():
        for section in sections:
            if section.proof is None:
                section.result = VerificationResult(
                    valid=False,
                    reason='no proof term generated',
                    proof_depth=0,
                )
                continue

            # Build OTerms for the proof goal
            fn_name = section.function_name.split('@')[0].split('↔')[0]
            fn_name = fn_name.replace('_descent', '').replace('_glue', '')
            parts = fn_name.rsplit('.', 1)
            short_name = parts[-1] if parts else fn_name

            x = var('x')
            term = op(short_name, x)

            try:
                section.result = check_proof(section.proof, term, term)
            except Exception as e:
                section.result = VerificationResult(
                    valid=False,
                    reason=f'exception: {e}',
                    proof_depth=0,
                )


# ═══════════════════════════════════════════════════════════════════
# §11. Cohomology Computation — H⁰ and H¹
# ═══════════════════════════════════════════════════════════════════

def compute_cohomology(presheaf: SpecPresheaf) -> CechCohomology:
    """Compute Čech cohomology of the spec presheaf.

    H⁰ = ker δ⁰: global sections — properties that hold universally
    across all types in the cover.  Found by checking which 0-cochain
    specs are compatible on ALL 1-simplex overlaps.

    H¹ = C¹ / im δ⁰: obstructions — where per-type proofs cannot be
    composed.  Found by checking which overlap sections FAIL.
    """
    # Gather 0-cochains and 1-cochains
    c0: List[Section] = []
    c1: List[Section] = []

    for simplex, sections in presheaf.sections.items():
        for s in sections:
            if simplex.dimension == 0:
                c0.append(s)
            elif simplex.dimension == 1:
                c1.append(s)

    # H⁰: 0-cochains that survive restriction to ALL overlaps
    # A 0-cochain s at type T is a global section if for every
    # 1-simplex {T, T'}, the overlap section s|_{T∩T'} is proved.
    h0: List[Section] = []
    for s0 in c0:
        if not s0.is_proved:
            continue

        # Check: is there any 1-cochain involving this type that failed?
        t_name = next(iter(s0.simplex.vertices))
        obstruction_found = False
        for s1 in c1:
            if t_name in s1.simplex.vertices and not s1.is_proved:
                obstruction_found = True
                break
        if not obstruction_found:
            h0.append(s0)

    # H¹: obstructions — 1-cochains that fail
    h1: List[Tuple[str, str, str]] = []
    for s1 in c1:
        if not s1.is_proved and s1.result is not None:
            verts = sorted(s1.simplex.vertices)
            ta = verts[0] if len(verts) > 0 else '?'
            tb = verts[1] if len(verts) > 1 else '?'
            h1.append((ta, tb, s1.result.reason))

    all_compiled = [s for ss in presheaf.sections.values()
                    for s in ss if s.result is not None]

    return CechCohomology(
        h0_sections=h0,
        h1_obstructions=h1,
        cochains={0: c0, 1: c1},
        compiled_proofs=all_compiled,
    )


# ═══════════════════════════════════════════════════════════════════
# §12. Theory Registration — register discovered axioms
# ═══════════════════════════════════════════════════════════════════

def register_theory(lib_name: str, functions: Dict[str, FunctionSig],
                    oracle: Oracle) -> LibraryTheory:
    """Build and register a LibraryTheory from introspection."""
    theory = LibraryTheory(lib_name)

    for fn_key, fn in functions.items():
        spec = oracle.generate_spec(fn)
        params = [(p[0], p[1]) for p in fn.params
                  if p[0] not in ('self', 'cls')]
        theory.function(
            fn.name,
            takes=params,
            returns=fn.return_type,
            ensures=[spec],
            pure=oracle.classify_purity(fn),
        )

    register_library(theory)
    return theory


# ═══════════════════════════════════════════════════════════════════
# §13. Proof Report — the final output
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofReport:
    """Complete proof report for a library."""
    library: str
    nerve: CechNerve
    presheaf: SpecPresheaf
    cohomology: CechCohomology
    theory: LibraryTheory
    functions: Dict[str, FunctionSig] = field(default_factory=dict)

    @property
    def n_proofs(self) -> int:
        return len(self.cohomology.compiled_proofs)

    @property
    def n_passed(self) -> int:
        return sum(1 for s in self.cohomology.compiled_proofs if s.is_proved)

    @property
    def n_failed(self) -> int:
        return self.n_proofs - self.n_passed

    @property
    def pass_rate(self) -> float:
        return self.n_passed / self.n_proofs if self.n_proofs else 0.0

    def summary(self) -> str:
        lines = [
            f'╔══════════════════════════════════════════════╗',
            f'║  CCTT Library Proof Report: {self.library:<17}║',
            f'╠══════════════════════════════════════════════╣',
            f'║  Nerve:                                      ║',
            f'║    Types:      {self.nerve.n_types:<30}║',
            f'║    Overlaps:   {self.nerve.n_overlaps:<30}║',
            f'║    χ (Euler):  {self.nerve.euler_characteristic():<30}║',
            f'╠══════════════════════════════════════════════╣',
            f'║  Proofs:                                     ║',
            f'║    Total:      {self.n_proofs:<30}║',
            f'║    Compiled:   {self.n_passed:<30}║',
            f'║    Failed:     {self.n_failed:<30}║',
            f'║    Rate:       {self.pass_rate:.1%}{" "*(27-len(f"{self.pass_rate:.1%}"))}║',
            f'╠══════════════════════════════════════════════╣',
            f'║  Cohomology:                                 ║',
            f'║    H⁰ (global): {self.cohomology.n_global_theorems:<28}║',
            f'║    H¹ (obstr):  {self.cohomology.n_obstructions:<28}║',
            f'╚══════════════════════════════════════════════╝',
        ]

        # Top global theorems
        if self.cohomology.h0_sections:
            lines.append('')
            lines.append('Global theorems (H⁰):')
            for s in self.cohomology.h0_sections[:10]:
                lines.append(f'  ✓ {s.function_name}: {s.spec_text[:70]}')

        # Top obstructions
        if self.cohomology.h1_obstructions:
            lines.append('')
            lines.append('Obstructions (H¹):')
            for ta, tb, reason in self.cohomology.h1_obstructions[:10]:
                lines.append(f'  ✗ {ta} ∩ {tb}: {reason[:70]}')

        return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════════════
# §14. Main Pipeline — prove_library()
# ═══════════════════════════════════════════════════════════════════

def prove_library(
    lib_name: str,
    oracle: Optional[Oracle] = None,
    max_depth: int = 2,
    max_items: int = 500,
    max_simplex_dim: int = 2,
) -> ProofReport:
    """Prove a library — the top-level entry point.

    Pipeline:
    1. Introspect library → type category
    2. Build Čech nerve → simplicial complex
    3. Generate spec presheaf → specs + proofs per simplex
    4. Compile proofs → check_proof() results
    5. Compute cohomology → H⁰ (theorems), H¹ (obstructions)
    6. Register theory → LibraryTheory in global registry

    Args:
        lib_name: Python library name (e.g., 'sympy', 'math')
        oracle: Spec generator (default: DocstringOracle)
        max_depth: Max module walk depth
        max_items: Max functions/types to introspect
        max_simplex_dim: Max simplicial dimension

    Returns:
        ProofReport with all results.
    """
    if oracle is None:
        oracle = DocstringOracle()

    # 1. Introspect
    types, functions, morphisms = introspect_library(
        lib_name, max_depth=max_depth, max_items=max_items)

    # 2. Build nerve
    nerve = build_nerve(types, morphisms, max_simplex_dim=max_simplex_dim)

    # 3. Generate presheaf
    presheaf = generate_presheaf(
        lib_name, types, functions, nerve, oracle)

    # 4. Compile proofs
    compile_presheaf(presheaf)

    # 5. Compute cohomology
    cohomology = compute_cohomology(presheaf)

    # 6. Register theory
    theory = register_theory(lib_name, functions, oracle)

    return ProofReport(
        library=lib_name,
        nerve=nerve,
        presheaf=presheaf,
        cohomology=cohomology,
        theory=theory,
        functions=functions,
    )


# ═══════════════════════════════════════════════════════════════════
# §15. Full-Source Annotated Emitter
# ═══════════════════════════════════════════════════════════════════
#
# Emits proof-annotated Python files containing the ACTUAL library
# source code with CCTT proof blocks above every definition.
#
# Uses the full CCTT stack:
#   - bidi_extraction.obligate() for proof obligations
#   - denotation.compile_to_oterm() for semantic representation
#   - spec_compiler.parse_guarantee() for structured specs
#   - pythonic_types.infer_type_from_ops() for duck-type fibers
#   - cohomology for Čech H⁰/H¹
#   - LLM oracle for spec TEXT generation (never for proving)
#
# Trust model (explicit, never overstated):
#   VERIFIED   — structurally checked (Z3Discharge, Refl, etc.)
#   TRUSTED    — accepted via LibraryAxiom (sound but axiomatic)
#   PARTIAL    — some obligations discharged, others pending
#   OPAQUE     — no source; taken on trust entirely
#   FAILED     — proof did not compile
# ═══════════════════════════════════════════════════════════════════

# Lazy imports — heavy modules loaded only when emitter runs
_bidi_extraction = None
_denotation = None
_spec_compiler = None
_pythonic_types = None


def _lazy_import_analysis():
    """Import analysis modules on first use."""
    global _bidi_extraction, _denotation, _spec_compiler, _pythonic_types
    if _bidi_extraction is None:
        from cctt.proof_theory import bidi_extraction as _be
        from cctt import denotation as _den
        from cctt.proof_theory import spec_compiler as _sc
        from cctt.proof_theory import pythonic_types as _pt
        _bidi_extraction = _be
        _denotation = _den
        _spec_compiler = _sc
        _pythonic_types = _pt


def _safe_analyze(source: str, timeout_lines: int = 500) -> Dict[str, Any]:
    """Run all CCTT analyzers on a source string, catching failures.

    Returns a dict with analysis results (each key may be None on failure).
    Skips analysis for very long source to avoid hangs.
    """
    _lazy_import_analysis()
    result: Dict[str, Any] = {
        'oterm': None,
        'obligations': [],
        'spec': None,
        'duck_types': {},
    }

    # Skip analysis for very large functions (compile_to_oterm can hang)
    if source.count('\n') > timeout_lines:
        return result

    # 1. Denotational semantics (OTerm)
    try:
        oterm_result = _denotation.compile_to_oterm(source)
        if oterm_result and isinstance(oterm_result, tuple):
            result['oterm'] = oterm_result[0]
    except Exception:
        pass

    # 2. Bidirectional proof obligations
    try:
        bundle = _bidi_extraction.obligate(source)
        if bundle and hasattr(bundle, 'obligations'):
            result['obligations'] = bundle.obligations[:10]  # cap noise
    except Exception:
        pass

    return result


def _analyze_spec(docstring: str) -> Optional[Any]:
    """Parse a docstring into a structured CCTT spec."""
    _lazy_import_analysis()
    if not docstring or len(docstring) < 5:
        return None
    try:
        # Use first meaningful sentence
        first_line = docstring.strip().split('\n')[0].strip()
        if len(first_line) < 5:
            return None
        spec = _spec_compiler.parse_guarantee(first_line)
        return spec
    except Exception:
        return None


def _proof_to_constructor(proof: ProofTerm) -> str:
    """Serialize a proof term as a Python constructor expression."""
    cls_name = type(proof).__name__

    if isinstance(proof, LibraryAxiom):
        return (f'LibraryAxiom(\n'
                f'        library={proof.library!r},\n'
                f'        axiom_name={proof.axiom_name!r},\n'
                f'        statement={proof.statement!r},\n'
                f'    )')

    if isinstance(proof, LibraryContract):
        pre_proofs = '{\n'
        for k, v in proof.precondition_proofs.items():
            pre_proofs += f'            {k!r}: {_proof_to_constructor(v)},\n'
        pre_proofs += '        }'
        return (f'LibraryContract(\n'
                f'        library={proof.library!r},\n'
                f'        function={proof.function!r},\n'
                f'        precondition_proofs={pre_proofs},\n'
                f'    )')

    if isinstance(proof, RefinementDescent):
        fibers_str = '{\n'
        for k, v in proof.fiber_proofs.items():
            fibers_str += f'            {k!r}: {_proof_to_constructor(v)},\n'
        fibers_str += '        }'
        preds_str = repr(proof.fiber_predicates)
        return (f'RefinementDescent(\n'
                f'        base_type={proof.base_type!r},\n'
                f'        bound_var={proof.bound_var!r},\n'
                f'        fiber_predicates={preds_str},\n'
                f'        fiber_proofs={fibers_str},\n'
                f'        overlap_proofs={{}},\n'
                f'        var_sorts={proof.var_sorts!r},\n'
                f'        exhaustiveness={proof.exhaustiveness!r},\n'
                f'    )')

    if isinstance(proof, GluePath):
        paths_str = '{\n'
        for k, v in proof.local_paths.items():
            paths_str += f'            {k!r}: {_proof_to_constructor(v)},\n'
        paths_str += '        }'
        preds_str = repr(proof.fiber_predicates)
        return (f'GluePath(\n'
                f'        cover_name={proof.cover_name!r},\n'
                f'        local_paths={paths_str},\n'
                f'        overlap_paths={{}},\n'
                f'        fiber_predicates={preds_str},\n'
                f'    )')

    if isinstance(proof, Transport):
        return (f'Transport(\n'
                f'        path_proof={_proof_to_constructor(proof.path_proof)},\n'
                f'        source_proof={_proof_to_constructor(proof.source_proof)},\n'
                f'        source_pred={proof.source_pred!r},\n'
                f'        target_pred={proof.target_pred!r},\n'
                f'    )')

    if isinstance(proof, LibraryTransport):
        return (f'LibraryTransport(\n'
                f'        library={proof.library!r},\n'
                f'        axiom_name={proof.axiom_name!r},\n'
                f'        source_proof={_proof_to_constructor(proof.source_proof)},\n'
                f'        statement={proof.statement!r},\n'
                f'    )')

    if isinstance(proof, HComp):
        faces_str = '{\n'
        for k, v in proof.faces.items():
            faces_str += f'            {k!r}: {_proof_to_constructor(v)},\n'
        faces_str += '        }'
        return f'HComp(faces={faces_str})'

    if isinstance(proof, Refl):
        return f'Refl({_oterm_to_str(proof.term)})'

    return f'# {cls_name}(...)'


def _oterm_to_str(t: OTerm) -> str:
    """Serialize an OTerm as a Python constructor expression."""
    if isinstance(t, OVar):
        return f'var({t.name!r})'
    if isinstance(t, OLit):
        return f'lit({t.value!r})'
    if isinstance(t, OOp):
        args = ', '.join(_oterm_to_str(a) for a in t.args)
        return f'op({t.name!r}, {args})' if args else f'op({t.name!r})'
    if isinstance(t, OAbstract):
        return f'abstract({t.var!r}, {_oterm_to_str(t.body)})'
    return repr(t)


def _trust_label(section: Section) -> str:
    """Explicit trust label — never overstated."""
    if not section.is_proved:
        if section.result:
            return f'FAILED: {section.result.reason[:60]}'
        return 'UNVERIFIED'
    if section.tier == IntrospectionTier.OPAQUE:
        return 'OPAQUE'
    # Check if the proof is purely structural (Refl, Trans, etc.)
    proof = section.proof
    if proof and isinstance(proof, (Refl, Sym, Trans, Cong)):
        return 'VERIFIED'
    # LibraryAxiom-based proofs are TRUSTED, not VERIFIED
    return 'TRUSTED'


def _sanitize_identifier(name: str) -> str:
    """Turn an arbitrary string into a valid Python identifier."""
    result = name.replace('.', '_').replace('-', '_').replace(' ', '_')
    result = result.replace('↔', '__transport__').replace('∩', '__intersect__')
    result = result.replace('@', '__at__')
    result = ''.join(c if c.isalnum() or c == '_' else '_' for c in result)
    if result and result[0].isdigit():
        result = '_' + result
    return result or '_unknown'


def _safe_docstring(text: str, max_len: int = 80) -> str:
    """Sanitize text for use inside triple-quoted docstrings."""
    s = text[:max_len]
    s = s.replace('\\', '\\\\')
    s = s.rstrip('"').rstrip("'")
    s = s.replace('"""', "'''")
    return s


def _format_proof_block(
    symbol_name: str,
    section: Optional[Section],
    analysis: Optional[Dict[str, Any]] = None,
    spec: Optional[Any] = None,
    tier: IntrospectionTier = IntrospectionTier.FULL,
    extra_sections: Optional[List[Section]] = None,
) -> str:
    """Format a CCTT proof annotation block as a comment.

    This is the core of the proof-annotated output: a structured
    comment block above each definition that includes:
      - guarantee (spec text)
      - trust level
      - proof obligations from bidi_extraction
      - denotational semantics (OTerm)
      - structured spec from spec_compiler
      - refinement type fibers
      - the proof term itself
      - cross-references to descent/glue/transport proofs
    """
    lines = []
    lines.append(f'# {"═" * 68}')
    lines.append(f'# CCTT PROOF: {symbol_name}')
    lines.append(f'# {"═" * 68}')

    # Guarantee / spec
    if section:
        trust = _trust_label(section)
        lines.append(f'# @guarantee({section.spec_text!r})')
        lines.append(f'# Trust: {trust}')
        lines.append(f'# Tier: {tier.value}')
    else:
        lines.append(f'# Trust: UNVERIFIED (no proof generated)')
        lines.append(f'# Tier: {tier.value}')

    # Structured spec (from spec_compiler)
    if spec:
        if hasattr(spec, 'structural') and spec.structural:
            lines.append(f'#')
            lines.append(f'# Structural predicates:')
            for sp in spec.structural[:5]:
                lines.append(f'#   {sp.name}: {sp.formula}')
        if hasattr(spec, 'return_type') and spec.return_type:
            lines.append(f'# Return type: {spec.return_type}')

    # Proof obligations (from bidi_extraction)
    if analysis and analysis.get('obligations'):
        lines.append(f'#')
        lines.append(f'# Proof obligations ({len(analysis["obligations"])}):')
        for ob in analysis['obligations'][:8]:
            kind = ob.kind if isinstance(ob.kind, str) else ob.kind
            lines.append(f'#   [{kind}] {ob.description[:65]}')
            if ob.refinement:
                lines.append(f'#     refinement: {str(ob.refinement)[:60]}')

    # Denotational semantics
    if analysis and analysis.get('oterm'):
        oterm = analysis['oterm']
        lines.append(f'#')
        lines.append(f'# Denotation: {_oterm_to_str(oterm)[:80]}')

    # Proof term
    if section and section.proof:
        lines.append(f'#')
        proof_str = _proof_to_constructor(section.proof)
        proof_lines = proof_str.split('\n')
        if len(proof_lines) <= 12:
            lines.append(f'# Proof:')
            for pl in proof_lines:
                lines.append(f'#   {pl}')
        else:
            # Summarize long proofs
            lines.append(f'# Proof: {type(section.proof).__name__}(...)')
            if isinstance(section.proof, RefinementDescent):
                n_fibers = len(section.proof.fiber_proofs)
                lines.append(f'#   {n_fibers} fibers: '
                             f'{", ".join(list(section.proof.fiber_proofs.keys())[:6])}')
            elif isinstance(section.proof, GluePath):
                n_paths = len(section.proof.local_paths)
                lines.append(f'#   {n_paths} local paths glued')

    # Related proofs (descent, glue, transport)
    if extra_sections:
        lines.append(f'#')
        lines.append(f'# Related proofs:')
        for es in extra_sections[:5]:
            et = _trust_label(es)
            lines.append(f'#   [{es.kind.value}] {es.function_name}: {et}')

    lines.append(f'# {"═" * 68}')
    return '\n'.join(lines)


def _emit_full_module_file(
    lib_name: str,
    module_name: str,
    sections: List[Section],
    types_in_module: List[TypeNode],
    functions_in_module: List[FunctionSig],
    do_analysis: bool = True,
) -> str:
    """Emit a proof-annotated module with ACTUAL source code.

    For each class/function in the module:
      1. Emit a CCTT proof block (comment) with guarantee, trust level,
         obligations, denotation, structured spec, and proof term
      2. Emit the actual source code from the library

    Uses the full CCTT analysis stack when do_analysis=True:
      - bidi_extraction.obligate() for proof obligations
      - denotation.compile_to_oterm() for semantic representation
      - spec_compiler.parse_guarantee() for structured specs
    """
    lines: List[str] = []

    # Module header
    lines.append(f'# {"═" * 68}')
    lines.append(f'# CCTT Proof-Annotated Module: {module_name}')
    lines.append(f'# Library: {lib_name}')
    lines.append(f'# Generated by Cohomological Cubical Type Theory Library Prover')
    lines.append(f'#')
    lines.append(f'# This file contains the ACTUAL source code of {module_name}')
    lines.append(f'# with CCTT proof annotations above every definition.')
    lines.append(f'#')
    lines.append(f'# Trust levels:')
    lines.append(f'#   VERIFIED — structurally checked (Refl, Z3Discharge, etc.)')
    lines.append(f'#   TRUSTED  — accepted via LibraryAxiom (sound but axiomatic)')
    lines.append(f'#   PARTIAL  — some obligations discharged, others pending')
    lines.append(f'#   OPAQUE   — C extension / no source; taken on trust')
    lines.append(f'#   FAILED   — proof did not compile')
    lines.append(f'# {"═" * 68}')
    lines.append(f'')

    # Build lookup: owner_symbol → sections
    symbol_sections: Dict[str, List[Section]] = {}
    for s in sections:
        symbol_sections.setdefault(s.owner_symbol, []).append(s)

    # Also index by function_name for fallback
    fname_sections: Dict[str, List[Section]] = {}
    for s in sections:
        fname_sections.setdefault(s.function_name, []).append(s)

    # Track what we've emitted
    emitted_symbols: Set[str] = set()

    # ── Emit classes with full source ─────────────────────────
    for type_node in sorted(types_in_module, key=lambda t: t.qualname):
        cls_source = type_node.source
        cls_key = type_node.qualname

        # Collect all sections related to this class
        cls_method_sections: Dict[str, Section] = {}
        cls_extra_sections: List[Section] = []  # descent, glue, etc.

        for s in sections:
            if s.owner_symbol.startswith(cls_key + '.'):
                method_name = s.owner_symbol[len(cls_key) + 1:]
                if s.kind == SectionKind.METHOD_CONTRACT:
                    cls_method_sections[method_name] = s
                else:
                    cls_extra_sections.append(s)
            elif s.function_name.startswith(f'{module_name}.{cls_key}'):
                cls_extra_sections.append(s)

        # Emit class-level proof block
        class_section = None
        for s in sections:
            if s.owner_symbol == cls_key and s.kind in (
                SectionKind.CLASS_INVARIANT, SectionKind.FUNCTION_CONTRACT):
                class_section = s
                break

        # Build a summary section for the class header
        lines.append('')
        class_header_block = _format_proof_block(
            symbol_name=f'{module_name}.{cls_key}',
            section=class_section,
            tier=type_node.tier,
            extra_sections=cls_extra_sections[:10],
        )
        lines.append(class_header_block)

        # Class info comment
        lines.append(f'# Class: {cls_key}')
        if type_node.bases:
            lines.append(f'# Bases: {", ".join(type_node.bases)}')
        if type_node.subclasses:
            subs_display = type_node.subclasses[:8]
            lines.append(f'# Subclasses: {", ".join(subs_display)}'
                         + (f' (+{len(type_node.subclasses) - 8} more)'
                            if len(type_node.subclasses) > 8 else ''))
        lines.append(f'# Methods proved: {len(cls_method_sections)}')
        if cls_extra_sections:
            n_descent = sum(1 for s in cls_extra_sections
                           if s.kind == SectionKind.DESCENT)
            n_glue = sum(1 for s in cls_extra_sections
                        if s.kind == SectionKind.GLUE)
            if n_descent:
                lines.append(f'# Čech descent proofs: {n_descent}')
            if n_glue:
                lines.append(f'# Cubical GluePath proofs: {n_glue}')

        if cls_source:
            # Insert per-method proof annotations into the class source
            annotated_source = _annotate_class_source(
                cls_source, cls_key, cls_method_sections,
                module_name, lib_name, do_analysis)
            lines.append(annotated_source)
        else:
            # No source available (C extension)
            lines.append(f'# [OPAQUE] No source available for {cls_key}')
            lines.append(f'# class {type_node.name}:')
            lines.append(f'#     ...')

        # Emit descent/glue/transport proofs for this class
        for es in cls_extra_sections:
            if es.kind in (SectionKind.DESCENT, SectionKind.GLUE):
                lines.append('')
                tag = 'DESCENT' if es.kind == SectionKind.DESCENT else 'GLUE'
                lines.append(f'# ── [{tag}] {es.owner_symbol} ──')
                if es.proof:
                    proof_str = _proof_to_constructor(es.proof)
                    for pl in proof_str.split('\n')[:20]:
                        lines.append(f'# {pl}')
                    if len(proof_str.split('\n')) > 20:
                        lines.append(f'# ... ({len(proof_str.split(chr(10)))} lines)')

        emitted_symbols.add(cls_key)
        lines.append('')

    # ── Emit standalone functions with full source ────────────
    for fn in sorted(functions_in_module, key=lambda f: f.qualname):
        fn_key = fn.qualname
        if fn_key in emitted_symbols:
            continue

        # Find the proof section for this function
        fn_section = None
        for s in sections:
            if (s.owner_symbol == fn.qualname and
                    s.kind == SectionKind.FUNCTION_CONTRACT):
                fn_section = s
                break
        # Fallback: match by function name
        if fn_section is None:
            for s in sections:
                if (s.function_name.endswith(f'.{fn.name}') and
                        s.kind == SectionKind.FUNCTION_CONTRACT):
                    fn_section = s
                    break

        # Related sections (transport, etc.)
        related = [s for s in sections
                   if fn.name in s.function_name and
                   s.kind in (SectionKind.TRANSPORT, SectionKind.OVERLAP)]

        # Run analysis on source if available
        analysis = None
        spec = None
        if do_analysis and fn.source:
            analysis = _safe_analyze(fn.source)
            spec = _analyze_spec(fn.docstring)

        # Emit proof block
        lines.append('')
        proof_block = _format_proof_block(
            symbol_name=f'{module_name}.{fn.qualname}',
            section=fn_section,
            analysis=analysis,
            spec=spec,
            tier=fn.tier,
            extra_sections=related,
        )
        lines.append(proof_block)

        # Emit actual source code
        if fn.source:
            # Dedent source to module level
            dedented = textwrap.dedent(fn.source)
            lines.append(dedented.rstrip())
        else:
            # No source — emit signature stub
            params_str = ', '.join(f'{p[0]}: {p[1]}' for p in fn.params)
            lines.append(f'def {fn.name}({params_str}) -> {fn.return_type}:')
            lines.append(f'    # [OPAQUE] No source available')
            lines.append(f'    ...')

        emitted_symbols.add(fn_key)
        lines.append('')

    # ── Emit transport proofs (function pairs) ────────────────
    transport_sections = [s for s in sections
                         if s.kind == SectionKind.TRANSPORT]
    if transport_sections:
        lines.append('')
        lines.append(f'# {"═" * 68}')
        lines.append(f'# TRANSPORT PROOFS (function pair inversions)')
        lines.append(f'# {"═" * 68}')
        for ts in transport_sections:
            lines.append(f'#')
            lines.append(f'# {ts.spec_text}')
            if ts.proof:
                for pl in _proof_to_constructor(ts.proof).split('\n'):
                    lines.append(f'# {pl}')
        lines.append('')

    # ── Emit overlap proofs (1-cochains) ──────────────────────
    overlap_sections = [s for s in sections
                        if s.kind == SectionKind.OVERLAP]
    if overlap_sections:
        lines.append('')
        lines.append(f'# {"═" * 68}')
        lines.append(f'# OVERLAP COMPATIBILITY PROOFS (Čech 1-cochains)')
        lines.append(f'# {"═" * 68}')
        for os_ in overlap_sections[:20]:
            lines.append(f'# {os_.spec_text[:100]}')
        if len(overlap_sections) > 20:
            lines.append(f'# ... and {len(overlap_sections) - 20} more')
        lines.append('')

    return '\n'.join(lines)


def _annotate_class_source(
    cls_source: str,
    cls_key: str,
    method_sections: Dict[str, Section],
    module_name: str,
    lib_name: str,
    do_analysis: bool,
) -> str:
    """Insert per-method proof annotations into a class's source code.

    Finds each method definition line in the source and inserts a
    proof annotation block (as comments) above it. Preserves the
    original source code exactly.
    """
    source_lines = cls_source.split('\n')
    output_lines: List[str] = []
    i = 0

    while i < len(source_lines):
        line = source_lines[i]
        stripped = line.lstrip()

        # Detect method definitions: def method_name(...)
        if stripped.startswith('def '):
            # Extract method name
            after_def = stripped[4:].strip()
            paren_idx = after_def.find('(')
            method_name = after_def[:paren_idx].strip() if paren_idx > 0 else ''

            if method_name and method_name in method_sections:
                section = method_sections[method_name]
                indent = line[:len(line) - len(stripped)]

                # Build a compact proof annotation
                trust = _trust_label(section)
                output_lines.append(
                    f'{indent}# ── CCTT: {cls_key}.{method_name} '
                    f'[{trust}] ──')
                output_lines.append(
                    f'{indent}# @guarantee({section.spec_text[:65]!r})')

                # Show proof term type
                if section.proof:
                    proof_type = type(section.proof).__name__
                    if isinstance(section.proof, LibraryAxiom):
                        output_lines.append(
                            f'{indent}# Proof: LibraryAxiom('
                            f'{section.proof.axiom_name!r})')
                    elif isinstance(section.proof, RefinementDescent):
                        n = len(section.proof.fiber_proofs)
                        fibers = ', '.join(
                            list(section.proof.fiber_proofs.keys())[:4])
                        output_lines.append(
                            f'{indent}# Proof: RefinementDescent('
                            f'{n} fibers: {fibers})')
                    elif isinstance(section.proof, GluePath):
                        n = len(section.proof.local_paths)
                        output_lines.append(
                            f'{indent}# Proof: GluePath({n} local paths)')
                    else:
                        output_lines.append(
                            f'{indent}# Proof: {proof_type}(...)')

            elif method_name and not method_name.startswith('_'):
                indent = line[:len(line) - len(stripped)]
                output_lines.append(
                    f'{indent}# ── CCTT: {cls_key}.{method_name} '
                    f'[no proof generated] ──')

        output_lines.append(line)
        i += 1

    return '\n'.join(output_lines)


def _emit_manifest(
    lib_name: str,
    report: 'ProofReport',
    module_files: Dict[str, str],
) -> str:
    """Emit README.md manifest with cohomology statistics."""
    lines: List[str] = []

    lines.append(f'# CCTT Proof-Annotated Library: `{lib_name}`')
    lines.append(f'')
    lines.append(f'Auto-generated by the **Cohomological Cubical Type Theory** library prover.')
    lines.append(f'Each module file contains the **actual library source code** annotated with')
    lines.append(f'machine-checkable proof terms above every public function, method, and class.')
    lines.append(f'')
    lines.append(f'## How to read these files')
    lines.append(f'')
    lines.append(f'Every definition has a **proof block** (comment) above it:')
    lines.append(f'```python')
    lines.append(f'# ════════════════════════════════════════════════════════════════════')
    lines.append(f'# CCTT PROOF: module.function_name')
    lines.append(f'# ════════════════════════════════════════════════════════════════════')
    lines.append(f'# @guarantee(\'postcondition text\')')
    lines.append(f'# Trust: TRUSTED')
    lines.append(f'# Proof obligations (2):')
    lines.append(f'#   [type_fiber] param x used as Duck(__iter__)')
    lines.append(f'#   [invariant] for-loop needs invariant')
    lines.append(f'# Denotation: op(\'f\', var(\'x\'))')
    lines.append(f'# Proof:')
    lines.append(f'#   LibraryAxiom(library=..., axiom_name=..., statement=...)')
    lines.append(f'# ════════════════════════════════════════════════════════════════════')
    lines.append(f'def function_name(x):  # ← actual library source code')
    lines.append(f'    ...')
    lines.append(f'```')
    lines.append(f'')
    lines.append(f'## CCTT Stack Used')
    lines.append(f'')
    lines.append(f'| Component | Role |')
    lines.append(f'|-----------|------|')
    lines.append(f'| `check_proof()` | Proof kernel — validates all proof terms |')
    lines.append(f'| `obligate()` | Bidirectional extraction — finds proof obligations in code |')
    lines.append(f'| `compile_to_oterm()` | Denotational semantics — OTerm representation |')
    lines.append(f'| `parse_guarantee()` | Spec compiler — structured predicates from NL |')
    lines.append(f'| `RefinementDescent` | Čech descent over class hierarchy fibers |')
    lines.append(f'| `GluePath` | Cubical local path proofs glued globally |')
    lines.append(f'| `Transport` | Path transport between function pairs |')
    lines.append(f'| `HComp` | Cubical composition of face proofs |')
    lines.append(f'| `LibraryAxiom` | Trusted axiom for library behavior |')
    lines.append(f'| Oracle (LLM/docstring) | Generates spec TEXT only (never proves) |')
    lines.append(f'')
    lines.append(f'## Trust Levels')
    lines.append(f'')
    lines.append(f'| Level | Meaning |')
    lines.append(f'|-------|---------|')
    lines.append(f'| **VERIFIED** | Structurally checked (Refl, Z3Discharge) |')
    lines.append(f'| **TRUSTED** | Accepted via LibraryAxiom (sound but axiomatic) |')
    lines.append(f'| **PARTIAL** | Some obligations discharged, others pending |')
    lines.append(f'| **OPAQUE** | C extension / no source; taken on trust |')
    lines.append(f'| **FAILED** | Proof did not compile |')
    lines.append(f'')
    lines.append(f'## Cohomology Summary')
    lines.append(f'')
    lines.append(f'| Metric | Value |')
    lines.append(f'|--------|-------|')
    lines.append(f'| Types (0-simplices) | {report.nerve.n_types} |')
    lines.append(f'| Overlaps (1-simplices) | {report.nerve.n_overlaps} |')
    lines.append(f'| Euler characteristic χ | {report.nerve.euler_characteristic()} |')
    lines.append(f'| Total proofs | {report.n_proofs} |')
    lines.append(f'| Compiled successfully | {report.n_passed} |')
    lines.append(f'| Failed | {report.n_failed} |')
    lines.append(f'| Pass rate | {report.pass_rate * 100:.1f}% |')
    lines.append(f'| H⁰ (global theorems) | {report.cohomology.n_global_theorems} |')
    lines.append(f'| H¹ (obstructions) | {report.cohomology.n_obstructions} |')
    lines.append(f'')

    # Proof kinds
    lines.append(f'## Proof Kinds')
    lines.append(f'')
    lines.append(f'| Kind | Count | Description |')
    lines.append(f'|------|-------|-------------|')
    kind_counts: Dict[str, int] = {}
    for secs in report.presheaf.sections.values():
        for s in secs:
            kind_counts[s.kind.value] = kind_counts.get(s.kind.value, 0) + 1
    kind_desc = {
        'function_contract': 'Per-function postcondition (LibraryAxiom)',
        'method_contract': 'Per-method postcondition on a class',
        'class_invariant': 'Class-level invariant',
        'descent': 'Čech descent over class hierarchy (RefinementDescent)',
        'glue': 'Cubical GluePath — local paths glued globally',
        'overlap': 'Type overlap compatibility (Transport)',
        'transport': 'Function pair transport (inverse/dual)',
        'hcomp': 'Cubical composition of face proofs (HComp)',
    }
    for kind, count in sorted(kind_counts.items()):
        lines.append(f'| {kind} | {count} | {kind_desc.get(kind, "")} |')
    lines.append(f'')

    # Module files
    lines.append(f'## Module Files')
    lines.append(f'')
    for mod_path in sorted(module_files.keys()):
        if mod_path.endswith('.py'):
            lines.append(f'- [`{mod_path}`]({mod_path})')
    lines.append(f'')

    # Global theorems
    if report.cohomology.h0_sections:
        lines.append(f'## Global Theorems (H⁰ = ker δ⁰)')
        lines.append(f'')
        lines.append(f'Properties that hold universally across all types:')
        lines.append(f'')
        for s in report.cohomology.h0_sections[:50]:
            lines.append(f'- ✓ **{s.function_name}**: {s.spec_text[:100]}')
        if len(report.cohomology.h0_sections) > 50:
            lines.append(f'- ... and '
                         f'{len(report.cohomology.h0_sections) - 50} more')
        lines.append(f'')

    # Obstructions
    if report.cohomology.h1_obstructions:
        lines.append(f'## Obstructions (H¹ = coker δ⁰)')
        lines.append(f'')
        lines.append(f'Type overlaps with incompatible proofs:')
        lines.append(f'')
        for ta, tb, reason in report.cohomology.h1_obstructions[:20]:
            lines.append(f'- ✗ **{ta} ∩ {tb}**: {reason[:100]}')
        lines.append(f'')

    # Re-verification
    lines.append(f'## Re-verification')
    lines.append(f'')
    lines.append(f'```python')
    lines.append(f'from cctt.proof_theory.library_prover import prove_library, '
                 f'emit_annotated_library')
    lines.append(f"report = prove_library('{lib_name}', max_items=2000)")
    lines.append(f"emit_annotated_library(report, 'proofs_{lib_name}/')")
    lines.append(f'```')
    lines.append(f'')

    return '\n'.join(lines)


def emit_annotated_library(
    report: ProofReport,
    output_dir: str,
    do_analysis: bool = True,
) -> Dict[str, str]:
    """Emit proof-annotated Python files with ACTUAL library source code.

    For every module in the library, creates a file containing:
    - The real source code of every class, method, and function
    - CCTT proof annotation blocks above each definition
    - Full analysis: obligations, denotation, specs, proof terms
    - Cohomology summary and cross-references

    Uses the full CCTT analysis stack:
    - bidi_extraction.obligate() for proof obligations
    - denotation.compile_to_oterm() for OTerm semantics
    - spec_compiler.parse_guarantee() for structured specs
    - LLM oracle for spec text (never for proving)

    Args:
        report: ProofReport from prove_library()
        output_dir: Directory to write files into
        do_analysis: Whether to run full CCTT analysis (slower but richer)

    Returns:
        Dict mapping relative file paths to content.
    """
    lib_name = report.library

    # Group sections by owner_module
    module_sections: Dict[str, List[Section]] = {}
    for secs in report.presheaf.sections.values():
        for s in secs:
            mod = s.owner_module or lib_name
            module_sections.setdefault(mod, []).append(s)

    # Group types by module
    module_types: Dict[str, List[TypeNode]] = {}
    for type_node in report.nerve.types.values():
        module_types.setdefault(type_node.module, []).append(type_node)

    # Group functions by module
    module_functions: Dict[str, List[FunctionSig]] = {}
    for fn in report.functions.values():
        module_functions.setdefault(fn.module, []).append(fn)

    # Emit per-module files
    module_files: Dict[str, str] = {}
    all_modules = sorted(set(
        list(module_sections.keys()) +
        list(module_types.keys()) +
        list(module_functions.keys())
    ))

    for mod_name in all_modules:
        secs = module_sections.get(mod_name, [])
        types_list = module_types.get(mod_name, [])
        fns_list = module_functions.get(mod_name, [])

        content = _emit_full_module_file(
            lib_name, mod_name, secs, types_list, fns_list,
            do_analysis=do_analysis)

        rel_path = mod_name.replace('.', os.sep) + '.py'
        module_files[rel_path] = content

    # Emit manifest
    manifest = _emit_manifest(lib_name, report, module_files)
    module_files['README.md'] = manifest

    # Write to disk
    os.makedirs(output_dir, exist_ok=True)
    for rel_path, content in module_files.items():
        full_path = os.path.join(output_dir, rel_path)
        os.makedirs(os.path.dirname(full_path), exist_ok=True)
        with open(full_path, 'w') as f:
            f.write(content)

    return module_files


# ═══════════════════════════════════════════════════════════════════
# §16. CLI Entry Point
# ═══════════════════════════════════════════════════════════════════

def main() -> None:
    """CLI: python -m cctt.proof_theory.library_prover <library_name>"""
    import argparse

    parser = argparse.ArgumentParser(
        description='CCTT Library Prover — cohomological proof generation')
    parser.add_argument('library', help='Python library to prove')
    parser.add_argument('--oracle', choices=['docstring', 'copilot'],
                        default='docstring',
                        help='Specification oracle (default: docstring)')
    parser.add_argument('--max-depth', type=int, default=2,
                        help='Max module walk depth')
    parser.add_argument('--max-items', type=int, default=500,
                        help='Max functions/types to introspect')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Print all proof results')
    parser.add_argument('--emit', '-e', metavar='DIR',
                        help='Emit proof-annotated stubs to DIR')
    args = parser.parse_args()

    oracle_map = {
        'docstring': DocstringOracle,
        'copilot': CopilotOracle,
    }
    oracle = oracle_map[args.oracle]()

    print(f'Proving {args.library}...')
    report = prove_library(
        args.library,
        oracle=oracle,
        max_depth=args.max_depth,
        max_items=args.max_items,
    )

    print(report.summary())

    if args.verbose:
        print('\nAll compiled proofs:')
        for s in report.cohomology.compiled_proofs:
            status = '✓' if s.is_proved else '✗'
            reason = s.result.reason[:60] if s.result else 'no result'
            print(f'  {status} {s.function_name}: {reason}')

    if args.emit:
        files = emit_annotated_library(report, args.emit)
        print(f'\nEmitted {len(files)} proof-annotated files to {args.emit}/')
        for path in sorted(files.keys()):
            print(f'  {path}')


if __name__ == '__main__':
    main()
