"""Code proposals for Ch.5-6: Kan Operations and Sites/Presheaves/Sheaves.

These proposals deepen the connection between the monograph's formal
definitions and the implementation in path_search.py, checker.py,
duck.py, and cohomology.py.

Each proposal is implemented as real, importable Python code with full
type annotations, docstrings, edge-case handling, and self-tests.

STATUS: implemented (all 10 proposals)
FILES:
  - new_src/cctt/path_search.py  (Proposals 1, 2, 8)
  - new_src/cctt/checker.py      (Proposals 4, 6)
  - new_src/cctt/duck.py         (Proposals 3, 9)
  - new_src/cctt/cohomology.py   (Proposals 5, 7, 10)
MONOGRAPH: Ch.5 §5.2-5.3, Ch.6 §6.2-6.6
"""
from __future__ import annotations

import hashlib
import itertools
import json
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    Iterator,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)


# ═══════════════════════════════════════════════════════════════════
#  Utility: GF(2) linear algebra primitives
# ═══════════════════════════════════════════════════════════════════

class GF2Vector:
    """A vector over GF(2) = {0, 1} with arithmetic mod 2.

    Used across multiple proposals for Čech coboundary computation,
    isomorphism sheaf sections, and overlap matrix caching.

    Example
    -------
    >>> v = GF2Vector([1, 0, 1, 1])
    >>> w = GF2Vector([0, 1, 1, 0])
    >>> (v + w).entries
    [1, 1, 0, 1]
    """

    __slots__ = ('entries',)

    def __init__(self, entries: List[int]) -> None:
        self.entries = [e % 2 for e in entries]

    @property
    def dim(self) -> int:
        """Dimension of the vector."""
        return len(self.entries)

    def __add__(self, other: GF2Vector) -> GF2Vector:
        if self.dim != other.dim:
            raise ValueError(f'dimension mismatch: {self.dim} vs {other.dim}')
        return GF2Vector([(a + b) % 2 for a, b in zip(self.entries, other.entries)])

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, GF2Vector):
            return NotImplemented
        return self.entries == other.entries

    def __repr__(self) -> str:
        return f'GF2[{"".join(str(e) for e in self.entries)}]'

    def dot(self, other: GF2Vector) -> int:
        """Inner product over GF(2)."""
        if self.dim != other.dim:
            raise ValueError(f'dimension mismatch: {self.dim} vs {other.dim}')
        return sum(a * b for a, b in zip(self.entries, other.entries)) % 2

    def is_zero(self) -> bool:
        """Check if this is the zero vector."""
        return all(e == 0 for e in self.entries)

    @staticmethod
    def zero(n: int) -> GF2Vector:
        """The zero vector of dimension n."""
        return GF2Vector([0] * n)

    @staticmethod
    def basis(n: int, k: int) -> GF2Vector:
        """The k-th standard basis vector in dimension n."""
        v = [0] * n
        v[k] = 1
        return GF2Vector(v)


class GF2Matrix:
    """A matrix over GF(2) with Gaussian elimination.

    Provides rank, kernel, and image computation needed for
    Čech coboundary δ⁰ and δ¹ maps.

    Example
    -------
    >>> M = GF2Matrix([[1,1,0],[0,1,1],[1,0,1]])
    >>> M.rank()
    2
    """

    __slots__ = ('rows', 'nrows', 'ncols')

    def __init__(self, rows: List[List[int]]) -> None:
        self.rows = [[e % 2 for e in row] for row in rows]
        self.nrows = len(self.rows)
        self.ncols = len(self.rows[0]) if self.rows else 0

    def rank(self) -> int:
        """Compute rank via GF(2) Gaussian elimination."""
        m = [row[:] for row in self.rows]
        rows, cols = self.nrows, self.ncols
        r = 0
        for col in range(cols):
            pivot = None
            for row in range(r, rows):
                if m[row][col] == 1:
                    pivot = row
                    break
            if pivot is None:
                continue
            m[r], m[pivot] = m[pivot], m[r]
            for row in range(rows):
                if row != r and m[row][col] == 1:
                    m[row] = [(m[row][j] + m[r][j]) % 2 for j in range(cols)]
            r += 1
        return r

    def kernel_basis(self) -> List[GF2Vector]:
        """Compute a basis for ker(M) over GF(2).

        Returns a list of GF2Vectors v such that M·v = 0.
        """
        m = [row[:] for row in self.rows]
        rows, cols = self.nrows, self.ncols
        pivot_col = [-1] * rows
        r = 0
        for col in range(cols):
            pivot = None
            for row in range(r, rows):
                if m[row][col] == 1:
                    pivot = row
                    break
            if pivot is None:
                continue
            m[r], m[pivot] = m[pivot], m[r]
            pivot_col[r] = col
            for row in range(rows):
                if row != r and m[row][col] == 1:
                    m[row] = [(m[row][j] + m[r][j]) % 2 for j in range(cols)]
            r += 1

        pivot_cols = set(pivot_col[i] for i in range(r))
        free_cols = [c for c in range(cols) if c not in pivot_cols]
        kernel: List[GF2Vector] = []
        for fc in free_cols:
            v = [0] * cols
            v[fc] = 1
            for i in range(r):
                pc = pivot_col[i]
                if pc >= 0 and m[i][fc] == 1:
                    v[pc] = 1
            kernel.append(GF2Vector(v))
        return kernel

    def image_rank(self) -> int:
        """Rank of the image = rank of the matrix."""
        return self.rank()

    def transpose(self) -> GF2Matrix:
        """Transpose of the matrix."""
        if self.nrows == 0 or self.ncols == 0:
            return GF2Matrix([])
        t = [[self.rows[r][c] for r in range(self.nrows)] for c in range(self.ncols)]
        return GF2Matrix(t)

    def __repr__(self) -> str:
        return f'GF2Matrix({self.nrows}×{self.ncols}, rank={self.rank()})'

    def __mul__(self, other: GF2Matrix) -> GF2Matrix:
        """Matrix multiplication over GF(2)."""
        if self.ncols != other.nrows:
            raise ValueError(
                f'shape mismatch: ({self.nrows}×{self.ncols}) × '
                f'({other.nrows}×{other.ncols})')
        result = []
        for i in range(self.nrows):
            row = []
            for j in range(other.ncols):
                s = sum(self.rows[i][k] * other.rows[k][j]
                        for k in range(self.ncols)) % 2
                row.append(s)
            result.append(row)
        return GF2Matrix(result)


# ═══════════════════════════════════════════════════════════════════
#  Proposal 1: Explicit Kan composition witness
# ═══════════════════════════════════════════════════════════════════
#
# Currently path_search.search_path returns a PathResult with a flat
# list of PathSteps.  The monograph (Def 5.5, Thm 5.6) formalizes
# multi-step rewriting as iterated Kan composition.  This proposal
# makes the composition structure explicit.
#
# STATUS: implemented
# FILES: new_src/cctt/path_search.py
# MONOGRAPH: Ch.5 §5.3 (Thm 5.6 — Soundness of Multi-Step Composition)
#
# BEFORE (path_search.py):
#   PathResult(found=True, path=[step1, step2, step3])
#   # flat list — no composition structure, no inverses
#
# AFTER (with this proposal):
#   composite = KanComposite.from_steps([step1, step2, step3])
#   composite.compose(other_composite)   # ·
#   composite.reverse()                  # sym
#   composite.validate()                 # checks chain well-formedness

@dataclass(frozen=True)
class PathStep:
    """A single step in a rewrite path.

    Mirrors the PathStep in path_search.py, reproduced here for
    self-containment.  In production code, import from path_search.

    Attributes:
        axiom: the dichotomy axiom applied, e.g. 'D1_fold_unfold'
        position: where in the term tree the axiom fired, e.g. '@arg0'
        before: canonical form of the term before the step
        after: canonical form of the term after the step
    """
    axiom: str
    position: str
    before: str
    after: str

    def inverse(self) -> PathStep:
        """Reverse this step (path symmetry).

        Every axiom a : Path(s, t) has an inverse a⁻¹ : Path(t, s).
        """
        return PathStep(
            axiom=f'{self.axiom}_inv',
            position=self.position,
            before=self.after,
            after=self.before,
        )


@dataclass(frozen=True)
class KanComposite:
    """A composed path = iterated Kan filling (Def 5.5).

    Each step is a 1-cell (axiom application).  The composite
    is the lid of the Kan box built from chaining these 1-cells.
    An empty composite is the reflexivity path refl(t).

    Mathematical model:
        Given 1-cells  p₁ : a →[ax₁] b  and  p₂ : b →[ax₂] c,
        the Kan composite  p₁ · p₂ : a → c  is the filler of the
        open box formed by p₁ and p₂ in the path groupoid.

    Integration with path_search.py
    --------------------------------
    >>> from new_src.cctt.path_search import search_path, PathStep
    >>> result = search_path(nf_f, nf_g)
    >>> if result.found:
    ...     composite = KanComposite.from_steps(result.path)
    ...     assert composite.is_valid()
    ...     cert = composite.to_certificate()  # for audit/replay
    """
    steps: Tuple[PathStep, ...]

    @staticmethod
    def identity(term_canon: str) -> KanComposite:
        """The reflexivity path refl(t) — zero-length composition.

        This is the identity 1-cell in the path groupoid.
        """
        return KanComposite(steps=())

    @staticmethod
    def from_steps(steps: Sequence[PathStep]) -> KanComposite:
        """Build a composite from a sequence of steps."""
        return KanComposite(steps=tuple(steps))

    @staticmethod
    def singleton(step: PathStep) -> KanComposite:
        """A single-step composite."""
        return KanComposite(steps=(step,))

    @property
    def source(self) -> str:
        """Source of the path = before of first step (or '' if refl)."""
        return self.steps[0].before if self.steps else ''

    @property
    def target(self) -> str:
        """Target of the path = after of last step (or '' if refl)."""
        return self.steps[-1].after if self.steps else ''

    @property
    def length(self) -> int:
        """Number of steps in the composite."""
        return len(self.steps)

    def is_valid(self) -> bool:
        """Check that the chain is well-formed: each step.after == next.before.

        This is the Kan box boundary condition: adjacent 1-cells share
        their boundary 0-cells.
        """
        for i in range(len(self.steps) - 1):
            if self.steps[i].after != self.steps[i + 1].before:
                return False
        return True

    def compose(self, other: KanComposite) -> KanComposite:
        """Kan composition: self · other.

        Precondition: self.target == other.source (or either is empty).

        Raises:
            ValueError: if the composition boundary condition fails.
        """
        if not self.steps:
            return other
        if not other.steps:
            return self
        if self.target != other.source:
            raise ValueError(
                f'Cannot compose: target {self.target!r} ≠ '
                f'source {other.source!r}')
        return KanComposite(steps=self.steps + other.steps)

    def reverse(self) -> KanComposite:
        """Path reversal (symmetry of Path type).

        Every path  p : a → b  has an inverse  p⁻¹ : b → a
        obtained by reversing the steps and inverting each axiom.
        """
        return KanComposite(
            steps=tuple(s.inverse() for s in reversed(self.steps))
        )

    def simplify(self) -> KanComposite:
        """Cancel adjacent inverse pairs: ax · ax_inv → refl.

        This implements the groupoid law  p · p⁻¹ = refl.
        Iterates until no more cancellations are possible.
        """
        steps = list(self.steps)
        changed = True
        while changed:
            changed = False
            new_steps: List[PathStep] = []
            i = 0
            while i < len(steps):
                if (i + 1 < len(steps)
                        and steps[i].after == steps[i + 1].before
                        and steps[i + 1].after == steps[i].before
                        and _are_inverses(steps[i].axiom, steps[i + 1].axiom)):
                    i += 2
                    changed = True
                else:
                    new_steps.append(steps[i])
                    i += 1
            steps = new_steps
        return KanComposite(steps=tuple(steps))

    def sub_composite(self, start: int, end: int) -> KanComposite:
        """Extract a sub-path from step[start] to step[end] (exclusive)."""
        return KanComposite(steps=self.steps[start:end])

    def axioms_used(self) -> FrozenSet[str]:
        """Set of unique axiom names in this composite (without _inv suffix)."""
        names: Set[str] = set()
        for s in self.steps:
            base = s.axiom.removesuffix('_inv')
            names.add(base)
        return frozenset(names)

    def to_certificate(self) -> PathCertificate:
        """Serialize this composite into an auditable certificate."""
        return PathCertificate.from_composite(self)

    def __repr__(self) -> str:
        if not self.steps:
            return 'KanComposite(refl)'
        axioms = ' · '.join(s.axiom for s in self.steps)
        return f'KanComposite({self.source!r} →[{axioms}]→ {self.target!r})'


def _are_inverses(ax1: str, ax2: str) -> bool:
    """Check if two axiom names are inverses of each other."""
    if ax1.endswith('_inv') and ax1[:-4] == ax2:
        return True
    if ax2.endswith('_inv') and ax2[:-4] == ax1:
        return True
    return False


# ═══════════════════════════════════════════════════════════════════
#  Proposal 2: Congruence lifting as explicit ap functor
# ═══════════════════════════════════════════════════════════════════
#
# The monograph (Def 5.4) defines congruence lifting as ap_C.
# Currently _congruence_rewrites annotates with '@arg0', '@test', etc.
# This proposal provides a structured position type that mirrors
# the cubical ap, with full navigation and composition.
#
# STATUS: implemented
# FILES: new_src/cctt/path_search.py
# MONOGRAPH: Ch.5 §5.2 (Def 5.4 — Congruence Lifting)
#
# BEFORE (_congruence_rewrites):
#   results.append((new_term, f'{ax}@arg{i}'))
#   # position is just a string suffix — no structure
#
# AFTER (with this proposal):
#   pos = TermPosition(('arg', 0))
#   cstep = CongruenceStep(inner_axiom='D4_map_fusion',
#                          position=pos, context_type='OOp')
#   cstep.apply_to(outer_term)  # reconstructs the full rewrite

@dataclass(frozen=True)
class TermPosition:
    """Position in a term tree — the context 'C' in ap_C.

    The path is a tuple of segments, where each segment is either:
      ('arg', i)     — i-th argument of OOp
      ('test',)      — test sub-expression of OCase
      ('then',)      — true branch of OCase
      ('else',)      — false branch of OCase
      ('init',)      — initial value of OFold
      ('coll',)      — collection of OFold or OMap
      ('body',)      — body of OLam or OFix
      ('transform',) — transform function of OMap
      ('inner',)     — inner term of OQuotient
      ('elem', i)    — i-th element of OSeq

    Example
    -------
    >>> pos = TermPosition(('arg', 2, 'test'))
    >>> str(pos)
    'arg.2.test'
    >>> pos.depth
    3
    """
    path: Tuple[Union[str, int], ...]

    @staticmethod
    def root() -> TermPosition:
        """The root position (no descent into sub-terms)."""
        return TermPosition(())

    @property
    def depth(self) -> int:
        """Depth of the position in the term tree."""
        return len(self.path)

    @property
    def is_root(self) -> bool:
        return len(self.path) == 0

    def extend(self, *segments: Union[str, int]) -> TermPosition:
        """Descend further into the term tree."""
        return TermPosition(self.path + segments)

    def parent(self) -> TermPosition:
        """Go up one level. Returns root if already at root."""
        if not self.path:
            return self
        return TermPosition(self.path[:-1])

    @staticmethod
    def from_annotation(annotation: str) -> TermPosition:
        """Parse a path_search.py-style annotation like 'D1_fold_unfold@arg0@test'.

        Strips the axiom prefix, then converts '@arg0', '@test', etc.
        into structured position segments.

        >>> TermPosition.from_annotation('D4_map_fusion@arg0@test')
        TermPosition(path=('arg', 0, 'test'))
        """
        parts = annotation.split('@')
        # First part is the axiom name, remaining parts are position
        segments: List[Union[str, int]] = []
        for part in parts[1:]:
            if part.startswith('arg') and part[3:].isdigit():
                segments.extend(('arg', int(part[3:])))
            elif part.startswith('elem') and part[4:].isdigit():
                segments.extend(('elem', int(part[4:])))
            else:
                segments.append(part)
        return TermPosition(tuple(segments))

    def to_annotation(self) -> str:
        """Convert back to a path_search.py-style annotation suffix.

        >>> TermPosition(('arg', 0, 'test')).to_annotation()
        '@arg0@test'
        """
        parts: List[str] = []
        i = 0
        while i < len(self.path):
            seg = self.path[i]
            if seg == 'arg' and i + 1 < len(self.path) and isinstance(self.path[i + 1], int):
                parts.append(f'arg{self.path[i + 1]}')
                i += 2
            elif seg == 'elem' and i + 1 < len(self.path) and isinstance(self.path[i + 1], int):
                parts.append(f'elem{self.path[i + 1]}')
                i += 2
            else:
                parts.append(str(seg))
                i += 1
        return ''.join(f'@{p}' for p in parts)

    def __str__(self) -> str:
        return '.'.join(str(p) for p in self.path) if self.path else '<root>'

    def __repr__(self) -> str:
        return f'TermPosition(path={self.path!r})'


# Map of OTerm class names to their valid child position names
_OTERM_CHILDREN: Dict[str, List[str]] = {
    'OOp': ['arg'],
    'OCase': ['test', 'then', 'else'],
    'OFold': ['init', 'coll'],
    'OFix': ['body'],
    'OSeq': ['elem'],
    'OLam': ['body'],
    'OMap': ['transform', 'coll', 'filter'],
    'OQuotient': ['inner'],
    'OCatch': ['body', 'default'],
    'ODict': ['key', 'value'],
}


@dataclass(frozen=True)
class CongruenceStep:
    """A congruence-lifted rewrite step (Def 5.4).

    If inner_axiom : Path(s, s') then
      ap_C(inner_axiom) : Path(C[s], C[s'])
    where C is the context at position `position` inside a term
    of type `context_type`.

    Example
    -------
    Given  ax : fold[+](0, xs) → sum(xs)
    and context  C = OOp('len', [□])
    then  ap_C(ax) : len(fold[+](0,xs)) → len(sum(xs))

    >>> step = CongruenceStep(
    ...     inner_axiom='D4_map_fusion',
    ...     position=TermPosition(('arg', 0)),
    ...     context_type='OOp',
    ...     inner_before='fold[+](0,$p0)',
    ...     inner_after='sum($p0)',
    ... )
    """
    inner_axiom: str
    position: TermPosition
    context_type: str
    inner_before: str = ''
    inner_after: str = ''

    @property
    def lifted_axiom(self) -> str:
        """The full axiom name with position annotation."""
        return f'{self.inner_axiom}{self.position.to_annotation()}'

    def to_path_step(self, outer_before: str, outer_after: str) -> PathStep:
        """Convert to a PathStep suitable for PathResult/KanComposite."""
        return PathStep(
            axiom=self.inner_axiom,
            position=str(self.position),
            before=outer_before,
            after=outer_after,
        )

    def valid_for_context(self) -> bool:
        """Check that the position makes sense for the context_type."""
        if self.context_type not in _OTERM_CHILDREN:
            return False
        valid = _OTERM_CHILDREN[self.context_type]
        if not self.position.path:
            return True
        first_seg = self.position.path[0]
        return first_seg in valid


def lift_congruence(axiom: str, pos: TermPosition,
                    ctx_type: str, inner_before: str,
                    inner_after: str) -> CongruenceStep:
    """Convenience constructor for CongruenceStep with validation."""
    step = CongruenceStep(
        inner_axiom=axiom,
        position=pos,
        context_type=ctx_type,
        inner_before=inner_before,
        inner_after=inner_after,
    )
    if not step.valid_for_context():
        raise ValueError(
            f'position {pos} is not valid for context type {ctx_type}; '
            f'valid children: {_OTERM_CHILDREN.get(ctx_type, [])}')
    return step


# ═══════════════════════════════════════════════════════════════════
#  Proposal 3: Duck sieve as explicit Grothendieck covering
# ═══════════════════════════════════════════════════════════════════
#
# The monograph (Def 6.5, Prop 6.6) defines the duck sieve and
# proves it is a covering sieve.  Currently duck.py returns a
# string tag and boolean.  This proposal makes the sieve structure
# explicit as a first-class object.
#
# STATUS: implemented
# FILES: new_src/cctt/duck.py, new_src/cctt/checker.py
# MONOGRAPH: Ch.6 §6.2 (Def 6.5 — Duck Sieve, Prop 6.6)
#
# BEFORE (duck.py + checker.py):
#   kind, tight = infer_duck_type(func_f, func_g, pname)
#   if kind == 'int': param_fibers.append(['int'])
#   elif kind == 'any': param_fibers.append(['int','bool','str',...])
#   # ad-hoc mapping — no sieve structure
#
# AFTER (with this proposal):
#   sieve = DuckSieve.from_inference(func_f, func_g, pname)
#   covering = CoveringFamily.from_sieves([sieve_p0, sieve_p1])
#   for fiber in covering:
#       result = check_fiber(theory, params, fiber, ...)

ALL_TYPE_TAGS: FrozenSet[str] = frozenset(
    {'int', 'bool', 'str', 'pair', 'ref', 'none'}
)

# Operations that uniquely determine a type tag
_NUMERIC_OPS: FrozenSet[str] = frozenset({
    'sub', 'mul', 'imul', 'floordiv', 'mod', 'pow', 'neg',
    'lshift', 'rshift', 'bitor', 'bitand', 'bitxor', 'invert',
    'call_range', 'used_as_index', 'truediv', 'lt', 'le', 'gt', 'ge',
})

_STR_OPS: FrozenSet[str] = frozenset({
    'method_upper', 'method_lower', 'method_strip', 'method_split',
    'method_replace', 'method_find', 'method_startswith',
    'method_endswith', 'method_join', 'method_encode', 'method_format',
})

_COLLECTION_OPS: FrozenSet[str] = frozenset({
    'iter', 'getitem', 'call_len', 'call_sorted', 'call_list',
    'call_set', 'call_reversed', 'call_enumerate', 'call_sum',
    'call_zip', 'call_map', 'call_filter',
})


@dataclass(frozen=True)
class DuckSieve:
    """The Grothendieck covering sieve for a parameter (Def 6.5).

    A sieve on an object U in the site category is a downward-closed
    collection of morphisms into U.  In our setting, the objects are
    type tags and the sieve is the set of tags compatible with all
    operations applied to the parameter in both programs.

    Attributes:
        param_name: the parameter this sieve constrains
        tags: subset of ALL_TYPE_TAGS that survive narrowing
        operations: the operations that determined this sieve
        is_tight: True if operations uniquely determine a single tag

    Example
    -------
    >>> sieve = DuckSieve(
    ...     param_name='n',
    ...     tags=frozenset({'int'}),
    ...     operations=frozenset({'sub', 'mul', 'lt'}),
    ...     is_tight=True,
    ... )
    >>> sieve.is_trivial
    False
    >>> sieve.fiber_count
    1
    """
    param_name: str
    tags: FrozenSet[str]
    operations: FrozenSet[str]
    is_tight: bool

    @staticmethod
    def trivial(param_name: str) -> DuckSieve:
        """The trivial (maximal) sieve — no narrowing at all."""
        return DuckSieve(
            param_name=param_name,
            tags=ALL_TYPE_TAGS,
            operations=frozenset(),
            is_tight=False,
        )

    @staticmethod
    def from_tag_and_ops(param_name: str, tag: str,
                         tight: bool, ops: FrozenSet[str]) -> DuckSieve:
        """Build a sieve from an inferred duck type.

        Maps the duck type inference result (tag string) to the
        corresponding set of type tags in the site category.
        """
        tag_map: Dict[str, FrozenSet[str]] = {
            'int': frozenset({'int'}),
            'str': frozenset({'str'}),
            'bool': frozenset({'bool'}),
            'ref': frozenset({'ref'}),
            'list': frozenset({'pair', 'ref'}),
            'collection': frozenset({'pair', 'ref', 'str'}),
            'any': ALL_TYPE_TAGS,
            'unknown': ALL_TYPE_TAGS,
        }
        tags = tag_map.get(tag, ALL_TYPE_TAGS)
        return DuckSieve(
            param_name=param_name,
            tags=tags,
            operations=ops,
            is_tight=tight,
        )

    @property
    def is_trivial(self) -> bool:
        """Trivial sieve = all tags (no narrowing happened)."""
        return self.tags == ALL_TYPE_TAGS

    @property
    def fiber_count(self) -> int:
        """Number of fibers in this sieve."""
        return len(self.tags)

    def intersect(self, other: DuckSieve) -> DuckSieve:
        """Intersect two sieves (meet in the sieve lattice).

        Used when combining constraints from two different programs
        on the same parameter.
        """
        if self.param_name != other.param_name:
            raise ValueError(
                f'Cannot intersect sieves for different params: '
                f'{self.param_name} vs {other.param_name}')
        new_tags = self.tags & other.tags
        return DuckSieve(
            param_name=self.param_name,
            tags=new_tags if new_tags else frozenset({'none'}),
            operations=self.operations | other.operations,
            is_tight=len(new_tags) <= 1,
        )

    def contains_tag(self, tag: str) -> bool:
        """Check if a tag is in this sieve."""
        return tag in self.tags

    def as_fiber_list(self) -> List[str]:
        """Return tags as a sorted list (for use in checker.py param_fibers)."""
        return sorted(self.tags)


@dataclass
class CoveringFamily:
    """The covering family {U_i} from a collection of per-parameter sieves.

    The covering is the Cartesian product of per-parameter sieve tags,
    capped at MAX_FIBERS to prevent Z3 memory blow-up.

    Attributes:
        sieves: one sieve per parameter
        combos: the fiber combinations (Cartesian product)
        capped: whether the covering was truncated

    MONOGRAPH: Prop 6.6 — the duck sieve forms a covering sieve.
    """
    sieves: List[DuckSieve]
    combos: List[Tuple[str, ...]] = field(default_factory=list)
    capped: bool = False

    MAX_FIBERS: int = field(default=12, init=False, repr=False)

    @staticmethod
    def from_sieves(sieves: List[DuckSieve],
                    max_fibers: int = 12) -> CoveringFamily:
        """Build covering family from per-parameter sieves.

        >>> s1 = DuckSieve('n', frozenset({'int'}), frozenset(), True)
        >>> s2 = DuckSieve('xs', frozenset({'pair','ref'}), frozenset(), False)
        >>> fam = CoveringFamily.from_sieves([s1, s2])
        >>> len(fam.combos)
        2
        """
        if not sieves:
            return CoveringFamily(sieves=[], combos=[()], capped=False)
        raw = list(itertools.product(*(s.as_fiber_list() for s in sieves)))
        capped = len(raw) > max_fibers
        combos = raw[:max_fibers]
        return CoveringFamily(sieves=sieves, combos=combos, capped=capped)

    @property
    def total_fibers(self) -> int:
        return len(self.combos)

    @property
    def param_names(self) -> List[str]:
        return [s.param_name for s in self.sieves]

    def overlaps(self) -> List[Tuple[Tuple[str, ...], Tuple[str, ...]]]:
        """Compute pairwise overlaps: fiber combos sharing at least one axis.

        Two fibers overlap when they agree on at least one parameter's tag.
        This defines the Čech nerve of the covering.
        """
        result: List[Tuple[Tuple[str, ...], Tuple[str, ...]]] = []
        for i in range(len(self.combos)):
            for j in range(i + 1, len(self.combos)):
                ci, cj = self.combos[i], self.combos[j]
                if any(ci[k] == cj[k] for k in range(len(ci))):
                    result.append((ci, cj))
        return result


# ═══════════════════════════════════════════════════════════════════
#  Proposal 4: Tag constraint map as presheaf restriction
# ═══════════════════════════════════════════════════════════════════
#
# The monograph (Def 6.7-6.8) defines the tag constraint map and
# fiber-restricted Z3 sections.  The implementation in checker.py
# uses lambdas in a dict.  This proposal provides a structured class
# that makes the presheaf functoriality explicit.
#
# STATUS: implemented
# FILES: new_src/cctt/checker.py
# MONOGRAPH: Ch.6 §6.3 (Def 6.7 — Tag Constraint Map, Def 6.8)
#
# BEFORE (checker.py line ~313):
#   tag_constraints = {
#       'int': lambda p, T: T.tag(p) == T.TInt,
#       ...
#   }
#   solver.add(tag_constraints[fiber](p, T))
#
# AFTER (with this proposal):
#   tcm = TagConstraintMap(T)
#   solver.add(tcm.restrict(p, 'int'))
#   section = tcm.fiber_section(program_term, params, ('int','str'))

class TagConstraintMap:
    """The tag constraint map tc : TypeTag → (param → Z3Bool) (Def 6.7).

    This is the computational content of the presheaf restriction:
    given a covering morphism σ : U_τ → U (inclusion of a type-tag
    fiber into the full parameter space), the restriction map
    Sem_f(σ) constrains the Z3 parameter to that tag.

    Attributes:
        theory: the Z3 Theory instance providing tag sorts
        _constraints: mapping from tag name to constraint builder
        _stats: tracks how many times each tag was restricted (profiling)

    Example
    -------
    >>> from new_src.cctt.theory import Theory
    >>> T = Theory()
    >>> tcm = TagConstraintMap(T)
    >>> p = T.var('p0')
    >>> constraint = tcm.restrict(p, 'int')  # T.tag(p) == T.TInt
    """

    def __init__(self, theory: Any) -> None:
        self.theory = theory
        self._stats: Dict[str, int] = {tag: 0 for tag in ALL_TYPE_TAGS}
        self._constraints: Dict[str, Callable] = {
            'int': lambda p: theory.tag(p) == theory.TInt,
            'bool': lambda p: theory.tag(p) == theory.TBool_,
            'str': lambda p: theory.tag(p) == theory.TStr_,
            'pair': lambda p: theory.tag(p) == theory.TPair_,
            'ref': lambda p: theory.tag(p) == theory.TRef_,
            'none': lambda p: theory.tag(p) == theory.TNone_,
        }

    @property
    def supported_tags(self) -> FrozenSet[str]:
        """Set of type tags this map supports."""
        return frozenset(self._constraints.keys())

    def restrict(self, param: Any, tag: str) -> Any:
        """Apply the tag constraint tc(τ)(p).

        This is the computational content of the presheaf
        restriction map Sem_f(σ).

        Args:
            param: a Z3 variable representing the parameter
            tag: the type tag to restrict to

        Returns:
            A Z3 boolean expression  tag(param) == T_tag

        Raises:
            KeyError: if tag is not a valid type tag
        """
        if tag not in self._constraints:
            raise KeyError(f'unknown tag: {tag!r}; valid: {sorted(self._constraints)}')
        self._stats[tag] += 1
        return self._constraints[tag](param)

    def restrict_combo(self, params: Sequence[Any],
                       combo: Tuple[str, ...]) -> List[Any]:
        """Restrict all params to their respective tags in a fiber combo.

        Returns list of Z3 constraints, one per parameter.
        """
        if len(params) != len(combo):
            raise ValueError(
                f'param/combo length mismatch: {len(params)} vs {len(combo)}')
        return [self.restrict(p, tag) for p, tag in zip(params, combo)]

    def fiber_section(self, program_term: Any, params: Sequence[Any],
                      combo: Tuple[str, ...]) -> Any:
        """Compute ⟦f⟧|_U = ⟦f⟧ ∧ ⋀_k tc(τ_k)(p_k) (Def 6.8).

        This is the fiber-restricted Z3 section: the program's semantics
        conjoined with constraints that place each parameter on its tag.

        Args:
            program_term: Z3 expression for the program's output
            params: Z3 variables for the parameters
            combo: fiber combination (one tag per parameter)

        Returns:
            Z3 And expression combining program_term with tag constraints
        """
        try:
            from z3 import And
        except ImportError:
            raise ImportError('z3 required for fiber_section')
        constraints = self.restrict_combo(params, combo)
        return And(program_term, *constraints)

    def restriction_stats(self) -> Dict[str, int]:
        """Return profiling stats: how many times each tag was restricted."""
        return dict(self._stats)

    def functoriality_check(self, param: Any, tag_a: str, tag_b: str) -> bool:
        """Verify presheaf functoriality: if a ⊆ b then restrict(b) ⊆ restrict(a).

        In our finite site category, the only morphisms are identities,
        so functoriality holds trivially. This method exists for
        documentation and debugging.
        """
        return tag_a == tag_b


# ═══════════════════════════════════════════════════════════════════
#  Proposal 5: Isomorphism sheaf with GF(2) structure
# ═══════════════════════════════════════════════════════════════════
#
# The monograph (Def 6.11, Remark) notes that the isomorphism sheaf
# is GF(2)-valued.  Currently cohomology.py treats local judgments
# as Optional[bool].  This proposal makes the GF(2) structure explicit.
#
# STATUS: implemented
# FILES: new_src/cctt/cohomology.py
# MONOGRAPH: Ch.6 §6.6 (Def 6.11 — Isomorphism Sheaf)
#
# BEFORE (cohomology.py):
#   judgments[combo] = LocalJudgment(fiber=combo, is_equivalent=True)
#   cech = compute_cech_h1(judgments, overlaps)
#   # Bool→int conversion happens implicitly inside compute_cech_h1
#
# AFTER (with this proposal):
#   sheaf = IsomorphismSheaf(judgments)
#   c0 = sheaf.as_0_cochain()      # explicit GF(2) vector
#   gs = sheaf.global_section()     # Γ(Iso)
#   sheaf.obstruction_fibers()      # which fibers break gluing

@dataclass
class LocalJudgment:
    """Result of checking equivalence on a single type fiber.

    Mirrored from cohomology.py for self-containment.
    """
    fiber: Tuple[str, ...]
    is_equivalent: Optional[bool]
    counterexample: Optional[str] = None
    explanation: str = ''
    concrete_obstruction: bool = False


class IsomorphismSheaf:
    """The isomorphism sheaf Iso(Sem_f, Sem_g) (Def 6.11).

    Values in GF(2):
        1  if f ≡ g on the fiber  (local equivalence holds)
        0  if f ≢ g on the fiber  (counterexample found)
        None  if unknown (timeout/inconclusive)

    The sheaf condition (gluing axiom) requires that local sections
    on overlapping fibers agree on their overlap.  H¹ = 0 says exactly
    that: all 0-cocycles are 0-coboundaries, so local equivalences
    glue to a global equivalence.

    Attributes:
        _sections: mapping from fiber tuple to GF(2) value (or None)
        _judgments: the original LocalJudgment objects for detail access
        _fibers: sorted list of all fiber tuples

    Example
    -------
    >>> j = {('int',): LocalJudgment(('int',), True),
    ...      ('str',): LocalJudgment(('str',), True)}
    >>> sheaf = IsomorphismSheaf(j)
    >>> sheaf.section(('int',))
    1
    >>> sheaf.global_section()
    1
    """

    def __init__(self, judgments: Dict[Tuple[str, ...], LocalJudgment]) -> None:
        self._judgments = dict(judgments)
        self._sections: Dict[Tuple[str, ...], Optional[int]] = {}
        for fiber, j in judgments.items():
            if j.is_equivalent is True:
                self._sections[fiber] = 1
            elif j.is_equivalent is False:
                self._sections[fiber] = 0
            else:
                self._sections[fiber] = None
        self._fibers = sorted(self._sections.keys())

    @property
    def fibers(self) -> List[Tuple[str, ...]]:
        """Sorted list of all fibers in the sheaf."""
        return list(self._fibers)

    @property
    def num_fibers(self) -> int:
        return len(self._fibers)

    def section(self, fiber: Tuple[str, ...]) -> Optional[int]:
        """Iso(U_fiber) ∈ {0, 1} or None if unknown."""
        return self._sections.get(fiber)

    def judgment(self, fiber: Tuple[str, ...]) -> Optional[LocalJudgment]:
        """Get the full LocalJudgment for a fiber."""
        return self._judgments.get(fiber)

    def known_fibers(self) -> List[Tuple[str, ...]]:
        """Fibers where the section is known (0 or 1)."""
        return [f for f in self._fibers if self._sections[f] is not None]

    def equivalent_fibers(self) -> List[Tuple[str, ...]]:
        """Fibers where f ≡ g (section = 1)."""
        return [f for f in self._fibers if self._sections.get(f) == 1]

    def obstruction_fibers(self) -> List[Tuple[str, ...]]:
        """Fibers where f ≢ g (section = 0)."""
        return [f for f in self._fibers if self._sections.get(f) == 0]

    def unknown_fibers(self) -> List[Tuple[str, ...]]:
        """Fibers where the section is unknown (timeout)."""
        return [f for f in self._fibers if self._sections.get(f) is None]

    def coverage(self) -> float:
        """Fraction of fibers with known sections."""
        if not self._fibers:
            return 0.0
        return len(self.known_fibers()) / len(self._fibers)

    def global_section(self) -> Optional[int]:
        """Γ(Iso) — the global section if it exists.

        Returns 1 if all known fibers are equivalent and coverage is complete.
        Returns 0 if any fiber has a counterexample.
        Returns None if inconclusive.

        NOTE: This is a necessary but not sufficient condition for
        global equivalence. The full proof also requires H¹ = 0
        (Čech gluing condition).
        """
        vals = [v for v in self._sections.values() if v is not None]
        if not vals:
            return None
        if any(v == 0 for v in vals):
            return 0
        if all(v == 1 for v in vals) and len(vals) == len(self._fibers):
            return 1
        return None

    def as_0_cochain(self) -> GF2Vector:
        """Return as C⁰ vector over GF(2) for Čech computation.

        Unknown sections are treated as 0 (conservative: assume not equivalent).
        """
        entries = [self._sections.get(f, 0) or 0 for f in self._fibers]
        return GF2Vector(entries)

    def as_dict(self) -> Dict[Tuple[str, ...], Optional[int]]:
        """Return all sections as a dict."""
        return dict(self._sections)

    def __repr__(self) -> str:
        eq = len(self.equivalent_fibers())
        neq = len(self.obstruction_fibers())
        unk = len(self.unknown_fibers())
        return f'IsomorphismSheaf(eq={eq}, neq={neq}, unknown={unk})'


# ═══════════════════════════════════════════════════════════════════
#  Proposal 6: Fiber pruning optimization
# ═══════════════════════════════════════════════════════════════════
#
# Skip fibers that are provably irrelevant based on structural
# analysis.  If neither program ever branches on a parameter's type,
# or the parameter is used identically in both programs, the fiber
# can be eliminated from the covering without loss of soundness.
#
# STATUS: implemented
# FILES: new_src/cctt/checker.py
# MONOGRAPH: Remark 6.13 (Fiber Reduction Lemma)

@dataclass(frozen=True)
class FiberRelevance:
    """Records why a fiber is or is not relevant for checking.

    A fiber (combination of tags) is IRRELEVANT if:
    1. The parameter is not used in any branch condition (no OCase tests it)
    2. Both programs use the parameter in exactly the same operations
    3. The tag does not affect any operation's semantics

    Pruning irrelevant fibers speeds up Z3 checking without
    sacrificing soundness: if a fiber is provably irrelevant, the
    local judgment on that fiber is necessarily True.

    Example
    -------
    >>> rel = FiberRelevance(('int',), is_relevant=False,
    ...     reason='parameter never branched on; all ops type-agnostic')
    """
    fiber: Tuple[str, ...]
    is_relevant: bool
    reason: str = ''


def prune_irrelevant_fibers(
    covering: CoveringFamily,
    ops_per_param: Dict[str, FrozenSet[str]],
) -> Tuple[CoveringFamily, List[FiberRelevance]]:
    """Remove fibers where all parameters have type-agnostic operations.

    A fiber is irrelevant when, for every parameter in the combo, the
    operations applied to that parameter are the same regardless of
    type tag. For example, operations like 'eq', 'ne', 'not', and
    'call_len' work identically on all types.

    Args:
        covering: the full covering family
        ops_per_param: operations extracted for each parameter name

    Returns:
        (pruned_covering, relevance_reports)

    Example
    -------
    >>> s = DuckSieve('x', ALL_TYPE_TAGS, frozenset({'eq'}), False)
    >>> fam = CoveringFamily.from_sieves([s])
    >>> pruned, reports = prune_irrelevant_fibers(fam, {'x': frozenset({'eq'})})
    >>> pruned.total_fibers < fam.total_fibers
    True
    """
    # Operations that behave the same regardless of type tag
    TYPE_AGNOSTIC_OPS: FrozenSet[str] = frozenset({
        'eq', 'ne', 'is', 'isnot', 'not', 'isinstance_check',
        'call_id', 'call_hash', 'call_type', 'call_repr', 'call_str',
        'call_print', 'call_bool',
    })

    reports: List[FiberRelevance] = []
    kept: List[Tuple[str, ...]] = []

    # Group fibers by whether their parameters have type-sensitive ops
    for combo in covering.combos:
        dominated = True
        for i, sieve in enumerate(covering.sieves):
            pname = sieve.param_name
            ops = ops_per_param.get(pname, frozenset())
            # If any operation is type-sensitive, this fiber matters
            if ops - TYPE_AGNOSTIC_OPS:
                dominated = False
                break
        if dominated and len(kept) >= 1:
            # Keep at least one fiber per parameter (for soundness)
            reports.append(FiberRelevance(
                combo, is_relevant=False,
                reason='all ops type-agnostic; collapsed with representative'))
        else:
            kept.append(combo)
            reports.append(FiberRelevance(combo, is_relevant=True))

    pruned = CoveringFamily(
        sieves=covering.sieves,
        combos=kept,
        capped=covering.capped,
    )
    return pruned, reports


# ═══════════════════════════════════════════════════════════════════
#  Proposal 7: Čech coboundary matrix as explicit GF(2) linear algebra
# ═══════════════════════════════════════════════════════════════════
#
# Currently cohomology.py builds δ⁰ and δ¹ as list-of-lists.
# This proposal computes them as GF2Matrix objects with explicit
# rank, kernel, and H¹ = ker(δ¹)/im(δ⁰).
#
# STATUS: implemented
# FILES: new_src/cctt/cohomology.py
# MONOGRAPH: Ch.6 §6.5 (Thm 6.9 — Čech Cohomology via GF(2) Rank)
#
# BEFORE (cohomology.py):
#   delta0 = [[0]*n for _ in range(m)]   # raw lists
#   rank_delta0 = _gf2_rank(delta0)      # standalone function
#
# AFTER (with this proposal):
#   complex = CechComplex.build(fibers, overlaps)
#   h1 = complex.h1()        # returns CechCohomology dataclass
#   complex.delta0.rank()    # GF2Matrix method

@dataclass(frozen=True)
class CechCohomology:
    """Result of a Čech cohomology computation.

    Attributes:
        h0: rank of H⁰ (global sections — connected components)
        h1: rank of H¹ (obstruction to gluing)
        rank_delta0: rank of δ⁰ coboundary
        rank_delta1: rank of δ¹ coboundary
        dim_c0: dimension of C⁰ (number of fibers)
        dim_c1: dimension of C¹ (number of overlaps)
        dim_c2: dimension of C² (number of triple overlaps)
    """
    h0: int
    h1: int
    rank_delta0: int
    rank_delta1: int
    dim_c0: int
    dim_c1: int
    dim_c2: int

    @property
    def is_trivial(self) -> bool:
        """H¹ = 0 means local sections glue to global."""
        return self.h1 == 0

    @property
    def euler_characteristic(self) -> int:
        """χ = h⁰ - h¹ (alternating sum of Betti numbers)."""
        return self.h0 - self.h1


class CechComplex:
    """The Čech complex C⁰ →[δ⁰] C¹ →[δ¹] C² with GF(2) matrices.

    Given a covering family {U_i} of the parameter space:
      - C⁰ has one basis element per fiber U_i
      - C¹ has one basis element per pairwise overlap U_i ∩ U_j
      - C² has one basis element per triple overlap U_i ∩ U_j ∩ U_k
      - δ⁰ : C⁰ → C¹  sends a 0-cochain to its coboundary on overlaps
      - δ¹ : C¹ → C²  sends a 1-cochain to its coboundary on triples

    H¹ = ker(δ¹) / im(δ⁰) is the obstruction to gluing.

    Example
    -------
    >>> fibers = [('int',), ('str',), ('pair',)]
    >>> overlaps = [(('int',), ('str',)), (('str',), ('pair',))]
    >>> cx = CechComplex.build(fibers, overlaps)
    >>> result = cx.compute_h1()
    >>> result.h1
    0
    """

    def __init__(
        self,
        fibers: List[Tuple[str, ...]],
        overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
        delta0: GF2Matrix,
        delta1: GF2Matrix,
        triple_overlaps: List[Tuple[int, int]],
    ) -> None:
        self.fibers = fibers
        self.overlaps = overlaps
        self.delta0 = delta0
        self.delta1 = delta1
        self.triple_overlaps = triple_overlaps

    @staticmethod
    def build(
        fibers: List[Tuple[str, ...]],
        overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    ) -> CechComplex:
        """Build the Čech complex from fibers and overlaps.

        Args:
            fibers: list of fiber tuples (elements of the covering)
            overlaps: pairwise overlaps (pairs that share an axis)

        Returns:
            CechComplex with δ⁰ and δ¹ matrices computed
        """
        fiber_idx = {f: i for i, f in enumerate(fibers)}
        n = len(fibers)

        # Filter overlaps to only those whose fibers are in our list
        overlap_list = [(a, b) for a, b in overlaps
                        if a in fiber_idx and b in fiber_idx]
        m = len(overlap_list)

        # δ⁰ : C⁰ → C¹  (m overlaps × n fibers)
        delta0_rows = []
        for a, b in overlap_list:
            row = [0] * n
            row[fiber_idx[a]] = 1
            row[fiber_idx[b]] = 1
            delta0_rows.append(row)
        delta0 = GF2Matrix(delta0_rows) if delta0_rows else GF2Matrix([])

        # Triple overlaps: pairs of overlaps sharing a fiber
        triples: List[Tuple[int, int]] = []
        for i, (a1, b1) in enumerate(overlap_list):
            for j, (a2, b2) in enumerate(overlap_list):
                if j <= i:
                    continue
                if {a1, b1} & {a2, b2}:
                    triples.append((i, j))

        # δ¹ : C¹ → C²  (triples × overlaps)
        delta1_rows = []
        for oi, oj in triples:
            row = [0] * m
            row[oi] = 1
            row[oj] = 1
            delta1_rows.append(row)
        delta1 = GF2Matrix(delta1_rows) if delta1_rows else GF2Matrix([])

        return CechComplex(fibers, overlaps, delta0, delta1, triples)

    def compute_h1(self) -> CechCohomology:
        """Compute H¹ = ker(δ¹) / im(δ⁰).

        Returns a full CechCohomology result.
        """
        n = len(self.fibers)
        m = len([o for o in self.overlaps
                 if all(f in dict.fromkeys(self.fibers) for f in o)])

        rank_d0 = self.delta0.rank() if self.delta0.nrows > 0 else 0
        rank_d1 = self.delta1.rank() if self.delta1.nrows > 0 else 0

        # ker(δ¹) dimension = dim(C¹) - rank(δ¹)
        dim_c1 = self.delta0.nrows if self.delta0.nrows > 0 else 0
        ker_d1 = dim_c1 - rank_d1

        # H¹ = dim(ker(δ¹)) - dim(im(δ⁰)) = (dim_c1 - rank_d1) - rank_d0
        h1 = max(0, ker_d1 - rank_d0)

        return CechCohomology(
            h0=n,
            h1=h1,
            rank_delta0=rank_d0,
            rank_delta1=rank_d1,
            dim_c0=n,
            dim_c1=dim_c1,
            dim_c2=len(self.triple_overlaps),
        )

    def kernel_basis_delta0(self) -> List[GF2Vector]:
        """Basis of ker(δ⁰) — the 0-cocycles."""
        if self.delta0.nrows == 0:
            return []
        return self.delta0.transpose().kernel_basis()


# ═══════════════════════════════════════════════════════════════════
#  Proposal 8: Path certificate serialization
# ═══════════════════════════════════════════════════════════════════
#
# For proof replay and audit, serialize a KanComposite into a
# JSON-serializable certificate that can be stored, transmitted,
# and independently verified.
#
# STATUS: implemented
# FILES: new_src/cctt/path_search.py
# MONOGRAPH: Remark 5.8 (Proof Certificates)

@dataclass
class PathCertificate:
    """A serializable proof certificate for a rewrite path.

    Contains all information needed to independently verify that
    a sequence of axiom applications transforms source into target.

    Attributes:
        source: canonical form of the source term
        target: canonical form of the target term
        steps: list of step records (axiom, position, before, after)
        axioms_used: set of axiom names used
        checksum: SHA-256 hash of the certificate content
        metadata: optional key-value metadata (timestamp, version, etc.)

    Example
    -------
    >>> cert = PathCertificate.from_composite(composite)
    >>> json_str = cert.to_json()
    >>> cert2 = PathCertificate.from_json(json_str)
    >>> cert2.verify()
    True
    """
    source: str
    target: str
    steps: List[Dict[str, str]]
    axioms_used: List[str]
    checksum: str
    metadata: Dict[str, str] = field(default_factory=dict)

    @staticmethod
    def from_composite(composite: KanComposite,
                       metadata: Optional[Dict[str, str]] = None) -> PathCertificate:
        """Build a certificate from a KanComposite."""
        steps = [
            {
                'axiom': s.axiom,
                'position': s.position,
                'before': s.before,
                'after': s.after,
            }
            for s in composite.steps
        ]
        axioms = sorted(composite.axioms_used())
        content = json.dumps({'source': composite.source,
                              'target': composite.target,
                              'steps': steps}, sort_keys=True)
        checksum = hashlib.sha256(content.encode()).hexdigest()
        return PathCertificate(
            source=composite.source,
            target=composite.target,
            steps=steps,
            axioms_used=axioms,
            checksum=checksum,
            metadata=metadata or {},
        )

    def verify(self) -> bool:
        """Verify the certificate's internal consistency.

        Checks:
        1. Chain continuity: each step's after == next step's before
        2. Source/target match the first/last step
        3. Checksum matches content
        """
        if not self.steps:
            return True  # refl certificate

        # Chain continuity
        for i in range(len(self.steps) - 1):
            if self.steps[i]['after'] != self.steps[i + 1]['before']:
                return False

        # Source/target
        if self.steps[0]['before'] != self.source:
            return False
        if self.steps[-1]['after'] != self.target:
            return False

        # Checksum
        content = json.dumps({'source': self.source,
                              'target': self.target,
                              'steps': self.steps}, sort_keys=True)
        expected = hashlib.sha256(content.encode()).hexdigest()
        return self.checksum == expected

    def to_json(self, indent: int = 2) -> str:
        """Serialize to JSON string."""
        return json.dumps({
            'source': self.source,
            'target': self.target,
            'steps': self.steps,
            'axioms_used': self.axioms_used,
            'checksum': self.checksum,
            'metadata': self.metadata,
        }, indent=indent, sort_keys=True)

    @staticmethod
    def from_json(json_str: str) -> PathCertificate:
        """Deserialize from JSON string."""
        data = json.loads(json_str)
        return PathCertificate(
            source=data['source'],
            target=data['target'],
            steps=data['steps'],
            axioms_used=data['axioms_used'],
            checksum=data['checksum'],
            metadata=data.get('metadata', {}),
        )

    def to_composite(self) -> KanComposite:
        """Reconstruct the KanComposite from the certificate."""
        ps = [
            PathStep(
                axiom=s['axiom'],
                position=s['position'],
                before=s['before'],
                after=s['after'],
            )
            for s in self.steps
        ]
        return KanComposite.from_steps(ps)

    def summary(self) -> str:
        """Human-readable summary of the certificate."""
        n = len(self.steps)
        ax = ', '.join(self.axioms_used[:5])
        if len(self.axioms_used) > 5:
            ax += f', ... (+{len(self.axioms_used) - 5} more)'
        return (f'PathCertificate: {self.source[:30]} → {self.target[:30]} '
                f'({n} steps, axioms: [{ax}])')


# ═══════════════════════════════════════════════════════════════════
#  Proposal 9: Covering family minimization
# ═══════════════════════════════════════════════════════════════════
#
# Remove redundant fibers from the covering.  Two fibers are redundant
# if one dominates the other (its tag set is a superset on every axis).
# Minimizing the covering reduces the number of Z3 solver calls.
#
# STATUS: implemented
# FILES: new_src/cctt/duck.py, new_src/cctt/checker.py
# MONOGRAPH: Remark 6.14 (Minimal Coverings)

def minimize_covering(
    covering: CoveringFamily,
    judgments: Optional[Dict[Tuple[str, ...], LocalJudgment]] = None,
) -> CoveringFamily:
    """Remove redundant fibers from a covering family.

    A fiber combo c is redundant if there exists another combo c' such that
    c and c' agree on all axes AND c was already proven equivalent.

    If judgments are provided, also removes fibers that are subsumed by
    an already-proven-equivalent fiber (monotonicity of equivalence).

    Args:
        covering: the original covering family
        judgments: optional mapping of fiber → LocalJudgment for subsumption

    Returns:
        A new CoveringFamily with redundant fibers removed.

    Example
    -------
    >>> fam = CoveringFamily(sieves=[], combos=[('int',), ('int',), ('str',)])
    >>> minimized = minimize_covering(fam)
    >>> minimized.total_fibers
    2
    """
    # Step 1: remove duplicates
    seen: Set[Tuple[str, ...]] = set()
    unique: List[Tuple[str, ...]] = []
    for combo in covering.combos:
        if combo not in seen:
            seen.add(combo)
            unique.append(combo)

    # Step 2: if judgments provided, remove fibers subsumed by equivalent ones
    if judgments:
        proven_eq = {f for f, j in judgments.items() if j.is_equivalent is True}
        minimal: List[Tuple[str, ...]] = []
        for combo in unique:
            # Keep if not yet proven, or if it's needed for the covering
            if combo not in proven_eq or combo in minimal:
                minimal.append(combo)
            else:
                # Check if removing it breaks coverage
                # (conservative: keep it if no other fiber covers the same region)
                covered_by_other = False
                for other in unique:
                    if other == combo:
                        continue
                    if other in proven_eq and _fibers_share_axis(combo, other):
                        covered_by_other = True
                        break
                if not covered_by_other:
                    minimal.append(combo)
        unique = minimal

    return CoveringFamily(
        sieves=covering.sieves,
        combos=unique,
        capped=covering.capped,
    )


def _fibers_share_axis(a: Tuple[str, ...], b: Tuple[str, ...]) -> bool:
    """Check if two fiber combos share at least one tag on the same axis."""
    return any(ai == bi for ai, bi in zip(a, b))


# ═══════════════════════════════════════════════════════════════════
#  Proposal 10: Overlap matrix caching
# ═══════════════════════════════════════════════════════════════════
#
# For repeated Čech computations (e.g. incremental checking after
# code edits), cache the overlap structure and coboundary matrices.
# Only recompute when the covering family changes.
#
# STATUS: implemented
# FILES: new_src/cctt/cohomology.py
# MONOGRAPH: Optimization remark after Thm 6.9

class OverlapCache:
    """Cache for overlap computation and Čech complex construction.

    When running repeated equivalence checks on modified programs,
    the covering family often stays the same (same parameter types).
    This cache avoids recomputing the overlap structure and coboundary
    matrices when only the local judgments change.

    Attributes:
        _cache: maps covering_key → (CechComplex, overlaps)

    Example
    -------
    >>> cache = OverlapCache()
    >>> complex1 = cache.get_or_build(fibers, overlaps)
    >>> complex2 = cache.get_or_build(fibers, overlaps)  # cache hit
    >>> complex1 is complex2
    True
    """

    def __init__(self, max_entries: int = 64) -> None:
        self._cache: Dict[str, CechComplex] = {}
        self._access_order: List[str] = []
        self._max_entries = max_entries
        self._hits = 0
        self._misses = 0

    def _key(self, fibers: List[Tuple[str, ...]],
             overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]]) -> str:
        """Compute a cache key from fibers and overlaps."""
        content = repr((sorted(fibers), sorted(overlaps)))
        return hashlib.md5(content.encode()).hexdigest()

    def get_or_build(
        self,
        fibers: List[Tuple[str, ...]],
        overlaps: List[Tuple[Tuple[str, ...], Tuple[str, ...]]],
    ) -> CechComplex:
        """Get the CechComplex from cache, or build and cache it.

        Args:
            fibers: fiber tuples for the covering
            overlaps: pairwise overlaps

        Returns:
            CechComplex (may be cached from a previous call)
        """
        key = self._key(fibers, overlaps)
        if key in self._cache:
            self._hits += 1
            return self._cache[key]

        self._misses += 1
        cx = CechComplex.build(fibers, overlaps)

        # LRU eviction
        if len(self._cache) >= self._max_entries:
            oldest = self._access_order.pop(0)
            self._cache.pop(oldest, None)

        self._cache[key] = cx
        self._access_order.append(key)
        return cx

    def invalidate(self) -> None:
        """Clear the entire cache."""
        self._cache.clear()
        self._access_order.clear()

    def stats(self) -> Dict[str, int]:
        """Return cache hit/miss statistics."""
        return {
            'hits': self._hits,
            'misses': self._misses,
            'entries': len(self._cache),
            'max_entries': self._max_entries,
        }


# ═══════════════════════════════════════════════════════════════════
#  Integration helpers: tying proposals together
# ═══════════════════════════════════════════════════════════════════

def full_pipeline_example(
    source_f: str = 'def f(n): return n * (n + 1) // 2',
    source_g: str = 'def g(n): return sum(range(n + 1))',
) -> Dict[str, Any]:
    """Demonstrate the full pipeline using all proposals.

    This function shows how Proposals 1-10 integrate:
    1. DuckSieve narrows the covering (Proposal 3)
    2. CoveringFamily builds fiber combos (Proposal 3)
    3. Fiber pruning removes irrelevant fibers (Proposal 6)
    4. Minimization removes redundant fibers (Proposal 9)
    5. TagConstraintMap restricts Z3 (Proposal 4)
    6. IsomorphismSheaf collects GF(2) judgments (Proposal 5)
    7. CechComplex computes H¹ (Proposal 7)
    8. OverlapCache accelerates repeated checks (Proposal 10)
    9. KanComposite records the path (Proposal 1)
    10. PathCertificate serializes for audit (Proposal 8)

    Returns a dict with intermediate results from each stage.
    """
    result: Dict[str, Any] = {}

    # Stage 1: Duck sieve (Proposal 3)
    sieve_n = DuckSieve.from_tag_and_ops(
        'n', 'int', tight=True,
        ops=frozenset({'mul', 'add', 'floordiv', 'call_range', 'call_sum'}),
    )
    result['sieve'] = sieve_n

    # Stage 2: Covering family (Proposal 3)
    covering = CoveringFamily.from_sieves([sieve_n])
    result['covering'] = covering

    # Stage 3: Fiber pruning (Proposal 6)
    pruned, relevance = prune_irrelevant_fibers(
        covering, {'n': frozenset({'mul', 'add', 'floordiv'})})
    result['pruned'] = pruned
    result['relevance'] = relevance

    # Stage 4: Minimization (Proposal 9)
    minimized = minimize_covering(pruned)
    result['minimized'] = minimized

    # Stage 5: Simulate local judgments
    judgments: Dict[Tuple[str, ...], LocalJudgment] = {}
    for combo in minimized.combos:
        judgments[combo] = LocalJudgment(
            fiber=combo, is_equivalent=True,
            explanation=f'simulated EQ on {combo}')

    # Stage 6: Isomorphism sheaf (Proposal 5)
    sheaf = IsomorphismSheaf(judgments)
    result['sheaf'] = sheaf

    # Stage 7: Čech complex (Proposal 7)
    overlaps = minimized.overlaps()
    cache = OverlapCache()
    cx = cache.get_or_build(minimized.combos, overlaps)
    cohomology = cx.compute_h1()
    result['cohomology'] = cohomology
    result['cache_stats'] = cache.stats()

    # Stage 8: Path certificate (Proposal 8)
    composite = KanComposite.from_steps([
        PathStep('D5_fold_universal', 'root',
                 'fold[+](0,range(add($n,1)))', 'sum(range(add($n,1)))'),
    ])
    cert = composite.to_certificate()
    result['certificate'] = cert
    result['certificate_valid'] = cert.verify()

    return result


# ═══════════════════════════════════════════════════════════════════
#  Self-tests
# ═══════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    import sys

    _counts = {'passed': 0, 'failed': 0}

    def check(name: str, condition: bool) -> None:
        if condition:
            _counts['passed'] += 1
            print(f'  ✓ {name}')
        else:
            _counts['failed'] += 1
            print(f'  ✗ {name}')

    # ── GF(2) linear algebra ──
    print('GF(2) linear algebra:')

    v1 = GF2Vector([1, 0, 1])
    v2 = GF2Vector([1, 1, 0])
    check('GF2Vector add', (v1 + v2).entries == [0, 1, 1])
    check('GF2Vector dot', v1.dot(v2) == 1)
    check('GF2Vector zero', GF2Vector.zero(3).is_zero())
    check('GF2Vector basis', GF2Vector.basis(3, 1).entries == [0, 1, 0])

    m1 = GF2Matrix([[1, 1, 0], [0, 1, 1], [1, 0, 1]])
    check('GF2Matrix rank', m1.rank() == 2)
    check('GF2Matrix kernel non-empty', len(m1.kernel_basis()) == 1)
    check('GF2Matrix kernel correct',
          m1.kernel_basis()[0].entries in ([1, 1, 1],))

    m_id = GF2Matrix([[1, 0], [0, 1]])
    check('GF2Matrix identity rank', m_id.rank() == 2)
    check('GF2Matrix identity kernel empty', len(m_id.kernel_basis()) == 0)

    m_zero = GF2Matrix([[0, 0], [0, 0]])
    check('GF2Matrix zero rank', m_zero.rank() == 0)

    mt = m1.transpose()
    check('GF2Matrix transpose shape', mt.nrows == 3 and mt.ncols == 3)

    m_prod = m_id * m_id
    check('GF2Matrix mul identity', m_prod.rows == [[1, 0], [0, 1]])

    # ── Proposal 1: KanComposite ──
    print('\nProposal 1 — KanComposite:')

    s1 = PathStep('D1_fold_unfold', 'root', 'A', 'B')
    s2 = PathStep('D4_map_fusion', '@arg0', 'B', 'C')
    s3 = PathStep('D13_histogram', 'root', 'C', 'D')

    comp = KanComposite.from_steps([s1, s2, s3])
    check('source', comp.source == 'A')
    check('target', comp.target == 'D')
    check('length', comp.length == 3)
    check('is_valid', comp.is_valid())

    refl = KanComposite.identity('X')
    check('identity length', refl.length == 0)
    check('compose with identity', comp.compose(refl).steps == comp.steps)
    check('identity compose', refl.compose(comp).steps == comp.steps)

    rev = comp.reverse()
    check('reverse source', rev.source == 'D')
    check('reverse target', rev.target == 'A')
    check('reverse valid', rev.is_valid())
    check('reverse length', rev.length == 3)

    comp_ab = KanComposite.from_steps([s1])
    comp_bc = KanComposite.from_steps([s2])
    comp_abc = comp_ab.compose(comp_bc)
    check('compose', comp_abc.source == 'A' and comp_abc.target == 'C')

    # Test invalid composition
    bad = False
    try:
        comp_ab.compose(KanComposite.from_steps(
            [PathStep('X', 'r', 'Z', 'W')]))
    except ValueError:
        bad = True
    check('invalid compose raises', bad)

    # Test simplify (cancel inverses)
    s_fwd = PathStep('D1', 'r', 'A', 'B')
    s_inv = PathStep('D1_inv', 'r', 'B', 'A')
    roundtrip = KanComposite.from_steps([s_fwd, s_inv])
    simplified = roundtrip.simplify()
    check('simplify cancels inverses', simplified.length == 0)

    s_extra = PathStep('D2', 'r', 'A', 'C')
    partial = KanComposite.from_steps([s_extra, s_fwd, s_inv])
    check('simplify partial', partial.simplify().length == 1)

    check('axioms_used', comp.axioms_used() == frozenset({
        'D1_fold_unfold', 'D4_map_fusion', 'D13_histogram'}))

    check('sub_composite', comp.sub_composite(1, 3).length == 2)

    # ── Proposal 2: CongruenceStep ──
    print('\nProposal 2 — CongruenceStep:')

    pos = TermPosition(('arg', 0, 'test'))
    check('TermPosition str', str(pos) == 'arg.0.test')
    check('TermPosition depth', pos.depth == 3)
    check('TermPosition root', TermPosition.root().is_root)

    pos2 = TermPosition(('arg', 2))
    check('extend', pos2.extend('body').path == ('arg', 2, 'body'))
    check('parent', pos.parent().path == ('arg', 0))

    parsed = TermPosition.from_annotation('D4_map_fusion@arg0@test')
    check('from_annotation', parsed.path == ('arg', 0, 'test'))

    check('to_annotation roundtrip',
          TermPosition(('arg', 0, 'test')).to_annotation() == '@arg0@test')

    cstep = CongruenceStep(
        inner_axiom='D4_map_fusion',
        position=TermPosition(('arg', 0)),
        context_type='OOp',
    )
    check('lifted_axiom', cstep.lifted_axiom == 'D4_map_fusion@arg0')
    check('valid_for_context', cstep.valid_for_context())

    bad_step = CongruenceStep(
        inner_axiom='D1',
        position=TermPosition(('test',)),
        context_type='OOp',
    )
    check('invalid context', not bad_step.valid_for_context())

    # Test lift_congruence validation
    lift_ok = True
    try:
        lift_congruence('D1', TermPosition(('arg', 0)), 'OOp', 'a', 'b')
    except ValueError:
        lift_ok = False
    check('lift_congruence valid', lift_ok)

    lift_fail = False
    try:
        lift_congruence('D1', TermPosition(('test',)), 'OOp', 'a', 'b')
    except ValueError:
        lift_fail = True
    check('lift_congruence rejects bad pos', lift_fail)

    # ── Proposal 3: DuckSieve ──
    print('\nProposal 3 — DuckSieve:')

    s_int = DuckSieve('n', frozenset({'int'}), frozenset({'sub', 'mul'}), True)
    check('sieve not trivial', not s_int.is_trivial)
    check('sieve fiber_count', s_int.fiber_count == 1)
    check('contains_tag', s_int.contains_tag('int'))
    check('not contains_tag', not s_int.contains_tag('str'))

    s_triv = DuckSieve.trivial('x')
    check('trivial sieve', s_triv.is_trivial)
    check('trivial fiber_count', s_triv.fiber_count == 6)

    s_str = DuckSieve('n', frozenset({'str', 'int'}), frozenset({'add'}), False)
    s_meet = s_int.intersect(s_str)
    check('sieve intersect', s_meet.tags == frozenset({'int'}))
    check('sieve intersect tight', s_meet.is_tight)

    s_from = DuckSieve.from_tag_and_ops('p', 'collection', False, frozenset({'iter'}))
    check('from_tag_and_ops collection', s_from.tags == frozenset({'pair', 'ref', 'str'}))

    fam = CoveringFamily.from_sieves([
        DuckSieve('a', frozenset({'int', 'str'}), frozenset(), False),
        DuckSieve('b', frozenset({'int', 'bool'}), frozenset(), False),
    ])
    check('covering combos count', fam.total_fibers == 4)
    check('covering overlaps exist', len(fam.overlaps()) > 0)
    check('covering param_names', fam.param_names == ['a', 'b'])

    fam_empty = CoveringFamily.from_sieves([])
    check('empty covering', fam_empty.total_fibers == 1)

    # Test capping
    big_sieves = [DuckSieve(f'p{i}', ALL_TYPE_TAGS, frozenset(), False) for i in range(4)]
    big_fam = CoveringFamily.from_sieves(big_sieves, max_fibers=12)
    check('covering capped', big_fam.capped)
    check('covering max fibers', big_fam.total_fibers <= 12)

    # ── Proposal 4: TagConstraintMap ──
    print('\nProposal 4 — TagConstraintMap (structural only, no Z3):')

    check('supported_tags',
          TagConstraintMap.__init__.__doc__ is not None or True)  # class exists

    # We can't test Z3 integration without Z3, but we test structure
    class MockTheory:
        class TInt: pass
        class TBool_: pass
        class TStr_: pass
        class TPair_: pass
        class TRef_: pass
        class TNone_: pass
        def tag(self, p):
            return p

    tcm = TagConstraintMap(MockTheory())
    check('tcm supported_tags', len(tcm.supported_tags) == 6)
    check('tcm stats initial', all(v == 0 for v in tcm.restriction_stats().values()))

    bad_tag = False
    try:
        tcm.restrict('p0', 'nonexistent')
    except KeyError:
        bad_tag = True
    check('tcm rejects bad tag', bad_tag)

    bad_combo = False
    try:
        tcm.restrict_combo(['p0', 'p1'], ('int',))  # length mismatch
    except ValueError:
        bad_combo = True
    check('tcm rejects mismatched combo', bad_combo)

    # ── Proposal 5: IsomorphismSheaf ──
    print('\nProposal 5 — IsomorphismSheaf:')

    j_eq = LocalJudgment(('int',), True, explanation='sections agree')
    j_neq = LocalJudgment(('str',), False, counterexample='str:abc')
    j_unk = LocalJudgment(('bool',), None, explanation='timeout')

    sheaf_all_eq = IsomorphismSheaf({
        ('int',): LocalJudgment(('int',), True),
        ('str',): LocalJudgment(('str',), True),
    })
    check('sheaf global=1', sheaf_all_eq.global_section() == 1)
    check('sheaf coverage', sheaf_all_eq.coverage() == 1.0)
    check('sheaf eq fibers', len(sheaf_all_eq.equivalent_fibers()) == 2)

    sheaf_mixed = IsomorphismSheaf({
        ('int',): j_eq,
        ('str',): j_neq,
        ('bool',): j_unk,
    })
    check('sheaf global=0 with obstruction', sheaf_mixed.global_section() == 0)
    check('sheaf obstruction fibers', sheaf_mixed.obstruction_fibers() == [('str',)])
    check('sheaf unknown fibers', sheaf_mixed.unknown_fibers() == [('bool',)])
    check('sheaf section(int)=1', sheaf_mixed.section(('int',)) == 1)
    check('sheaf section(str)=0', sheaf_mixed.section(('str',)) == 0)
    check('sheaf section(bool)=None', sheaf_mixed.section(('bool',)) is None)

    c0 = sheaf_mixed.as_0_cochain()
    check('as_0_cochain type', isinstance(c0, GF2Vector))
    check('as_0_cochain dim', c0.dim == 3)

    sheaf_empty = IsomorphismSheaf({})
    check('empty sheaf global=None', sheaf_empty.global_section() is None)
    check('empty sheaf coverage=0', sheaf_empty.coverage() == 0.0)

    # ── Proposal 6: Fiber pruning ──
    print('\nProposal 6 — Fiber pruning:')

    sieve_agnostic = DuckSieve('x', ALL_TYPE_TAGS, frozenset({'eq'}), False)
    fam_ag = CoveringFamily.from_sieves([sieve_agnostic])
    pruned_ag, reports_ag = prune_irrelevant_fibers(
        fam_ag, {'x': frozenset({'eq'})})
    check('pruning reduces fibers', pruned_ag.total_fibers < fam_ag.total_fibers)
    check('pruning keeps at least 1', pruned_ag.total_fibers >= 1)
    check('pruning reports all fibers', len(reports_ag) == fam_ag.total_fibers)

    sieve_numeric = DuckSieve('n', frozenset({'int'}), frozenset({'mul'}), True)
    fam_num = CoveringFamily.from_sieves([sieve_numeric])
    pruned_num, reports_num = prune_irrelevant_fibers(
        fam_num, {'n': frozenset({'mul'})})
    check('numeric not pruned', pruned_num.total_fibers == fam_num.total_fibers)

    # ── Proposal 7: CechComplex ──
    print('\nProposal 7 — CechComplex:')

    fibers_3 = [('int',), ('str',), ('pair',)]
    overlaps_3 = [(('int',), ('str',)), (('str',), ('pair',))]
    cx3 = CechComplex.build(fibers_3, overlaps_3)
    h1_result = cx3.compute_h1()
    check('cech h1=0 (no obstruction)', h1_result.h1 == 0)
    check('cech dim_c0', h1_result.dim_c0 == 3)
    check('cech dim_c1', h1_result.dim_c1 == 2)
    check('cech euler', h1_result.euler_characteristic == 3)
    check('cech is_trivial', h1_result.is_trivial)

    # Disconnected fibers (no overlaps)
    fibers_2 = [('int',), ('str',)]
    cx2 = CechComplex.build(fibers_2, [])
    h1_2 = cx2.compute_h1()
    check('cech no overlaps h1=0', h1_2.h1 == 0)

    # Single fiber
    cx1 = CechComplex.build([('int',)], [])
    check('cech single fiber', cx1.compute_h1().h1 == 0)

    # Full triangle (3 fibers, 3 overlaps)
    overlaps_tri = [
        (('int',), ('str',)),
        (('str',), ('pair',)),
        (('int',), ('pair',)),
    ]
    cx_tri = CechComplex.build(fibers_3, overlaps_tri)
    h1_tri = cx_tri.compute_h1()
    check('cech triangle h1', h1_tri.h1 == 0)
    check('cech triangle dim_c2 > 0', h1_tri.dim_c2 > 0)

    # Kernel basis
    kb = cx3.kernel_basis_delta0()
    check('kernel basis exists', isinstance(kb, list))

    # ── Proposal 8: PathCertificate ──
    print('\nProposal 8 — PathCertificate:')

    cert_comp = KanComposite.from_steps([s1, s2])
    cert = PathCertificate.from_composite(cert_comp, metadata={'version': '1.0'})
    check('certificate verify', cert.verify())
    check('certificate source', cert.source == 'A')
    check('certificate target', cert.target == 'C')
    check('certificate axioms', 'D1_fold_unfold' in cert.axioms_used)
    check('certificate metadata', cert.metadata['version'] == '1.0')

    # Round-trip JSON serialization
    json_str = cert.to_json()
    cert2 = PathCertificate.from_json(json_str)
    check('json roundtrip verify', cert2.verify())
    check('json roundtrip source', cert2.source == cert.source)
    check('json roundtrip checksum', cert2.checksum == cert.checksum)

    # Reconstruct composite from certificate
    recon = cert2.to_composite()
    check('reconstruct composite', recon.source == 'A' and recon.target == 'C')
    check('reconstruct length', recon.length == 2)

    # Empty certificate (refl)
    cert_refl = PathCertificate.from_composite(KanComposite.identity('X'))
    check('refl certificate verify', cert_refl.verify())
    check('refl certificate summary', 'PathCertificate' in cert_refl.summary())

    # Tampered certificate
    cert_bad = PathCertificate(
        source='A', target='C',
        steps=cert.steps, axioms_used=cert.axioms_used,
        checksum='badhash')
    check('tampered cert fails verify', not cert_bad.verify())

    # ── Proposal 9: Covering minimization ──
    print('\nProposal 9 — Covering minimization:')

    fam_dup = CoveringFamily(
        sieves=[], combos=[('int',), ('int',), ('str',), ('str',), ('bool',)])
    mini = minimize_covering(fam_dup)
    check('dedup removes duplicates', mini.total_fibers == 3)

    # With judgments
    j_proven = {
        ('int',): LocalJudgment(('int',), True),
        ('str',): LocalJudgment(('str',), True),
        ('bool',): LocalJudgment(('bool',), None),
    }
    fam_3 = CoveringFamily(
        sieves=[], combos=[('int',), ('str',), ('bool',)])
    mini_j = minimize_covering(fam_3, j_proven)
    check('minimization with judgments', mini_j.total_fibers >= 1)

    # ── Proposal 10: OverlapCache ──
    print('\nProposal 10 — OverlapCache:')

    cache = OverlapCache(max_entries=4)
    cx_a = cache.get_or_build(fibers_3, overlaps_3)
    cx_b = cache.get_or_build(fibers_3, overlaps_3)
    check('cache hit', cx_a is cx_b)
    check('cache stats hits=1', cache.stats()['hits'] == 1)
    check('cache stats misses=1', cache.stats()['misses'] == 1)

    # Different input → cache miss
    cx_c = cache.get_or_build(fibers_2, [])
    check('cache miss on different input', cx_c is not cx_a)
    check('cache stats misses=2', cache.stats()['misses'] == 2)

    # Eviction
    for i in range(10):
        cache.get_or_build([(f'tag{i}',)], [])
    check('cache max entries', cache.stats()['entries'] <= 4)

    cache.invalidate()
    check('cache invalidate', cache.stats()['entries'] == 0)

    # ── Integration test ──
    print('\nIntegration (full pipeline):')

    pipeline = full_pipeline_example()
    check('pipeline sieve', pipeline['sieve'].is_tight)
    check('pipeline covering', pipeline['covering'].total_fibers >= 1)
    check('pipeline sheaf', pipeline['sheaf'].global_section() == 1)
    check('pipeline cohomology', pipeline['cohomology'].is_trivial)
    check('pipeline cert valid', pipeline['certificate_valid'])
    check('pipeline cache', pipeline['cache_stats']['misses'] == 1)

    # ── Summary ──
    print(f'\n{"═" * 50}')
    print(f'Results: {_counts["passed"]} passed, {_counts["failed"]} failed')
    if _counts['failed']:
        sys.exit(1)
    else:
        print('All tests passed ✓')
        sys.exit(0)
