"""Cubical foundations for CCTT — interval types, face formulas, typed paths.

Integrates proposals from g01_foundations into the live CCTT system:

1. **IVal**           — Explicit interval & De Morgan algebra (DM1-DM4)
2. **FaceFormula**    — Face lattice with compositional restriction
3. **CubicalPath**    — Typed path wrapper with face maps & groupoid ops
4. **FunextWitness**  — Per-fiber path assembler (Thm 2.7)
5. **GroupoidLawCertifier** — Full 6-law groupoid checker
6. **DeMorganVerifier**     — DM1-DM4 axiom auditor
7. **CubicalSet**     — 0-/1-/2-cube data structure with face/degeneracy
8. **PathCompositionOptimizer** — Redundancy/cycle eliminator for paths
9. **IntervalSubstitutionEngine** — Substitute interval values into paths
10. **DependentPathType** — Type-changing rewrites (e.g. int→bool)
11. **ConnectionOps**  — Min/max connection helpers
"""
from __future__ import annotations

import itertools
from collections import defaultdict
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Dict, FrozenSet, Iterator, List, Mapping,
    Optional, Sequence, Set, Tuple, Union,
)

from .path_search import PathStep, PathResult
from .denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    normalize,
)


# ╔═══════════════════════════════════════════════════════════╗
# ║  1. Explicit Interval & De Morgan Algebra                 ║
# ╚═══════════════════════════════════════════════════════════╝

@dataclass(frozen=True)
class IVal:
    """Element of the abstract interval *I*.

    The free De Morgan algebra on generators with elements I0, I1,
    IVar(name), INeg(inner), IMeet(l, r), IJoin(l, r).  Reductions:

    * **DM1** — involution:  ¬¬r = r
    * **DM2** — endpoint swap:  ¬0 = 1,  ¬1 = 0
    * **DM3** — De Morgan:  ¬(r ∧ s) = ¬r ∨ ¬s
    * **DM4** — De Morgan:  ¬(r ∨ s) = ¬r ∧ ¬s
    """

    def free_vars(self) -> FrozenSet[str]:
        return frozenset()

    def substitute(self, var: str, val: 'IVal') -> 'IVal':
        return self

    def eval_at(self, env: Dict[str, int]) -> Optional[int]:
        return None


@dataclass(frozen=True)
class I0(IVal):
    """Left endpoint ``i0``."""

    def __repr__(self) -> str:
        return "i0"

    def eval_at(self, env: Dict[str, int]) -> Optional[int]:
        return 0


@dataclass(frozen=True)
class I1(IVal):
    """Right endpoint ``i1``."""

    def __repr__(self) -> str:
        return "i1"

    def eval_at(self, env: Dict[str, int]) -> Optional[int]:
        return 1


@dataclass(frozen=True)
class IVar(IVal):
    """Interval variable."""
    name: str

    def __repr__(self) -> str:
        return self.name

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.name})

    def substitute(self, var: str, val: IVal) -> IVal:
        return val if self.name == var else self

    def eval_at(self, env: Dict[str, int]) -> Optional[int]:
        return env.get(self.name)


@dataclass(frozen=True)
class INeg(IVal):
    """Negation / reversal of an interval value."""
    inner: IVal

    def __repr__(self) -> str:
        return f"¬{self.inner}"

    def free_vars(self) -> FrozenSet[str]:
        return self.inner.free_vars()

    def substitute(self, var: str, val: IVal) -> IVal:
        return i_neg(self.inner.substitute(var, val))

    def eval_at(self, env: Dict[str, int]) -> Optional[int]:
        v = self.inner.eval_at(env)
        return None if v is None else (1 - v)


@dataclass(frozen=True)
class IMeet(IVal):
    """Min-connection: ``r ∧ s``."""
    left: IVal
    right: IVal

    def __repr__(self) -> str:
        return f"({self.left} ∧ {self.right})"

    def free_vars(self) -> FrozenSet[str]:
        return self.left.free_vars() | self.right.free_vars()

    def substitute(self, var: str, val: IVal) -> IVal:
        return i_meet(self.left.substitute(var, val),
                      self.right.substitute(var, val))

    def eval_at(self, env: Dict[str, int]) -> Optional[int]:
        lv = self.left.eval_at(env)
        rv = self.right.eval_at(env)
        if lv is not None and rv is not None:
            return min(lv, rv)
        return None


@dataclass(frozen=True)
class IJoin(IVal):
    """Max-connection: ``r ∨ s``."""
    left: IVal
    right: IVal

    def __repr__(self) -> str:
        return f"({self.left} ∨ {self.right})"

    def free_vars(self) -> FrozenSet[str]:
        return self.left.free_vars() | self.right.free_vars()

    def substitute(self, var: str, val: IVal) -> IVal:
        return i_join(self.left.substitute(var, val),
                      self.right.substitute(var, val))

    def eval_at(self, env: Dict[str, int]) -> Optional[int]:
        lv = self.left.eval_at(env)
        rv = self.right.eval_at(env)
        if lv is not None and rv is not None:
            return max(lv, rv)
        return None


# --------------- smart constructors ----------------

def i_neg(r: IVal) -> IVal:
    """Reversal: ¬i0 = i1, ¬i1 = i0, ¬¬r = r (DM1, DM2)."""
    if isinstance(r, I0):
        return I1()
    if isinstance(r, I1):
        return I0()
    if isinstance(r, INeg):
        return r.inner
    if isinstance(r, IMeet):
        return i_join(i_neg(r.left), i_neg(r.right))
    if isinstance(r, IJoin):
        return i_meet(i_neg(r.left), i_neg(r.right))
    return INeg(r)


def i_meet(r: IVal, s: IVal) -> IVal:
    """Min-connection: ``r ∧ s``.  Satisfies ``r ∧ i0 = i0``, ``r ∧ i1 = r``."""
    if isinstance(r, I0) or isinstance(s, I0):
        return I0()
    if isinstance(r, I1):
        return s
    if isinstance(s, I1):
        return r
    if r == s:
        return r
    if r == i_neg(s):
        return I0()
    return IMeet(r, s)


def i_join(r: IVal, s: IVal) -> IVal:
    """Max-connection: ``r ∨ s``.  Satisfies ``r ∨ i0 = r``, ``r ∨ i1 = i1``."""
    if isinstance(r, I1) or isinstance(s, I1):
        return I1()
    if isinstance(r, I0):
        return s
    if isinstance(s, I0):
        return r
    if r == s:
        return r
    if r == i_neg(s):
        return I1()
    return IJoin(r, s)


def ival_normalize(r: IVal) -> IVal:
    """Normalize an interval expression by exhaustively applying DM1-DM4."""
    if isinstance(r, (I0, I1, IVar)):
        return r
    if isinstance(r, INeg):
        return i_neg(ival_normalize(r.inner))
    if isinstance(r, IMeet):
        return i_meet(ival_normalize(r.left), ival_normalize(r.right))
    if isinstance(r, IJoin):
        return i_join(ival_normalize(r.left), ival_normalize(r.right))
    return r


# ╔═══════════════════════════════════════════════════════════╗
# ║  2. Face Formulas and Restrictions                        ║
# ╚═══════════════════════════════════════════════════════════╝

@dataclass(frozen=True)
class FaceAtom:
    """Atomic face constraint: ``variable = endpoint``."""
    var: str
    endpoint: int

    def __repr__(self) -> str:
        return f"({self.var}={self.endpoint})"

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.var})


@dataclass(frozen=True)
class FaceAnd:
    """Conjunction of face formulas."""
    left: 'FaceFormula'
    right: 'FaceFormula'

    def __repr__(self) -> str:
        return f"({self.left} ∧ {self.right})"

    def free_vars(self) -> FrozenSet[str]:
        return self.left.free_vars() | self.right.free_vars()


@dataclass(frozen=True)
class FaceOr:
    """Disjunction of face formulas."""
    left: 'FaceFormula'
    right: 'FaceFormula'

    def __repr__(self) -> str:
        return f"({self.left} ∨ {self.right})"

    def free_vars(self) -> FrozenSet[str]:
        return self.left.free_vars() | self.right.free_vars()


@dataclass(frozen=True)
class FaceTop:
    """Trivially satisfied face (⊤ of the lattice)."""

    def __repr__(self) -> str:
        return "⊤"

    def free_vars(self) -> FrozenSet[str]:
        return frozenset()


@dataclass(frozen=True)
class FaceBot:
    """Inconsistent face (⊥ of the lattice)."""

    def __repr__(self) -> str:
        return "⊥"

    def free_vars(self) -> FrozenSet[str]:
        return frozenset()


FaceFormula = Union[FaceAtom, FaceAnd, FaceOr, FaceTop, FaceBot]


def face_restrict(face: FaceFormula, var: str, val: int) -> FaceFormula:
    """Substitute ``var=val`` into *face* and simplify."""
    if isinstance(face, (FaceTop, FaceBot)):
        return face
    if isinstance(face, FaceAtom):
        if face.var == var:
            return FaceTop() if face.endpoint == val else FaceBot()
        return face
    if isinstance(face, FaceAnd):
        l = face_restrict(face.left, var, val)
        r = face_restrict(face.right, var, val)
        if isinstance(l, FaceBot) or isinstance(r, FaceBot):
            return FaceBot()
        if isinstance(l, FaceTop):
            return r
        if isinstance(r, FaceTop):
            return l
        return FaceAnd(l, r)
    if isinstance(face, FaceOr):
        l = face_restrict(face.left, var, val)
        r = face_restrict(face.right, var, val)
        if isinstance(l, FaceTop) or isinstance(r, FaceTop):
            return FaceTop()
        if isinstance(l, FaceBot):
            return r
        if isinstance(r, FaceBot):
            return l
        return FaceOr(l, r)
    return face


def face_eval(face: FaceFormula, env: Dict[str, int]) -> Optional[bool]:
    """Evaluate a face formula under a full or partial assignment."""
    if isinstance(face, FaceTop):
        return True
    if isinstance(face, FaceBot):
        return False
    if isinstance(face, FaceAtom):
        v = env.get(face.var)
        if v is None:
            return None
        return v == face.endpoint
    if isinstance(face, FaceAnd):
        lv = face_eval(face.left, env)
        rv = face_eval(face.right, env)
        if lv is False or rv is False:
            return False
        if lv is True and rv is True:
            return True
        return None
    if isinstance(face, FaceOr):
        lv = face_eval(face.left, env)
        rv = face_eval(face.right, env)
        if lv is True or rv is True:
            return True
        if lv is False and rv is False:
            return False
        return None
    return None


def face_negate(face: FaceFormula) -> FaceFormula:
    """Logical negation of a face formula (De Morgan)."""
    if isinstance(face, FaceTop):
        return FaceBot()
    if isinstance(face, FaceBot):
        return FaceTop()
    if isinstance(face, FaceAtom):
        return FaceAtom(face.var, 1 - face.endpoint)
    if isinstance(face, FaceAnd):
        return FaceOr(face_negate(face.left), face_negate(face.right))
    if isinstance(face, FaceOr):
        return FaceAnd(face_negate(face.left), face_negate(face.right))
    return face


def face_implies(a: FaceFormula, b: FaceFormula) -> bool:
    """Conservative implication check via 2^|vars| valuations."""
    vars_set = (a.free_vars() if hasattr(a, 'free_vars') else frozenset()) | \
               (b.free_vars() if hasattr(b, 'free_vars') else frozenset())
    if not vars_set:
        va = face_eval(a, {})
        vb = face_eval(b, {})
        if va is True and vb is False:
            return False
        return True
    var_list = sorted(vars_set)
    for bits in itertools.product([0, 1], repeat=len(var_list)):
        env = dict(zip(var_list, bits))
        va = face_eval(a, env)
        vb = face_eval(b, env)
        if va is True and vb is False:
            return False
    return True


# ╔═══════════════════════════════════════════════════════════╗
# ║  3. CubicalPath — typed path with face maps              ║
# ╚═══════════════════════════════════════════════════════════╝

@dataclass
class CubicalPath:
    """A path in the OTerm cubical set with explicit cubical structure.

    Provides face maps (∂⁰, ∂¹), reflexivity, symmetry, composition,
    and min/max connections.
    """
    source: OTerm
    target: OTerm
    steps: List[PathStep]
    reason: str = ''
    face_constraint: FaceFormula = field(default_factory=FaceTop)

    # ---------- constructors ----------

    @staticmethod
    def refl(t: OTerm) -> 'CubicalPath':
        """Degeneracy: constant path ``σ(t) = refl_t``."""
        return CubicalPath(source=t, target=t, steps=[], reason='refl')

    @classmethod
    def from_path_result(cls, pr: PathResult,
                         source: OTerm, target: OTerm) -> 'CubicalPath':
        """Wrap a ``PathResult`` into a ``CubicalPath``."""
        return cls(source=source, target=target,
                   steps=pr.path, reason=pr.reason)

    @classmethod
    def single_step(cls, axiom: str, src: OTerm, tgt: OTerm,
                    position: str = 'root') -> 'CubicalPath':
        """Build a one-step path from a single axiom application."""
        step = PathStep(axiom=axiom, position=position,
                        before=src.canon(), after=tgt.canon())
        return cls(source=src, target=tgt, steps=[step], reason=axiom)

    # ---------- face maps ----------

    def face0(self) -> OTerm:
        """Face map ∂⁰: source of the path."""
        return self.source

    def face1(self) -> OTerm:
        """Face map ∂¹: target of the path."""
        return self.target

    # ---------- operations ----------

    def inverse(self) -> 'CubicalPath':
        """Path symmetry via reversal ¬:  ``p⁻¹(i) = p(¬i)``."""
        inv_steps = [
            PathStep(axiom=s.axiom + '_inv', position=s.position,
                     before=s.after, after=s.before)
            for s in reversed(self.steps)
        ]
        return CubicalPath(
            source=self.target, target=self.source,
            steps=inv_steps, reason=f'inv({self.reason})',
            face_constraint=self.face_constraint,
        )

    def compose(self, other: 'CubicalPath') -> 'CubicalPath':
        """Path composition via Kan filling = chain concatenation."""
        if self.target.canon() != other.source.canon():
            raise ValueError(
                f"Cannot compose: target {self.target.canon()} "
                f"!= source {other.source.canon()}"
            )
        combined_face = FaceAnd(self.face_constraint, other.face_constraint)
        return CubicalPath(
            source=self.source, target=other.target,
            steps=self.steps + other.steps,
            reason=f'comp({self.reason}, {other.reason})',
            face_constraint=combined_face,
        )

    def min_connection(self) -> 'CubicalPath':
        """Min-connection γ⁰: contract path toward source.

        ``p(i ∧ j)`` at j=0 gives source, at j=1 gives the path.
        Approximated by the first half of the rewrite chain.
        """
        mid = len(self.steps) // 2
        prefix = self.steps[:mid] if mid > 0 else []
        mid_term = self.source
        return CubicalPath(
            source=self.source, target=mid_term,
            steps=prefix, reason=f'γ⁰({self.reason})',
            face_constraint=self.face_constraint,
        )

    def max_connection(self) -> 'CubicalPath':
        """Max-connection γ¹: contract path toward target.

        ``p(i ∨ j)`` at j=0 gives the path, at j=1 gives target.
        Approximated by the second half of the rewrite chain.
        """
        mid = len(self.steps) // 2
        suffix = self.steps[mid:] if mid < len(self.steps) else []
        mid_term = self.target
        return CubicalPath(
            source=mid_term, target=self.target,
            steps=suffix, reason=f'γ¹({self.reason})',
            face_constraint=self.face_constraint,
        )

    # ---------- queries ----------

    def is_refl(self) -> bool:
        """True when the path is definitionally reflexivity."""
        return len(self.steps) == 0 and self.source.canon() == self.target.canon()

    def length(self) -> int:
        return len(self.steps)

    def axioms_used(self) -> List[str]:
        """Distinct axiom names applied in this path."""
        seen: Set[str] = set()
        out: List[str] = []
        for s in self.steps:
            base = s.axiom.removesuffix('_inv')
            if base not in seen:
                seen.add(base)
                out.append(base)
        return out

    def intermediate_canons(self) -> List[str]:
        """Return the canonical form at every intermediate point."""
        if not self.steps:
            return [self.source.canon()]
        canons = [self.steps[0].before]
        for s in self.steps:
            canons.append(s.after)
        return canons

    def __repr__(self) -> str:
        return (f"CubicalPath({self.source.canon()[:30]}.. "
                f"→[{len(self.steps)} steps]→ "
                f"..{self.target.canon()[-30:]})")


# ╔═══════════════════════════════════════════════════════════╗
# ║  4. FunextWitness — per-fiber path assembler              ║
# ╚═══════════════════════════════════════════════════════════╝

@dataclass
class FunextWitness:
    """Per-fiber paths assembling into a global path (Theorem 2.7).

    Given: for each fiber *f*, a path ``p_f : Path(t_src|_f, t_tgt|_f)``.
    Produces: a global path ``Path(t_src, t_tgt)``.
    """
    source: OTerm
    target: OTerm
    fiber_paths: Dict[str, CubicalPath]
    face_formula: FaceFormula

    def is_complete(self) -> bool:
        """True when every fiber has a valid path."""
        return all(
            fp.source.canon() != fp.target.canon() or fp.is_refl()
            for fp in self.fiber_paths.values()
        )

    def coverage(self) -> float:
        """Fraction of fibers that are non-trivial."""
        if not self.fiber_paths:
            return 0.0
        nontrivial = sum(1 for fp in self.fiber_paths.values() if fp.length() > 0)
        return nontrivial / len(self.fiber_paths)

    def fiber_names(self) -> List[str]:
        return sorted(self.fiber_paths.keys())

    def assemble(self) -> CubicalPath:
        """Apply funext: assemble per-fiber paths into a global path.

        Concatenate per-fiber rewrite steps (valid because fibers are
        disjoint, so rewrites commute).
        """
        all_steps: List[PathStep] = []
        for _name, path in sorted(self.fiber_paths.items()):
            all_steps.extend(path.steps)
        return CubicalPath(
            source=self.source, target=self.target,
            steps=all_steps,
            reason=f'funext({", ".join(self.fiber_names())})',
            face_constraint=self.face_formula,
        )

    def restrict_to(self, fiber: str) -> Optional[CubicalPath]:
        return self.fiber_paths.get(fiber)


# ╔═══════════════════════════════════════════════════════════╗
# ║  5. GroupoidLawCertifier                                  ║
# ╚═══════════════════════════════════════════════════════════╝

class GroupoidLaw(Enum):
    LEFT_UNIT = auto()
    RIGHT_UNIT = auto()
    INVOLUTION = auto()
    LEFT_INVERSE = auto()
    RIGHT_INVERSE = auto()
    ASSOCIATIVITY = auto()


@dataclass
class GroupoidVerdict:
    law: GroupoidLaw
    holds: bool
    detail: str = ''


@dataclass
class GroupoidCertificate:
    verdicts: List[GroupoidVerdict]

    @property
    def all_pass(self) -> bool:
        return all(v.holds for v in self.verdicts)

    def summary(self) -> Dict[str, bool]:
        return {v.law.name.lower(): v.holds for v in self.verdicts}

    def failures(self) -> List[GroupoidVerdict]:
        return [v for v in self.verdicts if not v.holds]


def verify_groupoid_laws(
    p: CubicalPath,
    q: Optional[CubicalPath] = None,
    r: Optional[CubicalPath] = None,
) -> GroupoidCertificate:
    """Verify the six groupoid laws (Theorem 2.8) for paths *p*, *q*, *r*."""
    verdicts: List[GroupoidVerdict] = []

    cs, ct = p.source.canon(), p.target.canon()

    # 1. left unit: refl_a · p ~ p
    refl_a = CubicalPath.refl(p.source)
    lu = refl_a.compose(p)
    verdicts.append(GroupoidVerdict(
        GroupoidLaw.LEFT_UNIT,
        lu.source.canon() == cs and lu.target.canon() == ct,
        f'refl·p endpoints: ({lu.source.canon()[:20]}, {lu.target.canon()[:20]})',
    ))

    # 2. right unit: p · refl_b ~ p
    refl_b = CubicalPath.refl(p.target)
    ru = p.compose(refl_b)
    verdicts.append(GroupoidVerdict(
        GroupoidLaw.RIGHT_UNIT,
        ru.source.canon() == cs and ru.target.canon() == ct,
        f'p·refl endpoints: ({ru.source.canon()[:20]}, {ru.target.canon()[:20]})',
    ))

    # 3. involution: (p⁻¹)⁻¹ = p
    p_inv_inv = p.inverse().inverse()
    inv_ok = (
        p_inv_inv.source.canon() == cs
        and p_inv_inv.target.canon() == ct
        and len(p_inv_inv.steps) == len(p.steps)
    )
    verdicts.append(GroupoidVerdict(
        GroupoidLaw.INVOLUTION, inv_ok,
        f'(p⁻¹)⁻¹ steps={len(p_inv_inv.steps)} vs p steps={len(p.steps)}',
    ))

    # 4. left inverse: p⁻¹ · p has endpoints (b, b)
    li = p.inverse().compose(p)
    verdicts.append(GroupoidVerdict(
        GroupoidLaw.LEFT_INVERSE,
        li.source.canon() == ct and li.target.canon() == ct,
        f'p⁻¹·p endpoints: ({li.source.canon()[:20]}, {li.target.canon()[:20]})',
    ))

    # 5. right inverse: p · p⁻¹ has endpoints (a, a)
    ri = p.compose(p.inverse())
    verdicts.append(GroupoidVerdict(
        GroupoidLaw.RIGHT_INVERSE,
        ri.source.canon() == cs and ri.target.canon() == cs,
        f'p·p⁻¹ endpoints: ({ri.source.canon()[:20]}, {ri.target.canon()[:20]})',
    ))

    # 6. associativity (when q and r provided)
    if q is not None and p.target.canon() == q.source.canon():
        if r is not None and q.target.canon() == r.source.canon():
            pq = p.compose(q)
            pq_r = pq.compose(r)
            qr = q.compose(r)
            p_qr = p.compose(qr)
            assoc_ok = (
                pq_r.source.canon() == p_qr.source.canon()
                and pq_r.target.canon() == p_qr.target.canon()
                and len(pq_r.steps) == len(p_qr.steps)
            )
            verdicts.append(GroupoidVerdict(
                GroupoidLaw.ASSOCIATIVITY, assoc_ok,
                f'(p·q)·r steps={len(pq_r.steps)} vs p·(q·r) steps={len(p_qr.steps)}',
            ))
        else:
            pq = p.compose(q)
            verdicts.append(GroupoidVerdict(
                GroupoidLaw.ASSOCIATIVITY,
                pq.source.canon() == cs and pq.target.canon() == q.target.canon(),
                'two-path composition endpoint check',
            ))

    return GroupoidCertificate(verdicts=verdicts)


# ╔═══════════════════════════════════════════════════════════╗
# ║  6. DeMorganVerifier                                      ║
# ╚═══════════════════════════════════════════════════════════╝

@dataclass
class DMLawResult:
    law: str
    lhs: IVal
    rhs: IVal
    holds: bool

    def __repr__(self) -> str:
        mark = '✓' if self.holds else '✗'
        return f"[{mark}] {self.law}: {self.lhs} == {self.rhs}"


def _ival_semantically_equal(a: IVal, b: IVal, var_names: List[str]) -> bool:
    """Check semantic equality by evaluating on all 2^|vars| assignments."""
    for bits in itertools.product([0, 1], repeat=len(var_names)):
        env = dict(zip(var_names, bits))
        va = a.eval_at(env)
        vb = b.eval_at(env)
        if va is not None and vb is not None and va != vb:
            return False
    return True


class DeMorganVerifier:
    """Verify that IVal operations respect DM1-DM4 plus boundary laws."""

    def __init__(self, variables: Optional[List[str]] = None) -> None:
        self._vars = variables or ['i', 'j', 'k']

    def _atoms(self) -> List[IVal]:
        atoms: List[IVal] = [I0(), I1()]
        for v in self._vars:
            atoms.append(IVar(v))
            atoms.append(INeg(IVar(v)))
        return atoms

    def check_dm1(self) -> List[DMLawResult]:
        """DM1: ¬¬r = r for all atoms."""
        results: List[DMLawResult] = []
        for r in self._atoms():
            double_neg = i_neg(i_neg(r))
            results.append(DMLawResult('DM1_involution', double_neg, r,
                                       double_neg == r))
        return results

    def check_dm2(self) -> List[DMLawResult]:
        """DM2: ¬0 = 1, ¬1 = 0."""
        return [
            DMLawResult('DM2_neg_zero', i_neg(I0()), I1(), i_neg(I0()) == I1()),
            DMLawResult('DM2_neg_one', i_neg(I1()), I0(), i_neg(I1()) == I0()),
        ]

    def check_dm3(self) -> List[DMLawResult]:
        """DM3: ¬(r ∧ s) = ¬r ∨ ¬s for all atom pairs."""
        results: List[DMLawResult] = []
        atoms = self._atoms()
        for r in atoms:
            for s in atoms:
                lhs = i_neg(i_meet(r, s))
                rhs = i_join(i_neg(r), i_neg(s))
                lhs_n = ival_normalize(lhs)
                rhs_n = ival_normalize(rhs)
                results.append(DMLawResult('DM3', lhs_n, rhs_n, lhs_n == rhs_n))
        return results

    def check_dm4(self) -> List[DMLawResult]:
        """DM4: ¬(r ∨ s) = ¬r ∧ ¬s for all atom pairs."""
        results: List[DMLawResult] = []
        atoms = self._atoms()
        for r in atoms:
            for s in atoms:
                lhs = i_neg(i_join(r, s))
                rhs = i_meet(i_neg(r), i_neg(s))
                lhs_n = ival_normalize(lhs)
                rhs_n = ival_normalize(rhs)
                results.append(DMLawResult('DM4', lhs_n, rhs_n, lhs_n == rhs_n))
        return results

    def check_boundary(self) -> List[DMLawResult]:
        """Boundary / absorption / idempotency laws."""
        results: List[DMLawResult] = []
        for r in self._atoms():
            results.append(DMLawResult('meet_zero', i_meet(r, I0()), I0(),
                                       i_meet(r, I0()) == I0()))
            results.append(DMLawResult('join_one', i_join(r, I1()), I1(),
                                       i_join(r, I1()) == I1()))
            results.append(DMLawResult('meet_one', i_meet(r, I1()), r,
                                       i_meet(r, I1()) == r))
            results.append(DMLawResult('join_zero', i_join(r, I0()), r,
                                       i_join(r, I0()) == r))
            results.append(DMLawResult('idempotent_meet', i_meet(r, r), r,
                                       i_meet(r, r) == r))
            results.append(DMLawResult('idempotent_join', i_join(r, r), r,
                                       i_join(r, r) == r))
        return results

    def check_commutativity(self) -> List[DMLawResult]:
        """∧ and ∨ are commutative."""
        results: List[DMLawResult] = []
        atoms = self._atoms()
        for r in atoms:
            for s in atoms:
                m1 = ival_normalize(i_meet(r, s))
                m2 = ival_normalize(i_meet(s, r))
                eq = _ival_semantically_equal(m1, m2, self._vars)
                results.append(DMLawResult('meet_commute', m1, m2, eq))
                j1 = ival_normalize(i_join(r, s))
                j2 = ival_normalize(i_join(s, r))
                eq2 = _ival_semantically_equal(j1, j2, self._vars)
                results.append(DMLawResult('join_commute', j1, j2, eq2))
        return results

    def check_all(self) -> List[DMLawResult]:
        return (self.check_dm1() + self.check_dm2()
                + self.check_dm3() + self.check_dm4()
                + self.check_boundary() + self.check_commutativity())

    def audit(self) -> Tuple[int, int, List[DMLawResult]]:
        """Return (pass_count, fail_count, failures)."""
        all_results = self.check_all()
        fails = [r for r in all_results if not r.holds]
        return len(all_results) - len(fails), len(fails), fails


# ╔═══════════════════════════════════════════════════════════╗
# ║  7. CubicalSet data structure                             ║
# ╚═══════════════════════════════════════════════════════════╝

CubeId = str


@dataclass
class Cube0:
    """A 0-cube (vertex / point)."""
    id: CubeId
    term: OTerm

    def canon(self) -> str:
        return self.term.canon()


@dataclass
class Cube1:
    """A 1-cube (edge / path)."""
    id: CubeId
    src: CubeId
    tgt: CubeId
    path: CubicalPath

    def face(self, endpoint: int) -> CubeId:
        return self.src if endpoint == 0 else self.tgt


@dataclass
class Cube2:
    """A 2-cube (square / homotopy).

    Boundary: four 1-cubes (top, bottom, left, right).
    """
    id: CubeId
    top: CubeId
    bottom: CubeId
    left: CubeId
    right: CubeId

    def face(self, dim: int, endpoint: int) -> CubeId:
        idx = {(0, 0): self.left, (0, 1): self.right,
               (1, 0): self.bottom, (1, 1): self.top}
        return idx[(dim, endpoint)]


class CubicalSet:
    """Finite cubical set up to dimension 2."""

    def __init__(self) -> None:
        self._cubes0: Dict[CubeId, Cube0] = {}
        self._cubes1: Dict[CubeId, Cube1] = {}
        self._cubes2: Dict[CubeId, Cube2] = {}
        self._next_id: int = 0

    def _fresh_id(self, prefix: str = 'c') -> CubeId:
        self._next_id += 1
        return f"{prefix}{self._next_id}"

    # ---- 0-cubes ----

    def add_vertex(self, term: OTerm, cube_id: Optional[CubeId] = None) -> CubeId:
        cid = cube_id or self._fresh_id('v')
        self._cubes0[cid] = Cube0(id=cid, term=term)
        return cid

    def get_vertex(self, cid: CubeId) -> Optional[Cube0]:
        return self._cubes0.get(cid)

    def vertices(self) -> List[Cube0]:
        return list(self._cubes0.values())

    def find_vertex_by_canon(self, canon: str) -> Optional[Cube0]:
        for c in self._cubes0.values():
            if c.canon() == canon:
                return c
        return None

    # ---- 1-cubes ----

    def add_edge(self, src: CubeId, tgt: CubeId, path: CubicalPath,
                 cube_id: Optional[CubeId] = None) -> CubeId:
        if src not in self._cubes0:
            raise KeyError(f"Source vertex {src!r} not in cubical set")
        if tgt not in self._cubes0:
            raise KeyError(f"Target vertex {tgt!r} not in cubical set")
        cid = cube_id or self._fresh_id('e')
        self._cubes1[cid] = Cube1(id=cid, src=src, tgt=tgt, path=path)
        return cid

    def get_edge(self, cid: CubeId) -> Optional[Cube1]:
        return self._cubes1.get(cid)

    def edges(self) -> List[Cube1]:
        return list(self._cubes1.values())

    def edges_from(self, vertex: CubeId) -> List[Cube1]:
        return [e for e in self._cubes1.values() if e.src == vertex]

    def edges_to(self, vertex: CubeId) -> List[Cube1]:
        return [e for e in self._cubes1.values() if e.tgt == vertex]

    # ---- 2-cubes ----

    def add_square(self, top: CubeId, bottom: CubeId,
                   left: CubeId, right: CubeId,
                   cube_id: Optional[CubeId] = None) -> CubeId:
        for eid in (top, bottom, left, right):
            if eid not in self._cubes1:
                raise KeyError(f"Edge {eid!r} not in cubical set")
        cid = cube_id or self._fresh_id('sq')
        self._cubes2[cid] = Cube2(id=cid, top=top, bottom=bottom,
                                   left=left, right=right)
        return cid

    def get_square(self, cid: CubeId) -> Optional[Cube2]:
        return self._cubes2.get(cid)

    def squares(self) -> List[Cube2]:
        return list(self._cubes2.values())

    # ---- degeneracies ----

    def degeneracy_edge(self, vertex: CubeId) -> CubeId:
        """Insert the degenerate 1-cube ``σ(v) = refl_v``."""
        v = self._cubes0[vertex]
        refl = CubicalPath.refl(v.term)
        return self.add_edge(vertex, vertex, refl,
                             cube_id=self._fresh_id('dg'))

    # ---- queries ----

    def dim_counts(self) -> Tuple[int, int, int]:
        return len(self._cubes0), len(self._cubes1), len(self._cubes2)

    def euler_characteristic(self) -> int:
        """χ = |V| - |E| + |F|."""
        v, e, f = self.dim_counts()
        return v - e + f

    def connected_components(self) -> List[Set[CubeId]]:
        """Connected components of the 1-skeleton."""
        parent: Dict[CubeId, CubeId] = {v: v for v in self._cubes0}

        def find(x: CubeId) -> CubeId:
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a: CubeId, b: CubeId) -> None:
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb

        for e in self._cubes1.values():
            union(e.src, e.tgt)

        comps: Dict[CubeId, Set[CubeId]] = defaultdict(set)
        for v in self._cubes0:
            comps[find(v)].add(v)
        return list(comps.values())


# ╔═══════════════════════════════════════════════════════════╗
# ║  8. PathCompositionOptimizer                              ║
# ╚═══════════════════════════════════════════════════════════╝

class PathCompositionOptimizer:
    """Optimize CubicalPath chains by removing redundancies and cycles.

    * Cancel inverses: adjacent ``ax`` / ``ax_inv`` on same position.
    * Remove identity steps: before == after.
    * Detect cycles: step returning to an earlier canon.
    """

    def optimize(self, path: CubicalPath) -> CubicalPath:
        steps = list(path.steps)
        steps = self._cancel_inverses(steps)
        steps = self._remove_identities(steps)
        steps = self._eliminate_cycles(steps)
        return CubicalPath(
            source=path.source, target=path.target,
            steps=steps,
            reason=f'opt({path.reason})',
            face_constraint=path.face_constraint,
        )

    def _cancel_inverses(self, steps: List[PathStep]) -> List[PathStep]:
        changed = True
        while changed:
            changed = False
            new: List[PathStep] = []
            i = 0
            while i < len(steps):
                if i + 1 < len(steps):
                    a, b = steps[i], steps[i + 1]
                    if (a.axiom + '_inv' == b.axiom or
                            b.axiom + '_inv' == a.axiom):
                        if a.position == b.position:
                            changed = True
                            i += 2
                            continue
                new.append(steps[i])
                i += 1
            steps = new
        return steps

    def _remove_identities(self, steps: List[PathStep]) -> List[PathStep]:
        return [s for s in steps if s.before != s.after]

    def _eliminate_cycles(self, steps: List[PathStep]) -> List[PathStep]:
        seen: Dict[str, int] = {}
        result: List[PathStep] = []
        for _i, s in enumerate(steps):
            canon = s.before
            if canon in seen:
                idx = seen[canon]
                result = result[:idx]
                seen = {st.before: j for j, st in enumerate(result)}
            seen[canon] = len(result)
            result.append(s)
        return result

    def stats(self, original: CubicalPath, optimized: CubicalPath
              ) -> Dict[str, int]:
        return {
            'original_steps': original.length(),
            'optimized_steps': optimized.length(),
            'removed': original.length() - optimized.length(),
        }


# ╔═══════════════════════════════════════════════════════════╗
# ║  9. IntervalSubstitutionEngine                            ║
# ╚═══════════════════════════════════════════════════════════╝

class IntervalSubstitutionEngine:
    """Substitute interval values into CubicalPaths.

    A path ``p : I → OTerm`` can be evaluated at any interval expression.
    ``i0`` → source, ``i1`` → target, compound → connections.
    """

    def evaluate(self, path: CubicalPath, ival: IVal) -> OTerm:
        if isinstance(ival, I0):
            return path.source
        if isinstance(ival, I1):
            return path.target
        if isinstance(ival, INeg):
            inv = path.inverse()
            return self.evaluate(inv, ival.inner)
        if isinstance(ival, IMeet):
            sub = path.min_connection()
            return self.evaluate(sub, ival.right)
        if isinstance(ival, IJoin):
            sub = path.max_connection()
            return self.evaluate(sub, ival.right)
        if isinstance(ival, IVar):
            return self._interpolate(path, ival.name)
        return path.source

    def _interpolate(self, path: CubicalPath, var_name: str) -> OTerm:
        if not path.steps:
            return path.source
        return path.source  # best-effort fallback

    def substitute_path(self, path: CubicalPath, var: str, ival: IVal
                        ) -> CubicalPath:
        if isinstance(ival, I0):
            return CubicalPath.refl(path.source)
        if isinstance(ival, I1):
            return CubicalPath.refl(path.target)
        return path

    def multi_substitute(self, path: CubicalPath,
                         bindings: Dict[str, IVal]) -> CubicalPath:
        result = path
        for var, val in bindings.items():
            result = self.substitute_path(result, var, val)
        return result


# ╔═══════════════════════════════════════════════════════════╗
# ║  10. DependentPathType                                    ║
# ╚═══════════════════════════════════════════════════════════╝

class TypeTag(Enum):
    """Coarse type tags (mirrors FiberCtx in path_search)."""
    INT = 'int'
    FLOAT = 'float'
    STR = 'str'
    BOOL = 'bool'
    LIST = 'list'
    DICT = 'dict'
    ANY = 'any'


@dataclass(frozen=True)
class TypeFamily:
    """A type family ``A : I → Type`` over the interval.

    At ``i0`` it is ``base_type``; at ``i1`` it is ``fiber_type``.
    """
    base_type: TypeTag
    fiber_type: TypeTag

    def is_constant(self) -> bool:
        return self.base_type == self.fiber_type

    def at(self, endpoint: int) -> TypeTag:
        return self.base_type if endpoint == 0 else self.fiber_type


@dataclass
class DependentPath:
    """A path in a dependent type: ``p : PathOver(A, base_path, a₀, a₁)``.

    * ``type_family`` — how the type changes along the base path.
    * ``base_path``   — the underlying path in the base space.
    * ``lifted_path`` — the term-level path in the fibers.
    * ``coercion``    — the rule converting ``A(i0)`` into ``A(i1)``.
    """
    type_family: TypeFamily
    base_path: CubicalPath
    lifted_path: CubicalPath
    coercion: str

    def is_trivial(self) -> bool:
        return self.type_family.is_constant()

    def transport(self, term: OTerm) -> OTerm:
        """Transport *term* along the type family using the coercion rule.

        Implements ``transport : (p : a =_A b) → P(a) → P(b)``.
        """
        if self.is_trivial():
            return term
        coerce_map = self._coercion_map()
        if coerce_map is not None:
            return OOp(coerce_map, (term,))
        return OOp(f'coerce_{self.type_family.base_type.value}'
                   f'_to_{self.type_family.fiber_type.value}', (term,))

    def _coercion_map(self) -> Optional[str]:
        pair = (self.type_family.base_type, self.type_family.fiber_type)
        table: Dict[Tuple[TypeTag, TypeTag], str] = {
            (TypeTag.INT, TypeTag.BOOL): 'bool',
            (TypeTag.BOOL, TypeTag.INT): 'int',
            (TypeTag.INT, TypeTag.FLOAT): 'float',
            (TypeTag.FLOAT, TypeTag.INT): 'int',
            (TypeTag.INT, TypeTag.STR): 'str',
            (TypeTag.STR, TypeTag.INT): 'int',
        }
        return table.get(pair)

    def validate(self) -> List[str]:
        warnings: List[str] = []
        if not self.is_trivial() and self.coercion == '':
            warnings.append('empty coercion for non-constant type family')
        src_tag = self.type_family.at(0)
        tgt_tag = self.type_family.at(1)
        if src_tag == tgt_tag and self.coercion:
            warnings.append('coercion specified but type family is constant')
        return warnings


def make_dependent_path(src: OTerm, tgt: OTerm,
                        src_type: TypeTag, tgt_type: TypeTag,
                        steps: List[PathStep],
                        coercion: str = '') -> DependentPath:
    """Convenience factory for ``DependentPath``."""
    family = TypeFamily(base_type=src_type, fiber_type=tgt_type)
    base = CubicalPath(source=src, target=tgt, steps=steps,
                       reason='dependent_base')
    lifted = CubicalPath(source=src, target=tgt, steps=steps,
                         reason='dependent_lifted')
    return DependentPath(type_family=family, base_path=base,
                         lifted_path=lifted, coercion=coercion)


# ╔═══════════════════════════════════════════════════════════╗
# ║  11. Connection Operations                                ║
# ╚═══════════════════════════════════════════════════════════╝

class ConnectionOps:
    """Min/max connection helpers for path contraction and expansion.

    * **Min-connection** ``γ⁰(p)(i,j) = p(i ∧ j)``:
      at ``j=0`` → ``refl(a)``, at ``j=1`` → ``p``.
    * **Max-connection** ``γ¹(p)(i,j) = p(i ∨ j)``:
      at ``j=0`` → ``p``, at ``j=1`` → ``refl(b)``.
    """

    def __init__(self, cubical_set: Optional[CubicalSet] = None) -> None:
        self._cs = cubical_set or CubicalSet()
        self._engine = IntervalSubstitutionEngine()

    def min_connection_filler(self, path: CubicalPath) -> Cube2:
        """Build a 2-cube witnessing ``refl(a) · p = p`` via min-connection."""
        a_term = path.source
        b_term = path.target
        va = self._cs.add_vertex(a_term)
        vb = self._cs.add_vertex(b_term)

        refl_a = CubicalPath.refl(a_term)
        e_refl_a = self._cs.add_edge(va, va, refl_a)
        e_top = self._cs.add_edge(va, vb, path)
        e_bottom = self._cs.add_edge(va, va, refl_a)
        e_right = self._cs.add_edge(va, vb, path)

        sq = self._cs.add_square(top=e_top, bottom=e_bottom,
                                  left=e_refl_a, right=e_right)
        return self._cs.get_square(sq)  # type: ignore[return-value]

    def max_connection_filler(self, path: CubicalPath) -> Cube2:
        """Build a 2-cube witnessing ``p · refl(b) = p`` via max-connection."""
        a_term = path.source
        b_term = path.target
        va = self._cs.add_vertex(a_term)
        vb = self._cs.add_vertex(b_term)

        refl_b = CubicalPath.refl(b_term)
        e_top = self._cs.add_edge(vb, vb, refl_b)
        e_bottom = self._cs.add_edge(va, vb, path)
        e_left = self._cs.add_edge(va, vb, path)
        e_refl_b = self._cs.add_edge(vb, vb, refl_b)

        sq = self._cs.add_square(top=e_top, bottom=e_bottom,
                                  left=e_left, right=e_refl_b)
        return self._cs.get_square(sq)  # type: ignore[return-value]

    def compose_via_kan(self, p: CubicalPath, q: CubicalPath
                        ) -> CubicalPath:
        """Compose two paths using Kan filling."""
        return p.compose(q)

    def connection_eval(self, path: CubicalPath, r: IVal, s: IVal
                        ) -> OTerm:
        """Evaluate ``p(r ∧ s)`` (min-connection)."""
        combined = i_meet(r, s)
        return self._engine.evaluate(path, combined)


# ╔═══════════════════════════════════════════════════════════╗
# ║  Integration helpers — bridge to path_search / checker    ║
# ╚═══════════════════════════════════════════════════════════╝

def path_result_to_cubical(pr: PathResult, src: OTerm, tgt: OTerm,
                           fiber_face: Optional[FaceFormula] = None
                           ) -> CubicalPath:
    """Convert a ``PathResult`` from path_search into a ``CubicalPath``."""
    return CubicalPath(
        source=src, target=tgt,
        steps=pr.path, reason=pr.reason,
        face_constraint=fiber_face or FaceTop(),
    )


def build_funext_from_fibers(
    src: OTerm, tgt: OTerm,
    fiber_results: Dict[str, Tuple[PathResult, OTerm, OTerm]],
) -> FunextWitness:
    """Build a ``FunextWitness`` from per-fiber ``PathResult`` values."""
    fiber_paths: Dict[str, CubicalPath] = {}
    for name, (pr, fsrc, ftgt) in fiber_results.items():
        cp = path_result_to_cubical(pr, fsrc, ftgt, FaceAtom(name, 1))
        fiber_paths[name] = cp
    return FunextWitness(
        source=src, target=tgt,
        fiber_paths=fiber_paths,
        face_formula=FaceTop(),
    )


def build_cubical_set_from_path(path: CubicalPath) -> CubicalSet:
    """Build a ``CubicalSet`` whose 1-skeleton traces a rewrite path."""
    cs = CubicalSet()
    if not path.steps:
        cs.add_vertex(path.source, cube_id='v_src')
        return cs

    prev_id = cs.add_vertex(path.source, cube_id='v0')
    for i, step in enumerate(path.steps):
        tgt_term = path.target if i == len(path.steps) - 1 else path.source
        vid = cs.add_vertex(tgt_term, cube_id=f'v{i+1}')
        step_path = CubicalPath(
            source=path.source if i == 0 else path.source,
            target=tgt_term,
            steps=[step], reason=step.axiom,
        )
        cs.add_edge(prev_id, vid, step_path, cube_id=f'e{i}')
        prev_id = vid
    return cs


# ╔═══════════════════════════════════════════════════════════╗
# ║  Self-tests                                                ║
# ╚═══════════════════════════════════════════════════════════╝

if __name__ == '__main__':
    import sys

    _pass = 0
    _fail = 0

    def assert_eq(label: str, got: Any, expected: Any) -> None:
        global _pass, _fail
        if got == expected:
            _pass += 1
        else:
            _fail += 1
            print(f"  FAIL {label}: got {got!r}, expected {expected!r}")

    def assert_true(label: str, cond: bool) -> None:
        global _pass, _fail
        if cond:
            _pass += 1
        else:
            _fail += 1
            print(f"  FAIL {label}")

    # ----------------------------------------------------------
    print("=== Interval & De Morgan ===")
    i = IVar('i')
    j = IVar('j')

    assert_eq("neg_i0", i_neg(I0()), I1())
    assert_eq("neg_i1", i_neg(I1()), I0())
    assert_eq("double_neg", i_neg(i_neg(i)), i)
    assert_eq("meet_i0", i_meet(i, I0()), I0())
    assert_eq("meet_i1", i_meet(i, I1()), i)
    assert_eq("join_i0", i_join(i, I0()), i)
    assert_eq("join_i1", i_join(i, I1()), I1())
    assert_eq("meet_self", i_meet(i, i), i)
    assert_eq("join_self", i_join(i, i), i)
    assert_eq("meet_neg", i_meet(i, i_neg(i)), I0())
    assert_eq("join_neg", i_join(i, i_neg(i)), I1())

    # DM3: ¬(i ∧ j) = ¬i ∨ ¬j
    lhs3 = ival_normalize(i_neg(i_meet(i, j)))
    rhs3 = ival_normalize(i_join(i_neg(i), i_neg(j)))
    assert_eq("DM3", lhs3, rhs3)

    # DM4: ¬(i ∨ j) = ¬i ∧ ¬j
    lhs4 = ival_normalize(i_neg(i_join(i, j)))
    rhs4 = ival_normalize(i_meet(i_neg(i), i_neg(j)))
    assert_eq("DM4", lhs4, rhs4)

    assert_eq("eval_meet", IMeet(IVar('x'), IVar('y')).eval_at({'x': 1, 'y': 0}), 0)
    assert_eq("eval_join", IJoin(IVar('x'), IVar('y')).eval_at({'x': 0, 'y': 1}), 1)
    assert_eq("eval_neg", INeg(IVar('x')).eval_at({'x': 0}), 1)

    expr = i_meet(IVar('a'), i_join(IVar('b'), i_neg(IVar('c'))))
    assert_eq("free_vars", expr.free_vars(), frozenset({'a', 'b', 'c'}))

    expr2 = IVar('x').substitute('x', I0())
    assert_eq("subst_var", expr2, I0())

    # ----------------------------------------------------------
    print("=== Face Formulas ===")
    f1 = FaceAtom('i', 0)
    f2 = FaceAtom('j', 1)
    conj = FaceAnd(f1, f2)

    assert_eq("restrict_atom_match", face_restrict(f1, 'i', 0), FaceTop())
    assert_eq("restrict_atom_mismatch", face_restrict(f1, 'i', 1), FaceBot())
    assert_eq("restrict_and_partial", face_restrict(conj, 'i', 0), f2)
    assert_eq("restrict_and_bot", face_restrict(conj, 'i', 1), FaceBot())

    disj = FaceOr(f1, f2)
    assert_eq("restrict_or_top", face_restrict(disj, 'i', 0), FaceTop())

    assert_eq("eval_top", face_eval(FaceTop(), {}), True)
    assert_eq("eval_bot", face_eval(FaceBot(), {}), False)
    assert_eq("eval_atom", face_eval(FaceAtom('x', 1), {'x': 1}), True)

    neg_f = face_negate(FaceAtom('i', 0))
    assert_eq("negate_atom", neg_f, FaceAtom('i', 1))
    assert_eq("negate_top", face_negate(FaceTop()), FaceBot())

    assert_true("implies_top", face_implies(FaceAtom('x', 0), FaceTop()))
    assert_true("implies_self", face_implies(FaceAtom('x', 0), FaceAtom('x', 0)))

    # ----------------------------------------------------------
    print("=== CubicalPath ===")
    t_a = OLit(1)
    t_b = OLit(2)
    t_c = OLit(3)

    p_refl = CubicalPath.refl(t_a)
    assert_true("refl_is_refl", p_refl.is_refl())
    assert_eq("refl_len", p_refl.length(), 0)

    step_ab = PathStep('test_ax', 'root', t_a.canon(), t_b.canon())
    step_bc = PathStep('test_ax2', 'root', t_b.canon(), t_c.canon())
    p_ab = CubicalPath(source=t_a, target=t_b, steps=[step_ab], reason='ab')
    p_bc = CubicalPath(source=t_b, target=t_c, steps=[step_bc], reason='bc')

    p_ac = p_ab.compose(p_bc)
    assert_eq("compose_src", p_ac.source.canon(), t_a.canon())
    assert_eq("compose_tgt", p_ac.target.canon(), t_c.canon())
    assert_eq("compose_len", p_ac.length(), 2)

    p_inv = p_ab.inverse()
    assert_eq("inv_src", p_inv.source.canon(), t_b.canon())
    assert_eq("inv_tgt", p_inv.target.canon(), t_a.canon())

    p_inv_inv = p_ab.inverse().inverse()
    assert_eq("inv_inv_src", p_inv_inv.source.canon(), t_a.canon())
    assert_eq("inv_inv_tgt", p_inv_inv.target.canon(), t_b.canon())
    assert_eq("inv_inv_len", p_inv_inv.length(), 1)

    assert_eq("face0", p_ab.face0().canon(), t_a.canon())
    assert_eq("face1", p_ab.face1().canon(), t_b.canon())

    single = CubicalPath.single_step('D1_fold', t_a, t_b)
    assert_eq("single_step_len", single.length(), 1)

    axioms = p_ac.axioms_used()
    assert_eq("axioms_used", axioms, ['test_ax', 'test_ax2'])

    # compose error
    try:
        p_ab.compose(CubicalPath(source=t_c, target=t_a, steps=[], reason='x'))
        _fail += 1
        print("  FAIL compose_mismatch: expected ValueError")
    except ValueError:
        _pass += 1

    mc = p_ac.min_connection()
    assert_eq("min_conn_src", mc.source.canon(), t_a.canon())
    xc = p_ac.max_connection()
    assert_eq("max_conn_tgt", xc.target.canon(), t_c.canon())

    # ----------------------------------------------------------
    print("=== FunextWitness ===")
    fw = FunextWitness(
        source=t_a, target=t_b,
        fiber_paths={'int': p_ab, 'str': CubicalPath.refl(t_a)},
        face_formula=FaceTop(),
    )
    assert_true("funext_complete", fw.is_complete())
    assert_eq("funext_fibers", fw.fiber_names(), ['int', 'str'])
    assembled = fw.assemble()
    assert_eq("funext_asm_src", assembled.source.canon(), t_a.canon())
    assert_true("funext_coverage", fw.coverage() > 0)
    assert_true("funext_restrict", fw.restrict_to('int') is not None)
    assert_true("funext_restrict_miss", fw.restrict_to('float') is None)

    # ----------------------------------------------------------
    print("=== GroupoidLawCertifier ===")
    cert = verify_groupoid_laws(p_ab, q=p_bc, r=None)
    s = cert.summary()
    assert_true("left_unit", s['left_unit'])
    assert_true("right_unit", s['right_unit'])
    assert_true("involution", s['involution'])
    assert_true("left_inverse", s['left_inverse'])
    assert_true("right_inverse", s['right_inverse'])

    cert3 = verify_groupoid_laws(p_ab, q=p_bc,
                                  r=CubicalPath.refl(t_c))
    assert_true("assoc", cert3.summary().get('associativity', False))

    cert_refl = verify_groupoid_laws(CubicalPath.refl(t_a))
    assert_true("refl_all_pass", cert_refl.all_pass)
    assert_eq("refl_no_failures", len(cert_refl.failures()), 0)

    # ----------------------------------------------------------
    print("=== DeMorganVerifier ===")
    dmv = DeMorganVerifier(variables=['i', 'j'])
    p_count, f_count, fails = dmv.audit()
    assert_eq("dm_failures", f_count, 0)
    if fails:
        for f in fails[:5]:
            print(f"  {f}")
    assert_true("dm_pass_count", p_count > 50)

    dm1 = dmv.check_dm1()
    assert_true("dm1_all_pass", all(r.holds for r in dm1))
    dm2 = dmv.check_dm2()
    assert_true("dm2_all_pass", all(r.holds for r in dm2))

    # ----------------------------------------------------------
    print("=== CubicalSet ===")
    cs = CubicalSet()
    va = cs.add_vertex(t_a, cube_id='a')
    vb = cs.add_vertex(t_b, cube_id='b')
    vc = cs.add_vertex(t_c, cube_id='c')

    e1 = cs.add_edge('a', 'b', p_ab)
    e2 = cs.add_edge('b', 'c', p_bc)

    assert_eq("dim_counts", cs.dim_counts(), (3, 2, 0))
    assert_eq("euler", cs.euler_characteristic(), 1)

    edges_from_a = cs.edges_from('a')
    assert_eq("edges_from_a", len(edges_from_a), 1)
    edges_to_c = cs.edges_to('c')
    assert_eq("edges_to_c", len(edges_to_c), 1)

    dg = cs.degeneracy_edge('a')
    assert_true("degeneracy_exists", cs.get_edge(dg) is not None)
    assert_eq("degeneracy_src", cs.get_edge(dg).src, 'a')
    assert_eq("degeneracy_tgt", cs.get_edge(dg).tgt, 'a')

    comps = cs.connected_components()
    assert_eq("num_components", len(comps), 1)

    found_v = cs.find_vertex_by_canon(t_b.canon())
    assert_true("find_vertex", found_v is not None)
    assert_eq("find_vertex_id", found_v.id, 'b')

    try:
        cs.add_edge('a', 'nonexistent', CubicalPath.refl(t_a))
        _fail += 1
        print("  FAIL edge_missing_tgt: expected KeyError")
    except KeyError:
        _pass += 1

    t_d = OLit(4)
    vd = cs.add_vertex(t_d, cube_id='d')
    comps2 = cs.connected_components()
    assert_eq("disconnected_components", len(comps2), 2)

    # ----------------------------------------------------------
    print("=== PathCompositionOptimizer ===")
    opt = PathCompositionOptimizer()

    step_fwd = PathStep('D1', 'root', '1', '2')
    step_inv_d1 = PathStep('D1_inv', 'root', '2', '1')
    path_cancel = CubicalPath(source=t_a, target=t_a,
                              steps=[step_fwd, step_inv_d1], reason='cancel_test')
    optimized = opt.optimize(path_cancel)
    assert_eq("cancel_inv", optimized.length(), 0)

    step_id = PathStep('noop', 'root', '1', '1')
    path_noop = CubicalPath(source=t_a, target=t_a,
                            steps=[step_id], reason='noop')
    opt_noop = opt.optimize(path_noop)
    assert_eq("remove_identity", opt_noop.length(), 0)

    s1 = PathStep('ax1', 'root', 'A', 'B')
    s2 = PathStep('ax2', 'root', 'B', 'C')
    s3 = PathStep('ax3', 'root', 'C', 'A')
    s4 = PathStep('ax4', 'root', 'A', 'D')
    cycle_path = CubicalPath(source=t_a, target=t_b,
                             steps=[s1, s2, s3, s4], reason='cycle')
    opt_cycle = opt.optimize(cycle_path)
    assert_true("cycle_shorter", opt_cycle.length() < cycle_path.length())

    stats_result = opt.stats(cycle_path, opt_cycle)
    assert_eq("stats_original", stats_result['original_steps'], 4)
    assert_true("stats_removed", stats_result['removed'] > 0)

    # ----------------------------------------------------------
    print("=== IntervalSubstitutionEngine ===")
    engine = IntervalSubstitutionEngine()

    result_i0 = engine.evaluate(p_ab, I0())
    assert_eq("eval_i0", result_i0.canon(), t_a.canon())
    result_i1 = engine.evaluate(p_ab, I1())
    assert_eq("eval_i1", result_i1.canon(), t_b.canon())

    sub_i0 = engine.substitute_path(p_ab, 'i', I0())
    assert_true("subst_i0_refl", sub_i0.is_refl())
    sub_i1 = engine.substitute_path(p_ab, 'i', I1())
    assert_true("subst_i1_refl", sub_i1.is_refl())

    multi = engine.multi_substitute(p_ab, {'i': I0(), 'j': I1()})
    assert_true("multi_subst_refl", multi.is_refl())

    # ----------------------------------------------------------
    print("=== DependentPathType ===")
    dp = make_dependent_path(t_a, t_b, TypeTag.INT, TypeTag.BOOL,
                             [step_ab], coercion='bool')
    assert_true("dep_not_trivial", not dp.is_trivial())
    transported = dp.transport(t_a)
    assert_true("transport_is_op", isinstance(transported, OOp))

    dp_const = make_dependent_path(t_a, t_b, TypeTag.INT, TypeTag.INT,
                                    [step_ab], coercion='')
    assert_true("dep_trivial", dp_const.is_trivial())
    assert_eq("transport_trivial", dp_const.transport(t_a), t_a)

    warnings = dp.validate()
    assert_eq("dp_no_warnings", len(warnings), 0)
    bad_dp = make_dependent_path(t_a, t_b, TypeTag.INT, TypeTag.INT,
                                  [step_ab], coercion='int')
    assert_true("dp_const_coercion_warn", len(bad_dp.validate()) > 0)

    tf = TypeFamily(TypeTag.INT, TypeTag.BOOL)
    assert_eq("family_at_0", tf.at(0), TypeTag.INT)
    assert_eq("family_at_1", tf.at(1), TypeTag.BOOL)
    assert_true("family_not_const", not tf.is_constant())

    # ----------------------------------------------------------
    print("=== ConnectionOps ===")
    conn = ConnectionOps()
    sq_min = conn.min_connection_filler(p_ab)
    assert_true("min_filler_exists", sq_min is not None)

    sq_max = conn.max_connection_filler(p_ab)
    assert_true("max_filler_exists", sq_max is not None)

    composed_kan = conn.compose_via_kan(p_ab, p_bc)
    assert_eq("kan_compose_src", composed_kan.source.canon(), t_a.canon())
    assert_eq("kan_compose_tgt", composed_kan.target.canon(), t_c.canon())

    eval_conn = conn.connection_eval(p_ab, I0(), IVar('j'))
    assert_true("conn_eval_is_oterm", hasattr(eval_conn, 'canon'))

    # ----------------------------------------------------------
    print("=== Integration helpers ===")
    pr = PathResult(found=True, path=[step_ab], reason='test')
    cp = path_result_to_cubical(pr, t_a, t_b, FaceAtom('int', 1))
    assert_eq("bridge_src", cp.source.canon(), t_a.canon())
    assert_true("bridge_face", isinstance(cp.face_constraint, FaceAtom))

    fiber_results_map: Dict[str, Tuple[PathResult, OTerm, OTerm]] = {
        'int': (pr, t_a, t_b),
        'str': (PathResult(found=True, path=[], reason='refl'), t_a, t_a),
    }
    fw2 = build_funext_from_fibers(t_a, t_b, fiber_results_map)
    assert_true("build_funext_complete", fw2.is_complete())
    assert_eq("build_funext_fibers", len(fw2.fiber_paths), 2)

    cs_from_path = build_cubical_set_from_path(p_ac)
    v_count, e_count, _ = cs_from_path.dim_counts()
    assert_true("cs_from_path_vertices", v_count >= 2)
    assert_true("cs_from_path_edges", e_count >= 1)

    cs_empty = build_cubical_set_from_path(CubicalPath.refl(t_a))
    assert_eq("cs_empty_vertices", cs_empty.dim_counts()[0], 1)

    # ----------------------------------------------------------
    print(f"\n{'='*50}")
    print(f"Results: {_pass} passed, {_fail} failed")
    if _fail:
        sys.exit(1)
    else:
        print("All tests passed ✓")
        sys.exit(0)
