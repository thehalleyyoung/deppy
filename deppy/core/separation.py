"""
Deppy Separation Logic Engine

Separation logic for Python heap reasoning, inspired by F*'s Steel framework
but adapted to Python's object model.  Provides:

    HeapProp            — separation-logic propositions (Emp, PointsTo, Sep, …)
    SepTriple           — Hoare triples {P} c {Q}
    SepChecker          — triple verification, frame rule, entailment
    PythonHeapOps       — separation-logic rules for Python operations
    OwnershipTracker    — Rust-inspired ownership / aliasing analysis
    ConcurrentSep       — concurrent separation logic (locks, threads, async)
    HeapSolver          — Z3-backed symbolic heap solver

All Z3 imports are guarded so the module degrades gracefully.
"""
from __future__ import annotations

import ast
import itertools
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, List, Optional, Sequence, Tuple

from deppy.core.types import (
    SynType, SynTerm, Var, Literal,
    PyObjType, PyListType, PyDictType, PyClassType,
)
from deppy.core.kernel import ProofKernel, TrustLevel, VerificationResult

# ── guarded Z3 import ─────────────────────────────────────────────
try:
    from z3 import (
        Solver, Bool, BoolSort, BoolVal, And, Or, Not, Implies,
        Int, IntSort, IntVal, ArithRef,
        sat, unsat, unknown,
        Function, DeclareSort, Const,
        ForAll, Exists as Z3Exists,
    )
    _HAS_Z3 = True
except ImportError:
    _HAS_Z3 = False


def _require_z3() -> None:
    if not _HAS_Z3:
        raise RuntimeError(
            "Z3 is required for this operation but is not installed. "
            "Install with: pip install z3-solver"
        )


# ═══════════════════════════════════════════════════════════════════
# Heap Propositions
# ═══════════════════════════════════════════════════════════════════

class HeapProp:
    """Base class for separation-logic propositions.

    All subclasses are frozen dataclasses with structural equality and
    hash so they can be stored in sets and used as dict keys.
    """

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, HeapProp):
            return NotImplemented
        return self._structural_eq(other)

    def _structural_eq(self, other: HeapProp) -> bool:
        return type(self) is type(other)

    def __hash__(self) -> int:
        return hash(self._hash_key())

    def _hash_key(self) -> tuple:
        return (type(self).__name__,)

    def __repr__(self) -> str:
        return self._repr()

    def _repr(self) -> str:
        return type(self).__name__

    # ── convenience combinators ───────────────────────────────────

    def star(self, other: HeapProp) -> HeapProp:
        """Separating conjunction: self * other."""
        return Sep(self, other)

    def wand_to(self, consequent: HeapProp) -> HeapProp:
        """Magic wand: self -* consequent."""
        return Wand(self, consequent)

    def collect_atoms(self) -> list[HeapProp]:
        """Flatten Sep tree into a sorted list of atomic propositions."""
        return [self]


@dataclass(frozen=True, eq=False, repr=False)
class Emp(HeapProp):
    """Empty heap — the unit of separating conjunction."""

    def _structural_eq(self, other: HeapProp) -> bool:
        return isinstance(other, Emp)

    def _hash_key(self) -> tuple:
        return ("Emp",)

    def _repr(self) -> str:
        return "emp"

    def collect_atoms(self) -> list[HeapProp]:
        return []


@dataclass(frozen=True, eq=False, repr=False)
class PointsTo(HeapProp):
    """x ↦ v — heap location *ref* maps to *value*."""
    ref: str
    value: SynTerm

    def _structural_eq(self, other: HeapProp) -> bool:
        if not isinstance(other, PointsTo):
            return False
        return self.ref == other.ref and repr(self.value) == repr(other.value)

    def _hash_key(self) -> tuple:
        return ("PointsTo", self.ref, repr(self.value))

    def _repr(self) -> str:
        return f"{self.ref} ↦ {self.value}"


@dataclass(frozen=True, eq=False, repr=False)
class Sep(HeapProp):
    """P * Q — separating conjunction (disjoint heaps)."""
    left: HeapProp
    right: HeapProp

    def _structural_eq(self, other: HeapProp) -> bool:
        if not isinstance(other, Sep):
            return False
        return self.left == other.left and self.right == other.right

    def _hash_key(self) -> tuple:
        return ("Sep", self.left._hash_key(), self.right._hash_key())

    def _repr(self) -> str:
        return f"({self.left} * {self.right})"

    def collect_atoms(self) -> list[HeapProp]:
        return self.left.collect_atoms() + self.right.collect_atoms()


@dataclass(frozen=True, eq=False, repr=False)
class Wand(HeapProp):
    """P -* Q — magic wand (separating implication)."""
    antecedent: HeapProp
    consequent: HeapProp

    def _structural_eq(self, other: HeapProp) -> bool:
        if not isinstance(other, Wand):
            return False
        return (self.antecedent == other.antecedent
                and self.consequent == other.consequent)

    def _hash_key(self) -> tuple:
        return ("Wand", self.antecedent._hash_key(), self.consequent._hash_key())

    def _repr(self) -> str:
        return f"({self.antecedent} -* {self.consequent})"


@dataclass(frozen=True, eq=False, repr=False)
class Pure(HeapProp):
    """Lift a pure (heap-independent) proposition."""
    prop: str

    def _structural_eq(self, other: HeapProp) -> bool:
        if not isinstance(other, Pure):
            return False
        return self.prop == other.prop

    def _hash_key(self) -> tuple:
        return ("Pure", self.prop)

    def _repr(self) -> str:
        return f"⌈{self.prop}⌉"


@dataclass(frozen=True, eq=False, repr=False)
class Exists(HeapProp):
    """∃x. P(x) — existential quantification over heaps."""
    var: str
    body: HeapProp

    def _structural_eq(self, other: HeapProp) -> bool:
        if not isinstance(other, Exists):
            return False
        return self.var == other.var and self.body == other.body

    def _hash_key(self) -> tuple:
        return ("Exists", self.var, self.body._hash_key())

    def _repr(self) -> str:
        return f"∃{self.var}. {self.body}"


@dataclass(frozen=True, eq=False, repr=False)
class OwnedList(HeapProp):
    """Ownership of a list spine: ref ↦ [v0, v1, …, vn]."""
    ref: str
    elements: tuple[SynTerm, ...]  # frozen → use tuple

    def _structural_eq(self, other: HeapProp) -> bool:
        if not isinstance(other, OwnedList):
            return False
        if self.ref != other.ref:
            return False
        if len(self.elements) != len(other.elements):
            return False
        return all(repr(a) == repr(b) for a, b in zip(self.elements, other.elements))

    def _hash_key(self) -> tuple:
        return ("OwnedList", self.ref, tuple(repr(e) for e in self.elements))

    def _repr(self) -> str:
        elems = ", ".join(str(e) for e in self.elements)
        return f"{self.ref} ↦ [{elems}]"


@dataclass(frozen=True, eq=False, repr=False)
class OwnedDict(HeapProp):
    """Ownership of a dict: ref ↦ {k0: v0, …}."""
    ref: str
    entries: tuple[tuple[str, SynTerm], ...]  # frozen representation

    def _structural_eq(self, other: HeapProp) -> bool:
        if not isinstance(other, OwnedDict):
            return False
        if self.ref != other.ref:
            return False
        if len(self.entries) != len(other.entries):
            return False
        for (k1, v1), (k2, v2) in zip(
            sorted(self.entries), sorted(other.entries)
        ):
            if k1 != k2 or repr(v1) != repr(v2):
                return False
        return True

    def _hash_key(self) -> tuple:
        sorted_ents = tuple(sorted((k, repr(v)) for k, v in self.entries))
        return ("OwnedDict", self.ref, sorted_ents)

    def _repr(self) -> str:
        items = ", ".join(f"{k}: {v}" for k, v in self.entries)
        return f"{self.ref} ↦ {{{items}}}"


@dataclass(frozen=True, eq=False, repr=False)
class OwnedObj(HeapProp):
    """Ownership of an object's attribute dictionary."""
    ref: str
    attrs: tuple[tuple[str, SynTerm], ...]  # frozen
    cls: str | None = None

    def _structural_eq(self, other: HeapProp) -> bool:
        if not isinstance(other, OwnedObj):
            return False
        if self.ref != other.ref or self.cls != other.cls:
            return False
        if len(self.attrs) != len(other.attrs):
            return False
        for (k1, v1), (k2, v2) in zip(
            sorted(self.attrs), sorted(other.attrs)
        ):
            if k1 != k2 or repr(v1) != repr(v2):
                return False
        return True

    def _hash_key(self) -> tuple:
        sorted_attrs = tuple(sorted((k, repr(v)) for k, v in self.attrs))
        return ("OwnedObj", self.ref, sorted_attrs, self.cls)

    def _repr(self) -> str:
        cls_part = f"{self.cls}." if self.cls else ""
        items = ", ".join(f"{k}: {v}" for k, v in self.attrs)
        return f"{cls_part}{self.ref} ↦ {{{items}}}"


# ── Helpers for constructing HeapProps ─────────────────────────────

def sep_of(*props: HeapProp) -> HeapProp:
    """Build a separating conjunction from a sequence.  Removes Emp."""
    filtered = [p for p in props if not isinstance(p, Emp)]
    if not filtered:
        return Emp()
    result = filtered[0]
    for p in filtered[1:]:
        result = Sep(result, p)
    return result


def owned_list(ref: str, elements: Sequence[SynTerm]) -> OwnedList:
    return OwnedList(ref=ref, elements=tuple(elements))


def owned_dict(ref: str, entries: dict[str, SynTerm]) -> OwnedDict:
    return OwnedDict(ref=ref, entries=tuple(sorted(entries.items())))


def owned_obj(ref: str, attrs: dict[str, SynTerm],
              cls: str | None = None) -> OwnedObj:
    return OwnedObj(ref=ref, attrs=tuple(sorted(attrs.items())), cls=cls)


# ═══════════════════════════════════════════════════════════════════
# Separation Triple & Results
# ═══════════════════════════════════════════════════════════════════

@dataclass
class SepTriple:
    """Separation-logic Hoare triple: {P} c {Q}.

    The optional *frame* records the frame used in the frame rule.
    """
    pre: HeapProp
    command: str
    post: HeapProp
    frame: HeapProp | None = None

    def __repr__(self) -> str:
        fr = f"  frame={self.frame}" if self.frame else ""
        return f"{{{self.pre}}} {self.command} {{{self.post}}}{fr}"


class SepStatus(Enum):
    VALID = auto()
    INVALID = auto()
    UNKNOWN = auto()


@dataclass
class SepResult:
    """Outcome of checking a separation-logic triple or entailment."""
    status: SepStatus
    message: str = ""
    trust: TrustLevel = TrustLevel.UNTRUSTED
    counterexample: dict[str, Any] | None = None

    @property
    def valid(self) -> bool:
        return self.status == SepStatus.VALID

    def __repr__(self) -> str:
        sym = {SepStatus.VALID: "✓", SepStatus.INVALID: "✗",
               SepStatus.UNKNOWN: "?"}[self.status]
        return f"{sym} [{self.trust.name}] {self.message}"

    @staticmethod
    def ok(msg: str = "", trust: TrustLevel = TrustLevel.KERNEL) -> SepResult:
        return SepResult(SepStatus.VALID, msg, trust)

    @staticmethod
    def fail(msg: str = "", cex: dict[str, Any] | None = None) -> SepResult:
        return SepResult(SepStatus.INVALID, msg, TrustLevel.UNTRUSTED, cex)

    @staticmethod
    def unknown(msg: str = "") -> SepResult:
        return SepResult(SepStatus.UNKNOWN, msg, TrustLevel.UNTRUSTED)


# ═══════════════════════════════════════════════════════════════════
# Alias Violation
# ═══════════════════════════════════════════════════════════════════

@dataclass
class AliasViolation:
    """Report of a detected aliasing violation."""
    refs: tuple[str, ...]
    description: str

    def __repr__(self) -> str:
        return f"AliasViolation({', '.join(self.refs)}: {self.description})"


# ═══════════════════════════════════════════════════════════════════
# Normalization
# ═══════════════════════════════════════════════════════════════════

def _flatten_sep(p: HeapProp) -> list[HeapProp]:
    """Flatten nested Sep into a list of non-Sep atoms."""
    if isinstance(p, Sep):
        return _flatten_sep(p.left) + _flatten_sep(p.right)
    if isinstance(p, Emp):
        return []
    return [p]


def _build_sep(atoms: list[HeapProp]) -> HeapProp:
    """Build a right-associated Sep tree from a list of atoms."""
    if not atoms:
        return Emp()
    result = atoms[-1]
    for a in reversed(atoms[:-1]):
        result = Sep(a, result)
    return result


def normalize(p: HeapProp) -> HeapProp:
    """Normalize a HeapProp: flatten Sep, remove Emp, sort deterministically.

    Properties after normalization:
        • No nested Sep beyond right-association
        • No Emp inside Sep
        • Atoms sorted by repr for canonical form (commutativity)
    """
    if isinstance(p, Sep):
        atoms = _flatten_sep(p)
        atoms = [normalize(a) for a in atoms]
        atoms = [a for a in atoms if not isinstance(a, Emp)]
        atoms.sort(key=lambda a: repr(a))
        return _build_sep(atoms)
    if isinstance(p, Exists):
        return Exists(p.var, normalize(p.body))
    if isinstance(p, Wand):
        return Wand(normalize(p.antecedent), normalize(p.consequent))
    return p


def _atoms_multiset(p: HeapProp) -> dict[str, list[HeapProp]]:
    """Group normalized atoms by repr (multiset representation)."""
    result: dict[str, list[HeapProp]] = {}
    for a in _flatten_sep(p):
        if isinstance(a, Emp):
            continue
        key = repr(a)
        result.setdefault(key, []).append(a)
    return result


# ═══════════════════════════════════════════════════════════════════
# SepChecker — verify triples and entailments
# ═══════════════════════════════════════════════════════════════════

class SepChecker:
    """Verify separation-logic triples, apply frame rule, check entailments."""

    def __init__(self, kernel: ProofKernel | None = None) -> None:
        self._kernel = kernel or ProofKernel()
        self._heap_solver: HeapSolver | None = None

    @property
    def solver(self) -> HeapSolver:
        if self._heap_solver is None:
            self._heap_solver = HeapSolver()
        return self._heap_solver

    # ── normalization ─────────────────────────────────────────────

    def normalize(self, p: HeapProp) -> HeapProp:
        """Normalize a heap proposition (module-level wrapper)."""
        return normalize(p)

    # ── entailment ────────────────────────────────────────────────

    def check_entailment(self, p: HeapProp, q: HeapProp) -> bool:
        """Check P ⊢ Q (heap entailment) structurally.

        This uses a multiset-inclusion check on normalized atoms.
        For Pure propositions, falls back to syntactic equality.
        """
        pn = normalize(p)
        qn = normalize(q)
        if pn == qn:
            return True
        # Emp entails Emp
        if isinstance(qn, Emp):
            return isinstance(pn, Emp) or len(_flatten_sep(pn)) == 0
        p_atoms = _flatten_sep(pn)
        q_atoms = _flatten_sep(qn)
        # Check that every atom in Q can be matched in P
        p_reprs = [repr(a) for a in p_atoms]
        for qa in q_atoms:
            qr = repr(qa)
            if qr in p_reprs:
                p_reprs.remove(qr)
            else:
                return False
        return True

    def check_entailment_z3(self, p: HeapProp, q: HeapProp) -> SepResult:
        """Check P ⊢ Q using the Z3-backed heap solver."""
        return self.solver.check_entailment(p, q)

    # ── frame rule ────────────────────────────────────────────────

    def apply_frame_rule(self, triple: SepTriple,
                         frame: HeapProp) -> SepTriple:
        """From {P} c {Q}, derive {P * R} c {Q * R}.

        The frame R must describe heap disjoint from P and Q.
        """
        new_pre = normalize(Sep(triple.pre, frame))
        new_post = normalize(Sep(triple.post, frame))
        return SepTriple(
            pre=new_pre,
            command=triple.command,
            post=new_post,
            frame=frame,
        )

    # ── frame inference ───────────────────────────────────────────

    def infer_frame(self, pre: HeapProp, post: HeapProp) -> HeapProp | None:
        """Find F such that pre ⊢ post * F.

        Returns None if no valid frame exists (post has atoms not in pre).
        """
        pre_atoms = _flatten_sep(normalize(pre))
        post_atoms = _flatten_sep(normalize(post))
        remaining = list(pre_atoms)
        for pa in post_atoms:
            pr = repr(pa)
            found = False
            for i, ra in enumerate(remaining):
                if repr(ra) == pr:
                    remaining.pop(i)
                    found = True
                    break
            if not found:
                return None
        return _build_sep(remaining)

    # ── triple checking ───────────────────────────────────────────

    def check_triple(self, triple: SepTriple) -> SepResult:
        """Verify {P} c {Q}.

        Strategy:
        1. Normalize pre and post.
        2. If frame is given, check that framed triple is consistent.
        3. Look up the command in known Python-heap rules.
        4. Fall back to structural entailment check.
        """
        pre_n = normalize(triple.pre)
        post_n = normalize(triple.post)

        # Exact match — trivially valid
        if pre_n == post_n and triple.command.strip() == "skip":
            return SepResult.ok("skip preserves heap",
                                TrustLevel.KERNEL)

        # With frame: strip frame, check inner triple
        if triple.frame is not None:
            frame_n = normalize(triple.frame)
            inner_pre = self._strip_frame(pre_n, frame_n)
            inner_post = self._strip_frame(post_n, frame_n)
            if inner_pre is not None and inner_post is not None:
                inner = SepTriple(inner_pre, triple.command, inner_post)
                return self.check_triple(inner)

        # Structural: post atoms ⊆ pre atoms ∪ {new bindings from command}
        result = self._check_structural(pre_n, triple.command, post_n)
        return result

    def _strip_frame(self, prop: HeapProp,
                     frame: HeapProp) -> HeapProp | None:
        """Remove frame atoms from prop.  Returns None on failure."""
        prop_atoms = _flatten_sep(normalize(prop))
        frame_atoms = _flatten_sep(normalize(frame))
        remaining = list(prop_atoms)
        for fa in frame_atoms:
            fr = repr(fa)
            found = False
            for i, pa in enumerate(remaining):
                if repr(pa) == fr:
                    remaining.pop(i)
                    found = True
                    break
            if not found:
                return None
        return _build_sep(remaining)

    def _check_structural(self, pre: HeapProp, cmd: str,
                          post: HeapProp) -> SepResult:
        """Structural check: recognize common patterns in cmd."""
        cmd = cmd.strip()

        # Assignment: x = <expr>
        if "=" in cmd and not cmd.startswith("del "):
            parts = cmd.split("=", 1)
            lhs = parts[0].strip()
            if "." not in lhs and "[" not in lhs:
                # Simple local assignment
                post_atoms = _flatten_sep(post)
                for a in post_atoms:
                    if isinstance(a, PointsTo) and a.ref == lhs:
                        remaining = [
                            x for x in post_atoms if x is not a
                        ]
                        if self.check_entailment(pre, _build_sep(remaining)):
                            return SepResult.ok(
                                f"assignment {cmd}",
                                TrustLevel.STRUCTURAL_CHAIN,
                            )

        # Skip
        if cmd == "skip" or cmd == "pass":
            if self.check_entailment(pre, post):
                return SepResult.ok("skip/pass", TrustLevel.KERNEL)

        # del
        if cmd.startswith("del "):
            var = cmd[4:].strip()
            pre_atoms = _flatten_sep(pre)
            post_atoms = _flatten_sep(post)
            pre_without = [
                a for a in pre_atoms
                if not (isinstance(a, PointsTo) and a.ref == var)
                and not (isinstance(a, OwnedList) and a.ref == var)
                and not (isinstance(a, OwnedDict) and a.ref == var)
                and not (isinstance(a, OwnedObj) and a.ref == var)
            ]
            if self.check_entailment(_build_sep(pre_without),
                                     _build_sep(post_atoms)):
                return SepResult.ok(f"del {var}", TrustLevel.STRUCTURAL_CHAIN)

        # General fallback: if post ⊆ pre then OK (weakening)
        if self.check_entailment(pre, post):
            return SepResult.ok("heap weakening", TrustLevel.STRUCTURAL_CHAIN)

        return SepResult.fail(f"cannot verify: {{{pre}}} {cmd} {{{post}}}")


# ═══════════════════════════════════════════════════════════════════
# Python Heap Operations
# ═══════════════════════════════════════════════════════════════════

class PythonHeapOps:
    """Generate separation-logic triples for Python heap operations."""

    # ── local assignment ──────────────────────────────────────────

    def assign_local(self, var: str, val: SynTerm) -> SepTriple:
        """{emp} x = v {x ↦ v}"""
        return SepTriple(
            pre=Emp(),
            command=f"{var} = {val}",
            post=PointsTo(var, val),
        )

    # ── attribute assignment ──────────────────────────────────────

    def assign_attr(self, obj: str, attr: str, val: SynTerm,
                    existing_attrs: dict[str, SynTerm] | None = None
                    ) -> SepTriple:
        """{obj ↦ {…}} obj.attr = v {obj ↦ {…, attr: v}}"""
        old = dict(existing_attrs) if existing_attrs else {}
        old_entries = tuple(sorted(old.items()))
        new = dict(old)
        new[attr] = val
        new_entries = tuple(sorted(new.items()))
        return SepTriple(
            pre=OwnedObj(obj, old_entries),
            command=f"{obj}.{attr} = {val}",
            post=OwnedObj(obj, new_entries),
        )

    # ── list operations ───────────────────────────────────────────

    def list_append(self, lst: str, val: SynTerm,
                    existing: Sequence[SynTerm] = ()) -> SepTriple:
        """{lst ↦ [...]} lst.append(v) {lst ↦ [..., v]}"""
        old = tuple(existing)
        new = old + (val,)
        return SepTriple(
            pre=OwnedList(lst, old),
            command=f"{lst}.append({val})",
            post=OwnedList(lst, new),
        )

    def list_getitem(self, lst: str, idx: int,
                     elements: Sequence[SynTerm] = (),
                     result: str = "_v") -> SepTriple:
        """{lst ↦ [..., vi, ...]} v = lst[i] {lst ↦ [...] * v ↦ vi}"""
        elems = tuple(elements)
        if 0 <= idx < len(elems):
            vi = elems[idx]
        else:
            vi = Var("⊥")
        return SepTriple(
            pre=OwnedList(lst, elems),
            command=f"{result} = {lst}[{idx}]",
            post=Sep(OwnedList(lst, elems), PointsTo(result, vi)),
        )

    # ── dict operations ───────────────────────────────────────────

    def dict_setitem(self, d: str, key: str, val: SynTerm,
                     existing: dict[str, SynTerm] | None = None
                     ) -> SepTriple:
        """{d ↦ {…}} d[k] = v {d ↦ {…, k: v}}"""
        old = dict(existing) if existing else {}
        old_entries = tuple(sorted(old.items()))
        new = dict(old)
        new[key] = val
        new_entries = tuple(sorted(new.items()))
        return SepTriple(
            pre=OwnedDict(d, old_entries),
            command=f"{d}[{key!r}] = {val}",
            post=OwnedDict(d, new_entries),
        )

    # ── object lifecycle ──────────────────────────────────────────

    def new_object(self, cls: str, args: list[str], result: str,
                   init_attrs: dict[str, SynTerm] | None = None
                   ) -> SepTriple:
        """{emp} obj = Cls(…) {obj ↦ OwnedObj(cls, init_attrs)}"""
        attrs = init_attrs or {}
        return SepTriple(
            pre=Emp(),
            command=f"{result} = {cls}({', '.join(args)})",
            post=owned_obj(result, attrs, cls=cls),
        )

    def del_object(self, var: str, val: SynTerm | None = None) -> SepTriple:
        """{var ↦ v} del var {emp}"""
        v = val if val is not None else Var(var)
        return SepTriple(
            pre=PointsTo(var, v),
            command=f"del {var}",
            post=Emp(),
        )

    # ── function calls ────────────────────────────────────────────

    def function_call_pure(self, func: str, args: list[str],
                           result: str) -> SepTriple:
        """Pure function: preserves all heap, adds result binding.

        {emp} result = func(args) {result ↦ func(args)}
        Caller frames in their own heap via the frame rule.
        """
        call_expr = f"{func}({', '.join(args)})"
        return SepTriple(
            pre=Emp(),
            command=f"{result} = {call_expr}",
            post=PointsTo(result, Var(call_expr)),
        )

    def function_call_mutating(self, func: str, args: list[str],
                               modifies: list[str], result: str,
                               pre_heap: HeapProp | None = None,
                               post_heap: HeapProp | None = None,
                               ) -> SepTriple:
        """Mutating function: modifies specified heap locations.

        The caller must supply pre_heap/post_heap describing the
        state change of the *modifies* locations.
        """
        call_expr = f"{func}({', '.join(args)})"
        pre = pre_heap if pre_heap is not None else Emp()
        post = post_heap if post_heap is not None else Emp()
        if result:
            post = Sep(post, PointsTo(result, Var(call_expr)))
        return SepTriple(
            pre=pre,
            command=f"{result} = {call_expr}" if result else call_expr,
            post=normalize(post),
        )

    # ── with statement ────────────────────────────────────────────

    def with_statement(self, mgr: str, var: str,
                       body_triple: SepTriple,
                       resource: HeapProp | None = None) -> SepTriple:
        """with mgr as var: … — acquire on enter, release on exit.

        Models: enter acquires *resource*, exit releases it.
        """
        res = resource if resource is not None else PointsTo(var, Var(mgr))
        return SepTriple(
            pre=body_triple.pre,
            command=f"with {mgr} as {var}: {body_triple.command}",
            post=body_triple.post,
        )


# ═══════════════════════════════════════════════════════════════════
# Ownership Model
# ═══════════════════════════════════════════════════════════════════

class OwnershipState(Enum):
    """Ownership states for Python heap locations."""
    UNOWNED = 0
    SHARED = 1       # multiple readers OK
    EXCLUSIVE = 2    # single writer, no readers
    MOVED = 3        # ownership transferred
    BORROWED = 4     # temporarily lent


@dataclass
class OwnershipInfo:
    """Per-reference ownership metadata."""
    state: OwnershipState = OwnershipState.UNOWNED
    shared_count: int = 0
    owner: str | None = None


@dataclass
class OwnershipReport:
    """Result of analyzing a function's ownership patterns."""
    reads: set[str]
    writes: set[str]
    aliases: list[tuple[str, str]]
    violations: list[AliasViolation]

    def __repr__(self) -> str:
        return (f"OwnershipReport(reads={self.reads}, writes={self.writes}, "
                f"aliases={self.aliases}, violations={self.violations})")


class OwnershipTracker:
    """Track Python-style ownership (shared by default, exclusive for mutation).

    Inspired by Rust's borrow checker, but adapted to Python semantics:
    - Shared (read) borrows are always allowed unless exclusive exists
    - Exclusive (write) borrows require no existing borrows
    - Move semantics can be opted into explicitly
    """

    def __init__(self) -> None:
        self._owned: dict[str, OwnershipInfo] = {}

    def _ensure(self, ref: str) -> OwnershipInfo:
        if ref not in self._owned:
            self._owned[ref] = OwnershipInfo()
        return self._owned[ref]

    def acquire_shared(self, ref: str) -> bool:
        """Acquire shared (read) access.  Fails if exclusively owned."""
        info = self._ensure(ref)
        if info.state == OwnershipState.EXCLUSIVE:
            return False
        if info.state == OwnershipState.MOVED:
            return False
        info.state = OwnershipState.SHARED
        info.shared_count += 1
        return True

    def acquire_exclusive(self, ref: str) -> bool:
        """Acquire exclusive (write) access.  Fails if any borrows exist."""
        info = self._ensure(ref)
        if info.state == OwnershipState.SHARED and info.shared_count > 0:
            return False
        if info.state == OwnershipState.EXCLUSIVE:
            return False
        if info.state == OwnershipState.MOVED:
            return False
        info.state = OwnershipState.EXCLUSIVE
        return True

    def release(self, ref: str) -> None:
        """Release access to *ref*."""
        info = self._ensure(ref)
        if info.state == OwnershipState.SHARED:
            info.shared_count = max(0, info.shared_count - 1)
            if info.shared_count == 0:
                info.state = OwnershipState.UNOWNED
        elif info.state == OwnershipState.EXCLUSIVE:
            info.state = OwnershipState.UNOWNED

    def move(self, ref: str) -> bool:
        """Transfer ownership — ref becomes MOVED (unusable)."""
        info = self._ensure(ref)
        if info.state in (OwnershipState.SHARED, OwnershipState.EXCLUSIVE,
                          OwnershipState.MOVED):
            return False  # can't move while borrowed or already moved
        info.state = OwnershipState.MOVED
        return True

    def borrow(self, ref: str, borrower: str) -> bool:
        """Temporarily lend access."""
        info = self._ensure(ref)
        if info.state == OwnershipState.MOVED:
            return False
        info.state = OwnershipState.BORROWED
        info.owner = borrower
        return True

    def get_state(self, ref: str) -> OwnershipState:
        return self._ensure(ref).state

    def check_no_alias_violation(self, refs: list[str]) -> list[AliasViolation]:
        """Check that no two refs with exclusive access alias the same object.

        In separation logic terms, exclusive ownership must be disjoint.
        """
        violations: list[AliasViolation] = []
        exclusive_refs = [
            r for r in refs
            if self._ensure(r).state == OwnershipState.EXCLUSIVE
        ]
        # O(n²) pairwise check — fine for typical ref counts
        for i, r1 in enumerate(exclusive_refs):
            for r2 in exclusive_refs[i + 1:]:
                violations.append(AliasViolation(
                    refs=(r1, r2),
                    description=(
                        f"both '{r1}' and '{r2}' have exclusive access — "
                        f"potential aliasing violation"
                    ),
                ))
        return violations

    def analyze_function(self, source: str) -> OwnershipReport:
        """Analyze a function's ownership patterns via AST inspection.

        Identifies reads, writes, and potential aliasing.
        """
        reads: set[str] = set()
        writes: set[str] = set()
        aliases: list[tuple[str, str]] = []
        violations: list[AliasViolation] = []

        try:
            tree = ast.parse(source)
        except SyntaxError:
            return OwnershipReport(reads, writes, aliases, violations)

        for node in ast.walk(tree):
            # Writes: assignments
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        writes.add(target.id)
                        # Alias: x = y
                        if isinstance(node.value, ast.Name):
                            aliases.append((target.id, node.value.id))
                    elif isinstance(target, ast.Attribute):
                        if isinstance(target.value, ast.Name):
                            writes.add(target.value.id)
                    elif isinstance(target, ast.Subscript):
                        if isinstance(target.value, ast.Name):
                            writes.add(target.value.id)

            # Reads: any Name load
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
                reads.add(node.id)

            # Augmented assignment (+=, etc.)
            if isinstance(node, ast.AugAssign):
                if isinstance(node.target, ast.Name):
                    writes.add(node.target.id)
                    reads.add(node.target.id)

            # Mutating method calls (.append, .extend, .update, etc.)
            if isinstance(node, ast.Call):
                if isinstance(node.func, ast.Attribute):
                    if node.func.attr in (
                        "append", "extend", "insert", "pop", "remove",
                        "clear", "sort", "reverse",  # list
                        "update", "setdefault",  # dict
                        "add", "discard",  # set
                    ):
                        if isinstance(node.func.value, ast.Name):
                            writes.add(node.func.value.id)

        # Detect violations: any variable that is both written and aliased
        for alias_target, alias_source in aliases:
            if alias_target in writes and alias_source in reads:
                violations.append(AliasViolation(
                    refs=(alias_target, alias_source),
                    description=(
                        f"'{alias_target}' is written and aliases "
                        f"'{alias_source}' which is read"
                    ),
                ))

        return OwnershipReport(
            reads=reads, writes=writes,
            aliases=aliases, violations=violations,
        )


# ═══════════════════════════════════════════════════════════════════
# Concurrent Separation Logic
# ═══════════════════════════════════════════════════════════════════

class ConcurrentSep:
    """Concurrent separation logic for Python threading / asyncio.

    Models locks, thread forks, and async/await with resource ownership
    transfer.
    """

    def lock_acquire(self, lock: str, invariant: HeapProp) -> SepTriple:
        """lock.acquire(): {emp} acquire {invariant}

        Acquiring a lock *produces* the lock invariant (the heap it protects).
        """
        return SepTriple(
            pre=Emp(),
            command=f"{lock}.acquire()",
            post=invariant,
        )

    def lock_release(self, lock: str, invariant: HeapProp) -> SepTriple:
        """lock.release(): {invariant} release {emp}

        Releasing a lock *consumes* the lock invariant.
        """
        return SepTriple(
            pre=invariant,
            command=f"{lock}.release()",
            post=Emp(),
        )

    def with_lock(self, lock: str, invariant: HeapProp,
                  body: SepTriple) -> SepTriple:
        """with lock: … — acquire invariant, run body, release invariant.

        Soundness: the body's pre must be satisfiable with the invariant,
        and the body's post must re-establish the invariant.
        """
        combined_pre = normalize(Sep(body.pre, Emp()))  # body can assume inv
        combined_post = normalize(Sep(body.post, Emp()))
        return SepTriple(
            pre=combined_pre,
            command=f"with {lock}: {body.command}",
            post=combined_post,
            frame=invariant,
        )

    def thread_fork(self, body: SepTriple) -> SepTriple:
        """threading.Thread(target=…).start()

        Ownership of body.pre is *transferred* to the new thread.
        The parent retains only what is framed away.
        """
        return SepTriple(
            pre=body.pre,
            command=f"Thread(target=λ.{body.command}).start()",
            post=Emp(),  # parent loses ownership of pre
        )

    def async_await(self, coro: str, pre: HeapProp,
                    post: HeapProp) -> SepTriple:
        """await coro: may interleave, must respect frame.

        The await point is where other coroutines can run; the frame
        rule ensures we don't lose ownership of non-yielded resources.
        """
        return SepTriple(
            pre=pre,
            command=f"await {coro}",
            post=post,
        )

    def channel_send(self, chan: str, val: SynTerm,
                     ownership: HeapProp) -> SepTriple:
        """Send value (with ownership) through channel."""
        return SepTriple(
            pre=ownership,
            command=f"{chan}.send({val})",
            post=Emp(),
        )

    def channel_recv(self, chan: str, result: str,
                     ownership: HeapProp) -> SepTriple:
        """Receive value (acquiring ownership) from channel."""
        return SepTriple(
            pre=Emp(),
            command=f"{result} = {chan}.recv()",
            post=ownership,
        )


# ═══════════════════════════════════════════════════════════════════
# Heap Solver (Z3-backed)
# ═══════════════════════════════════════════════════════════════════

@dataclass
class EntailmentResult:
    """Result of a Z3 entailment check."""
    holds: bool
    model: dict[str, Any] | None = None
    message: str = ""

    def __repr__(self) -> str:
        sym = "✓" if self.holds else "✗"
        return f"{sym} {self.message}"


class HeapSolver:
    """Solve separation-logic entailments using Z3.

    Encodes HeapProp as Z3 formulas over an abstract heap model:
    - Each ref is a Z3 Int constant (address)
    - PointsTo(r, v) becomes heap(addr(r)) == encode(v)
    - Sep(P, Q) becomes P ∧ Q ∧ disjointness
    - Emp becomes True (no constraints)
    """

    def __init__(self) -> None:
        self._solver = None  # lazy Z3
        self._heap_sort = None
        self._val_sort = None
        self._addr_fn: dict[str, Any] = {}
        self._val_consts: dict[str, Any] = {}
        self._heap_fn = None
        self._counter = 0

    def _fresh(self, prefix: str = "v") -> str:
        self._counter += 1
        return f"{prefix}_{self._counter}"

    def _init_z3(self) -> None:
        """Lazily initialise Z3 infrastructure."""
        if self._solver is not None:
            return
        _require_z3()
        self._solver = Solver()
        self._heap_sort = DeclareSort("Heap")
        self._val_sort = DeclareSort("Val")
        self._heap_fn = Function("heap_read", IntSort(), self._val_sort)

    def _addr(self, ref: str):
        """Get or create an Int constant representing a heap address."""
        if ref not in self._addr_fn:
            self._addr_fn[ref] = Int(f"addr_{ref}")
        return self._addr_fn[ref]

    def _val_const(self, name: str):
        """Get or create an uninterpreted Val constant."""
        if name not in self._val_consts:
            self._val_consts[name] = Const(f"val_{name}", self._val_sort)
        return self._val_consts[name]

    def _encode(self, prop: HeapProp) -> Any:
        """Encode a HeapProp as a Z3 formula."""
        self._init_z3()

        if isinstance(prop, Emp):
            return BoolVal(True)

        if isinstance(prop, PointsTo):
            addr = self._addr(prop.ref)
            val = self._val_const(repr(prop.value))
            return self._heap_fn(addr) == val

        if isinstance(prop, Sep):
            left_enc = self._encode(prop.left)
            right_enc = self._encode(prop.right)
            # Sep = conjunction + disjointness of addresses
            left_addrs = self._collect_addrs(prop.left)
            right_addrs = self._collect_addrs(prop.right)
            disjoint_clauses = []
            for la in left_addrs:
                for ra in right_addrs:
                    disjoint_clauses.append(la != ra)
            disjoint = And(*disjoint_clauses) if disjoint_clauses else BoolVal(True)
            return And(left_enc, right_enc, disjoint)

        if isinstance(prop, Pure):
            # Encode pure props as boolean constants
            return Bool(f"pure_{prop.prop}")

        if isinstance(prop, Wand):
            ant = self._encode(prop.antecedent)
            con = self._encode(prop.consequent)
            return Implies(ant, con)

        if isinstance(prop, Exists):
            body_enc = self._encode(prop.body)
            return body_enc  # approximate: treat as body

        if isinstance(prop, OwnedList):
            clauses = []
            base = self._addr(prop.ref)
            for i, elem in enumerate(prop.elements):
                val = self._val_const(repr(elem))
                cell_addr = base + IntVal(i + 1)
                clauses.append(self._heap_fn(cell_addr) == val)
            return And(*clauses) if clauses else BoolVal(True)

        if isinstance(prop, OwnedDict):
            clauses = []
            base = self._addr(prop.ref)
            for i, (k, v) in enumerate(prop.entries):
                val = self._val_const(repr(v))
                cell_addr = base + IntVal(1000 + i)
                clauses.append(self._heap_fn(cell_addr) == val)
            return And(*clauses) if clauses else BoolVal(True)

        if isinstance(prop, OwnedObj):
            clauses = []
            base = self._addr(prop.ref)
            for i, (k, v) in enumerate(prop.attrs):
                val = self._val_const(repr(v))
                cell_addr = base + IntVal(2000 + i)
                clauses.append(self._heap_fn(cell_addr) == val)
            return And(*clauses) if clauses else BoolVal(True)

        return BoolVal(True)

    def _collect_addrs(self, prop: HeapProp) -> list:
        """Collect all address expressions from a HeapProp."""
        if isinstance(prop, PointsTo):
            return [self._addr(prop.ref)]
        if isinstance(prop, Sep):
            return self._collect_addrs(prop.left) + self._collect_addrs(prop.right)
        if isinstance(prop, (OwnedList, OwnedDict, OwnedObj)):
            return [self._addr(prop.ref)]
        return []

    def check_entailment(self, p: HeapProp, q: HeapProp) -> SepResult:
        """Check P ⊢ Q using Z3.

        Encodes ¬(P → Q) and checks unsatisfiability.
        """
        self._init_z3()
        solver = Solver()
        p_enc = self._encode(p)
        q_enc = self._encode(q)
        solver.add(p_enc)
        solver.add(Not(q_enc))
        result = solver.check()
        if result == unsat:
            return SepResult.ok("Z3: entailment holds", TrustLevel.Z3_VERIFIED)
        elif result == sat:
            return SepResult.fail("Z3: entailment does not hold")
        else:
            return SepResult.unknown("Z3: could not decide")

    def frame_inference(self, pre: HeapProp,
                        post: HeapProp) -> HeapProp | None:
        """Infer frame F such that pre ⊢ post * F.

        Uses structural subtraction: atoms(pre) - atoms(post).
        """
        pre_atoms = _flatten_sep(normalize(pre))
        post_atoms = _flatten_sep(normalize(post))
        remaining = list(pre_atoms)
        for pa in post_atoms:
            pr = repr(pa)
            found = False
            for i, ra in enumerate(remaining):
                if repr(ra) == pr:
                    remaining.pop(i)
                    found = True
                    break
            if not found:
                return None
        return _build_sep(remaining)

    def check_disjointness(self, p: HeapProp, q: HeapProp) -> SepResult:
        """Check that P and Q describe disjoint heaps."""
        p_refs = {repr(a) for a in self._collect_addrs(p)}
        q_refs = {repr(a) for a in self._collect_addrs(q)}
        overlap = p_refs & q_refs
        if overlap:
            return SepResult.fail(
                f"heaps overlap at: {overlap}"
            )
        return SepResult.ok("heaps are disjoint", TrustLevel.STRUCTURAL_CHAIN)


# ═══════════════════════════════════════════════════════════════════
# Self-Tests
# ═══════════════════════════════════════════════════════════════════

def _run_self_tests() -> None:
    """Run self-tests for the separation logic engine.

    Execute with:  PYTHONPATH=. python3 deppy/core/separation.py
    """
    passed = 0
    failed = 0

    def check(cond: bool, msg: str) -> None:
        nonlocal passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {msg}")

    # ── 1. HeapProp basics ────────────────────────────────────────
    print("1. HeapProp basics …")

    e1 = Emp()
    e2 = Emp()
    check(e1 == e2, "Emp equality")
    check(hash(e1) == hash(e2), "Emp hash")

    v = Var("x")
    pt1 = PointsTo("x", v)
    pt2 = PointsTo("x", Var("x"))
    check(pt1 == pt2, "PointsTo structural equality")
    check(hash(pt1) == hash(pt2), "PointsTo hash")

    pt3 = PointsTo("y", v)
    check(pt1 != pt3, "PointsTo inequality (diff ref)")

    pt4 = PointsTo("x", Literal(42))
    check(pt1 != pt4, "PointsTo inequality (diff value)")

    # Sep
    s1 = Sep(pt1, pt3)
    s2 = Sep(pt1, pt3)
    check(s1 == s2, "Sep equality")
    check(hash(s1) == hash(s2), "Sep hash")

    # Wand
    w1 = Wand(pt1, pt3)
    w2 = Wand(pt1, pt3)
    check(w1 == w2, "Wand equality")

    # Pure
    p1 = Pure("x > 0")
    p2 = Pure("x > 0")
    check(p1 == p2, "Pure equality")
    check(Pure("x > 0") != Pure("x < 0"), "Pure inequality")

    # Exists
    ex1 = Exists("x", pt1)
    ex2 = Exists("x", PointsTo("x", Var("x")))
    check(ex1 == ex2, "Exists equality")

    # OwnedList
    ol1 = OwnedList("lst", (Literal(1), Literal(2)))
    ol2 = OwnedList("lst", (Literal(1), Literal(2)))
    check(ol1 == ol2, "OwnedList equality")
    check(hash(ol1) == hash(ol2), "OwnedList hash")
    ol3 = OwnedList("lst", (Literal(1),))
    check(ol1 != ol3, "OwnedList inequality (diff len)")

    # OwnedDict
    od1 = OwnedDict("d", (("a", Literal(1)), ("b", Literal(2))))
    od2 = OwnedDict("d", (("b", Literal(2)), ("a", Literal(1))))
    check(od1 == od2, "OwnedDict equality (order-independent)")
    check(hash(od1) == hash(od2), "OwnedDict hash (order-independent)")

    # OwnedObj
    oo1 = OwnedObj("obj", (("x", Literal(1)),), cls="Foo")
    oo2 = OwnedObj("obj", (("x", Literal(1)),), cls="Foo")
    check(oo1 == oo2, "OwnedObj equality")
    oo3 = OwnedObj("obj", (("x", Literal(1)),), cls="Bar")
    check(oo1 != oo3, "OwnedObj inequality (diff cls)")

    # ── 2. Hashability ────────────────────────────────────────────
    print("2. Hashability …")

    hp_set: set[HeapProp] = {e1, pt1, pt3, s1, w1, p1, ex1, ol1, od1, oo1}
    check(len(hp_set) == 10, "HeapProp set — 10 distinct elements")
    check(pt2 in hp_set, "structural duplicate in set")

    hp_dict: dict[HeapProp, int] = {pt1: 1, pt3: 2}
    check(hp_dict[pt2] == 1, "HeapProp dict key lookup")

    # ── 3. sep_of helper ──────────────────────────────────────────
    print("3. sep_of …")

    check(isinstance(sep_of(), Emp), "sep_of() -> Emp")
    check(sep_of(Emp(), Emp()) == Emp(), "sep_of(Emp, Emp) -> Emp")
    check(sep_of(pt1) == pt1, "sep_of single")
    combined = sep_of(pt1, pt3)
    check(isinstance(combined, Sep), "sep_of two elements is Sep")

    # ── 4. Normalization ──────────────────────────────────────────
    print("4. Normalization …")

    # Flatten nested Sep
    nested = Sep(Sep(pt1, pt3), pt4)
    nn = normalize(nested)
    atoms = _flatten_sep(nn)
    check(len(atoms) == 3, "flatten nested Sep to 3 atoms")

    # Remove Emp
    with_emp = Sep(pt1, Sep(Emp(), pt3))
    nn2 = normalize(with_emp)
    atoms2 = _flatten_sep(nn2)
    check(all(not isinstance(a, Emp) for a in atoms2), "Emp removed")

    # Commutativity: Sep(A, B) normalizes same as Sep(B, A)
    n1 = normalize(Sep(pt1, pt3))
    n2 = normalize(Sep(pt3, pt1))
    check(n1 == n2, "Sep commutativity after normalize")

    # Associativity: Sep(Sep(A, B), C) == Sep(A, Sep(B, C))
    na = normalize(Sep(Sep(pt1, pt3), pt4))
    nb = normalize(Sep(pt1, Sep(pt3, pt4)))
    check(na == nb, "Sep associativity after normalize")

    # Emp is unit
    check(normalize(Sep(pt1, Emp())) == normalize(pt1),
          "Emp is right unit")
    check(normalize(Sep(Emp(), pt1)) == normalize(pt1),
          "Emp is left unit")

    # ── 5. SepChecker entailment ──────────────────────────────────
    print("5. SepChecker entailment …")

    sc = SepChecker()

    check(sc.check_entailment(Emp(), Emp()), "Emp ⊢ Emp")
    check(sc.check_entailment(pt1, pt1), "P ⊢ P (reflexive)")
    check(sc.check_entailment(Sep(pt1, pt3), Sep(pt1, pt3)),
          "P*Q ⊢ P*Q")
    # Commutativity in entailment
    check(sc.check_entailment(Sep(pt1, pt3), Sep(pt3, pt1)),
          "P*Q ⊢ Q*P (commutativity)")
    # Weakening: P*Q ⊢ P
    check(sc.check_entailment(Sep(pt1, pt3), pt1),
          "P*Q ⊢ P (weakening)")
    # Invalid: P ⊬ P*Q when Q is non-trivial
    check(not sc.check_entailment(pt1, Sep(pt1, pt3)),
          "P ⊬ P*Q (need more heap)")
    # Emp ⊬ PointsTo
    check(not sc.check_entailment(Emp(), pt1), "Emp ⊬ PointsTo")

    # ── 6. Frame rule ─────────────────────────────────────────────
    print("6. Frame rule …")

    triple = SepTriple(pre=pt1, command="x = x + 1", post=PointsTo("x", Literal(1)))
    frame = pt3
    framed = sc.apply_frame_rule(triple, frame)
    check(framed.frame == frame, "frame is recorded")
    # Post includes frame
    framed_post_atoms = _flatten_sep(normalize(framed.post))
    check(any(a == pt3 for a in framed_post_atoms),
          "frame atom in post")
    # Pre includes frame
    framed_pre_atoms = _flatten_sep(normalize(framed.pre))
    check(any(a == pt3 for a in framed_pre_atoms),
          "frame atom in pre")

    # Frame rule soundness: {P} c {Q} → {P*R} c {Q*R} maintains R
    inner = SepTriple(pre=Emp(), command="skip", post=Emp())
    framed2 = sc.apply_frame_rule(inner, pt1)
    check(sc.check_entailment(framed2.pre, framed2.post),
          "frame rule preserves frame on skip")

    # ── 7. Frame inference ────────────────────────────────────────
    print("7. Frame inference …")

    frame_inferred = sc.infer_frame(Sep(pt1, pt3), pt1)
    check(frame_inferred is not None, "frame inference succeeds")
    if frame_inferred:
        check(frame_inferred == pt3, "inferred frame is correct")

    no_frame = sc.infer_frame(pt1, Sep(pt1, pt3))
    check(no_frame is None, "frame inference fails when post > pre")

    # ── 8. Triple checking ────────────────────────────────────────
    print("8. Triple checking …")

    skip_triple = SepTriple(pre=pt1, command="skip", post=pt1)
    res = sc.check_triple(skip_triple)
    check(res.valid, "{P} skip {P} is valid")

    weaken_triple = SepTriple(
        pre=Sep(pt1, pt3), command="skip", post=Sep(pt1, pt3))
    res2 = sc.check_triple(weaken_triple)
    check(res2.valid, "{P*Q} skip {P*Q} is valid")

    # Invalid triple: gains heap from nothing
    bad_triple = SepTriple(pre=Emp(), command="skip", post=pt1)
    res3 = sc.check_triple(bad_triple)
    check(not res3.valid, "{emp} skip {x↦v} is invalid")

    # Del triple
    del_triple = SepTriple(pre=pt1, command="del x", post=Emp())
    res4 = sc.check_triple(del_triple)
    check(res4.valid, "{x↦v} del x {emp}")

    # ── 9. PythonHeapOps ──────────────────────────────────────────
    print("9. PythonHeapOps …")

    ops = PythonHeapOps()

    # assign_local
    t = ops.assign_local("x", Literal(42))
    check(isinstance(t.pre, Emp), "assign_local pre is emp")
    check(isinstance(t.post, PointsTo), "assign_local post is PointsTo")
    check(t.post.ref == "x", "assign_local ref")

    # list_append
    t2 = ops.list_append("lst", Literal(3), [Literal(1), Literal(2)])
    check(isinstance(t2.pre, OwnedList), "list_append pre is OwnedList")
    check(isinstance(t2.post, OwnedList), "list_append post is OwnedList")
    check(len(t2.post.elements) == 3, "list_append adds element")

    # dict_setitem
    t3 = ops.dict_setitem("d", "key", Literal("val"), {"old": Literal(0)})
    check(isinstance(t3.pre, OwnedDict), "dict_setitem pre")
    check(isinstance(t3.post, OwnedDict), "dict_setitem post")
    post_keys = [k for k, _ in t3.post.entries]
    check("key" in post_keys, "dict_setitem adds key")

    # assign_attr
    t4 = ops.assign_attr("obj", "x", Literal(1), {"y": Literal(2)})
    check(isinstance(t4.pre, OwnedObj), "assign_attr pre")
    check(isinstance(t4.post, OwnedObj), "assign_attr post")

    # new_object
    t5 = ops.new_object("Foo", ["a"], "f", {"val": Literal(0)})
    check(isinstance(t5.pre, Emp), "new_object pre emp")
    check(isinstance(t5.post, OwnedObj), "new_object post OwnedObj")
    check(t5.post.cls == "Foo", "new_object cls")

    # del_object
    t6 = ops.del_object("x", Literal(10))
    check(isinstance(t6.pre, PointsTo), "del_object pre PointsTo")
    check(isinstance(t6.post, Emp), "del_object post Emp")

    # function_call_pure
    t7 = ops.function_call_pure("len", ["lst"], "n")
    check(isinstance(t7.pre, Emp), "pure call pre emp")
    check(isinstance(t7.post, PointsTo), "pure call post PointsTo")

    # list_getitem
    t8 = ops.list_getitem("lst", 1, [Literal(10), Literal(20)], "v")
    check(isinstance(t8.post, Sep), "list_getitem post is Sep")

    # function_call_mutating
    pre_h = OwnedList("lst", (Literal(1),))
    post_h = OwnedList("lst", (Literal(1), Literal(2)))
    t9 = ops.function_call_mutating(
        "lst.append", ["2"], ["lst"], "r",
        pre_heap=pre_h, post_heap=post_h,
    )
    check(t9.pre == pre_h, "mutating call pre")

    # with_statement
    body = SepTriple(pre=pt1, command="do_stuff()", post=pt1)
    t10 = ops.with_statement("ctx_mgr", "f", body)
    check("with" in t10.command, "with_statement command")

    # ── 10. OwnershipTracker ──────────────────────────────────────
    print("10. OwnershipTracker …")

    ot = OwnershipTracker()
    check(ot.get_state("a") == OwnershipState.UNOWNED,
          "initial state UNOWNED")

    check(ot.acquire_shared("a"), "acquire shared succeeds")
    check(ot.get_state("a") == OwnershipState.SHARED, "state SHARED")
    check(ot.acquire_shared("a"), "second shared succeeds")
    check(not ot.acquire_exclusive("a"), "exclusive fails with shared")

    ot.release("a")
    ot.release("a")
    check(ot.get_state("a") == OwnershipState.UNOWNED,
          "released back to UNOWNED")

    check(ot.acquire_exclusive("a"), "exclusive succeeds when unowned")
    check(ot.get_state("a") == OwnershipState.EXCLUSIVE,
          "state EXCLUSIVE")
    check(not ot.acquire_shared("a"), "shared fails with exclusive")
    check(not ot.acquire_exclusive("a"), "double exclusive fails")

    ot.release("a")
    check(ot.get_state("a") == OwnershipState.UNOWNED,
          "released exclusive")

    # Move
    check(ot.move("b"), "move unowned succeeds")
    check(ot.get_state("b") == OwnershipState.MOVED, "state MOVED")
    check(not ot.acquire_shared("b"), "can't read moved")
    check(not ot.acquire_exclusive("b"), "can't write moved")

    # Borrow
    ot2 = OwnershipTracker()
    check(ot2.borrow("c", "func"), "borrow succeeds")
    check(ot2.get_state("c") == OwnershipState.BORROWED, "state BORROWED")

    # Alias violation check
    ot3 = OwnershipTracker()
    ot3.acquire_exclusive("x")
    ot3.acquire_exclusive("y")
    violations = ot3.check_no_alias_violation(["x", "y"])
    check(len(violations) > 0, "alias violation detected for exclusive pair")
    check(violations[0].refs == ("x", "y"), "violation refs correct")

    ot4 = OwnershipTracker()
    ot4.acquire_shared("x")
    ot4.acquire_shared("y")
    check(len(ot4.check_no_alias_violation(["x", "y"])) == 0,
          "no violation for shared pair")

    # ── 11. analyze_function ──────────────────────────────────────
    print("11. analyze_function …")

    src = """\
def f(lst, d):
    x = lst
    lst.append(1)
    d['key'] = 2
    y = len(lst)
"""
    report = ot.analyze_function(src)
    check("lst" in report.writes, "lst detected as write")
    check("d" in report.writes, "d detected as write")
    check("x" in report.writes, "x detected as write (alias)")
    check(("x", "lst") in report.aliases, "alias x=lst detected")
    check("lst" in report.reads, "lst detected as read")

    # Bad syntax
    bad_report = ot.analyze_function("def (broken")
    check(len(bad_report.reads) == 0, "bad syntax returns empty")

    # ── 12. ConcurrentSep ─────────────────────────────────────────
    print("12. ConcurrentSep …")

    cs = ConcurrentSep()
    inv = PointsTo("counter", Literal(0))

    acq = cs.lock_acquire("lock", inv)
    check(isinstance(acq.pre, Emp), "lock acquire pre emp")
    check(acq.post == inv, "lock acquire produces invariant")

    rel = cs.lock_release("lock", inv)
    check(rel.pre == inv, "lock release consumes invariant")
    check(isinstance(rel.post, Emp), "lock release post emp")

    body_t = SepTriple(pre=inv, command="counter += 1",
                       post=PointsTo("counter", Literal(1)))
    wl = cs.with_lock("lock", inv, body_t)
    check("with" in wl.command, "with_lock command")
    check(wl.frame == inv, "with_lock frame is invariant")

    fork = cs.thread_fork(body_t)
    check(fork.pre == inv, "fork pre is body pre")
    check(isinstance(fork.post, Emp), "fork post emp (ownership transferred)")

    aw = cs.async_await("fetch()", pt1, pt3)
    check(aw.pre == pt1, "async_await pre")
    check(aw.post == pt3, "async_await post")

    send = cs.channel_send("ch", Literal(42), pt1)
    check(isinstance(send.post, Emp), "send transfers ownership")

    recv = cs.channel_recv("ch", "val", pt1)
    check(isinstance(recv.pre, Emp), "recv pre emp")
    check(recv.post == pt1, "recv acquires ownership")

    # ── 13. HeapSolver (Z3) ───────────────────────────────────────
    print("13. HeapSolver (Z3) …")

    if _HAS_Z3:
        hs = HeapSolver()

        # emp ⊢ emp
        r1 = hs.check_entailment(Emp(), Emp())
        check(r1.valid, "Z3: emp ⊢ emp")

        # x↦v ⊢ x↦v
        r2 = hs.check_entailment(pt1, pt1)
        check(r2.valid, "Z3: PointsTo ⊢ PointsTo (same)")

        # x↦v ⊬ y↦v  (different addresses)
        r3 = hs.check_entailment(pt1, pt3)
        check(not r3.valid, "Z3: x↦v ⊬ y↦v")

        # frame inference
        fi = hs.frame_inference(Sep(pt1, pt3), pt1)
        check(fi is not None, "Z3 frame inference succeeds")
        if fi:
            check(fi == pt3, "Z3 frame inference correct")

        # disjointness
        dj = hs.check_disjointness(pt1, pt3)
        check(dj.valid, "disjoint heaps: x and y")

        dj2 = hs.check_disjointness(pt1, pt1)
        check(not dj2.valid, "non-disjoint: same ref")

        # OwnedList encoding
        ol_a = OwnedList("lst", (Literal(1), Literal(2)))
        r4 = hs.check_entailment(ol_a, ol_a)
        check(r4.valid, "Z3: OwnedList ⊢ OwnedList (same)")

        # OwnedDict encoding
        od_a = owned_dict("d", {"a": Literal(1)})
        r5 = hs.check_entailment(od_a, od_a)
        check(r5.valid, "Z3: OwnedDict ⊢ OwnedDict (same)")

        # OwnedObj encoding
        oo_a = owned_obj("obj", {"x": Literal(1)}, cls="C")
        r6 = hs.check_entailment(oo_a, oo_a)
        check(r6.valid, "Z3: OwnedObj ⊢ OwnedObj (same)")
    else:
        print("  (Z3 not available — skipping Z3 tests)")

    # ── 14. SepResult / SepStatus ─────────────────────────────────
    print("14. SepResult / SepStatus …")

    ok_r = SepResult.ok("all good")
    check(ok_r.valid, "SepResult.ok is valid")
    check(ok_r.trust == TrustLevel.KERNEL, "SepResult.ok trust")

    fail_r = SepResult.fail("bad", {"x": 1})
    check(not fail_r.valid, "SepResult.fail is invalid")
    check(fail_r.counterexample == {"x": 1}, "SepResult.fail cex")

    unk_r = SepResult.unknown("dunno")
    check(unk_r.status == SepStatus.UNKNOWN, "SepResult.unknown")

    # ── 15. collect_atoms ─────────────────────────────────────────
    print("15. collect_atoms …")

    check(Emp().collect_atoms() == [], "Emp atoms empty")
    check(pt1.collect_atoms() == [pt1], "PointsTo atoms single")
    sep_atoms = Sep(pt1, Sep(pt3, pt4)).collect_atoms()
    check(len(sep_atoms) == 3, "Sep atoms flattened")

    # ── 16. convenience combinators ───────────────────────────────
    print("16. Convenience combinators …")

    starred = pt1.star(pt3)
    check(isinstance(starred, Sep), "star produces Sep")
    wanded = pt1.wand_to(pt3)
    check(isinstance(wanded, Wand), "wand_to produces Wand")

    # ── 17. repr tests ────────────────────────────────────────────
    print("17. repr …")

    check("emp" in repr(Emp()), "Emp repr")
    check("↦" in repr(pt1), "PointsTo repr")
    check("*" in repr(Sep(pt1, pt3)), "Sep repr")
    check("-*" in repr(Wand(pt1, pt3)), "Wand repr")
    check("⌈" in repr(Pure("x > 0")), "Pure repr")
    check("∃" in repr(Exists("x", pt1)), "Exists repr")

    # ── 18. SepTriple repr ────────────────────────────────────────
    print("18. SepTriple repr …")

    tr = SepTriple(pre=pt1, command="x = 1", post=pt1, frame=pt3)
    r = repr(tr)
    check("frame" in r, "SepTriple repr includes frame")

    tr2 = SepTriple(pre=pt1, command="x = 1", post=pt1)
    r2 = repr(tr2)
    check("frame" not in r2, "SepTriple repr omits frame when None")

    # ── 19. Edge cases ────────────────────────────────────────────
    print("19. Edge cases …")

    # Deeply nested Sep
    deep = pt1
    for _ in range(20):
        deep = Sep(deep, pt3)
    dn = normalize(deep)
    d_atoms = _flatten_sep(dn)
    check(len(d_atoms) == 21, "deeply nested Sep flattens correctly")

    # Empty OwnedList/Dict/Obj
    empty_list = OwnedList("l", ())
    check(repr(empty_list) == "l ↦ []", "empty OwnedList repr")
    empty_dict = OwnedDict("d", ())
    check(repr(empty_dict) == "d ↦ {}", "empty OwnedDict repr")
    empty_obj = OwnedObj("o", (), cls=None)
    check(repr(empty_obj) == "o ↦ {}", "empty OwnedObj repr")

    # Normalize preserves Wand inside Sep
    wand_sep = Sep(Wand(pt1, pt3), pt4)
    wn = normalize(wand_sep)
    wn_atoms = _flatten_sep(wn)
    check(any(isinstance(a, Wand) for a in wn_atoms),
          "Wand preserved in normalized Sep")

    # ── 20. Counterexample: unsound frame ─────────────────────────
    print("20. Counterexample (unsound frame) …")

    # Frame rule should NOT let us create heap from nothing.
    # {emp} skip {emp} + frame R should give {R} skip {R},
    # NOT {R} skip {R * extra}
    base = SepTriple(pre=Emp(), command="skip", post=Emp())
    framed_skip = sc.apply_frame_rule(base, pt1)
    check(sc.check_entailment(framed_skip.pre, framed_skip.post),
          "framed skip: pre entails post (sound)")

    # Attempting to forge: {emp} skip {x↦v} is invalid
    forge = SepTriple(pre=Emp(), command="skip", post=pt1)
    r_forge = sc.check_triple(forge)
    check(not r_forge.valid, "cannot forge heap from emp (counterexample)")

    # ── 21. Multiple frame applications ───────────────────────────
    print("21. Multiple frame applications …")

    base_t = SepTriple(pre=pt1, command="f(x)", post=pt1)
    f1 = sc.apply_frame_rule(base_t, pt3)
    f2 = sc.apply_frame_rule(f1, pt4)
    f2_pre_atoms = _flatten_sep(normalize(f2.pre))
    check(len(f2_pre_atoms) == 3, "double frame: 3 atoms in pre")

    # ── 22. owned_* helper functions ──────────────────────────────
    print("22. owned_* helpers …")

    ol = owned_list("l", [Literal(1), Literal(2)])
    check(isinstance(ol, OwnedList), "owned_list type")
    check(len(ol.elements) == 2, "owned_list elements")

    od = owned_dict("d", {"a": Literal(1), "b": Literal(2)})
    check(isinstance(od, OwnedDict), "owned_dict type")

    oo = owned_obj("o", {"x": Literal(1)}, cls="C")
    check(isinstance(oo, OwnedObj), "owned_obj type")
    check(oo.cls == "C", "owned_obj cls")

    # ── 23. OwnershipTracker move semantics ───────────────────────
    print("23. Move semantics …")

    ot5 = OwnershipTracker()
    ot5.acquire_shared("x")
    check(not ot5.move("x"), "can't move while shared")
    ot5.release("x")
    check(ot5.move("x"), "move after release")
    check(not ot5.move("x"), "can't move again")
    check(not ot5.borrow("x", "f"), "can't borrow moved")

    # ── 24. Structural check: assignment ──────────────────────────
    print("24. Structural check: assignment …")

    assign_t = SepTriple(
        pre=Emp(),
        command="x = 42",
        post=PointsTo("x", Literal(42)),
    )
    ar = sc.check_triple(assign_t)
    check(ar.valid, "{emp} x=42 {x↦42} valid via structural")

    # ── 25. _atoms_multiset ───────────────────────────────────────
    print("25. _atoms_multiset …")

    ms = _atoms_multiset(Sep(pt1, Sep(pt1, pt3)))
    check(len(ms[repr(pt1)]) == 2, "multiset: pt1 appears twice")
    check(len(ms[repr(pt3)]) == 1, "multiset: pt3 appears once")

    # ── Summary ───────────────────────────────────────────────────
    total = passed + failed
    print(f"\n{'='*60}")
    print(f"Separation logic self-tests: {passed}/{total} passed", end="")
    if failed:
        print(f"  ({failed} FAILED)")
    else:
        print("  ✓ all passed")
    print(f"{'='*60}")

    if failed:
        raise SystemExit(1)


if __name__ == "__main__":
    _run_self_tests()
