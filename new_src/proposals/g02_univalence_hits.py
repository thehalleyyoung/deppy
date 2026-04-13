"""Code improvement proposals for Ch 3–4 (Univalence & HITs).

Exhaustive, importable implementations for:
  1.  Transport along PyComp paths (Theorem 3.5)
  2.  Fix→Fold recognition (D1 path constructor, Definition 4.1)
  3.  Type equivalence registry with caching & composition
  4.  Shared function symbol table (univalence, Theorem 3.5)
  5.  PyComp HIT: 13 point constructors + 24 path constructors
  6.  PyComp eliminator with full dispatch (Theorem 4.4)
  7.  Glue type for univalence (cubical construction)
  8.  Set-level truncation (quotient by higher paths)
  9.  All 24 dichotomy path recognisers
  10. Free-algebra completeness checker
  11. Path composition, inverse, and groupoid operations
  12. Elimination-principle dispatcher for OTerm

All classes are fully implemented, typed, docstring'd, and tested
in the ``if __name__ == '__main__'`` block at the bottom.
"""
from __future__ import annotations

import hashlib
import itertools
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import (
    Any, Callable, Dict, FrozenSet, Generic, List, Mapping,
    Optional, Protocol, Set, Sequence, Tuple, TypeVar, Union,
)

# ── Imports from sibling modules ───────────────────────────
from new_src.cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
    _subst, normalize,
)
from new_src.cctt.path_search import (
    PathStep, PathResult, FiberCtx,
    search_path, hit_path_equiv,
    _extract_params_from_term, _extract_free_vars,
    _is_commutative_op, _identify_spec,
)

T = TypeVar("T")


# ═══════════════════════════════════════════════════════════════════
#  §1  PATH COMPOSITION, INVERSE, AND GROUPOID OPERATIONS
# ═══════════════════════════════════════════════════════════════════

def compose_paths(p: PathResult, q: PathResult) -> PathResult:
    """Compose two paths: *p · q* where *p* ends where *q* starts.

    Implements path concatenation in PyComp (Proposition 3.4).

    Raises ``ValueError`` when the endpoint of *p* does not match the
    startpoint of *q*.
    """
    if not p.found or not q.found:
        return PathResult(
            found=None,
            path=[],
            reason="cannot compose: one or both paths not found",
        )
    if p.path and q.path:
        if p.path[-1].after != q.path[0].before:
            raise ValueError(
                f"Paths not composable: "
                f"endpoint {p.path[-1].after!r} ≠ startpoint {q.path[0].before!r}"
            )
    merged = list(p.path) + list(q.path)
    return PathResult(
        found=True,
        path=merged,
        reason=f"composition: ({p.reason}) · ({q.reason})",
    )


def invert_path(p: PathResult) -> PathResult:
    """Invert a path: *p⁻¹* goes from endpoint to startpoint.

    Each step's axiom is annotated with ``^{-1}``.
    """
    if not p.found:
        return p
    reversed_steps: List[PathStep] = []
    for step in reversed(p.path):
        reversed_steps.append(
            PathStep(
                axiom=step.axiom + "^{-1}",
                position=step.position,
                before=step.after,
                after=step.before,
            )
        )
    return PathResult(
        found=True,
        path=reversed_steps,
        reason=f"inverse of: {p.reason}",
    )


def refl_path(term: OTerm) -> PathResult:
    """The reflexivity path: *refl(a)* is the trivial path a = a."""
    return PathResult(found=True, path=[], reason="refl")


def path_startpoint(p: PathResult) -> Optional[str]:
    """Return the canonical form at the start of a path, or ``None``."""
    if not p.path:
        return None
    return p.path[0].before


def path_endpoint(p: PathResult) -> Optional[str]:
    """Return the canonical form at the end of a path, or ``None``."""
    if not p.path:
        return None
    return p.path[-1].after


def path_length(p: PathResult) -> int:
    """Number of axiom applications in the path."""
    return len(p.path)


def path_axioms_used(p: PathResult) -> List[str]:
    """Return the ordered list of axiom names used in *p*."""
    return [s.axiom for s in p.path]


# ═══════════════════════════════════════════════════════════════════
#  §2  TRANSPORT ALONG PYCOMP PATHS  (Theorem 3.5)
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ProofCertificate:
    """A proof certificate for a property of a program term.

    Fields
    ------
    property_name : str
        e.g. ``"correctness"``, ``"termination"``, ``"purity"``.
    term_canon : str
        Canonical form of the term this proof is about.
    evidence : dict
        Arbitrary evidence payload (Z3 model, test results, …).
    trust_level : str
        One of ``"LEAN_VERIFIED"``, ``"Z3_PROVEN"``,
        ``"LLM_JUDGED"``, ``"RUNTIME_CHECKED"``, ``"UNTRUSTED"``.
    """

    property_name: str
    term_canon: str
    evidence: dict
    trust_level: str = "UNTRUSTED"


class TransportEngine:
    """Transport proof certificates along PyComp paths.

    Given a path ``[s₀ →[ax₁] s₁ →[ax₂] … →[axₖ] sₖ]`` and a
    :class:`ProofCertificate` for ``s₀``, produces a certificate for
    ``sₖ``.

    Each axiom carries a *soundness witness*: a function that rewrites
    the evidence payload according to the axiom's semantics.  Axioms
    without a registered witness produce ``UNTRUSTED`` certificates.
    """

    def __init__(self) -> None:
        self._witnesses: Dict[str, Callable[[dict], dict]] = {}

    # ── registration ──

    def register_witness(
        self, axiom_prefix: str, fn: Callable[[dict], dict]
    ) -> None:
        """Register a soundness witness for axiom names starting with *axiom_prefix*."""
        self._witnesses[axiom_prefix] = fn

    def _lookup_witness(self, axiom: str) -> Optional[Callable[[dict], dict]]:
        base = axiom.replace("^{-1}", "")
        for prefix, fn in self._witnesses.items():
            if base.startswith(prefix):
                return fn
        return None

    # ── transport ──

    def transport(
        self,
        path: PathResult,
        source_cert: ProofCertificate,
    ) -> ProofCertificate:
        """Transport *source_cert* along *path*.

        Returns a new certificate whose ``term_canon`` is the path's
        endpoint.

        Trust degrades to ``UNTRUSTED`` whenever a step lacks a
        registered soundness witness.
        """
        if not path.found:
            raise ValueError("Cannot transport along a non-existent path")

        current_evidence = dict(source_cert.evidence)
        current_trust = source_cert.trust_level
        current_canon = source_cert.term_canon

        for step in path.path:
            witness = self._lookup_witness(step.axiom)
            if witness is not None:
                current_evidence = witness(current_evidence)
            else:
                current_trust = "UNTRUSTED"
                current_evidence = {
                    "transported_from": current_canon,
                    "axiom": step.axiom,
                    "original_evidence": current_evidence,
                }
            current_canon = step.after

        return ProofCertificate(
            property_name=source_cert.property_name,
            term_canon=current_canon,
            evidence=current_evidence,
            trust_level=current_trust,
        )

    def transport_property(
        self,
        path_steps: List[PathStep],
        property_name: str,
        source_proof: dict,
    ) -> dict:
        """Legacy helper: thin wrapper producing a plain dict."""
        cert = ProofCertificate(
            property_name=property_name,
            term_canon=path_steps[0].before if path_steps else "",
            evidence=source_proof,
            trust_level="Z3_PROVEN",
        )
        pr = PathResult(found=True, path=path_steps, reason="explicit")
        result = self.transport(pr, cert)
        return {
            "property": result.property_name,
            "term": result.term_canon,
            "trust": result.trust_level,
            "evidence": result.evidence,
        }


# ═══════════════════════════════════════════════════════════════════
#  §3  FIX→FOLD RECOGNITION  (D1 path constructor, Def 4.1)
# ═══════════════════════════════════════════════════════════════════

def _find_recursive_call(term: OTerm, fix_name: str) -> Optional[OTerm]:
    """Locate a call ``fix_name(…)`` inside *term*.

    Returns the full ``OOp`` node representing the recursive call,
    or ``None`` if not found.
    """
    if isinstance(term, OOp):
        if term.name == fix_name:
            return term
        for arg in term.args:
            found = _find_recursive_call(arg, fix_name)
            if found is not None:
                return found
    if isinstance(term, OCase):
        for sub in (term.test, term.true_branch, term.false_branch):
            found = _find_recursive_call(sub, fix_name)
            if found is not None:
                return found
    if isinstance(term, OFold):
        for sub in (term.init, term.collection):
            found = _find_recursive_call(sub, fix_name)
            if found is not None:
                return found
    return None


def _extract_accumulation_op(branch: OTerm, rec_call: OTerm) -> Optional[str]:
    """Identify the binary operator combining *rec_call* with a step value.

    Patterns:
        ``op(rec_call, step)``  →  *op*
        ``op(step, rec_call)``  →  *op*
    """
    if not isinstance(branch, OOp):
        return None
    if len(branch.args) != 2:
        return None
    rc_canon = rec_call.canon()
    if branch.args[0].canon() == rc_canon or branch.args[1].canon() == rc_canon:
        return branch.name
    return None


def _extract_range_from_guard(test: OTerm) -> Optional[OTerm]:
    """Heuristic: extract a range term from a base-case guard.

    Recognises ``lte($n, 0)``, ``eq($n, 0)``, ``lt($n, 1)``, etc.
    and returns ``OOp('range', (OOp('add', (var, OLit(1))),))``.
    """
    if not isinstance(test, OOp):
        return None
    if test.name in ("lte", "lt", "eq") and len(test.args) == 2:
        if isinstance(test.args[1], OLit) and test.args[1].value in (0, 1):
            var = test.args[0]
            bound = OOp("add", (var, OLit(1)))
            return OOp("range", (bound,))
    return None


def try_extract_fold_from_fix(term: OFix) -> Optional[OTerm]:
    """Recognise a fold pattern inside a fix-point body (D1).

    Pattern::

        fix[h](case(base_cond, base_val,
                     op(h(recursive_call), step_val)))

    becomes ``fold[op](base_val, collection)``.
    """
    if not isinstance(term, OFix):
        return None
    body = term.body
    if not isinstance(body, OCase):
        return None

    rec_call = _find_recursive_call(body.false_branch, term.name)
    if rec_call is None:
        return None

    op_name = _extract_accumulation_op(body.false_branch, rec_call)
    if op_name is None:
        return None

    coll = _extract_range_from_guard(body.test)
    if coll is None:
        return None

    return OFold(op_name, body.true_branch, coll)


# ═══════════════════════════════════════════════════════════════════
#  §4  TYPE-EQUIVALENCE REGISTRY  (ua-paths, Example 3.8)
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class TypeEquivEdge:
    """A single ua-path between two types."""
    source: str
    target: str
    label: str
    coercion_fn: Optional[Callable[[Any], Any]] = None


class TypeEquivRegistry:
    """Registry of ua-paths between Python types.

    Tracks equivalences established by univalence (Example 3.8)
    with caching and transitive composition.

    Supported equivalences (pre-loaded):
      - ``bool ≃ {0,1} ⊂ int``
      - ``int  ≃ float``  (widening)
      - ``bytes ≃ list[int]``
      - ``str  ≃ list[str]``  (character iteration)
      - ``tuple ≃ list``  (structural, non-mutable)
    """

    def __init__(self) -> None:
        self._edges: Dict[Tuple[str, str], TypeEquivEdge] = {}
        self._path_cache: Dict[Tuple[str, str], Optional[List[str]]] = {}
        self._coerce_cache: Dict[Tuple[str, str], Optional[Callable]] = {}
        self._load_defaults()

    def _load_defaults(self) -> None:
        defaults = [
            TypeEquivEdge("bool", "int", "bool_int_coercion", lambda b: int(b)),
            TypeEquivEdge("int", "float", "int_float_widening", float),
            TypeEquivEdge("bytes", "list[int]", "bytes_listint", list),
            TypeEquivEdge("str", "list[str]", "str_liststr", list),
            TypeEquivEdge("tuple", "list", "tuple_list", list),
        ]
        for e in defaults:
            self.register(e)

    # ── mutation ──

    def register(self, edge: TypeEquivEdge) -> None:
        """Register a ua-path."""
        self._edges[(edge.source, edge.target)] = edge
        self._path_cache.clear()
        self._coerce_cache.clear()

    # ── queries ──

    def are_equivalent(self, t1: str, t2: str) -> bool:
        """Check (possibly transitive) equivalence."""
        if t1 == t2:
            return True
        return self._find_path(t1, t2) is not None

    def get_coercion_path(self, t1: str, t2: str) -> Optional[List[str]]:
        """Return the list of edge labels forming a path *t1 → t2*."""
        return self._find_path(t1, t2)

    def coerce(self, value: Any, src: str, tgt: str) -> Any:
        """Apply the coercion chain *src → tgt* to *value*."""
        if src == tgt:
            return value
        path = self._find_path(src, tgt)
        if path is None:
            raise TypeError(f"No ua-path from {src} to {tgt}")
        current = value
        for label in path:
            edge = self._edge_by_label(label)
            if edge is not None and edge.coercion_fn is not None:
                current = edge.coercion_fn(current)
        return current

    # ── internal BFS ──

    def _find_path(self, src: str, tgt: str) -> Optional[List[str]]:
        key = (src, tgt)
        if key in self._path_cache:
            return self._path_cache[key]
        visited: Set[str] = set()
        queue: List[Tuple[str, List[str]]] = [(src, [])]
        while queue:
            current, labels = queue.pop(0)
            if current == tgt:
                self._path_cache[key] = labels
                return labels
            if current in visited:
                continue
            visited.add(current)
            for (s, t), edge in self._edges.items():
                if s == current and t not in visited:
                    queue.append((t, labels + [edge.label]))
                if t == current and s not in visited:
                    queue.append((s, labels + [edge.label + "^{-1}"]))
        self._path_cache[key] = None
        return None

    def _edge_by_label(self, label: str) -> Optional[TypeEquivEdge]:
        base = label.replace("^{-1}", "")
        for e in self._edges.values():
            if e.label == base:
                return e
        return None

    def all_types(self) -> Set[str]:
        """Return all types that appear in at least one edge."""
        result: Set[str] = set()
        for (s, t) in self._edges:
            result.add(s)
            result.add(t)
        return result

    def all_edges(self) -> List[TypeEquivEdge]:
        """Return every registered edge."""
        return list(self._edges.values())


# ═══════════════════════════════════════════════════════════════════
#  §5  SHARED FUNCTION SYMBOL TABLE  (Theorem 3.5)
# ═══════════════════════════════════════════════════════════════════

class SharedSymbolTable:
    """Canonical function symbol table enforcing univalence.

    By univalence (Theorem 3.5) any two references to the same
    Python built-in must denote the same entity.  This class maps
    surface names to canonical Z3/OTerm symbols.
    """

    _CANONICAL: Dict[str, str] = {
        "sorted": "py_sorted",
        "len": "py_len",
        "sum": "py_sum",
        "min": "py_min",
        "max": "py_max",
        "abs": "py_abs",
        "range": "py_range",
        "enumerate": "py_enumerate",
        "zip": "py_zip",
        "map": "py_map",
        "filter": "py_filter",
        "reversed": "py_reversed",
        "set": "py_set",
        "list": "py_list",
        "dict": "py_dict",
        "tuple": "py_tuple",
        "int": "py_int",
        "float": "py_float",
        "str": "py_str",
        "bool": "py_bool",
        "any": "py_any",
        "all": "py_all",
        "print": "py_print",
        "input": "py_input",
        "open": "py_open",
        "isinstance": "py_isinstance",
        "type": "py_type",
        "iter": "py_iter",
        "next": "py_next",
        "hash": "py_hash",
        "id": "py_id",
    }

    _METHODS: Dict[str, str] = {
        ".append": "py_list.append",
        ".extend": "py_list.extend",
        ".pop": "py_list.pop",
        ".get": "py_dict.get",
        ".keys": "py_dict.keys",
        ".values": "py_dict.values",
        ".items": "py_dict.items",
        ".update": "py_dict.update",
        ".add": "py_set.add",
        ".remove": "py_set.remove",
        ".discard": "py_set.discard",
        ".split": "py_str.split",
        ".join": "py_str.join",
        ".strip": "py_str.strip",
        ".lower": "py_str.lower",
        ".upper": "py_str.upper",
        ".replace": "py_str.replace",
        ".startswith": "py_str.startswith",
        ".endswith": "py_str.endswith",
        ".find": "py_str.find",
        ".count": "py_str.count",
        ".sort": "py_list.sort",
    }

    def __init__(self) -> None:
        self._user: Dict[str, str] = {}

    @classmethod
    def canonicalize(cls, func_name: str) -> str:
        """Return the canonical symbol for *func_name*."""
        if func_name in cls._CANONICAL:
            return cls._CANONICAL[func_name]
        if func_name in cls._METHODS:
            return cls._METHODS[func_name]
        return func_name

    def register(self, surface: str, canonical: str) -> None:
        """Register a user-defined canonical symbol."""
        self._user[surface] = canonical

    def lookup(self, name: str) -> str:
        """Full lookup: user overrides → built-in canonical → identity."""
        if name in self._user:
            return self._user[name]
        return self.canonicalize(name)

    def all_canonical(self) -> Dict[str, str]:
        """Return full merged table."""
        merged = dict(self._CANONICAL)
        merged.update(self._METHODS)
        merged.update(self._user)
        return merged

    def is_canonical(self, name: str) -> bool:
        """True if *name* is already the canonical form."""
        return name in self._CANONICAL.values() or name in self._METHODS.values()


# ═══════════════════════════════════════════════════════════════════
#  §6  PYCOMP HIT  (13 point + 24 path constructors, Def 4.1)
# ═══════════════════════════════════════════════════════════════════

class PointTag(Enum):
    """Tags for the 13 point constructors of the PyComp HIT."""
    LIT = auto()
    VAR = auto()
    OP = auto()
    FOLD = auto()
    CASE = auto()
    FIX = auto()
    SEQ = auto()
    DICT = auto()
    LAM = auto()
    MAP = auto()
    CATCH = auto()
    QUOTIENT = auto()
    ABSTRACT = auto()


@dataclass(frozen=True)
class PyCompPoint:
    """A point in the PyComp HIT, wrapping an OTerm with its tag."""
    tag: PointTag
    term: OTerm

    @staticmethod
    def from_oterm(t: OTerm) -> "PyCompPoint":
        """Construct a ``PyCompPoint`` from an ``OTerm``."""
        tag_map: Dict[type, PointTag] = {
            OLit: PointTag.LIT,
            OVar: PointTag.VAR,
            OOp: PointTag.OP,
            OFold: PointTag.FOLD,
            OCase: PointTag.CASE,
            OFix: PointTag.FIX,
            OSeq: PointTag.SEQ,
            ODict: PointTag.DICT,
            OLam: PointTag.LAM,
            OMap: PointTag.MAP,
            OCatch: PointTag.CATCH,
            OQuotient: PointTag.QUOTIENT,
            OAbstract: PointTag.ABSTRACT,
        }
        tag = tag_map.get(type(t), PointTag.ABSTRACT)
        return PyCompPoint(tag=tag, term=t)

    def canon(self) -> str:
        """Canonical form delegates to the inner OTerm."""
        return self.term.canon()


class DichotomyGroup(Enum):
    """The four dichotomy groups from the monograph."""
    CONTROL_FLOW = "D1-D8"
    DATA_STRUCTURE = "D9-D14"
    ALGORITHM_STRATEGY = "D15-D20"
    LANGUAGE_FEATURE = "D21-D24"


@dataclass(frozen=True)
class DichotomyAxiom:
    """Metadata for one of the 24 dichotomies."""
    index: int
    name: str
    short: str
    group: DichotomyGroup
    lhs_tag: Optional[PointTag]
    rhs_tag: Optional[PointTag]
    description: str
    is_involutive: bool = False


ALL_DICHOTOMIES: List[DichotomyAxiom] = [
    DichotomyAxiom(1, "D1_fold_unfold", "rec↔iter",
                   DichotomyGroup.CONTROL_FLOW, PointTag.FIX, PointTag.FOLD,
                   "Recursive fix ↔ iterative fold"),
    DichotomyAxiom(2, "D2_beta", "inline",
                   DichotomyGroup.CONTROL_FLOW, PointTag.OP, PointTag.OP,
                   "β-reduction / helper inlining", is_involutive=False),
    DichotomyAxiom(3, "D3_loop_form", "while↔for",
                   DichotomyGroup.CONTROL_FLOW, PointTag.FIX, PointTag.FOLD,
                   "Loop normal form"),
    DichotomyAxiom(4, "D4_comp_fusion", "comp↔loop",
                   DichotomyGroup.CONTROL_FLOW, PointTag.MAP, PointTag.MAP,
                   "Comprehension / catamorphism fusion"),
    DichotomyAxiom(5, "D5_fold_universal", "reduce↔loop",
                   DichotomyGroup.CONTROL_FLOW, PointTag.FOLD, PointTag.FOLD,
                   "Fold universality"),
    DichotomyAxiom(6, "D6_lazy_eager", "gen↔eager",
                   DichotomyGroup.CONTROL_FLOW, PointTag.MAP, PointTag.MAP,
                   "Laziness adjunction"),
    DichotomyAxiom(7, "D7_tailrec", "tailrec↔loop",
                   DichotomyGroup.CONTROL_FLOW, PointTag.FIX, PointTag.FOLD,
                   "CPS / tail-recursion elimination"),
    DichotomyAxiom(8, "D8_section_merge", "multi↔single",
                   DichotomyGroup.CONTROL_FLOW, PointTag.CASE, PointTag.CASE,
                   "Section merging / guard reordering"),
    DichotomyAxiom(9, "D9_stack_rec", "stack↔rec",
                   DichotomyGroup.DATA_STRUCTURE, PointTag.FIX, PointTag.FIX,
                   "Explicit stack vs recursion (defunctionalisation)"),
    DichotomyAxiom(10, "D10_pq", "heapq↔bisect",
                   DichotomyGroup.DATA_STRUCTURE, PointTag.FOLD, PointTag.FOLD,
                   "Priority queue abstraction"),
    DichotomyAxiom(11, "D11_adt", "orddict↔linked",
                   DichotomyGroup.DATA_STRUCTURE, PointTag.DICT, PointTag.DICT,
                   "ADT refinement"),
    DichotomyAxiom(12, "D12_map_construct", "ddict↔setdefault",
                   DichotomyGroup.DATA_STRUCTURE, PointTag.DICT, PointTag.DICT,
                   "Map construction with defaults"),
    DichotomyAxiom(13, "D13_histogram", "Counter↔count",
                   DichotomyGroup.DATA_STRUCTURE, PointTag.OP, PointTag.FOLD,
                   "Histogram equivalence"),
    DichotomyAxiom(14, "D14_indexing", "array↔dict",
                   DichotomyGroup.DATA_STRUCTURE, PointTag.SEQ, PointTag.DICT,
                   "Dense index → dict lookup"),
    DichotomyAxiom(15, "D15_traversal", "BFS↔DFS",
                   DichotomyGroup.ALGORITHM_STRATEGY, PointTag.FIX, PointTag.FIX,
                   "Traversal-order invariance"),
    DichotomyAxiom(16, "D16_memo_dp", "memo↔DP",
                   DichotomyGroup.ALGORITHM_STRATEGY, PointTag.FIX, PointTag.FOLD,
                   "Top-down memo ↔ bottom-up DP"),
    DichotomyAxiom(17, "D17_assoc", "d&c↔iter",
                   DichotomyGroup.ALGORITHM_STRATEGY, PointTag.FOLD, PointTag.FOLD,
                   "Tree fold ↔ linear fold (associativity)"),
    DichotomyAxiom(18, "D18_greedy", "greedy↔DP",
                   DichotomyGroup.ALGORITHM_STRATEGY, PointTag.FOLD, PointTag.FIX,
                   "Matroid / greedy theorem"),
    DichotomyAxiom(19, "D19_sort_scan", "sort+scan↔sweep",
                   DichotomyGroup.ALGORITHM_STRATEGY, PointTag.FOLD, PointTag.FOLD,
                   "Sort-then-scan ↔ sweep"),
    DichotomyAxiom(20, "D20_spec_unify", "specA↔specB",
                   DichotomyGroup.ALGORITHM_STRATEGY, PointTag.ABSTRACT, PointTag.ABSTRACT,
                   "Yoneda + spec discovery"),
    DichotomyAxiom(21, "D21_dispatch", "isinstance↔dict",
                   DichotomyGroup.LANGUAGE_FEATURE, PointTag.CASE, PointTag.DICT,
                   "isinstance chain ↔ dispatch table"),
    DichotomyAxiom(22, "D22_effect_elim", "try↔cond",
                   DichotomyGroup.LANGUAGE_FEATURE, PointTag.CATCH, PointTag.CASE,
                   "Exception elimination"),
    DichotomyAxiom(23, "D23_sort_process", "sorted+proc↔direct",
                   DichotomyGroup.LANGUAGE_FEATURE, PointTag.FOLD, PointTag.FOLD,
                   "Sort-then-process ↔ direct"),
    DichotomyAxiom(24, "D24_eta", "λx.f(x)↔f",
                   DichotomyGroup.LANGUAGE_FEATURE, PointTag.LAM, PointTag.OP,
                   "η-expansion / contraction", is_involutive=True),
]


class PyCompHIT:
    """The PyComp HIT as an explicit Python object.

    Contains 13 point constructors (one per ``PointTag``) and the
    24 dichotomy path constructors.

    This class lets callers:
    - Inject a point into PyComp.
    - List which path constructors *could* fire on a pair.
    - Enumerate neighbourhood (one-step rewrites) of a point.
    """

    def __init__(self) -> None:
        self._dichotomies = {d.index: d for d in ALL_DICHOTOMIES}

    def inject(self, t: OTerm) -> PyCompPoint:
        """Inject an OTerm into the HIT."""
        return PyCompPoint.from_oterm(t)

    def dichotomy(self, index: int) -> DichotomyAxiom:
        """Look up dichotomy by 1-based index."""
        return self._dichotomies[index]

    def all_dichotomies(self) -> List[DichotomyAxiom]:
        """Return all 24 dichotomies."""
        return list(ALL_DICHOTOMIES)

    def applicable_dichotomies(
        self, a: PyCompPoint, b: PyCompPoint
    ) -> List[DichotomyAxiom]:
        """Return dichotomies whose LHS/RHS tags match *a* and *b*."""
        results: List[DichotomyAxiom] = []
        for d in ALL_DICHOTOMIES:
            if d.lhs_tag is None or d.rhs_tag is None:
                results.append(d)
                continue
            if (a.tag == d.lhs_tag and b.tag == d.rhs_tag) or \
               (a.tag == d.rhs_tag and b.tag == d.lhs_tag):
                results.append(d)
        return results

    def group_dichotomies(self) -> Dict[DichotomyGroup, List[DichotomyAxiom]]:
        """Group dichotomies by their monograph group."""
        groups: Dict[DichotomyGroup, List[DichotomyAxiom]] = {}
        for d in ALL_DICHOTOMIES:
            groups.setdefault(d.group, []).append(d)
        return groups

    def neighbourhood(
        self, point: PyCompPoint, ctx: Optional[FiberCtx] = None
    ) -> List[Tuple[PyCompPoint, str]]:
        """One-step rewrites of *point* through all path constructors.

        Returns ``(new_point, axiom_name)`` pairs.
        """
        if ctx is None:
            ctx = FiberCtx(param_duck_types={})
        from new_src.cctt.path_search import _all_rewrites
        results: List[Tuple[PyCompPoint, str]] = []
        for new_term, axiom in _all_rewrites(point.term, ctx):
            results.append((PyCompPoint.from_oterm(new_term), axiom))
        return results


# ═══════════════════════════════════════════════════════════════════
#  §7  DICHOTOMY RECOGNISER  (detect which D a pair falls into)
# ═══════════════════════════════════════════════════════════════════

class DichotomyRecogniser:
    """Given two OTerms, detect which of the 24 dichotomies apply.

    Each recogniser is a predicate: ``(OTerm, OTerm) → bool``.
    """

    @staticmethod
    def recognise_d1(a: OTerm, b: OTerm) -> bool:
        """D1  rec ↔ iter:  one is OFix, the other is OFold."""
        return (isinstance(a, OFix) and isinstance(b, OFold)) or \
               (isinstance(a, OFold) and isinstance(b, OFix))

    @staticmethod
    def recognise_d2(a: OTerm, b: OTerm) -> bool:
        """D2  β-reduction:  one is ``apply(λ…, args)``."""
        def _is_beta(t: OTerm) -> bool:
            return (isinstance(t, OOp) and t.name == "apply" and
                    len(t.args) >= 2 and isinstance(t.args[0], OLam))
        return _is_beta(a) or _is_beta(b)

    @staticmethod
    def recognise_d3(a: OTerm, b: OTerm) -> bool:
        """D3  while ↔ for:  both OFix / OFold, loop forms."""
        return (isinstance(a, (OFix, OFold)) and isinstance(b, (OFix, OFold))
                and type(a) != type(b))

    @staticmethod
    def recognise_d4(a: OTerm, b: OTerm) -> bool:
        """D4  comp fusion:  nested OMap."""
        def _has_nested_map(t: OTerm) -> bool:
            return isinstance(t, OMap) and isinstance(t.collection, OMap)
        return _has_nested_map(a) or _has_nested_map(b)

    @staticmethod
    def recognise_d5(a: OTerm, b: OTerm) -> bool:
        """D5  fold universality:  two OFolds, same init+coll, diff op."""
        if isinstance(a, OFold) and isinstance(b, OFold):
            return (a.init.canon() == b.init.canon() and
                    a.collection.canon() == b.collection.canon() and
                    a.op_name != b.op_name)
        return False

    @staticmethod
    def recognise_d6(a: OTerm, b: OTerm) -> bool:
        """D6  gen ↔ eager:  OOp('list', OMap(…)) vs OMap."""
        def _is_eagered(t: OTerm) -> bool:
            return (isinstance(t, OOp) and t.name == "list" and
                    len(t.args) == 1 and isinstance(t.args[0], OMap))
        return _is_eagered(a) or _is_eagered(b)

    @staticmethod
    def recognise_d7(a: OTerm, b: OTerm) -> bool:
        """D7  tailrec ↔ loop:  subsumed by D1 in OTerm world."""
        return DichotomyRecogniser.recognise_d1(a, b)

    @staticmethod
    def recognise_d8(a: OTerm, b: OTerm) -> bool:
        """D8  section merge:  nested OCase with complementary guards."""
        if isinstance(a, OCase) and isinstance(b, OCase):
            if isinstance(a.false_branch, OCase) or isinstance(b.false_branch, OCase):
                return True
        return False

    @staticmethod
    def recognise_d9(a: OTerm, b: OTerm) -> bool:
        """D9  stack ↔ rec:  two OFix with different body structure."""
        return isinstance(a, OFix) and isinstance(b, OFix) and a.name != b.name

    @staticmethod
    def recognise_d10(a: OTerm, b: OTerm) -> bool:
        """D10  heapq ↔ bisect:  OFolds with pq-like op names."""
        if isinstance(a, OFold) and isinstance(b, OFold):
            pq_ops = {"heappush", "heappop", "insort", "bisect"}
            return a.op_name in pq_ops or b.op_name in pq_ops
        return False

    @staticmethod
    def recognise_d11(a: OTerm, b: OTerm) -> bool:
        """D11  ADT refinement:  both ODict."""
        return isinstance(a, ODict) and isinstance(b, ODict)

    @staticmethod
    def recognise_d12(a: OTerm, b: OTerm) -> bool:
        """D12  defaultdict ↔ setdefault:  OOp names match pattern."""
        names = set()
        for t in (a, b):
            if isinstance(t, OOp):
                names.add(t.name)
        return bool(names & {"defaultdict", "setdefault"})

    @staticmethod
    def recognise_d13(a: OTerm, b: OTerm) -> bool:
        """D13  Counter ↔ manual count."""
        def _is_counter(t: OTerm) -> bool:
            return isinstance(t, OOp) and t.name in ("Counter", "collections.Counter")
        def _is_count_fold(t: OTerm) -> bool:
            return isinstance(t, OFold) and t.op_name in ("count_freq", "freq_count")
        return (_is_counter(a) and _is_count_fold(b)) or \
               (_is_counter(b) and _is_count_fold(a))

    @staticmethod
    def recognise_d14(a: OTerm, b: OTerm) -> bool:
        """D14  array ↔ dict table."""
        return (isinstance(a, OSeq) and isinstance(b, ODict)) or \
               (isinstance(a, ODict) and isinstance(b, OSeq))

    @staticmethod
    def recognise_d15(a: OTerm, b: OTerm) -> bool:
        """D15  BFS ↔ DFS:  two OFix over same domain, commutative fold."""
        if isinstance(a, OFix) and isinstance(b, OFix):
            return _extract_free_vars(a) == _extract_free_vars(b)
        return False

    @staticmethod
    def recognise_d16(a: OTerm, b: OTerm) -> bool:
        """D16  memo ↔ DP:  OFix vs OFold with matching spec."""
        if (isinstance(a, OFix) and isinstance(b, OFold)) or \
           (isinstance(a, OFold) and isinstance(b, OFix)):
            sa = _identify_spec(a)
            sb = _identify_spec(b)
            return sa is not None and sb is not None and sa[0] == sb[0]
        return False

    @staticmethod
    def recognise_d17(a: OTerm, b: OTerm) -> bool:
        """D17  tree fold ↔ linear fold."""
        if isinstance(a, OFold) and isinstance(b, OFold):
            if isinstance(a.collection, OOp) and a.collection.name in ("tree_split", "divide"):
                return True
            if isinstance(b.collection, OOp) and b.collection.name in ("tree_split", "divide"):
                return True
        return False

    @staticmethod
    def recognise_d18(a: OTerm, b: OTerm) -> bool:
        """D18  greedy ↔ DP:  spec-level comparison."""
        sa = _identify_spec(a)
        sb = _identify_spec(b)
        if sa and sb and sa[0] == sb[0]:
            return (isinstance(a, OFold) and isinstance(b, OFix)) or \
                   (isinstance(a, OFix) and isinstance(b, OFold))
        return False

    @staticmethod
    def recognise_d19(a: OTerm, b: OTerm) -> bool:
        """D19  sort-then-scan ↔ sweep."""
        for t in (a, b):
            if isinstance(t, OFold):
                if isinstance(t.collection, OOp) and t.collection.name == "sorted":
                    return True
        return False

    @staticmethod
    def recognise_d20(a: OTerm, b: OTerm) -> bool:
        """D20  different algorithms, same spec."""
        sa = _identify_spec(a)
        sb = _identify_spec(b)
        return sa is not None and sb is not None and sa[0] == sb[0]

    @staticmethod
    def recognise_d21(a: OTerm, b: OTerm) -> bool:
        """D21  isinstance ↔ dispatch table."""
        return (isinstance(a, OCase) and isinstance(b, ODict)) or \
               (isinstance(a, ODict) and isinstance(b, OCase))

    @staticmethod
    def recognise_d22(a: OTerm, b: OTerm) -> bool:
        """D22  try/except ↔ conditional."""
        return (isinstance(a, OCatch) and isinstance(b, OCase)) or \
               (isinstance(a, OCase) and isinstance(b, OCatch))

    @staticmethod
    def recognise_d23(a: OTerm, b: OTerm) -> bool:
        """D23  sorted+process ↔ direct:  subsumed by D19."""
        return DichotomyRecogniser.recognise_d19(a, b)

    @staticmethod
    def recognise_d24(a: OTerm, b: OTerm) -> bool:
        """D24  η-expansion:  λx.f(x) ↔ f."""
        def _is_eta(lam: OTerm, fn: OTerm) -> bool:
            if not isinstance(lam, OLam) or len(lam.params) != 1:
                return False
            if isinstance(lam.body, OOp) and len(lam.body.args) == 1:
                if isinstance(lam.body.args[0], OVar) and lam.body.args[0].name == lam.params[0]:
                    return isinstance(fn, OOp) and fn.name == lam.body.name
            return False
        return _is_eta(a, b) or _is_eta(b, a)

    # ── bulk helpers ──

    _ALL = None  # lazily built

    @classmethod
    def _recognisers(cls) -> List[Tuple[int, Callable[[OTerm, OTerm], bool]]]:
        if cls._ALL is None:
            cls._ALL = [
                (i, getattr(cls, f"recognise_d{i}"))
                for i in range(1, 25)
            ]
        return cls._ALL

    @classmethod
    def detect_all(
        cls, a: OTerm, b: OTerm
    ) -> List[DichotomyAxiom]:
        """Return every dichotomy that fires on *(a, b)*."""
        result: List[DichotomyAxiom] = []
        for idx, fn in cls._recognisers():
            if fn(a, b):
                result.append(ALL_DICHOTOMIES[idx - 1])
        return result

    @classmethod
    def detect_primary(
        cls, a: OTerm, b: OTerm
    ) -> Optional[DichotomyAxiom]:
        """Return the *first* (highest-priority) matching dichotomy."""
        hits = cls.detect_all(a, b)
        return hits[0] if hits else None


# ═══════════════════════════════════════════════════════════════════
#  §8  GLUE TYPE FOR UNIVALENCE  (cubical construction)
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Equiv:
    """A type equivalence *A ≃ B* with forward and backward maps.

    Both maps must satisfy ``backward(forward(a)) == a`` and
    ``forward(backward(b)) == b`` (up to path equality).
    """
    source: str
    target: str
    forward: Callable[[Any], Any]
    backward: Callable[[Any], Any]

    def check_roundtrip(self, samples: Sequence[Any]) -> bool:
        """Verify roundtrip on concrete samples."""
        for s in samples:
            if self.backward(self.forward(s)) != s:
                return False
        return True


@dataclass
class GlueType:
    """Cubical Glue type implementing univalence.

    In cubical type theory, ``Glue(B, [(φ₁, A₁, e₁), …])`` is a
    type that is ``B`` on the *interior* of the cube and ``Aᵢ`` on
    the face where ``φᵢ = 1``, glued via the equivalence ``eᵢ``.

    Simplified to a single face: ``Glue(B, A, e)`` where:
      - at ``i=0`` the type is ``A``
      - at ``i=1`` the type is ``B``
      - ``e : A ≃ B``
    """

    base: str
    face_type: str
    equiv: Equiv

    def at_zero(self) -> str:
        """Type at ``i = 0`` (the face)."""
        return self.face_type

    def at_one(self) -> str:
        """Type at ``i = 1`` (the base)."""
        return self.base

    def glue_value(self, a_val: Any) -> Any:
        """Given a value in the face type *A*, produce the glued value in *B*."""
        return self.equiv.forward(a_val)

    def unglue_value(self, b_val: Any) -> Any:
        """Given a value in the base type *B*, extract the face value in *A*."""
        return self.equiv.backward(b_val)

    def ua_path(self) -> PathResult:
        """The univalence path *A = B* induced by the equivalence.

        This is the core of univalence: an equivalence gives a path
        in the universe.
        """
        step = PathStep(
            axiom="ua",
            position="root",
            before=self.face_type,
            after=self.base,
        )
        return PathResult(
            found=True,
            path=[step],
            reason=f"ua({self.equiv.source} ≃ {self.equiv.target})",
        )


def glue_compose(g1: GlueType, g2: GlueType) -> GlueType:
    """Compose two glue types: ``Glue(B, A, e₁) ∘ Glue(C, B, e₂)``
    gives ``Glue(C, A, e₂ ∘ e₁)``.

    Requires ``g1.base == g2.face_type``.
    """
    if g1.base != g2.face_type:
        raise ValueError(
            f"Glue types not composable: {g1.base} ≠ {g2.face_type}"
        )
    composed_equiv = Equiv(
        source=g1.face_type,
        target=g2.base,
        forward=lambda a: g2.equiv.forward(g1.equiv.forward(a)),
        backward=lambda c: g1.equiv.backward(g2.equiv.backward(c)),
    )
    return GlueType(
        base=g2.base,
        face_type=g1.face_type,
        equiv=composed_equiv,
    )


# ═══════════════════════════════════════════════════════════════════
#  §9  SET-LEVEL TRUNCATION  (quotient by higher paths)
# ═══════════════════════════════════════════════════════════════════

@dataclass
class Truncation(Generic[T]):
    """0-truncation (set-truncation) of a type.

    Quotients a type by *all* higher paths: any two proofs of
    ``a = b`` are themselves equal.  This makes PyComp a *set*
    (Definition 5.1).

    Concretely: two wrapped values are equal iff their canonical
    forms are equal.
    """

    _value: T
    _canon_fn: Callable[[T], str]

    def __init__(self, value: T, canon_fn: Callable[[T], str]) -> None:
        self._value = value
        self._canon_fn = canon_fn

    @property
    def value(self) -> T:
        return self._value

    def canon(self) -> str:
        return self._canon_fn(self._value)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Truncation):
            return NotImplemented
        return self.canon() == other.canon()

    def __hash__(self) -> int:
        return hash(self.canon())

    def __repr__(self) -> str:
        return f"|{self.canon()}|₀"


def truncate_oterm(t: OTerm) -> Truncation[OTerm]:
    """0-truncate an OTerm: wrap it so equality is by canonical form."""
    return Truncation(t, lambda x: x.canon())


class TruncatedSet(Generic[T]):
    """A set-truncated collection: elements equal up to canonical form.

    Inserting a term whose canon already exists is a no-op (quotient).
    """

    def __init__(self, canon_fn: Callable[[T], str]) -> None:
        self._canon_fn = canon_fn
        self._elements: Dict[str, T] = {}

    def insert(self, value: T) -> bool:
        """Insert *value*; returns ``True`` if actually new."""
        c = self._canon_fn(value)
        if c in self._elements:
            return False
        self._elements[c] = value
        return True

    def __contains__(self, value: T) -> bool:
        return self._canon_fn(value) in self._elements

    def __len__(self) -> int:
        return len(self._elements)

    def __iter__(self):
        return iter(self._elements.values())

    def as_list(self) -> List[T]:
        return list(self._elements.values())


# ═══════════════════════════════════════════════════════════════════
#  §10  PYCOMP ELIMINATOR  (Theorem 4.4 — full dispatch)
# ═══════════════════════════════════════════════════════════════════

class PyCompEliminator:
    """Elimination principle for PyComp (Theorem 4.4).

    To define ``h : PyComp → X`` for a set ``X``, provide:

    1. A handler for **each** of the 13 point constructors.
    2. A proof (assertion) that *h* respects each path constructor.

    The eliminator then dispatches on the term's constructor and
    verifies the path conditions.
    """

    def __init__(self) -> None:
        self._handlers: Dict[PointTag, Callable[..., Any]] = {}
        self._path_checks: List[Tuple[str, Callable[..., bool]]] = []
        self._verified = False

    # ── handler registration (decorator style) ──

    def on(self, tag: PointTag) -> Callable:
        """Register a handler for *tag* (decorator)."""
        def decorator(fn: Callable) -> Callable:
            self._handlers[tag] = fn
            self._verified = False
            return fn
        return decorator

    def on_lit(self, fn: Callable) -> Callable:
        return self.on(PointTag.LIT)(fn)

    def on_var(self, fn: Callable) -> Callable:
        return self.on(PointTag.VAR)(fn)

    def on_op(self, fn: Callable) -> Callable:
        return self.on(PointTag.OP)(fn)

    def on_fold(self, fn: Callable) -> Callable:
        return self.on(PointTag.FOLD)(fn)

    def on_case(self, fn: Callable) -> Callable:
        return self.on(PointTag.CASE)(fn)

    def on_fix(self, fn: Callable) -> Callable:
        return self.on(PointTag.FIX)(fn)

    def on_seq(self, fn: Callable) -> Callable:
        return self.on(PointTag.SEQ)(fn)

    def on_dict(self, fn: Callable) -> Callable:
        return self.on(PointTag.DICT)(fn)

    def on_lam(self, fn: Callable) -> Callable:
        return self.on(PointTag.LAM)(fn)

    def on_map(self, fn: Callable) -> Callable:
        return self.on(PointTag.MAP)(fn)

    def on_catch(self, fn: Callable) -> Callable:
        return self.on(PointTag.CATCH)(fn)

    def on_quotient(self, fn: Callable) -> Callable:
        return self.on(PointTag.QUOTIENT)(fn)

    def on_abstract(self, fn: Callable) -> Callable:
        return self.on(PointTag.ABSTRACT)(fn)

    # ── path-respecting assertions ──

    def respects_path(
        self,
        axiom_name: str,
        check_fn: Callable[..., bool],
    ) -> None:
        """Assert that *h* respects path constructor *axiom_name*.

        *check_fn(h, lhs_term, rhs_term) → bool* must return ``True``.
        """
        self._path_checks.append((axiom_name, check_fn))
        self._verified = False

    # ── dispatch ──

    def _tag_of(self, term: OTerm) -> PointTag:
        tag_map: Dict[type, PointTag] = {
            OLit: PointTag.LIT,
            OVar: PointTag.VAR,
            OOp: PointTag.OP,
            OFold: PointTag.FOLD,
            OCase: PointTag.CASE,
            OFix: PointTag.FIX,
            OSeq: PointTag.SEQ,
            ODict: PointTag.DICT,
            OLam: PointTag.LAM,
            OMap: PointTag.MAP,
            OCatch: PointTag.CATCH,
            OQuotient: PointTag.QUOTIENT,
            OAbstract: PointTag.ABSTRACT,
        }
        return tag_map.get(type(term), PointTag.ABSTRACT)

    def apply(self, term: OTerm) -> Any:
        """Apply the eliminator to a PyComp term.

        Raises ``KeyError`` if no handler is registered for the
        term's constructor.
        """
        tag = self._tag_of(term)
        handler = self._handlers.get(tag)
        if handler is None:
            raise KeyError(
                f"No handler registered for {tag.name}; "
                f"need handlers for all 13 point constructors"
            )
        return handler(term)

    # ── verification ──

    def missing_handlers(self) -> List[PointTag]:
        """Return point constructors that lack a handler."""
        return [t for t in PointTag if t not in self._handlers]

    def is_total(self) -> bool:
        """True iff every point constructor has a handler."""
        return len(self.missing_handlers()) == 0

    def verify_paths(
        self, sample_pairs: Optional[List[Tuple[OTerm, OTerm]]] = None
    ) -> List[str]:
        """Verify all path equations.

        If *sample_pairs* is given, each path-check function is tested
        on those pairs.  Returns list of failure descriptions.
        """
        failures: List[str] = []
        if not self.is_total():
            failures.append(
                f"Missing handlers: {[t.name for t in self.missing_handlers()]}"
            )
        if sample_pairs:
            for axiom_name, check_fn in self._path_checks:
                for lhs, rhs in sample_pairs:
                    try:
                        ok = check_fn(self.apply, lhs, rhs)
                        if not ok:
                            failures.append(
                                f"{axiom_name}: failed on "
                                f"({lhs.canon()}, {rhs.canon()})"
                            )
                    except Exception as exc:
                        failures.append(f"{axiom_name}: raised {exc}")
        self._verified = len(failures) == 0
        return failures


# ═══════════════════════════════════════════════════════════════════
#  §11  ELIMINATION-PRINCIPLE DISPATCHER FOR OTERM
# ═══════════════════════════════════════════════════════════════════

def oterm_dispatch(
    term: OTerm,
    *,
    on_lit: Callable[[OLit], T] = lambda t: t,  # type: ignore[assignment]
    on_var: Callable[[OVar], T] = lambda t: t,  # type: ignore[assignment]
    on_op: Callable[[OOp], T] = lambda t: t,  # type: ignore[assignment]
    on_fold: Callable[[OFold], T] = lambda t: t,  # type: ignore[assignment]
    on_case: Callable[[OCase], T] = lambda t: t,  # type: ignore[assignment]
    on_fix: Callable[[OFix], T] = lambda t: t,  # type: ignore[assignment]
    on_seq: Callable[[OSeq], T] = lambda t: t,  # type: ignore[assignment]
    on_dict: Callable[[ODict], T] = lambda t: t,  # type: ignore[assignment]
    on_lam: Callable[[OLam], T] = lambda t: t,  # type: ignore[assignment]
    on_map: Callable[[OMap], T] = lambda t: t,  # type: ignore[assignment]
    on_catch: Callable[[OCatch], T] = lambda t: t,  # type: ignore[assignment]
    on_quotient: Callable[[OQuotient], T] = lambda t: t,  # type: ignore[assignment]
    on_abstract: Callable[[OAbstract], T] = lambda t: t,  # type: ignore[assignment]
    on_unknown: Callable[[OUnknown], T] = lambda t: t,  # type: ignore[assignment]
) -> T:
    """Dispatch on the constructor of *term* with keyword callbacks.

    Every OTerm variant has a corresponding ``on_*`` kwarg.  Unhandled
    variants fall through to the identity.
    """
    if isinstance(term, OLit):
        return on_lit(term)
    if isinstance(term, OVar):
        return on_var(term)
    if isinstance(term, OOp):
        return on_op(term)
    if isinstance(term, OFold):
        return on_fold(term)
    if isinstance(term, OCase):
        return on_case(term)
    if isinstance(term, OFix):
        return on_fix(term)
    if isinstance(term, OSeq):
        return on_seq(term)
    if isinstance(term, ODict):
        return on_dict(term)
    if isinstance(term, OLam):
        return on_lam(term)
    if isinstance(term, OMap):
        return on_map(term)
    if isinstance(term, OCatch):
        return on_catch(term)
    if isinstance(term, OQuotient):
        return on_quotient(term)
    if isinstance(term, OAbstract):
        return on_abstract(term)
    if isinstance(term, OUnknown):
        return on_unknown(term)
    raise TypeError(f"Unknown OTerm variant: {type(term)}")


def oterm_fold(
    term: OTerm,
    leaf: Callable[[OTerm], T],
    combine: Callable[[str, List[T]], T],
) -> T:
    """Catamorphism (fold) over the OTerm tree.

    *leaf* handles constructors with no children (OLit, OVar, OUnknown).
    *combine(constructor_name, child_results)* handles the rest.
    """
    if isinstance(term, (OLit, OVar, OUnknown)):
        return leaf(term)
    if isinstance(term, OOp):
        children = [oterm_fold(a, leaf, combine) for a in term.args]
        return combine("OOp:" + term.name, children)
    if isinstance(term, OFold):
        ci = oterm_fold(term.init, leaf, combine)
        cc = oterm_fold(term.collection, leaf, combine)
        return combine("OFold:" + term.op_name, [ci, cc])
    if isinstance(term, OCase):
        ct = oterm_fold(term.test, leaf, combine)
        cy = oterm_fold(term.true_branch, leaf, combine)
        cn = oterm_fold(term.false_branch, leaf, combine)
        return combine("OCase", [ct, cy, cn])
    if isinstance(term, OFix):
        cb = oterm_fold(term.body, leaf, combine)
        return combine("OFix:" + term.name, [cb])
    if isinstance(term, OSeq):
        children = [oterm_fold(e, leaf, combine) for e in term.elements]
        return combine("OSeq", children)
    if isinstance(term, ODict):
        children = []
        for k, v in term.pairs:
            children.append(oterm_fold(k, leaf, combine))
            children.append(oterm_fold(v, leaf, combine))
        return combine("ODict", children)
    if isinstance(term, OLam):
        cb = oterm_fold(term.body, leaf, combine)
        return combine("OLam", [cb])
    if isinstance(term, OMap):
        ct = oterm_fold(term.transform, leaf, combine)
        cc = oterm_fold(term.collection, leaf, combine)
        children = [ct, cc]
        if term.filter_pred is not None:
            children.append(oterm_fold(term.filter_pred, leaf, combine))
        return combine("OMap", children)
    if isinstance(term, OCatch):
        cb = oterm_fold(term.body, leaf, combine)
        cd = oterm_fold(term.default, leaf, combine)
        return combine("OCatch", [cb, cd])
    if isinstance(term, OQuotient):
        ci = oterm_fold(term.inner, leaf, combine)
        return combine("OQuotient:" + term.equiv_class, [ci])
    if isinstance(term, OAbstract):
        children = [oterm_fold(a, leaf, combine) for a in term.inputs]
        return combine("OAbstract:" + term.spec, children)
    return leaf(term)  # type: ignore[arg-type]


def oterm_depth(term: OTerm) -> int:
    """Compute the depth of an OTerm tree."""
    return oterm_fold(
        term,
        leaf=lambda _: 0,
        combine=lambda _name, children: 1 + max(children, default=0),
    )


def oterm_size(term: OTerm) -> int:
    """Count the number of nodes in an OTerm tree."""
    return oterm_fold(
        term,
        leaf=lambda _: 1,
        combine=lambda _name, children: 1 + sum(children),
    )


# ═══════════════════════════════════════════════════════════════════
#  §12  FREE-ALGEBRA COMPLETENESS CHECKER
# ═══════════════════════════════════════════════════════════════════

class FreeAlgebraChecker:
    """Verify that path search covers all HIT path constructors.

    Given a set of sample term-pairs, checks:
    1. Every dichotomy D1–D24 was exercised at least once.
    2. Every point constructor appears as an LHS or RHS at least once.
    3. The rewrite closure is reflexive and symmetric (up to depth).

    This is the *completeness* direction: the HIT should freely
    generate all paths from the axioms.
    """

    def __init__(self) -> None:
        self._exercised: Dict[int, int] = {i: 0 for i in range(1, 25)}
        self._tags_seen: Set[PointTag] = set()
        self._pairs_tested: int = 0

    def check_pair(
        self, a: OTerm, b: OTerm, ctx: Optional[FiberCtx] = None
    ) -> List[DichotomyAxiom]:
        """Test which dichotomies fire on *(a, b)* and record coverage."""
        self._pairs_tested += 1
        self._tags_seen.add(PyCompPoint.from_oterm(a).tag)
        self._tags_seen.add(PyCompPoint.from_oterm(b).tag)
        hits = DichotomyRecogniser.detect_all(a, b)
        for d in hits:
            self._exercised[d.index] += 1
        return hits

    def uncovered_dichotomies(self) -> List[DichotomyAxiom]:
        """Return dichotomies never exercised."""
        return [ALL_DICHOTOMIES[i - 1]
                for i, count in self._exercised.items()
                if count == 0]

    def uncovered_tags(self) -> List[PointTag]:
        """Return point constructors never seen."""
        return [t for t in PointTag if t not in self._tags_seen]

    def coverage_ratio(self) -> float:
        """Fraction of dichotomies exercised (0.0–1.0)."""
        exercised = sum(1 for c in self._exercised.values() if c > 0)
        return exercised / 24.0

    def tag_coverage_ratio(self) -> float:
        """Fraction of point constructors seen (0.0–1.0)."""
        return len(self._tags_seen) / len(PointTag)

    def report(self) -> str:
        """Human-readable coverage report."""
        lines = [
            f"Pairs tested:  {self._pairs_tested}",
            f"Dichotomy coverage: {self.coverage_ratio():.0%}  "
            f"({24 - len(self.uncovered_dichotomies())}/24)",
            f"Tag coverage: {self.tag_coverage_ratio():.0%}  "
            f"({len(self._tags_seen)}/{len(PointTag)})",
        ]
        uncov = self.uncovered_dichotomies()
        if uncov:
            lines.append("Uncovered dichotomies:")
            for d in uncov:
                lines.append(f"  {d.name}: {d.description}")
        uncov_tags = self.uncovered_tags()
        if uncov_tags:
            lines.append("Uncovered tags:")
            for t in uncov_tags:
                lines.append(f"  {t.name}")
        return "\n".join(lines)

    def check_symmetry(
        self, a: OTerm, b: OTerm, ctx: Optional[FiberCtx] = None
    ) -> bool:
        """Verify path search is symmetric: path(a,b) ↔ path(b,a)."""
        if ctx is None:
            ctx = FiberCtx(param_duck_types={})
        r_ab = hit_path_equiv(a, b, ctx)
        r_ba = hit_path_equiv(b, a, ctx)
        return r_ab == r_ba

    def check_reflexivity(self, t: OTerm) -> bool:
        """Verify path search finds refl(t)."""
        ctx = FiberCtx(param_duck_types={})
        r = hit_path_equiv(t, t, ctx)
        return r is True


# ═══════════════════════════════════════════════════════════════════
#  §13  EQUIVALENCE REGISTRY WITH CACHING AND COMPOSITION
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class EquivCacheKey:
    """Cache key for path-search results."""
    canon_a: str
    canon_b: str
    duck_types: FrozenSet[Tuple[str, str]]


class EquivRegistry:
    """Caching layer over ``search_path`` / ``hit_path_equiv``.

    Caches results and supports composition: if *a ≡ b* and *b ≡ c*
    have been established, automatically derives *a ≡ c*.
    """

    def __init__(self, max_depth: int = 4) -> None:
        self._cache: Dict[EquivCacheKey, PathResult] = {}
        self._adjacency: Dict[str, Set[str]] = {}
        self._max_depth = max_depth

    def _make_key(
        self, a: OTerm, b: OTerm,
        duck_types: Optional[Dict[str, str]] = None,
    ) -> EquivCacheKey:
        dt = frozenset((duck_types or {}).items())
        return EquivCacheKey(a.canon(), b.canon(), dt)

    def query(
        self,
        a: OTerm,
        b: OTerm,
        duck_types: Optional[Dict[str, str]] = None,
    ) -> PathResult:
        """Check equivalence (cached)."""
        key = self._make_key(a, b, duck_types)
        if key in self._cache:
            return self._cache[key]
        result = search_path(
            a, b,
            max_depth=self._max_depth,
            param_duck_types=duck_types,
        )
        self._cache[key] = result
        if result.found:
            ca, cb = a.canon(), b.canon()
            self._adjacency.setdefault(ca, set()).add(cb)
            self._adjacency.setdefault(cb, set()).add(ca)
        return result

    def is_equivalent(
        self,
        a: OTerm,
        b: OTerm,
        duck_types: Optional[Dict[str, str]] = None,
    ) -> bool:
        """Boolean check (uses cache + transitive closure)."""
        ca, cb = a.canon(), b.canon()
        if ca == cb:
            return True
        if self._transitively_connected(ca, cb):
            return True
        result = self.query(a, b, duck_types)
        return result.found is True

    def compose(
        self,
        a: OTerm,
        b: OTerm,
        c: OTerm,
        duck_types: Optional[Dict[str, str]] = None,
    ) -> Optional[PathResult]:
        """If *a ≡ b* and *b ≡ c*, compose to get *a ≡ c*."""
        r_ab = self.query(a, b, duck_types)
        r_bc = self.query(b, c, duck_types)
        if r_ab.found and r_bc.found:
            composed = compose_paths(r_ab, r_bc)
            key = self._make_key(a, c, duck_types)
            self._cache[key] = composed
            ca, cc = a.canon(), c.canon()
            self._adjacency.setdefault(ca, set()).add(cc)
            self._adjacency.setdefault(cc, set()).add(ca)
            return composed
        return None

    def _transitively_connected(self, ca: str, cb: str) -> bool:
        """BFS on the adjacency graph of established equivalences."""
        if ca == cb:
            return True
        visited: Set[str] = set()
        queue = [ca]
        while queue:
            current = queue.pop(0)
            if current == cb:
                return True
            if current in visited:
                continue
            visited.add(current)
            for nbr in self._adjacency.get(current, set()):
                if nbr not in visited:
                    queue.append(nbr)
        return False

    def cache_size(self) -> int:
        """Number of cached results."""
        return len(self._cache)

    def known_terms(self) -> Set[str]:
        """All canonical forms that appear in the adjacency graph."""
        return set(self._adjacency.keys())

    def clear(self) -> None:
        """Clear caches."""
        self._cache.clear()
        self._adjacency.clear()


# ═══════════════════════════════════════════════════════════════════
#  SELF-TESTS
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import sys
    passed = 0
    failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global passed, failed
        if cond:
            passed += 1
        else:
            failed += 1
            print(f"  FAIL: {msg}", file=sys.stderr)

    print("§1  Path groupoid operations")
    s1 = PathStep("D1", "root", "fix[h](x)", "fold[add](0,x)")
    s2 = PathStep("D5", "root", "fold[add](0,x)", "sum(x)")
    p1 = PathResult(found=True, path=[s1], reason="D1")
    p2 = PathResult(found=True, path=[s2], reason="D5")
    comp = compose_paths(p1, p2)
    _assert(comp.found is True, "compose found")
    _assert(len(comp.path) == 2, "compose length")
    inv = invert_path(p1)
    _assert(inv.path[0].before == s1.after, "invert start")
    _assert(inv.path[0].after == s1.before, "invert end")
    _assert("^{-1}" in inv.path[0].axiom, "invert axiom label")
    r = refl_path(OLit(42))
    _assert(r.found and len(r.path) == 0, "refl")
    _assert(path_length(comp) == 2, "path_length")
    _assert(path_axioms_used(comp) == ["D1", "D5"], "path_axioms_used")

    print("§2  Transport engine")
    engine = TransportEngine()
    engine.register_witness("D1", lambda ev: {**ev, "transported": True})
    cert = ProofCertificate("correctness", "fix[h](x)", {"z3_model": True}, "Z3_PROVEN")
    transported = engine.transport(p1, cert)
    _assert(transported.term_canon == "fold[add](0,x)", "transport endpoint")
    _assert(transported.trust_level == "Z3_PROVEN", "transport preserves trust")
    _assert(transported.evidence.get("transported") is True, "witness ran")
    no_witness = engine.transport(p2, transported)
    _assert(no_witness.trust_level == "UNTRUSTED", "no witness → untrusted")

    print("§3  Fix→Fold recognition (D1)")
    fix_body = OCase(
        OOp("lte", (OVar("n"), OLit(0))),
        OLit(0),
        OOp("add", (OOp("h", (OOp("sub", (OVar("n"), OLit(1))),)),
                     OVar("n"))),
    )
    fix_term = OFix("h", fix_body)
    fold_result = try_extract_fold_from_fix(fix_term)
    _assert(fold_result is not None, "fold recognised")
    if fold_result is not None:
        _assert(isinstance(fold_result, OFold), "is OFold")
        _assert(fold_result.op_name == "add", "fold op is add")

    print("§4  Type equivalence registry")
    reg = TypeEquivRegistry()
    _assert(reg.are_equivalent("bool", "int"), "bool ≃ int")
    _assert(reg.are_equivalent("int", "bool"), "int ≃ bool (symmetric)")
    _assert(reg.are_equivalent("bool", "float"), "bool ≃ float (transitive)")
    _assert(not reg.are_equivalent("str", "int"), "str ≄ int")
    path = reg.get_coercion_path("bool", "float")
    _assert(path is not None and len(path) == 2, "coercion path length")
    _assert(reg.coerce(True, "bool", "int") == 1, "coerce True→1")

    print("§5  Shared symbol table")
    sst = SharedSymbolTable()
    _assert(sst.canonicalize("sorted") == "py_sorted", "sorted canonical")
    _assert(sst.canonicalize("my_func") == "my_func", "unknown passthrough")
    sst.register("my_func", "canon_my_func")
    _assert(sst.lookup("my_func") == "canon_my_func", "user override")
    _assert(sst.is_canonical("py_sorted"), "is_canonical true")
    _assert(not sst.is_canonical("sorted"), "is_canonical false")

    print("§6  PyComp HIT")
    hit = PyCompHIT()
    pt = hit.inject(OLit(42))
    _assert(pt.tag == PointTag.LIT, "inject lit")
    _assert(hit.dichotomy(1).name == "D1_fold_unfold", "dichotomy lookup")
    _assert(len(hit.all_dichotomies()) == 24, "24 dichotomies")
    groups = hit.group_dichotomies()
    _assert(len(groups) == 4, "4 groups")

    print("§7  Dichotomy recogniser")
    dr = DichotomyRecogniser()
    a_fix = OFix("h", OLit(1))
    b_fold = OFold("add", OLit(0), OVar("xs"))
    _assert(dr.recognise_d1(a_fix, b_fold), "D1 recognised")
    _assert(not dr.recognise_d1(OLit(1), OLit(2)), "D1 not on lits")
    lam = OLam(("x",), OOp("f", (OVar("x"),)))
    fn = OOp("f", ())
    _assert(dr.recognise_d24(lam, fn), "D24 recognised")
    all_hits = dr.detect_all(a_fix, b_fold)
    _assert(any(d.index == 1 for d in all_hits), "detect_all includes D1")

    print("§8  Glue type")
    bool_int_equiv = Equiv("bool", "int", int, bool)
    glue = GlueType(base="int", face_type="bool", equiv=bool_int_equiv)
    _assert(glue.at_zero() == "bool", "face at 0")
    _assert(glue.at_one() == "int", "base at 1")
    _assert(glue.glue_value(True) == 1, "glue True → 1")
    _assert(glue.unglue_value(0) == False, "unglue 0 → False")
    ua = glue.ua_path()
    _assert(ua.found and ua.path[0].axiom == "ua", "ua path")
    _assert(bool_int_equiv.check_roundtrip([True, False]), "roundtrip")

    int_float_equiv = Equiv("int", "float", float, int)
    glue2 = GlueType(base="float", face_type="int", equiv=int_float_equiv)
    composed_glue = glue_compose(glue, glue2)
    _assert(composed_glue.face_type == "bool", "composed face")
    _assert(composed_glue.base == "float", "composed base")
    _assert(composed_glue.glue_value(True) == 1.0, "composed glue")

    print("§9  Truncation")
    t1 = truncate_oterm(OOp("add", (OLit(1), OLit(2))))
    t2 = truncate_oterm(OOp("add", (OLit(1), OLit(2))))
    _assert(t1 == t2, "truncated equality")
    _assert(hash(t1) == hash(t2), "truncated hash")
    ts = TruncatedSet(lambda t: t.canon())
    _assert(ts.insert(OLit(1)) is True, "insert new")
    _assert(ts.insert(OLit(1)) is False, "insert dup")
    _assert(len(ts) == 1, "truncated set size")

    print("§10  PyComp eliminator")
    elim = PyCompEliminator()

    @elim.on_lit
    def h_lit(t: OLit):
        return ("lit", t.value)

    @elim.on(PointTag.VAR)
    def h_var(t: OVar):
        return ("var", t.name)

    @elim.on_op
    def h_op(t: OOp):
        return ("op", t.name)

    _assert(elim.apply(OLit(7)) == ("lit", 7), "elim lit")
    _assert(elim.apply(OVar("x")) == ("var", "x"), "elim var")
    _assert(not elim.is_total(), "not total yet")
    missing = elim.missing_handlers()
    _assert(PointTag.FOLD in missing, "fold missing")

    print("§11  oterm_dispatch + fold")
    depth = oterm_depth(OOp("add", (OLit(1), OOp("mul", (OLit(2), OLit(3))))))
    _assert(depth == 2, f"depth={depth}")
    size = oterm_size(OOp("add", (OLit(1), OLit(2))))
    _assert(size == 3, f"size={size}")
    tag = oterm_dispatch(
        OLit(42),
        on_lit=lambda t: "lit",
        on_var=lambda t: "var",
    )
    _assert(tag == "lit", "dispatch lit")

    print("§12  Free-algebra completeness checker")
    checker = FreeAlgebraChecker()
    checker.check_pair(a_fix, b_fold)
    _assert(checker.coverage_ratio() > 0.0, "coverage > 0")
    _assert(checker.check_reflexivity(OLit(1)), "reflexivity")
    _assert(checker.check_symmetry(OLit(1), OLit(1)), "symmetry refl")

    print("§13  Equivalence registry")
    ereg = EquivRegistry(max_depth=2)
    t_a = OOp("add", (OLit(1), OLit(2)))
    t_b = OOp("add", (OLit(2), OLit(1)))
    _assert(ereg.is_equivalent(t_a, t_a), "refl in registry")
    r1 = ereg.query(t_a, t_b, duck_types={"p0": "int"})
    _assert(ereg.cache_size() >= 1, "cache populated")

    print()
    print(f"Results: {passed} passed, {failed} failed")
    sys.exit(1 if failed else 0)
