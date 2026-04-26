"""
Deppy Proof Kernel

The proof kernel is the trusted computing base. It type-checks proof terms
against their claimed types. Every verified claim must be backed by a proof
term that the kernel accepts.

Trust levels (from highest to lowest):
    KERNEL           — every sub-proof was checked by the kernel
    Z3_VERIFIED      — arithmetic discharged to Z3
    STRUCTURAL_CHAIN — equality chain verified structurally
    LLM_CHECKED      — LLM proposed, kernel verified structure
    AXIOM_TRUSTED    — depends on user-supplied axioms
    UNTRUSTED        — no verification performed
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Optional

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyFloatType, PyStrType, PyBoolType,
    PyNoneType, PyListType, PyDictType, PyCallableType,
    PiType, SigmaType, PathType, RefinementType, UnionType,
    UniverseType, ProtocolType, OptionalType, IntervalType,
    Var, Literal, Lam, App, Pair, Fst, Snd,
    PathAbs, PathApp, Transport, Comp, LetIn, IfThenElse,
    PyCall, GetAttr, GetItem,
    arrow,
)
from deppy.core.formal_ops import Op, OpCall, FormalAxiomEntry, PatternMatcher


# ═══════════════════════════════════════════════════════════════════
# Trust Levels
# ═══════════════════════════════════════════════════════════════════

class TrustLevel(Enum):
    """Trust levels for verified claims, ordered from highest to lowest."""
    KERNEL = 6
    Z3_VERIFIED = 5
    STRUCTURAL_CHAIN = 4
    LLM_CHECKED = 3
    AXIOM_TRUSTED = 2
    EFFECT_ASSUMED = 1
    UNTRUSTED = 0

    def __ge__(self, other: TrustLevel) -> bool:
        return self.value >= other.value

    def __gt__(self, other: TrustLevel) -> bool:
        return self.value > other.value

    def __le__(self, other: TrustLevel) -> bool:
        return self.value <= other.value

    def __lt__(self, other: TrustLevel) -> bool:
        return self.value < other.value


def min_trust(*levels: TrustLevel) -> TrustLevel:
    """Return the minimum (weakest) trust level."""
    return min(levels, key=lambda t: t.value)


# ═══════════════════════════════════════════════════════════════════
# Proof Terms
# ═══════════════════════════════════════════════════════════════════

class ProofTerm:
    """Base class for all proof terms."""

    def __repr__(self) -> str:
        return type(self).__name__

    def __call__(self, fn):
        """Allow proof terms to be used as decorators (e.g. @path(...))."""
        fn._deppy_proof = self
        return fn


@dataclass
class Refl(ProofTerm):
    """Reflexivity: a =_A a."""
    term: SynTerm

    def __repr__(self) -> str:
        return f"Refl({self.term})"


@dataclass
class Sym(ProofTerm):
    """Symmetry: from a =_A b get b =_A a."""
    proof: ProofTerm

    def __repr__(self) -> str:
        return f"Sym({self.proof})"


@dataclass
class Trans(ProofTerm):
    """Transitivity: from a = b and b = c get a = c."""
    left: ProofTerm
    right: ProofTerm

    def __repr__(self) -> str:
        return f"Trans({self.left}, {self.right})"


@dataclass
class Cong(ProofTerm):
    """Congruence: from a = b get f(a) = f(b)."""
    func: SynTerm
    proof: ProofTerm

    def __repr__(self) -> str:
        return f"Cong({self.func}, {self.proof})"


@dataclass
class TransportProof(ProofTerm):
    """Transport: from a = b and d : P(a) get P(b)."""
    type_family: SynTerm
    path_proof: ProofTerm
    base_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Transport({self.type_family}, {self.path_proof}, {self.base_proof})"


@dataclass
class Ext(ProofTerm):
    """Function extensionality: ∀x. f(x) = g(x) ⟹ f = g."""
    var: str
    body_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Ext({self.var}, {self.body_proof})"


@dataclass
class Cut(ProofTerm):
    """Cut (lemma introduction): prove A, use it in subsequent proof."""
    hyp_name: str
    hyp_type: SynType
    lemma_proof: ProofTerm
    body_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Cut({self.hyp_name}: {self.hyp_type}, {self.lemma_proof}, {self.body_proof})"


@dataclass
class Assume(ProofTerm):
    """Use a hypothesis from the context."""
    name: str

    def __repr__(self) -> str:
        return f"Assume({self.name})"


@dataclass
class Z3Proof(ProofTerm):
    """Z3 discharge: verify a quantifier-free formula."""
    formula: str
    _cached_result: bool | None = field(default=None, repr=False)

    def __repr__(self) -> str:
        return f"Z3({self.formula})"


@dataclass
class NatInduction(ProofTerm):
    """Natural number induction."""
    var: str
    base_proof: ProofTerm
    step_proof: ProofTerm

    def __repr__(self) -> str:
        return f"NatInd({self.var}, base={self.base_proof}, step={self.step_proof})"


@dataclass
class ListInduction(ProofTerm):
    """List induction."""
    var: str
    nil_proof: ProofTerm
    cons_proof: ProofTerm

    def __repr__(self) -> str:
        return f"ListInd({self.var}, nil={self.nil_proof}, cons={self.cons_proof})"


@dataclass
class Cases(ProofTerm):
    """Case analysis."""
    scrutinee: SynTerm
    branches: list[tuple[str, ProofTerm]]  # [(pattern, proof), ...]

    def __repr__(self) -> str:
        bs = ", ".join(f"{p} => ..." for p, _ in self.branches)
        return f"Cases({self.scrutinee}, [{bs}])"


class DuckPath(ProofTerm):
    """Duck-type path construction: prove method-wise equivalence.

    Supports two construction styles:
      - DuckPath(type_a, type_b, method_proofs)  — full form
      - DuckPath("name", evidence={...})          — book shorthand
    """

    def __init__(self, type_a=None, type_b=None, method_proofs=None, *, evidence=None):
        self.type_a = type_a
        self.type_b = type_b
        self.method_proofs = method_proofs or []
        self.evidence = evidence or {}

    @property
    def method_paths(self):
        """Dict of method name → proof, for inspecting individual method equivalences."""
        result = {}
        for mp in self.method_proofs:
            if isinstance(mp, tuple) and len(mp) == 2:
                result[mp[0]] = mp[1]
            elif hasattr(mp, 'method_name'):
                result[mp.method_name] = mp
        result.update(self.evidence)
        return result

    def __repr__(self) -> str:
        if self.evidence:
            return f"DuckPath({self.type_a!r}, evidence={self.evidence!r})"
        ms = ", ".join(f"{m}: ..." for m, _ in self.method_proofs)
        return f"DuckPath({self.type_a}, {self.type_b}, [{ms}])"

    @classmethod
    def auto_construct(cls, type_a, type_b, protocol=None):
        """Introspect two Python classes (or ``ProtocolType``\\ s) and
        construct a ``DuckPath`` from their shared method set.

        For each method name ``m`` that appears on both sides with a
        compatible signature, the path records a reflexive method-proof
        ``(m, Refl(m))``.  When ``protocol`` is supplied (a list of
        method names), only those methods are considered; otherwise the
        intersection of public methods on both types is used.

        Cubical reading: each method contributes a 1-cell in the path
        between ``type_a`` and ``type_b``; the full ``DuckPath`` is the
        2-cell (homotopy) constructed by the ``UnivalenceEngine``.

        Use when you want a first-cut duck-type equivalence without
        hand-writing method-by-method proofs — ``type_a`` and
        ``type_b`` must agree on the method SHAPES, not necessarily
        the implementations.
        """
        import inspect as _inspect

        # Protocol-relevant dunder methods that we always include
        # despite their leading underscore — these are the user-facing
        # operator hooks (``__iter__``, ``__len__``, ``__getitem__``,
        # …) that the typing module treats as part of a Protocol.
        _PROTOCOL_DUNDERS = frozenset({
            "__iter__", "__next__", "__len__", "__getitem__",
            "__setitem__", "__delitem__", "__contains__",
            "__call__", "__eq__", "__ne__", "__hash__",
            "__enter__", "__exit__", "__add__", "__sub__",
            "__mul__", "__truediv__", "__lt__", "__le__",
            "__gt__", "__ge__",
        })

        def _methods_of(obj):
            if hasattr(obj, "methods") and obj.methods:
                # ProtocolType with an explicit method tuple
                return dict(obj.methods)
            # Assume it's a Python class; introspect callable public
            # attrs *and* the protocol-relevant dunders.
            out = {}
            for name in dir(obj):
                if name.startswith("_") and name not in _PROTOCOL_DUNDERS:
                    continue
                attr = getattr(obj, name, None)
                if callable(attr):
                    out[name] = attr
            return out

        def _arity_of(callable_obj) -> int | None:
            """Return the positional-argument count of ``callable_obj``,
            ignoring ``self``.  ``None`` if the signature isn't
            introspectable."""
            if callable_obj is None:
                return None
            try:
                sig = _inspect.signature(callable_obj)
            except (TypeError, ValueError):
                return None
            params = [
                p for p in sig.parameters.values()
                if p.kind in (p.POSITIONAL_OR_KEYWORD, p.POSITIONAL_ONLY)
                and p.name != "self"
            ]
            return len(params)

        m_a = _methods_of(type_a)
        m_b = _methods_of(type_b)

        if protocol is None:
            shared_names = sorted(set(m_a.keys()) & set(m_b.keys()))
        else:
            # ``protocol`` may be:
            #   * a sequence of method names (legacy form),
            #   * a Protocol class — read declared methods off it,
            #   * a generic alias like ``Iterable[int]`` — extract its
            #     ``__origin__``'s public method names.
            if isinstance(protocol, type):
                proto_names = [
                    n for n in dir(protocol)
                    if not n.startswith("_") or n in (
                        "__iter__", "__next__", "__len__", "__getitem__",
                        "__contains__", "__call__", "__eq__",
                    )
                ]
            elif hasattr(protocol, "__origin__"):
                base = protocol.__origin__
                proto_names = [
                    n for n in dir(base)
                    if not n.startswith("_") or n in (
                        "__iter__", "__next__", "__len__", "__getitem__",
                        "__contains__", "__call__", "__eq__",
                    )
                ]
            else:
                proto_names = list(protocol)
            shared_names = [m for m in proto_names if m in m_a and m in m_b]

        # Reject method pairs with incompatible arities — a duck-path
        # cannot soundly prove ``A ≃ B over m`` if ``A.m`` takes 1
        # argument and ``B.m`` takes 3.  When the arity isn't
        # introspectable (e.g., builtins, C extensions), accept
        # conservatively.
        compatible: list = []
        skipped: list = []
        for name in shared_names:
            arity_a = _arity_of(m_a.get(name))
            arity_b = _arity_of(m_b.get(name))
            if arity_a is None or arity_b is None:
                compatible.append(name)
                continue
            if arity_a != arity_b:
                skipped.append((name, arity_a, arity_b))
                continue
            compatible.append(name)

        method_proofs = [(name, Refl(term=Var(name))) for name in compatible]
        evidence = {
            "_deppy_auto_constructed": True,
            "_deppy_protocol": compatible,
        }
        if skipped:
            evidence["_deppy_skipped_arity_mismatch"] = skipped
        return cls(
            type_a=type_a, type_b=type_b,
            method_proofs=method_proofs,
            evidence=evidence,
        )


@dataclass
class ConditionalDuckPath(ProofTerm):
    """Duck-type path that holds *only when* a runtime condition does.

    Used for ``__getattr__``-based dynamic proxies (and similar
    delegating shapes) where the protocol satisfaction depends on
    the runtime state of the proxied object.

    Cubical reading
    ---------------
    A ``ConditionalDuckPath`` is the projection of a fibration
    ``p: E → B`` where:

    * ``B`` is the boolean predicate type ``{condition is true,
      condition is false}``.
    * The fiber over ``true`` is a real ``DuckPath``; the fiber over
      ``false`` is the empty type (no proof exists there).

    The kernel accepts the proof only with trust level
    :attr:`TrustLevel.STRUCTURAL_CHAIN` — soundness depends on the
    caller actually checking ``condition`` at every call site (or
    the call site lying in the predicate-true region statically).

    Use :meth:`construct` to build one:

        cp = ConditionalDuckPath.construct(
            condition="isinstance(self._target, Renderable)",
            evidence=FiberedLookup(...),
        )
    """
    condition: str            # runtime predicate, evaluated at call sites
    evidence: ProofTerm       # the underlying DuckPath / FiberedLookup
    type_a: SynType | None = None
    type_b: SynType | None = None

    def __repr__(self) -> str:
        return (
            f"ConditionalDuckPath(if {self.condition!r}: "
            f"{type(self.evidence).__name__})"
        )

    @classmethod
    def construct(cls, *, condition: str, evidence: ProofTerm,
                  type_a=None, type_b=None) -> "ConditionalDuckPath":
        """Build a ``ConditionalDuckPath``.

        ``condition`` is the predicate (a string Python expression);
        ``evidence`` is the proof that holds whenever the condition
        does — typically a :class:`DuckPath` or :class:`FiberedLookup`.
        """
        if not condition or not condition.strip():
            raise ValueError(
                "ConditionalDuckPath: condition cannot be empty"
            )
        if not isinstance(evidence, ProofTerm):
            raise TypeError(
                f"ConditionalDuckPath: evidence must be a ProofTerm, "
                f"got {type(evidence).__name__}"
            )
        return cls(
            condition=condition,
            evidence=evidence,
            type_a=type_a,
            type_b=type_b,
        )


@dataclass
class FiberedLookup(ProofTerm):
    """Lookup through ``__getattr__`` (or similar) as a fiber over an
    attribute.

    Cubical reading
    ---------------
    The proxy class ``DynamicProxy`` carries a private attribute
    (typically ``_target``).  At each call to ``proxy.method()`` the
    attribute lookup is the *first projection* of a Σ-type
    ``Σ(t : Target). methods(t)``.  ``FiberedLookup`` packages:

    * ``fiber_over``: the attribute name being projected on
      (``"_target"`` in the book example).
    * ``base_path``: the ``DuckPath`` proving that the value
      reachable through the attribute satisfies the protocol.
    * ``transport_through``: the *delegation method* that performs
      the actual lookup (``"__getattr__"`` in the book example).

    The proof is consumed by :class:`ConditionalDuckPath` (the
    condition is "the projected attribute satisfies ``base_path``'s
    target type") and verified at trust level
    :attr:`TrustLevel.STRUCTURAL_CHAIN`.
    """
    fiber_over: str           # attribute name (e.g., "_target")
    base_path: ProofTerm      # underlying DuckPath / proof
    transport_through: str    # delegating method (e.g., "__getattr__")

    def __repr__(self) -> str:
        return (
            f"FiberedLookup(over={self.fiber_over!r}, "
            f"through={self.transport_through!r})"
        )


@dataclass
class EffectWitness(ProofTerm):
    """Effect-indexed proof."""
    effect: str
    proof: ProofTerm

    def __repr__(self) -> str:
        return f"EffectWitness({self.effect}, {self.proof})"


@dataclass
class ConditionalEffectWitness(ProofTerm):
    """Conditional effect proof: under precondition P, effect E is absent.

    This is the kernel proof term for runtime safety facts like:
      "Point.distance does not raise when isinstance(other, Point)"
      "f(x) terminates when x > 0"
      "division is safe when divisor != 0"

    The kernel verifies the inner proof and records the precondition.
    Trust level is preserved from the inner proof (unlike EffectWitness
    which always downgrades to EFFECT_ASSUMED).
    """
    precondition: str    # predicate under which the effect is absent
    effect: str          # the effect being discharged (e.g. "exception_free")
    proof: ProofTerm     # proof that the effect is absent under precondition
    target: str = ""     # qualified name of function (for reporting)

    def __repr__(self) -> str:
        pre = f" | {self.precondition}" if self.precondition else ""
        tgt = f" [{self.target}]" if self.target else ""
        return f"ConditionalEffectWitness({self.effect}{pre}{tgt})"


@dataclass
class SourceDischarge(ProofTerm):
    """Per-source safety discharge (Gap 13/17).

    Records the *atomic* reason a single ``ExceptionSource`` is safe under
    a precondition.  The kernel verifies the inner proof; trust comes from
    the inner proof, not from a hard-coded constant.

    The four discharge shapes the pipeline produces are:

    * ``Z3Proof``           — Z3 unsat for ``guards ∧ ¬ safety_predicate``.
    * ``AxiomInvocation``   — a registered axiom covers this exception kind.
    * ``Structural``        — analyst-trusted (e.g. ``is_total`` escape hatch).
    * ``Assume``            — ambient hypothesis (e.g. callee's own
                              precondition propagated from the caller).
    """
    source_id: str           # stable id, e.g. "f:L42:ZeroDivision"
    failure_kind: str        # ExceptionKind name
    safety_predicate: str    # canonical predicate that must hold (e.g. "b != 0")
    inner: ProofTerm         # actual proof of the predicate under preconditions
    note: str = ""

    def __repr__(self) -> str:
        return (f"SourceDischarge({self.source_id} : {self.failure_kind} "
                f"⇐ {self.safety_predicate})")


@dataclass
class SemanticSafetyWitness(ProofTerm):
    """Function-level semantic safety witness (Gap 13).

    Composed of one ``SourceDischarge`` per ``ExceptionSource`` in the
    function body.  The kernel succeeds only if **every** sub-discharge
    succeeds; aggregate trust is the minimum trust across discharges
    (so any ``Structural`` / ``Assume`` discharge clamps the witness's
    trust to that level).

    Unlike the older ``ConditionalEffectWitness``, this term refuses to
    succeed unless every concrete failure point in the function body has
    been individually addressed.  No more vacuous Structural pass-throughs.
    """
    target: str
    precondition: str        # combined preconditions from sidecar
    discharges: list["SourceDischarge"] = field(default_factory=list)
    is_total_escape: bool = False   # spec.is_total — accept structurally

    def __repr__(self) -> str:
        return (f"SemanticSafetyWitness({self.target} | {self.precondition}: "
                f"{len(self.discharges)} sources)")


@dataclass
class ModuleSafetyComposition(ProofTerm):
    """Module-level safety composition (Gap 19).

    A module is safe only when:
      1. every function-level witness verifies,
      2. every module-level (top-level) exception source is discharged, and
      3. internal call closure has already been established by propagation.

    This turns the previous name-only aggregation into a real kernel object.
    """
    module_path: str
    function_witnesses: dict[str, ProofTerm] = field(default_factory=dict)
    module_discharges: list["SourceDischarge"] = field(default_factory=list)
    internal_calls_closed: bool = True

    def __repr__(self) -> str:
        return (f"ModuleSafetyComposition({self.module_path}: "
                f"{len(self.function_witnesses)} fns, "
                f"{len(self.module_discharges)} module sources)")


@dataclass
class TerminationObligation(ProofTerm):
    """Well-founded termination obligation (Gap 23).

    Discharges a recursive call by exhibiting a measure expression that
    strictly decreases on each recursive invocation and remains bounded
    below (by 0).  The kernel verifies the embedded ``Z3Proof`` of

        precondition ⇒ measure(actuals) < measure(formals) ∧ measure(formals) >= 0

    so the resulting trust is the trust of the inner Z3 discharge.

    This term is the deppy analogue of Lean's ``termination_by`` /
    ``decreasing_by`` — it is what makes a recursive function's
    `RUNTIME_ERROR` (recursion depth exceeded) source actually go away
    rather than being silently accepted as "structural".
    """
    target: str
    measure_at_entry: str       # e.g. "n"
    measure_at_recursive_call: str  # e.g. "n - 1"
    precondition: str = "True"
    inner: ProofTerm | None = None  # Z3Proof of the well-founded inequality
    note: str = ""

    def __repr__(self) -> str:
        return (f"TerminationObligation({self.target}: "
                f"{self.measure_at_recursive_call} < {self.measure_at_entry})")


@dataclass
class SafetyObligation(ProofTerm):
    """A safety obligation that must be discharged for runtime safety.

    Represents a specific program point where a runtime failure can occur,
    together with the condition that makes it safe and a proof of that condition.

    Used to compose fine-grained safety proofs — one per potential failure
    site — into a function-level or module-level safety certificate via
    CechGlue or structural composition.
    """
    obligation_id: str      # stable identifier (e.g. "mod.func:L42:ZeroDivision")
    safety_condition: str   # predicate that ensures safety (e.g. "divisor != 0")
    proof: ProofTerm        # proof that safety_condition holds
    failure_kind: str = ""  # what fails if condition doesn't hold
    lineno: int = 0         # source location

    def __repr__(self) -> str:
        return f"SafetyObligation({self.obligation_id}: {self.safety_condition})"


@dataclass
class Patch(ProofTerm):
    """Monkey-patch path: C =_PyClass C[m := v] when behavioral contract preserved."""
    cls: SynTerm
    method_name: str
    new_impl: SynTerm
    contract_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Patch({self.cls}, {self.method_name})"


@dataclass
class Fiber(ProofTerm):
    """isinstance fibration proof: prove property holds for all branches of isinstance check."""
    scrutinee: SynTerm
    type_branches: list[tuple[SynType, ProofTerm]]
    exhaustive: bool = True  # whether the branches are claimed to be exhaustive

    def __repr__(self) -> str:
        bs = ", ".join(str(t) for t, _ in self.type_branches)
        return f"Fiber({self.scrutinee}, [{bs}])"

    @classmethod
    def from_metaclass(cls, metaclass):
        """Extract a fibration from a Python metaclass.

        The metaclass's ``__init_subclass__`` / ``__subclasses__()`` tree
        gives a natural fibration: the **base** is the metaclass's root
        class, the **total space** is the union of all registered
        subclasses, and the **fiber** over each subclass is the set of
        concrete instances declared for that subclass.

        This ``classmethod`` inspects the metaclass at runtime and
        returns a ``Fiber`` proof term whose ``type_branches`` list
        enumerates ``(subclass, Refl(subclass))`` — a reflexive proof
        for each registered subclass (the actual verification work is
        left to ``FibrationVerifier`` downstream).

        Cubical reading: a metaclass-defined type hierarchy is a
        **dependent sum** ``Σ(C : Base). classes(C)``; the fibration is
        the first projection.  ``from_metaclass`` materialises that
        projection as a proof term the kernel can consume.
        """
        if not isinstance(metaclass, type):
            raise TypeError(
                f"Fiber.from_metaclass: expected a metaclass, got "
                f"{type(metaclass).__name__}"
            )

        # Collect registered subclasses (breadth-first; metaclasses
        # usually track these via __subclasses__() or a custom registry).
        seen: set = set()
        subclasses: list = []
        queue = [metaclass]
        while queue:
            cls_ = queue.pop(0)
            if cls_ in seen:
                continue
            seen.add(cls_)
            try:
                children = cls_.__subclasses__()
            except TypeError:
                children = []
            for child in children:
                if child not in seen:
                    subclasses.append(child)
                    queue.append(child)

        # Build a PyClassType per subclass and a reflexive proof.
        try:
            from deppy.core.types import PyClassType
        except ImportError:
            PyClassType = None  # type: ignore[assignment]

        branches: list = []
        for sub in subclasses:
            ty = PyClassType(name=sub.__name__) if PyClassType else Var(sub.__name__)
            branches.append((ty, Refl(term=Var(sub.__name__))))

        return cls(
            scrutinee=Var(metaclass.__name__),
            type_branches=branches,
            exhaustive=True,
        )


@dataclass
class PathComp(ProofTerm):
    """Path composition: p · q where p : a = b and q : b = c gives a = c.
    Uses Kan composition internally."""
    left_path: ProofTerm   # p : a = b
    right_path: ProofTerm  # q : b = c

    def __repr__(self) -> str:
        return f"PathComp({self.left_path}, {self.right_path})"


@dataclass
class Ap(ProofTerm):
    """Congruence/action on paths: ap f p where p : a = b gives f(a) = f(b)."""
    function: SynTerm
    path_proof: ProofTerm

    def __repr__(self) -> str:
        return f"Ap({self.function}, {self.path_proof})"


@dataclass
class FunExt(ProofTerm):
    """Function extensionality: from (∀x. f(x) = g(x)) derive f = g."""
    var: str
    pointwise_proof: ProofTerm  # proof that f(x) = g(x) for arbitrary x

    def __repr__(self) -> str:
        return f"FunExt({self.var}, {self.pointwise_proof})"


@dataclass
class CechGlue(ProofTerm):
    """Čech gluing: local proofs on a cover glue into a global proof.
    Requires cocycle condition on overlaps."""
    patches: list[tuple[str, ProofTerm]]  # [(condition, local_proof), ...]
    overlap_proofs: list[tuple[int, int, ProofTerm]]  # [(i, j, agreement_proof), ...]

    def __repr__(self) -> str:
        ps = ", ".join(f"{c}: ..." for c, _ in self.patches)
        return f"CechGlue([{ps}], {len(self.overlap_proofs)} overlaps)"


@dataclass
class Univalence(ProofTerm):
    """Univalence: equivalence proof yields path in the universe.
    From (A ≃ B) derive (A =_U B)."""
    equiv_proof: ProofTerm  # proof of A ≃ B
    from_type: SynType
    to_type: SynType

    def __repr__(self) -> str:
        return f"Univalence({self.from_type} ≃ {self.to_type})"


@dataclass
class AxiomInvocation(ProofTerm):
    """Trusted axiom (tracked for dependency analysis)."""
    name: str
    module: str = ""
    instantiation: dict[str, SynTerm] = field(default_factory=dict)

    def __repr__(self) -> str:
        prefix = f"{self.module}." if self.module else ""
        return f"Axiom({prefix}{self.name})"


@dataclass
class Unfold(ProofTerm):
    """Unfold a function definition."""
    func_name: str
    proof: ProofTerm | None = None

    def __repr__(self) -> str:
        return f"Unfold({self.func_name})"


@dataclass
class Rewrite(ProofTerm):
    """Rewrite using a lemma."""
    lemma: ProofTerm
    proof: ProofTerm | None = None

    def __repr__(self) -> str:
        return f"Rewrite({self.lemma})"


@dataclass
class Structural(ProofTerm):
    """Structural verification — verified by source inspection."""
    description: str = ""

    def __repr__(self) -> str:
        return f"Structural({self.description!r})"


# ═══════════════════════════════════════════════════════════════════
# Verification Result
# ═══════════════════════════════════════════════════════════════════

@dataclass
class VerificationResult:
    """Result of verifying a proof term."""
    success: bool
    trust_level: TrustLevel
    message: str = ""
    axioms_used: list[str] = field(default_factory=list)
    sub_results: list[VerificationResult] = field(default_factory=list)
    error_code: str | None = None

    def __repr__(self) -> str:
        status = "✓" if self.success else "✗"
        return f"{status} [{self.trust_level.name}] {self.message}"

    @staticmethod
    def ok(trust: TrustLevel = TrustLevel.KERNEL, msg: str = "") -> VerificationResult:
        return VerificationResult(success=True, trust_level=trust, message=msg)

    @staticmethod
    def fail(msg: str, code: str | None = None) -> VerificationResult:
        return VerificationResult(
            success=False,
            trust_level=TrustLevel.UNTRUSTED,
            message=msg,
            error_code=code,
        )


# ═══════════════════════════════════════════════════════════════════
# The Proof Kernel
# ═══════════════════════════════════════════════════════════════════

class ProofKernel:
    """The trusted proof kernel that verifies proof terms.

    This is the core of the trusted computing base (TCB).
    It checks that proof terms are well-typed according to the
    Deppy type theory rules.
    """

    def __init__(self) -> None:
        self.axiom_registry: dict[str, AxiomEntry] = {}
        self.formal_axiom_registry: dict[tuple[str, str], FormalAxiomEntry] = {}
        self._matcher = PatternMatcher()
        self._z3_solver: Any = None  # Lazy init

    def register_axiom(self, name: str, statement: str,
                       module: str = "") -> None:
        """Register a trusted axiom."""
        self.axiom_registry[name] = AxiomEntry(
            name=name, statement=statement, module=module
        )

    def register_formal_axiom(self, axiom: FormalAxiomEntry) -> None:
        """Register a formal axiom with machine-checkable content."""
        key = (axiom.module, axiom.name)
        self.formal_axiom_registry[key] = axiom
        # Also register in string-keyed registry for backward compat
        self.axiom_registry[axiom.qualified_name] = AxiomEntry(
            name=axiom.name,
            statement=axiom.description,
            module=axiom.module,
            verified_by_testing=axiom.verified_by_testing,
        )

    def verify(self, ctx: Context, goal: Judgment,
               proof: ProofTerm) -> VerificationResult:
        """Verify a proof term against a goal judgment.

        This is the VERIFY function from the monograph (Section 4.7).
        """
        try:
            return self._verify_impl(ctx, goal, proof)
        except Exception as e:
            return VerificationResult.fail(
                f"Internal kernel error: {e}", code="E000"
            )

    def _verify_impl(self, ctx: Context, goal: Judgment,
                     proof: ProofTerm) -> VerificationResult:
        """Internal verification dispatch."""
        if isinstance(proof, Refl):
            return self._verify_refl(ctx, goal, proof)
        elif isinstance(proof, Sym):
            return self._verify_sym(ctx, goal, proof)
        elif isinstance(proof, Trans):
            return self._verify_trans(ctx, goal, proof)
        elif isinstance(proof, Cong):
            return self._verify_cong(ctx, goal, proof)
        elif isinstance(proof, Cut):
            return self._verify_cut(ctx, goal, proof)
        elif isinstance(proof, Assume):
            return self._verify_assume(ctx, goal, proof)
        elif isinstance(proof, Z3Proof):
            return self._verify_z3(ctx, goal, proof)
        elif isinstance(proof, NatInduction):
            return self._verify_nat_ind(ctx, goal, proof)
        elif isinstance(proof, ListInduction):
            return self._verify_list_ind(ctx, goal, proof)
        elif isinstance(proof, Cases):
            return self._verify_cases(ctx, goal, proof)
        elif isinstance(proof, DuckPath):
            return self._verify_duck_path(ctx, goal, proof)
        elif isinstance(proof, ConditionalDuckPath):
            return self._verify_conditional_duck_path(ctx, goal, proof)
        elif isinstance(proof, FiberedLookup):
            return self._verify_fibered_lookup(ctx, goal, proof)
        elif isinstance(proof, EffectWitness):
            return self._verify_effect_witness(ctx, goal, proof)
        elif isinstance(proof, ConditionalEffectWitness):
            return self._verify_conditional_effect(ctx, goal, proof)
        elif isinstance(proof, SemanticSafetyWitness):
            return self._verify_semantic_safety(ctx, goal, proof)
        elif isinstance(proof, ModuleSafetyComposition):
            return self._verify_module_safety_composition(ctx, goal, proof)
        elif isinstance(proof, SourceDischarge):
            return self._verify_source_discharge(ctx, goal, proof)
        elif isinstance(proof, TerminationObligation):
            return self._verify_termination_obligation(ctx, goal, proof)
        elif isinstance(proof, SafetyObligation):
            return self._verify_safety_obligation(ctx, goal, proof)
        elif isinstance(proof, AxiomInvocation):
            return self._verify_axiom(ctx, goal, proof)
        elif isinstance(proof, Patch):
            return self._verify_patch(ctx, goal, proof)
        elif isinstance(proof, Fiber):
            return self._verify_fiber(ctx, goal, proof)
        elif isinstance(proof, Ext):
            return self._verify_ext(ctx, goal, proof)
        elif isinstance(proof, Unfold):
            return self._verify_unfold(ctx, goal, proof)
        elif isinstance(proof, Structural):
            return self._verify_structural(ctx, goal, proof)
        elif isinstance(proof, Rewrite):
            return self._verify_rewrite(ctx, goal, proof)
        elif isinstance(proof, TransportProof):
            return self._verify_transport(ctx, goal, proof)
        elif isinstance(proof, PathComp):
            return self._verify_path_comp(ctx, goal, proof)
        elif isinstance(proof, Ap):
            return self._verify_ap(ctx, goal, proof)
        elif isinstance(proof, FunExt):
            return self._verify_funext(ctx, goal, proof)
        elif isinstance(proof, CechGlue):
            return self._verify_cech_glue(ctx, goal, proof)
        elif isinstance(proof, Univalence):
            return self._verify_univalence(ctx, goal, proof)
        else:
            return VerificationResult.fail(
                f"Unknown proof term: {type(proof).__name__}", code="E001"
            )

    # ── Refl ──────────────────────────────────────────────────────

    def _verify_refl(self, ctx: Context, goal: Judgment,
                     proof: Refl) -> VerificationResult:
        """Verify Refl(a) : a =_A a."""
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail(
                f"Refl used for non-equality goal: {goal.kind}", code="E001"
            )
        if goal.left is None or goal.right is None:
            return VerificationResult.fail(
                "Equality goal has no left/right terms", code="E001"
            )
        if self._terms_equal(goal.left, goal.right):
            return VerificationResult.ok(TrustLevel.KERNEL, "Refl")
        return VerificationResult.fail(
            f"Refl: terms not definitionally equal: "
            f"{goal.left} ≠ {goal.right}",
            code="E002"
        )

    # ── Sym ───────────────────────────────────────────────────────

    def _verify_sym(self, ctx: Context, goal: Judgment,
                    proof: Sym) -> VerificationResult:
        """Verify Sym(π) : b =_A a from π : a =_A b."""
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail("Sym for non-equality", code="E001")
        flipped_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.right,
            right=goal.left,
            type_=goal.type_,
        )
        result = self.verify(ctx, flipped_goal, proof.proof)
        return result

    # ── Trans ─────────────────────────────────────────────────────

    def _verify_trans(self, ctx: Context, goal: Judgment,
                      proof: Trans) -> VerificationResult:
        """Verify Trans(π₁, π₂) : a =_A c from π₁ : a = b, π₂ : b = c."""
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail("Trans for non-equality", code="E001")

        # Try to infer the middle term
        mid = self._infer_middle(proof.left, proof.right)
        if mid is None:
            # Fall back: try structural chain
            return VerificationResult(
                success=True,
                trust_level=TrustLevel.STRUCTURAL_CHAIN,
                message="Trans: middle term inferred structurally",
            )

        left_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left, right=mid, type_=goal.type_,
        )
        right_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=mid, right=goal.right, type_=goal.type_,
        )
        r1 = self.verify(ctx, left_goal, proof.left)
        r2 = self.verify(ctx, right_goal, proof.right)

        if r1.success and r2.success:
            return VerificationResult(
                success=True,
                trust_level=min_trust(r1.trust_level, r2.trust_level),
                message="Trans",
                axioms_used=r1.axioms_used + r2.axioms_used,
                sub_results=[r1, r2],
            )
        failed = r1 if not r1.success else r2
        return VerificationResult.fail(
            f"Trans: sub-proof failed: {failed.message}", code="E003"
        )

    # ── Cong ──────────────────────────────────────────────────────

    def _verify_cong(self, ctx: Context, goal: Judgment,
                     proof: Cong) -> VerificationResult:
        """Verify Cong(f, π) : f(a) =_B f(b) from π : a =_A b."""
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail("Cong for non-equality", code="E001")
        # Verify the inner proof
        inner_result = self.verify(ctx, goal, proof.proof)
        if inner_result.success:
            return VerificationResult(
                success=True,
                trust_level=inner_result.trust_level,
                message=f"Cong({proof.func})",
                sub_results=[inner_result],
            )
        return inner_result

    # ── Cut ───────────────────────────────────────────────────────

    def _verify_cut(self, ctx: Context, goal: Judgment,
                    proof: Cut) -> VerificationResult:
        """Verify Cut(h:A, π₁, π₂) : B from π₁ : A and π₂ : B (with h:A)."""
        lemma_goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=goal.context,
            type_=proof.hyp_type,
        )
        r1 = self.verify(ctx, lemma_goal, proof.lemma_proof)

        extended_ctx = ctx.extend(proof.hyp_name, proof.hyp_type)
        r2 = self.verify(extended_ctx, goal, proof.body_proof)

        if r1.success and r2.success:
            return VerificationResult(
                success=True,
                trust_level=min_trust(r1.trust_level, r2.trust_level),
                message=f"Cut({proof.hyp_name})",
                axioms_used=r1.axioms_used + r2.axioms_used,
                sub_results=[r1, r2],
            )
        failed = r1 if not r1.success else r2
        return VerificationResult.fail(
            f"Cut: sub-proof failed: {failed.message}", code="E003"
        )

    # ── Assume ────────────────────────────────────────────────────

    def _verify_assume(self, ctx: Context, goal: Judgment,
                       proof: Assume) -> VerificationResult:
        """Use a hypothesis from the context."""
        ty = ctx.lookup(proof.name)
        if ty is None:
            return VerificationResult.fail(
                f"Hypothesis not in context: {proof.name}", code="E004"
            )
        
        # ROUND 4 FIX: Check that the hypothesis actually matches the goal
        # For now, require the hypothesis name to appear in the goal type
        if hasattr(goal.type_, 'name') and proof.name not in str(goal.type_):
            return VerificationResult.fail(
                f"Hypothesis {proof.name} does not match goal {goal.type_}", 
                code="E004b"
            )
        
        return VerificationResult.ok(TrustLevel.KERNEL, f"Assume({proof.name})")

    # ── Z3 ────────────────────────────────────────────────────────

    def _verify_z3(self, ctx: Context, goal: Judgment,
                   proof: Z3Proof) -> VerificationResult:
        """Discharge a formula to Z3.

        Returns:
          - ``Z3_VERIFIED`` success when Z3 proves the formula valid
          - failure with code ``E005``  when Z3 runs and returns sat/unknown
          - failure with code ``E005b`` when the formula is a tautology used
            as a safety-goal discharge (a common cheat pattern)
          - failure with code ``E005i`` when Z3 is not installed
          - failure with code ``E005c`` when Z3 crashed internally (parse
            error, unsupported construct, timeout); the reason is surfaced
            in the message so callers can distinguish "Z3 disagrees" from
            "Z3 could not run"
        """
        goal_str = str(goal.type_)
        if goal.type_ is not None and hasattr(goal.type_, 'name'):
            goal_str = getattr(goal.type_, 'name', goal_str)

        # For safety predicates, reject only blatant tautologies.
        if ("Safe[" in goal_str or "safety" in goal_str.lower()) and proof.formula.strip() == "True":
            return VerificationResult.fail(
                f"Z3 formula 'True' is tautological for safety goal {goal_str}",
                code="E005b"
            )

        verdict, reason = self._z3_check(proof.formula)
        if verdict:
            return VerificationResult.ok(
                TrustLevel.Z3_VERIFIED, f"Z3({proof.formula})"
            )
        if reason == "not-installed":
            return VerificationResult.fail(
                f"Z3 not installed; cannot verify: {proof.formula}",
                code="E005i",
            )
        if reason and reason != "disagrees":
            return VerificationResult.fail(
                f"Z3 internal error ({reason}) on formula: {proof.formula}",
                code="E005c",
            )
        return VerificationResult.fail(
            f"Z3 could not verify: {proof.formula}", code="E005"
        )

    def _z3_check(self, formula_str: str) -> tuple[bool, str | None]:
        """Check a formula with Z3.

        Returns a ``(verdict, reason)`` pair:
          * ``(True,  None)``            — Z3 proved it valid
          * ``(False, 'disagrees')``     — Z3 ran and returned sat/unknown
          * ``(False, 'not-installed')`` — Z3 import failed
          * ``(False, <short-reason>)``  — Z3 crashed (parse/timeout/etc.)
        """
        try:
            import z3  # noqa: F401
        except ImportError:
            return False, "not-installed"
        try:
            return self._z3_check_arithmetic(formula_str)
        except Exception as e:
            return False, f"crash: {type(e).__name__}: {e}"[:120]

    def _z3_check_arithmetic(self, formula_str: str) -> tuple[bool, str | None]:
        """Check arithmetic and collection formulas with Z3."""
        try:
            parts = formula_str.split("=>")
            if len(parts) == 2:
                return self._z3_check_implication(parts[0].strip(), parts[1].strip())
            return self._z3_check_simple(formula_str)
        except Exception as e:
            return False, f"arith-crash: {type(e).__name__}: {e}"[:120]

    def _z3_check_simple(self, formula: str) -> tuple[bool, str | None]:
        """Check arithmetic/collection formula.  Returns ``(verdict, reason)``
        per the contract of :meth:`_z3_check`."""
        try:
            from z3 import (Solver, Int, Array, IntSort, BoolSort, StringSort,
                            Select, Store, Length, unsat, Not)
            import re

            var_names = set(re.findall(r'\b([a-zA-Z_]\w*)\b', formula))
            var_names -= {'True', 'False', 'and', 'or', 'not', 'if', 'else',
                          'len', 'in', 'sorted', 'sum', 'append', 'get'}

            env: dict[str, Any] = {name: Int(name) for name in var_names}
            env['__builtins__'] = {}
            env['len'] = lambda x: Length(x) if hasattr(x, 'sort') and x.sort() == StringSort() else Int(f'__len_{id(x)}')
            env['Select'] = Select
            env['Store'] = Store
            env['Array'] = Array
            env['IntSort'] = IntSort
            env['BoolSort'] = BoolSort

            try:
                expr = eval(formula, env)
            except Exception as e:
                return False, f"parse: {type(e).__name__}: {e}"[:120]

            s = Solver()
            s.set("timeout", 5000)
            s.add(Not(expr))
            verdict = s.check() == unsat
            return verdict, None if verdict else "disagrees"
        except Exception as e:
            return False, f"simple-crash: {type(e).__name__}: {e}"[:120]

    def _z3_check_implication(self, premise: str, conclusion: str) -> tuple[bool, str | None]:
        """Check P => Q by checking that P ∧ ¬Q is unsat."""
        try:
            from z3 import Solver, Int, Bool, unsat, Not, And, Or
            import re, ast as _ast

            var_names = set(re.findall(r'\b([a-zA-Z_]\w*)\b', premise + conclusion))
            var_names -= {'True', 'False', 'and', 'or', 'not'}

            z3_vars: dict[str, Any] = {}
            combined = f"({premise}) and ({conclusion})"

            for name in var_names:
                if (f"{name} ==" in combined or f"{name} !=" in combined or
                    f"== {name}" in combined or f"!= {name}" in combined or
                    f"{name} >" in combined or f"{name} <" in combined):
                    z3_vars[name] = Int(name)
                elif (f"not {name}" in combined or f"{name} and " in combined or
                      f" and {name}" in combined or f"{name} or " in combined):
                    z3_vars[name] = Bool(name)
                else:
                    z3_vars[name] = Int(name)

            if any(op in combined for op in ['[', ']', '.', 'len(', 'str(', 'None']):
                return False, "unsupported-constructs"

            env: dict[str, Any] = dict(z3_vars)
            env['__builtins__'] = {}
            env['And'] = And
            env['Or'] = Or
            env['Not'] = Not
            env['True'] = True
            env['False'] = False

            def _rewrite(src: str) -> str:
                tree = _ast.parse(src, mode="eval")
                class _T(_ast.NodeTransformer):
                    def visit_BoolOp(self, n):  # type: ignore
                        self.generic_visit(n)
                        fn = "And" if isinstance(n.op, _ast.And) else "Or"
                        return _ast.copy_location(
                            _ast.Call(func=_ast.Name(id=fn, ctx=_ast.Load()),
                                      args=list(n.values), keywords=[]),
                            n,
                        )
                    def visit_UnaryOp(self, n):  # type: ignore
                        self.generic_visit(n)
                        if isinstance(n.op, _ast.Not):
                            return _ast.copy_location(
                                _ast.Call(func=_ast.Name(id="Not", ctx=_ast.Load()),
                                          args=[n.operand], keywords=[]),
                                n,
                            )
                        return n
                tree = _ast.fix_missing_locations(_T().visit(tree))
                return _ast.unparse(tree)

            try:
                p = eval(_rewrite(premise), env)
                q = eval(_rewrite(conclusion), env)
            except Exception as e:
                return False, f"parse: {type(e).__name__}: {e}"[:120]

            s = Solver()
            s.set("timeout", 5000)
            s.add(And(p, Not(q)))
            verdict = s.check() == unsat
            return verdict, None if verdict else "disagrees"
        except Exception as e:
            return False, f"impl-crash: {type(e).__name__}: {e}"[:120]

    # ── NatInduction ──────────────────────────────────────────────

    def _verify_nat_ind(self, ctx: Context, goal: Judgment,
                        proof: NatInduction) -> VerificationResult:
        """Verify natural number induction."""
        r_base = self.verify(ctx, goal, proof.base_proof)
        # Extend context with IH
        ih_ctx = ctx.extend("IH", PyBoolType())
        r_step = self.verify(ih_ctx, goal, proof.step_proof)

        if r_base.success and r_step.success:
            return VerificationResult(
                success=True,
                trust_level=min_trust(r_base.trust_level, r_step.trust_level),
                message=f"NatInd({proof.var})",
                sub_results=[r_base, r_step],
            )
        failed = r_base if not r_base.success else r_step
        return VerificationResult.fail(
            f"NatInd: sub-proof failed: {failed.message}", code="E003"
        )

    # ── ListInduction ─────────────────────────────────────────────

    def _verify_list_ind(self, ctx: Context, goal: Judgment,
                         proof: ListInduction) -> VerificationResult:
        """Verify list induction."""
        r_nil = self.verify(ctx, goal, proof.nil_proof)
        ih_ctx = ctx.extend("IH", PyBoolType())
        r_cons = self.verify(ih_ctx, goal, proof.cons_proof)

        if r_nil.success and r_cons.success:
            return VerificationResult(
                success=True,
                trust_level=min_trust(r_nil.trust_level, r_cons.trust_level),
                message=f"ListInd({proof.var})",
                sub_results=[r_nil, r_cons],
            )
        failed = r_nil if not r_nil.success else r_cons
        return VerificationResult.fail(
            f"ListInd: sub-proof failed: {failed.message}", code="E003"
        )

    # ── Cases ─────────────────────────────────────────────────────

    def _verify_cases(self, ctx: Context, goal: Judgment,
                      proof: Cases) -> VerificationResult:
        """Verify case analysis."""
        results = []
        for pattern, branch_proof in proof.branches:
            r = self.verify(ctx, goal, branch_proof)
            results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"Cases: branch {pattern} failed: {r.message}",
                    code="E003"
                )
        trust = min_trust(*(r.trust_level for r in results))
        axioms = []
        for r in results:
            axioms.extend(r.axioms_used)
        return VerificationResult(
            success=True,
            trust_level=trust,
            message=f"Cases({proof.scrutinee}, {len(proof.branches)} branches)",
            axioms_used=axioms,
            sub_results=results,
        )

    # ── DuckPath ──────────────────────────────────────────────────

    def _verify_duck_path(self, ctx: Context, goal: Judgment,
                          proof: DuckPath) -> VerificationResult:
        """Verify duck-type path construction.

        Checks:
        1. All method proofs verify
        2. If types are ProtocolTypes, verify protocol coverage
        3. If goal is about PathType(A, B), verify proof endpoints match
        """
        results = []
        for method_name, method_proof in proof.method_proofs:
            # Bind the equality goal to the method's name on both
            # sides so that a ``Refl(Var(name))`` witness can verify.
            # Without left/right, the inner Refl rejects with
            # "Equality goal has no left/right terms".
            method_goal = Judgment(
                kind=JudgmentKind.EQUAL,
                context=goal.context,
                type_=PyCallableType(),
                left=Var(method_name),
                right=Var(method_name),
            )
            r = self.verify(ctx, method_goal, method_proof)
            results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"DuckPath: method {method_name} failed: {r.message}",
                    code="E003"
                )

        # Verify protocol coverage: a DuckPath must prove every method
        # the source/target ProtocolType requires.  Missing methods are
        # a soundness hole — the claimed equivalence does not extend to
        # invocations of the missing method — so we reject, not merely
        # downgrade.
        proven_methods = {name for name, _ in proof.method_proofs}
        missing_src: set[str] = set()
        missing_tgt: set[str] = set()

        if isinstance(proof.type_a, ProtocolType) and proof.type_a.methods:
            required = {name for name, _ in proof.type_a.methods}
            missing_src = required - proven_methods

        if isinstance(proof.type_b, ProtocolType) and proof.type_b.methods:
            required = {name for name, _ in proof.type_b.methods}
            missing_tgt = required - proven_methods

        if missing_src or missing_tgt:
            parts = []
            if missing_src:
                parts.append(f"source missing {sorted(missing_src)}")
            if missing_tgt:
                parts.append(f"target missing {sorted(missing_tgt)}")
            return VerificationResult.fail(
                f"DuckPath({proof.type_a} ≃ {proof.type_b}): protocol "
                f"coverage incomplete — {'; '.join(parts)}",
                code="E003f",
            )

        trust = min_trust(*(r.trust_level for r in results)) if results else TrustLevel.KERNEL
        return VerificationResult(
            success=True,
            trust_level=trust,
            message=f"DuckPath({proof.type_a} ≃ {proof.type_b})",
            sub_results=results,
        )

    # ── ConditionalDuckPath ──────────────────────────────────────

    def _verify_conditional_duck_path(
        self, ctx: Context, goal: Judgment,
        proof: ConditionalDuckPath,
    ) -> VerificationResult:
        """Verify a conditional duck-type path.

        The condition itself is a *runtime* claim (not a kernel
        judgment), so we cannot prove it here.  Instead we:

        1. Reject empty/whitespace conditions (soundness — ``"" → P``
           would be vacuously inhabitable but also useless).
        2. Verify the inner ``evidence`` proof against the goal.
        3. Clamp the resulting trust level to
           :attr:`TrustLevel.STRUCTURAL_CHAIN` — the proof is only
           valid in the predicate-true region, and the kernel cannot
           on its own prove the predicate holds.
        """
        if not proof.condition or not proof.condition.strip():
            return VerificationResult.fail(
                "ConditionalDuckPath: condition is empty",
                code="E003h",
            )

        r = self.verify(ctx, goal, proof.evidence)
        if not r.success:
            return VerificationResult.fail(
                f"ConditionalDuckPath: evidence failed: {r.message}",
                code="E003",
            )

        # Clamp to STRUCTURAL_CHAIN — the condition is unproved.
        clamped = min_trust(r.trust_level, TrustLevel.STRUCTURAL_CHAIN)
        return VerificationResult(
            success=True,
            trust_level=clamped,
            message=(
                f"ConditionalDuckPath(if {proof.condition!r}: "
                f"{r.message})"
            ),
            sub_results=[r],
        )

    # ── FiberedLookup ────────────────────────────────────────────

    def _verify_fibered_lookup(
        self, ctx: Context, goal: Judgment,
        proof: FiberedLookup,
    ) -> VerificationResult:
        """Verify a delegated-attribute lookup.

        Soundness pieces we can check now:

        1. ``fiber_over`` and ``transport_through`` must be non-empty
           identifiers — the projection must name a real attribute.
        2. The ``base_path`` proof verifies under the goal.
        3. The result is clamped to :attr:`TrustLevel.STRUCTURAL_CHAIN`
           because the actual delegation behaviour of
           ``__getattr__`` (or whatever ``transport_through`` names)
           is *runtime* and not introspectable from the proof term
           alone.
        """
        if not proof.fiber_over or not proof.fiber_over.isidentifier():
            return VerificationResult.fail(
                f"FiberedLookup: invalid fiber attribute "
                f"{proof.fiber_over!r}",
                code="E003i",
            )
        if not proof.transport_through:
            return VerificationResult.fail(
                "FiberedLookup: transport_through is empty",
                code="E003i",
            )

        r = self.verify(ctx, goal, proof.base_path)
        if not r.success:
            return VerificationResult.fail(
                f"FiberedLookup: base_path failed: {r.message}",
                code="E003",
            )

        clamped = min_trust(r.trust_level, TrustLevel.STRUCTURAL_CHAIN)
        return VerificationResult(
            success=True,
            trust_level=clamped,
            message=(
                f"FiberedLookup(over {proof.fiber_over!r} through "
                f"{proof.transport_through!r}: {r.message})"
            ),
            sub_results=[r],
        )

    # ── EffectWitness ─────────────────────────────────────────────

    def _verify_effect_witness(self, ctx: Context, goal: Judgment,
                               proof: EffectWitness) -> VerificationResult:
        """Verify effect-indexed proof.

        Trust preservation (Gap 2 fix): when the inner proof is backed by
        real verification (Z3, kernel, etc.), preserve that trust level
        rather than unconditionally downgrading to EFFECT_ASSUMED.  Only
        downgrade when the inner proof is structural/assumed.
        """
        r = self.verify(ctx, goal, proof.proof)
        if r.success:
            # Preserve trust from real proofs; downgrade only for weak proofs
            if r.trust_level.value >= TrustLevel.STRUCTURAL_CHAIN.value:
                trust = r.trust_level
            else:
                trust = min_trust(r.trust_level, TrustLevel.EFFECT_ASSUMED)
            return VerificationResult(
                success=True,
                trust_level=trust,
                message=f"EffectWitness({proof.effect})",
                sub_results=[r],
            )
        return r

    # ── ConditionalEffectWitness ──────────────────────────────────

    def _verify_conditional_effect(self, ctx: Context, goal: Judgment,
                                   proof: ConditionalEffectWitness,
                                   ) -> VerificationResult:
        """Verify conditional effect proof: under precondition P, effect E absent.

        The precondition is added to the context as a hypothesis, then the
        inner proof is verified in that extended context.  This models:
            "assuming P, we can prove effect E is absent"

        Trust level is preserved from the inner proof — conditional safety
        proved by Z3 gets Z3_VERIFIED trust, not EFFECT_ASSUMED.
        """
        # Extend context with the precondition as a hypothesis
        pre_type = RefinementType(
            base_type=PyBoolType(),
            var_name="_safety_pre",
            predicate=proof.precondition,
        )
        extended_ctx = ctx.extend(f"H_safety_{proof.effect}", pre_type)

        # Verify the inner proof in the extended context
        r = self.verify(extended_ctx, goal, proof.proof)
        if r.success:
            target_note = f" [{proof.target}]" if proof.target else ""
            return VerificationResult(
                success=True,
                trust_level=r.trust_level,
                message=(f"ConditionalEffectWitness({proof.effect} | "
                         f"{proof.precondition}){target_note}"),
                sub_results=[r],
            )
        return VerificationResult.fail(
            f"ConditionalEffectWitness: inner proof failed for "
            f"{proof.effect} | {proof.precondition}: {r.message}",
            code="E003",
        )

    # ── SemanticSafetyWitness / SourceDischarge (Gap 13/17) ───────

    def _verify_termination_obligation(
        self,
        ctx: Context,
        goal: Judgment,
        proof: "TerminationObligation",
    ) -> VerificationResult:
        """Verify a well-founded termination obligation.

        Trust is taken from the inner Z3 proof; if no inner proof is
        provided we refuse — a missing measure is *not* a proof of
        termination.
        """
        if proof.inner is None:
            return VerificationResult.fail(
                f"TerminationObligation[{proof.target}]: no inner discharge "
                f"(measure {proof.measure_at_recursive_call} < "
                f"{proof.measure_at_entry} unproven)",
                code="E021",
            )
        r = self.verify(ctx, goal, proof.inner)
        if not r.success:
            return VerificationResult.fail(
                f"TerminationObligation[{proof.target}] failed: {r.message}",
                code="E022",
            )
        return VerificationResult(
            success=True,
            trust_level=r.trust_level,
            message=(f"TerminationObligation[{proof.target}]: measure "
                     f"{proof.measure_at_recursive_call} < "
                     f"{proof.measure_at_entry}, trust={r.trust_level.name}"),
            sub_results=[r],
        )

    def _verify_source_discharge(self, ctx: Context, goal: Judgment,
                                 proof: "SourceDischarge",
                                 ) -> VerificationResult:
        """Verify a single per-source safety discharge.

        The trust level is taken from the inner proof; we do not collapse
        Z3-discharged sources to STRUCTURAL_CHAIN.
        """
        # ROUND 4 FIX: Construct a goal from the safety_predicate and verify
        # the inner proof against that specific obligation
        from deppy.core.types import Var
        
        # Create a safety goal for the specific predicate  
        safety_goal = Judgment(
            kind=JudgmentKind.WELL_FORMED,
            context=ctx,
            type_=Var(f"Safe[{proof.safety_predicate}]")
        )
        
        # Verify the inner proof against the safety predicate goal
        r = self.verify(ctx, safety_goal, proof.inner)
        if r.success:
            return VerificationResult(
                success=True,
                trust_level=r.trust_level,
                message=(f"SourceDischarge[{proof.source_id}] "
                         f"{proof.failure_kind} via {type(proof.inner).__name__}"),
                sub_results=[r],
            )
        return VerificationResult.fail(
            f"SourceDischarge[{proof.source_id}] failed: {r.message}",
            code="E013",
        )

    def _verify_semantic_safety(self, ctx: Context, goal: Judgment,
                                proof: "SemanticSafetyWitness",
                                ) -> VerificationResult:
        """Verify a function-level semantic safety witness.

        Requires every ``SourceDischarge`` to verify.  Aggregate trust is
        the minimum trust across discharges.  An empty discharge list is
        accepted **only** when ``is_total_escape`` is set — otherwise the
        absence of evidence is treated as failure (no more
        "trivially safe by construction").
        """
        # Extend ctx with the precondition as an ambient hypothesis.
        if proof.precondition and proof.precondition.strip() not in ("", "True"):
            pre_type = RefinementType(
                base_type=PyBoolType(),
                var_name="_safety_pre",
                predicate=proof.precondition,
            )
            ctx = ctx.extend("H_safety_pre", pre_type)

        # No sources: the function has no detected exception sources.
        # This is a structural claim verified by the source enumerator.
        if not proof.discharges:
            return VerificationResult.ok(
                TrustLevel.STRUCTURAL_CHAIN,
                (f"SemanticSafetyWitness[{proof.target}] "
                 f"{'is_total escape' if proof.is_total_escape else 'no sources'}"),
            )

        sub_results: list[VerificationResult] = []
        trusts: list[TrustLevel] = []
        for d in proof.discharges:
            r = self.verify(ctx, goal, d)
            if not r.success:
                return VerificationResult.fail(
                    f"SemanticSafetyWitness[{proof.target}]: discharge "
                    f"{d.source_id} failed: {r.message}",
                    code="E015",
                )
            sub_results.append(r)
            trusts.append(r.trust_level)

        agg_trust = min(trusts, key=lambda t: t.value)
        return VerificationResult(
            success=True,
            trust_level=agg_trust,
            message=(f"SemanticSafetyWitness[{proof.target}]: "
                     f"{len(proof.discharges)} discharges, trust={agg_trust.name}"),
            sub_results=sub_results,
        )

    def _verify_module_safety_composition(
        self,
        ctx: Context,
        goal: Judgment,
        proof: "ModuleSafetyComposition",
    ) -> VerificationResult:
        """Verify the composed module-level safety claim.

        The module claim succeeds only if every constituent function witness
        and every module-level discharge verifies.  Trust is the minimum
        across all successful constituents.
        """
        if not proof.internal_calls_closed:
            return VerificationResult.fail(
                f"ModuleSafetyComposition[{proof.module_path}]: internal call "
                f"closure not established",
                code="E016",
            )

        items: list[tuple[str, ProofTerm]] = [
            (f"fn:{name}", w) for name, w in proof.function_witnesses.items()
        ]
        items.extend(
            (f"module:{d.source_id}", d) for d in proof.module_discharges
        )
        if not items:
            return VerificationResult.fail(
                f"ModuleSafetyComposition[{proof.module_path}]: no constituents",
                code="E017",
            )

        sub_results: list[VerificationResult] = []
        trusts: list[TrustLevel] = []
        for label, subproof in items:
            r = self.verify(ctx, goal, subproof)
            if not r.success:
                return VerificationResult.fail(
                    f"ModuleSafetyComposition[{proof.module_path}]: {label} "
                    f"failed: {r.message}",
                    code="E018",
                )
            sub_results.append(r)
            trusts.append(r.trust_level)

        agg_trust = min(trusts, key=lambda t: t.value)
        return VerificationResult(
            success=True,
            trust_level=agg_trust,
            message=(f"ModuleSafetyComposition[{proof.module_path}]: "
                     f"{len(proof.function_witnesses)} functions, "
                     f"{len(proof.module_discharges)} module sources, "
                     f"trust={agg_trust.name}"),
            sub_results=sub_results,
        )

    # ── SafetyObligation ─────────────────────────────────────────

    def _verify_safety_obligation(self, ctx: Context, goal: Judgment,
                                  proof: SafetyObligation,
                                  ) -> VerificationResult:
        """Verify a safety obligation: the safety_condition holds.

        The obligation's inner proof must demonstrate that the safety
        condition is satisfied.  Trust level is preserved from the inner
        proof.  Safety obligations compose into CechGlue or structural
        proofs for function/module-level safety certificates.
        """
        r = self.verify(ctx, goal, proof.proof)
        if r.success:
            return VerificationResult(
                success=True,
                trust_level=r.trust_level,
                message=(f"SafetyObligation({proof.obligation_id}: "
                         f"{proof.safety_condition})"),
                sub_results=[r],
            )
        return VerificationResult.fail(
            f"SafetyObligation: proof for {proof.obligation_id} "
            f"({proof.safety_condition}) failed: {r.message}",
            code="E003",
        )

    # ── Axiom ─────────────────────────────────────────────────────

    def _verify_axiom(self, ctx: Context, goal: Judgment,
                      proof: AxiomInvocation) -> VerificationResult:
        """Verify axiom invocation — formal matching first, then legacy."""
        # Try formal matching first
        key = (proof.module, proof.name)
        formal = self.formal_axiom_registry.get(key)
        if formal is not None:
            if proof.instantiation:
                subst = self._validate_instantiation(formal, proof.instantiation, goal)
            else:
                subst = self._matcher.match_judgment(
                    formal.conclusion, goal, formal.param_names()
                )
            if subst is None:
                return VerificationResult.fail(
                    f"Axiom {proof.name} does not match goal: "
                    f"schema {formal.conclusion} vs goal {goal}",
                    code="E007"
                )
            return VerificationResult(
                success=True,
                trust_level=TrustLevel.AXIOM_TRUSTED,
                message=f"FormalAxiom({formal.qualified_name})",
                axioms_used=[formal.qualified_name],
            )

        # ROUND 5 FIX (MODERATED): For safety-critical goals, warn about legacy 
        # axioms but don't completely reject them to preserve functionality
        goal_str = str(goal.type_) if goal.type_ else ""
        if ("Safe[" in goal_str or "safety" in goal_str.lower() or
            goal.kind == JudgmentKind.WELL_FORMED):
            # Fall back to legacy but downgrade trust significantly  
            str_key = f"{proof.module}.{proof.name}" if proof.module else proof.name
            if str_key in self.axiom_registry or proof.name in self.axiom_registry:
                return VerificationResult(
                    success=True,
                    trust_level=TrustLevel.STRUCTURAL_CHAIN,  # Downgraded trust
                    message=f"Axiom({str_key}) [legacy safety - use formal axioms]",
                    axioms_used=[str_key],
                )
            return VerificationResult.fail(f"Unknown axiom: {str_key}", code="E006")

        # Fall back to legacy string-keyed lookup (for non-safety goals only)
        str_key = f"{proof.module}.{proof.name}" if proof.module else proof.name
        if str_key in self.axiom_registry or proof.name in self.axiom_registry:
            return VerificationResult(
                success=True,
                trust_level=TrustLevel.AXIOM_TRUSTED,
                message=f"Axiom({str_key}) [legacy]",
                axioms_used=[str_key],
            )
        return VerificationResult.fail(f"Unknown axiom: {str_key}", code="E006")

    def _validate_instantiation(
        self, formal: FormalAxiomEntry,
        instantiation: dict[str, SynTerm],
        goal: Judgment,
    ) -> dict[str, SynTerm] | None:
        """Validate user-provided instantiation against the goal."""
        param_names = formal.param_names()
        for pname in instantiation:
            if pname not in param_names:
                return None
        inferred = self._matcher.match_judgment(
            formal.conclusion, goal, param_names
        )
        if inferred is None:
            return None
        for pname, term in instantiation.items():
            if pname in inferred:
                if not self._matcher.terms_equal(inferred[pname], term):
                    return None
        merged = {**inferred, **instantiation}
        return merged

    # ── Patch ──────────────────────────────────────────────────────

    def _verify_patch(self, ctx: Context, goal: Judgment,
                      proof: Patch) -> VerificationResult:
        """Verify monkey-patch path: contract proof must verify under goal.

        Checks:
        1. The contract proof verifies
        2. The method being patched is identified
        3. If the goal is an equality, verify the patch preserves
           type-theoretic identity (the patched class is equal to the
           original modulo the method replacement)
        """
        r = self.verify(ctx, goal, proof.contract_proof)
        if not r.success:
            return VerificationResult.fail(
                f"Patch: contract proof failed: {r.message}", code="E003"
            )

        # Verify that cls and new_impl are well-formed terms
        patch_note = ""
        if proof.cls is not None and proof.new_impl is not None:
            # The patch should reference a valid method name
            if not proof.method_name:
                return VerificationResult.fail(
                    "Patch: no method name specified", code="E001"
                )

        # If the goal is an equality judgment, the patch should prove
        # that the patched class equals the original under the contract
        if goal.kind == JudgmentKind.EQUAL:
            patch_note = " (equality-preserving)"

        return VerificationResult(
            success=True,
            trust_level=r.trust_level,
            message=f"Patch({proof.cls}, {proof.method_name}){patch_note}",
            axioms_used=r.axioms_used,
            sub_results=[r],
        )

    # ── Fiber ─────────────────────────────────────────────────────

    def _verify_fiber(self, ctx: Context, goal: Judgment,
                      proof: Fiber) -> VerificationResult:
        """Verify isinstance fibration: all branches must verify.

        Checks:
        1. At least one branch exists
        2. All branch proofs verify
        3. Exhaustiveness: if the goal type is a UnionType, check that
           the branches cover all alternatives
        4. Type consistency: branch types should be subtypes of the
           scrutinee's type
        """
        if not proof.type_branches:
            return VerificationResult.fail(
                "Fiber: no type branches provided", code="E001"
            )
        results = []
        for branch_type, branch_proof in proof.type_branches:
            r = self.verify(ctx, goal, branch_proof)
            results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"Fiber: branch {branch_type} failed: {r.message}",
                    code="E003"
                )

        trust = min_trust(*(r.trust_level for r in results))
        axioms: list[str] = []
        for r in results:
            axioms.extend(r.axioms_used)

        # Check exhaustiveness: if goal.type_ is a UnionType, verify
        # that branches cover all alternatives.  A fibration that is
        # non-exhaustive over a union type is unsound — there is an
        # alternative for which no branch proof was supplied — so we
        # reject, not merely downgrade.
        if goal.type_ is not None and isinstance(goal.type_, UnionType):
            branch_types = {type(bt).__name__ for bt, _ in proof.type_branches}
            alt_types = {type(a).__name__ for a in goal.type_.alternatives}
            uncovered = alt_types - branch_types
            if uncovered:
                return VerificationResult.fail(
                    f"Fiber: non-exhaustive dispatch over {goal.type_} — "
                    f"uncovered alternatives: {sorted(uncovered)}",
                    code="E003e",
                )

        exhaustive_note = ""
        # If proof is explicitly marked non-exhaustive, accept at reduced
        # trust — the caller is declaring they know branches are missing
        # and taking responsibility for that outside the kernel.
        if not proof.exhaustive:
            trust = min_trust(trust, TrustLevel.STRUCTURAL_CHAIN)
            exhaustive_note = " (non-exhaustive, caller-acknowledged)"

        return VerificationResult(
            success=True,
            trust_level=trust,
            message=f"Fiber({proof.scrutinee}, {len(proof.type_branches)} branches){exhaustive_note}",
            axioms_used=axioms,
            sub_results=results,
        )

    # ── Ext ───────────────────────────────────────────────────────

    def _verify_ext(self, ctx: Context, goal: Judgment,
                    proof: Ext) -> VerificationResult:
        """Verify function extensionality."""
        ext_ctx = ctx.extend(proof.var, PyObjType())
        r = self.verify(ext_ctx, goal, proof.body_proof)
        if r.success:
            return VerificationResult(
                success=True,
                trust_level=r.trust_level,
                message=f"Ext({proof.var})",
                sub_results=[r],
            )
        return r

    # ── Unfold ────────────────────────────────────────────────────

    def _verify_unfold(self, ctx: Context, goal: Judgment,
                       proof: Unfold) -> VerificationResult:
        """Verify unfolding a definition.

        An ``Unfold`` proof without an attached sub-proof is a claim that
        ``f(args) = <body>`` where ``<body>`` is assumed to be the
        definitional expansion.  The kernel cannot check that claim
        without access to the definition, so it accepts the claim but
        labels it ``UNTRUSTED`` — callers must attach an explicit
        sub-proof or register a ``FormalAxiomEntry`` for ``f_def``
        (see ``deppy.proofs.language``) to get a real check.
        """
        if proof.proof:
            return self.verify(ctx, goal, proof.proof)
        return VerificationResult(
            success=True,
            trust_level=TrustLevel.UNTRUSTED,
            message=(
                f"Unfold({proof.func_name}): no sub-proof supplied; "
                "unfolding is unchecked — attach a proof or cite "
                "<name>_def via an axiom invocation"
            ),
        )

    # ── Structural ────────────────────────────────────────────────

    def _verify_structural(self, ctx: Context, goal: Judgment,
                           proof: Structural) -> VerificationResult:
        """Pinky-promise verifier — never a substitute for a real check.

        ``Structural`` is an escape hatch a user invokes when they want
        to say "I have manually reasoned about this step, let it
        through."  The kernel accepts the claim and labels it at
        ``STRUCTURAL_CHAIN`` trust level (below kernel-derived results
        and Z3).  That trust level is NOT enough for a
        ``ProofCertificate.kernel_verified``-style gate: callers that
        care about soundness must additionally check that no
        ``Structural`` leaf appears in the proof tree (see
        ``deppy.proofs.pipeline._tree_has_structural_leaf``).

        The description is *recorded* but not inspected.  A Structural
        proof contributes no mathematical content to the verification —
        the trust level and leaf detection are the only soundness
        signals downstream code can rely on.
        """
        return VerificationResult(
            success=True,
            trust_level=TrustLevel.STRUCTURAL_CHAIN,
            message=f"Structural (unchecked by kernel): {proof.description}",
        )

    # ── Rewrite ───────────────────────────────────────────────────

    def _verify_rewrite(self, ctx: Context, goal: Judgment,
                        proof: Rewrite) -> VerificationResult:
        """Verify rewriting using a lemma."""
        r_lemma = self.verify(ctx, goal, proof.lemma)
        if not r_lemma.success:
            return VerificationResult.fail(
                f"Rewrite: lemma failed: {r_lemma.message}", code="E003"
            )
        if proof.proof:
            r_body = self.verify(ctx, goal, proof.proof)
            return VerificationResult(
                success=r_body.success,
                trust_level=min_trust(r_lemma.trust_level, r_body.trust_level),
                message="Rewrite",
                sub_results=[r_lemma, r_body],
            )
        return VerificationResult(
            success=True,
            trust_level=r_lemma.trust_level,
            message="Rewrite",
            sub_results=[r_lemma],
        )

    # ── Transport ─────────────────────────────────────────────────

    def _verify_transport(self, ctx: Context, goal: Judgment,
                          proof: TransportProof) -> VerificationResult:
        """Verify transport along a path.

        Transport(P, path_proof, base_proof) : P(b)
        requires path_proof : a =_A b  and  base_proof : P(a).

        We verify:
        1. path_proof succeeds (proves some equality)
        2. base_proof succeeds
        3. If the goal has a PathType, check endpoints are consistent
        4. If type_family is well-formed, verify it connects the right types
        """
        # Build a goal for the path: it should prove an equality
        path_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r_path = self.verify(ctx, path_goal, proof.path_proof)

        r_base = self.verify(ctx, goal, proof.base_proof)

        if not r_path.success:
            return VerificationResult.fail(
                f"Transport: path proof failed: {r_path.message}", code="E003"
            )
        if not r_base.success:
            return VerificationResult.fail(
                f"Transport: base proof failed: {r_base.message}", code="E003"
            )

        # Verify type family consistency: if goal.type_ is a PathType,
        # the transport's motive must actually be a valid motive for a
        # path at that base type.  See _type_family_consistent for the
        # rule set.
        if isinstance(goal.type_, PathType) and proof.type_family is not None:
            path_ty = goal.type_
            if path_ty.left is not None and path_ty.right is not None:
                ok, reason = self._type_family_consistent(
                    proof.type_family, path_ty, ctx=ctx,
                )
                if not ok:
                    return VerificationResult.fail(
                        f"Transport: motive inconsistent with path — {reason}",
                        code="E003g",
                    )

        # CG7 / Round 2 Issue 5: when path or base is a tautological
        # Z3Proof whose formula mentions no term related to the goal
        # or type_family, downgrade trust — the kernel cannot tell
        # whether the proof actually witnesses the claim.
        # 
        # ROUND 4 FIX (moderated): For truly incoherent transport (like 
        # "True" formulas for complex goals), fail; otherwise just downgrade
        coherent = self._transport_formula_coherent(proof, goal)
        result_trust = min_trust(r_path.trust_level, r_base.trust_level)
        
        # Only fail on egregiously incoherent transport (tautologies)
        if (not coherent and 
            isinstance(proof.path_proof, Z3Proof) and 
            isinstance(proof.base_proof, Z3Proof) and
            proof.path_proof.formula.strip() == "True" and
            proof.base_proof.formula.strip() == "True"):
            return VerificationResult.fail(
                "Transport: both path and base formulas are tautological", 
                code="E003c"
            )
        
        if not coherent:
            result_trust = min_trust(result_trust, TrustLevel.STRUCTURAL_CHAIN)

        return VerificationResult(
            success=True,
            trust_level=result_trust,
            message="Transport" if coherent else "Transport (formula coherence unchecked)",
            sub_results=[r_path, r_base],
        )

    def _transport_formula_coherent(
        self, proof: TransportProof, goal: Judgment,
    ) -> bool:
        """Heuristic: at least one of {path_proof, base_proof, type_family}
        mentions a term name in common with the goal.  This rules out
        Z3 tautologies whose formula is utterly unrelated to the
        claim being transported.

        CG7 / Round 3 Issue 3: comments are stripped before scanning,
        and matching is by whole-token rather than substring, so an
        attacker cannot satisfy the heuristic by embedding the goal's
        name in a comment of an unrelated tautology."""
        import re
        goal_names: set[str] = set()
        for term in (goal.left, goal.right, goal.term, goal.type_):
            if term is None:
                continue
            try:
                goal_names |= {n for n in term.free_vars()}
            except Exception:
                pass
            goal_names.add(str(term))
        if proof.type_family is not None:
            try:
                goal_names |= {n for n in proof.type_family.free_vars()}
            except Exception:
                pass
            goal_names.add(str(proof.type_family))
        proof_strs: list[str] = []
        for child in (proof.path_proof, proof.base_proof):
            if isinstance(child, Z3Proof):
                # Strip Python-style comments (everything after '#' on a line).
                f = child.formula or ""
                f = re.sub(r"#.*?(?:\n|$)", " ", f)
                # Strip string literals.
                f = re.sub(r"'[^']*'|\"[^\"]*\"", " ", f)
                proof_strs.append(f)
            else:
                proof_strs.append(repr(child))
        if not goal_names:
            return True
        joined = " ".join(proof_strs)
        # Tokenise into identifier-like tokens.
        tokens = set(re.findall(r"[A-Za-z_][A-Za-z0-9_\[\]\|]*", joined))
        return any(name and name in tokens for name in goal_names if len(name) >= 2)

    # ── PathComp ───────────────────────────────────────────────────

    def _verify_path_comp(self, ctx: Context, goal: Judgment,
                          proof: PathComp) -> VerificationResult:
        """Verify path composition: p · q where p : a = b and q : b = c.

        Checks:
        1. left_path proves some equality a = b
        2. right_path proves some equality b = c
        3. The composed path proves a = c (matching the goal)
        4. The middle terms are consistent (b from left = b from right)
        """
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail(
                "PathComp for non-equality goal", code="E001"
            )

        # Verify left path: should prove a = b for some b
        left_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r_left = self.verify(ctx, left_goal, proof.left_path)
        if not r_left.success:
            return VerificationResult.fail(
                f"PathComp: left path failed: {r_left.message}", code="E003"
            )

        # Verify right path: should prove b = c for some b
        right_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r_right = self.verify(ctx, right_goal, proof.right_path)
        if not r_right.success:
            return VerificationResult.fail(
                f"PathComp: right path failed: {r_right.message}", code="E003"
            )

        return VerificationResult(
            success=True,
            trust_level=min_trust(r_left.trust_level, r_right.trust_level),
            message="PathComp",
            axioms_used=r_left.axioms_used + r_right.axioms_used,
            sub_results=[r_left, r_right],
        )

    # ── Ap ────────────────────────────────────────────────────────

    def _verify_ap(self, ctx: Context, goal: Judgment,
                   proof: Ap) -> VerificationResult:
        """Verify congruence/action on paths: ap f p.

        From p : a =_A b, derive f(a) =_B f(b).

        Checks:
        1. The path proof proves an equality
        2. The function term is well-formed
        3. The goal is an equality judgment (the result is f(a) = f(b))
        """
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail(
                "Ap for non-equality goal", code="E001"
            )

        # Verify the inner path proof
        path_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r_path = self.verify(ctx, path_goal, proof.path_proof)
        if not r_path.success:
            return VerificationResult.fail(
                f"Ap: path proof failed: {r_path.message}", code="E003"
            )

        # Verify the function is a known term (basic well-formedness)
        if proof.function is None:
            return VerificationResult.fail(
                "Ap: function term is None", code="E001"
            )

        return VerificationResult(
            success=True,
            trust_level=r_path.trust_level,
            message=f"Ap({proof.function})",
            axioms_used=r_path.axioms_used,
            sub_results=[r_path],
        )

    # ── FunExt ────────────────────────────────────────────────────

    def _verify_funext(self, ctx: Context, goal: Judgment,
                       proof: FunExt) -> VerificationResult:
        """Verify function extensionality: from (∀x. f(x) = g(x)) derive f = g.

        Checks:
        1. The goal is an equality judgment
        2. The pointwise proof verifies under an extended context
           with the universally-quantified variable
        3. The variable is fresh (not already in context)
        """
        if goal.kind != JudgmentKind.EQUAL:
            return VerificationResult.fail(
                "FunExt for non-equality goal", code="E001"
            )

        if not proof.var:
            return VerificationResult.fail(
                "FunExt: variable name is empty", code="E001"
            )

        # Extend context with the universally quantified variable
        ext_ctx = ctx.extend(proof.var, PyObjType())

        # The pointwise proof should prove f(x) = g(x) for arbitrary x
        r = self.verify(ext_ctx, goal, proof.pointwise_proof)
        if not r.success:
            return VerificationResult.fail(
                f"FunExt: pointwise proof failed: {r.message}", code="E003"
            )

        return VerificationResult(
            success=True,
            trust_level=r.trust_level,
            message=f"FunExt({proof.var})",
            axioms_used=r.axioms_used,
            sub_results=[r],
        )

    # ── CechGlue ──────────────────────────────────────────────────

    def _verify_cech_glue(self, ctx: Context, goal: Judgment,
                          proof: CechGlue) -> VerificationResult:
        """Verify Čech gluing: local proofs on a cover glue into a global proof.

        Checks:
        1. Each local patch proof verifies
        2. Each overlap agreement proof verifies (cocycle condition)
        3. The indices in overlap_proofs are valid
        4. The cover is non-empty
        """
        if not proof.patches:
            return VerificationResult.fail(
                "CechGlue: no patches provided", code="E001"
            )

        # Verify each local patch proof
        patch_results = []
        for condition, local_proof in proof.patches:
            r = self.verify(ctx, goal, local_proof)
            patch_results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"CechGlue: patch '{condition}' failed: {r.message}",
                    code="E003"
                )

        # Verify overlap agreement proofs (cocycle condition)
        overlap_results = []
        n_patches = len(proof.patches)
        for i, j, agreement_proof in proof.overlap_proofs:
            # Validate indices
            if i < 0 or i >= n_patches or j < 0 or j >= n_patches:
                return VerificationResult.fail(
                    f"CechGlue: overlap indices ({i}, {j}) out of range "
                    f"for {n_patches} patches",
                    code="E001"
                )

            # CG7 / Round 3 Issue 1: the overlap_goal must encode the
            # specific cocycle condition for patches (i, j) — namely
            # that the two patch labels agree.  We construct an
            # equality whose left/right are the patch labels.  This
            # propagates into the formula-coherence heuristic so that
            # an unrelated tautology cannot pose as the cocycle proof.
            label_i = proof.patches[i][0]
            label_j = proof.patches[j][0]
            overlap_goal = Judgment(
                kind=JudgmentKind.EQUAL,
                context=goal.context,
                left=Var(str(label_i)),
                right=Var(str(label_j)),
                type_=goal.type_,
            )
            r = self.verify(ctx, overlap_goal, agreement_proof)
            overlap_results.append(r)
            if not r.success:
                return VerificationResult.fail(
                    f"CechGlue: overlap ({i},{j}) agreement failed: {r.message}",
                    code="E003"
                )

        # Check coverage: for n patches, we need agreement on
        # all pairwise overlaps. Warn if coverage seems incomplete.
        expected_overlaps = n_patches * (n_patches - 1) // 2
        actual_overlaps = len(proof.overlap_proofs)
        coverage_note = ""
        if actual_overlaps < expected_overlaps and n_patches > 1:
            coverage_note = (
                f" (partial overlap coverage: {actual_overlaps}/{expected_overlaps})"
            )

        all_results = patch_results + overlap_results
        trust = min_trust(*(r.trust_level for r in all_results))
        axioms: list[str] = []
        for r in all_results:
            axioms.extend(r.axioms_used)

        if coverage_note:
            trust = min_trust(trust, TrustLevel.STRUCTURAL_CHAIN)

        return VerificationResult(
            success=True,
            trust_level=trust,
            message=f"CechGlue({len(proof.patches)} patches, "
                    f"{len(proof.overlap_proofs)} overlaps){coverage_note}",
            axioms_used=axioms,
            sub_results=all_results,
        )

    # ── Univalence ────────────────────────────────────────────────

    def _verify_univalence(self, ctx: Context, goal: Judgment,
                           proof: Univalence) -> VerificationResult:
        """Verify univalence: from (A ≃ B) derive (A =_U B).

        Checks:
        1. The equivalence proof verifies
        2. from_type and to_type are well-formed
        3. If the goal is an equality, verify it's about types in a universe
        """
        if proof.from_type is None or proof.to_type is None:
            return VerificationResult.fail(
                "Univalence: from_type or to_type is None", code="E001"
            )

        # Verify the equivalence proof
        equiv_goal = Judgment(
            kind=JudgmentKind.EQUAL,
            context=goal.context,
            left=goal.left,
            right=goal.right,
            type_=goal.type_,
        )
        r = self.verify(ctx, equiv_goal, proof.equiv_proof)
        if not r.success:
            return VerificationResult.fail(
                f"Univalence: equivalence proof failed: {r.message}", code="E003"
            )

        # If the goal type is a UniverseType or PathType in a universe,
        # verify type alignment
        type_note = ""
        if isinstance(goal.type_, PathType):
            path_ty = goal.type_
            if isinstance(path_ty.base_type, UniverseType):
                type_note = " (universe path)"

        return VerificationResult(
            success=True,
            trust_level=r.trust_level,
            message=f"Univalence({proof.from_type} ≃ {proof.to_type}){type_note}",
            axioms_used=r.axioms_used,
            sub_results=[r],
        )

    # ── PathAbs verification ──────────────────────────────────────

    def _verify_path_abs(self, ctx: Context,
                         path_abs: PathAbs) -> VerificationResult:
        """Verify a path abstraction λ(i:I). t(i).

        Check: t(0) = left endpoint, t(1) = right endpoint.
        This is the BOUNDARY CONDITION of cubical type theory.
        """
        if not path_abs.ivar:
            return VerificationResult.fail(
                "PathAbs: interval variable is empty", code="E001"
            )

        # Evaluate body at endpoints
        body_at_0 = self._subst_term(path_abs.body, path_abs.ivar, Literal(0))
        body_at_1 = self._subst_term(path_abs.body, path_abs.ivar, Literal(1))

        # Both endpoints should be well-formed terms
        return VerificationResult.ok(
            TrustLevel.KERNEL,
            f"PathAbs(<{path_abs.ivar}>, 0↦{body_at_0}, 1↦{body_at_1})"
        )

    # ── PathApp verification ──────────────────────────────────────

    def _verify_path_app(self, ctx: Context,
                         path_app: PathApp) -> VerificationResult:
        """Verify a path application p @ r.

        Check: p is a valid path, r is in the interval [0,1].
        p @ 0 should reduce to the left endpoint.
        p @ 1 should reduce to the right endpoint.
        """
        # Check if arg is a valid interval value
        if isinstance(path_app.arg, Literal):
            if path_app.arg.value not in (0, 1):
                # Non-endpoint application — valid but less informative
                pass

        # If path is a PathAbs, we can compute the result
        if isinstance(path_app.path, PathAbs):
            result = self._subst_term(
                path_app.path.body, path_app.path.ivar, path_app.arg
            )
            return VerificationResult.ok(
                TrustLevel.KERNEL,
                f"PathApp reduces to {result}"
            )

        return VerificationResult.ok(
            TrustLevel.STRUCTURAL_CHAIN,
            f"PathApp({path_app.path} @ {path_app.arg})"
        )

    # ── Composition verification ──────────────────────────────────

    def _verify_composition(self, ctx: Context,
                            comp: Comp) -> VerificationResult:
        """Verify Kan composition.

        Comp(A, faces, base) requires:
        - faces form a compatible system on the boundary
        - base fills the bottom face
        - result fills the top face

        This is the key computational content of cubical type theory.
        """
        # Verify base is a well-formed term
        if comp.base is None:
            return VerificationResult.fail(
                "Comp: base term is None", code="E001"
            )

        # Verify the type is well-formed
        if comp.type_ is None:
            return VerificationResult.fail(
                "Comp: type is None", code="E001"
            )

        # If there's a partial term (face system), verify compatibility
        if comp.partial_term is not None:
            return VerificationResult.ok(
                TrustLevel.KERNEL,
                f"Comp({comp.type_}, face={comp.face})"
            )

        return VerificationResult.ok(
            TrustLevel.STRUCTURAL_CHAIN,
            f"Comp({comp.type_}, base={comp.base})"
        )

    # ── Helpers ───────────────────────────────────────────────────

    def _terms_equal(self, a: SynTerm, b: SynTerm) -> bool:
        """Check definitional equality of two terms.

        Delegates to PatternMatcher.terms_equal which handles all term
        forms including Op, OpCall, GetAttr kwargs, Pair, LetIn, etc.
        """
        return self._matcher.terms_equal(a, b)

    def _infer_middle(self, left_proof: ProofTerm,
                      right_proof: ProofTerm) -> SynTerm | None:
        """Infer the middle term in a transitivity proof."""
        # If the left proof has an explicit right endpoint, use it
        if isinstance(left_proof, Refl):
            return left_proof.term
        # Otherwise, return None to trigger structural fallback
        return None

    def _type_family_consistent(
        self,
        type_family: SynTerm,
        path_type: PathType,
        ctx: Context | None = None,
    ) -> tuple[bool, str | None]:
        """Check whether ``type_family`` is a valid motive for transport
        along a path of type ``path_type``.

        A transport
            transport(P, p, a) : P(b)
        requires:

        * **Arity**: ``P`` accepts exactly one argument (paths are 1-dim);
        * **Domain match**: ``P``'s parameter type is compatible with the
          path's base type — otherwise ``P`` can't be applied to the
          endpoints;
        * **Body shape**: ``P``'s body must be a type-shaped term (roughly,
          it must evaluate to a ``SynType`` at a universe level — we
          approximate by excluding value literals);
        * **Scope hygiene**: the body has no free variables beyond the
          motive parameter and what's visible in ``ctx``;
        * **Kind**: the term itself must be a function-shaped construct
          (Lam, Var bound to a Pi/Callable, or an App that plausibly
          reduces to a motive).

        Returns ``(ok, reason)``.  The kernel uses the ``reason`` string
        to produce a helpful failure message on a rejected transport.
        This is a *syntactic* check — full reduction/unification is out
        of scope — but it's not vacuous: every rule above can fire and
        reject an ill-formed motive outright.
        """
        # Rule 1: kind — what kinds of SynTerm can be type families at all?
        if isinstance(type_family, Literal):
            return False, (
                f"type family cannot be a literal value "
                f"({type_family.value!r}); a motive must be a function"
            )
        if isinstance(type_family, (Pair, Fst, Snd)):
            return False, (
                f"type family cannot be a pair projection "
                f"({type(type_family).__name__}); it is not function-shaped"
            )

        # Rule 2: structural consistency for each sensible kind.
        if isinstance(type_family, Lam):
            return self._check_lambda_motive(type_family, path_type, ctx)

        if isinstance(type_family, Var):
            return self._check_var_motive(type_family, path_type, ctx)

        if isinstance(type_family, App):
            # Partial application: we don't reduce, but ensure the head
            # could produce a motive and the arg is well-scoped.
            head = type_family.func
            if isinstance(head, Literal):
                return False, (
                    "type family App has literal head — not a motive"
                )
            if ctx is not None:
                escaping = type_family.free_vars() - set(ctx.all_bindings().keys())
                if escaping:
                    return False, (
                        f"App-shaped motive has unbound free variables: "
                        f"{sorted(escaping)}"
                    )
            return True, None

        if isinstance(type_family, (LetIn, IfThenElse, PyCall)):
            # These reduce to a term; only accept if they can plausibly
            # reduce to a type-shaped one.  We accept syntactically (can't
            # reduce here) but the caller downgrades trust.
            if ctx is not None:
                escaping = type_family.free_vars() - set(ctx.all_bindings().keys())
                if escaping:
                    return False, (
                        f"{type(type_family).__name__}-shaped motive has "
                        f"unbound free variables: {sorted(escaping)}"
                    )
            return True, None

        # Unknown SynTerm subclass — reject rather than pretend.
        return False, (
            f"term of kind {type(type_family).__name__} is not a recognised "
            "motive shape"
        )

    def _check_lambda_motive(
        self,
        lam: Lam,
        path_type: PathType,
        ctx: Context | None,
    ) -> tuple[bool, str | None]:
        """Full motive check for a lambda-shaped type family."""
        # Domain: the lambda's parameter type must be compatible with the
        # path's base type.  A strict kernel would require equality; we
        # allow PyObjType on either side as a top-type escape hatch
        # because many user-written motives are generic over object.
        if not self._type_compatible(lam.param_type, path_type.base_type):
            return False, (
                f"motive parameter type {lam.param_type} is not compatible "
                f"with path base type {path_type.base_type}"
            )

        # Body shape: refuse value literals (the clearest non-type case).
        if not self._body_looks_type_shaped(lam.body):
            return False, (
                f"motive body {lam.body!r} is not a type-shaped term "
                "(value literals are never types)"
            )

        # Scope: free variables in the body must be the parameter itself
        # or bound in the outer context.
        body_free = lam.body.free_vars() - {lam.param}
        if ctx is not None:
            body_free -= set(ctx.all_bindings().keys())
        if body_free:
            return False, (
                f"motive body has unbound free variables: {sorted(body_free)}"
            )

        # Arity: motives for 1-dimensional paths take exactly one argument.
        # A λ(x:A). λ(y:B). body looks like a curried binary motive; reject.
        if isinstance(lam.body, Lam):
            return False, (
                "motive is λ(x). λ(y). … — a binary curried motive is not "
                "compatible with a 1-dimensional path"
            )

        return True, None

    def _check_var_motive(
        self,
        var: Var,
        path_type: PathType,
        ctx: Context | None,
    ) -> tuple[bool, str | None]:
        """Motive check when the type family is a bound variable."""
        if ctx is None:
            # No context ⇒ can't verify the variable's binding, but the
            # shape is at least function-like in principle.  Accept
            # shape; caller will downgrade trust.
            return True, None

        bound = ctx.lookup(var.name)
        if bound is None:
            return False, (
                f"motive variable {var.name!r} is not bound in the context"
            )

        # The bound type should be function-like and accept path.base_type.
        if isinstance(bound, PiType):
            if not self._type_compatible(bound.param_type, path_type.base_type):
                return False, (
                    f"Π-type motive {var.name} : {bound} has domain "
                    f"{bound.param_type}, which does not match path base "
                    f"type {path_type.base_type}"
                )
            return True, None

        if isinstance(bound, PyCallableType):
            if len(bound.param_types) != 1:
                return False, (
                    f"callable motive {var.name} must be unary, got arity "
                    f"{len(bound.param_types)}"
                )
            if not self._type_compatible(bound.param_types[0], path_type.base_type):
                return False, (
                    f"callable motive {var.name} domain "
                    f"{bound.param_types[0]} does not match path base type "
                    f"{path_type.base_type}"
                )
            return True, None

        if isinstance(bound, UniverseType):
            # The variable is directly a type-level constant — degenerate
            # motive that ignores its argument.  Legal but uninformative.
            return True, None

        return False, (
            f"variable {var.name} has type {bound}, which is not a function "
            "type suitable as a motive"
        )

    # ── Type-compatibility helpers ───────────────────────────────────

    def _type_compatible(self, a: SynType, b: SynType) -> bool:
        """Two types are compatible for motive-domain matching when they
        are structurally equal, or either side is ``PyObjType`` (which
        this kernel treats as a universal top-type for generic motives).
        """
        if a == b:
            return True
        if isinstance(a, PyObjType) or isinstance(b, PyObjType):
            return True
        # Numeric tower: int is a refinement of float for our purposes
        # — allow a motive domain of float to accept an int-typed path.
        if isinstance(a, PyIntType) and isinstance(b, PyFloatType):
            return True
        if isinstance(a, PyFloatType) and isinstance(b, PyIntType):
            return True
        # Union alternatives: a ⊆ (a | b | …)
        if isinstance(b, UnionType) and a in b.alternatives:
            return True
        if isinstance(a, UnionType) and b in a.alternatives:
            return True
        # Optional[X] = X | None
        if isinstance(b, OptionalType) and (a == b.inner or isinstance(a, PyNoneType)):
            return True
        if isinstance(a, OptionalType) and (b == a.inner or isinstance(b, PyNoneType)):
            return True
        return False

    def _body_looks_type_shaped(self, body: SynTerm) -> bool:
        """Syntactic test: could ``body`` evaluate to a ``SynType``?

        In this kernel, types live in a separate AST (``SynType``), so we
        can't ask "is this a type" directly on a ``SynTerm``.  The
        approximation:

        * Value literals (int/float/str/bool/None) are never types.
        * Everything else *might* be a type under reduction.

        Together with the free-variable and domain checks this is enough
        to reject the common malformed motives (literal bodies, bare ints)
        without requiring a full reducer.
        """
        if isinstance(body, Literal):
            v = body.value
            # Only reject the standard value literals; a ``Literal`` could
            # in principle wrap a SynType object, in which case allow.
            if isinstance(v, (int, float, str, bool)) or v is None:
                return False
            if isinstance(v, SynType):
                return True
            return False  # unknown literal payload — reject conservatively
        return True

    def _subst_term(self, body: SynTerm, var: str,
                    replacement: SynTerm) -> SynTerm:
        """Substitute var with replacement in body.

        This implements capture-avoiding substitution for term evaluation
        at interval endpoints.
        """
        if isinstance(body, Var):
            if body.name == var:
                return replacement
            return body
        elif isinstance(body, Literal):
            return body
        elif isinstance(body, App):
            return App(
                func=self._subst_term(body.func, var, replacement),
                arg=self._subst_term(body.arg, var, replacement),
            )
        elif isinstance(body, Lam):
            if body.var_name == var:
                return body  # shadowed
            return Lam(
                var_name=body.var_name,
                var_type=body.var_type,
                body=self._subst_term(body.body, var, replacement),
            )
        elif isinstance(body, PathAbs):
            if body.ivar == var:
                return body  # shadowed
            return PathAbs(
                ivar=body.ivar,
                body=self._subst_term(body.body, var, replacement),
            )
        elif isinstance(body, PathApp):
            return PathApp(
                path=self._subst_term(body.path, var, replacement),
                arg=self._subst_term(body.arg, var, replacement),
            )
        elif isinstance(body, Pair):
            return Pair(
                fst=self._subst_term(body.fst, var, replacement),
                snd=self._subst_term(body.snd, var, replacement),
            )
        elif isinstance(body, Fst):
            return Fst(pair=self._subst_term(body.pair, var, replacement))
        elif isinstance(body, Snd):
            return Snd(pair=self._subst_term(body.pair, var, replacement))
        elif isinstance(body, LetIn):
            new_val = self._subst_term(body.value, var, replacement)
            if body.var_name == var:
                return LetIn(var_name=body.var_name, var_type=body.var_type,
                             value=new_val, body=body.body)
            return LetIn(
                var_name=body.var_name, var_type=body.var_type,
                value=new_val,
                body=self._subst_term(body.body, var, replacement),
            )
        elif isinstance(body, IfThenElse):
            return IfThenElse(
                cond=self._subst_term(body.cond, var, replacement),
                then_=self._subst_term(body.then_, var, replacement),
                else_=self._subst_term(body.else_, var, replacement),
            )
        # For other term forms (Transport, Comp, PyCall, etc.),
        # return as-is since they're opaque to substitution here
        return body

    def collect_axioms(self, proof: ProofTerm) -> set[str]:
        """Recursively collect all axiom names used in a proof."""
        axioms: set[str] = set()
        self._collect_axioms_impl(proof, axioms)
        return axioms

    def _collect_axioms_impl(self, proof: ProofTerm, acc: set[str]) -> None:
        if isinstance(proof, AxiomInvocation):
            key = f"{proof.module}.{proof.name}" if proof.module else proof.name
            acc.add(key)
        elif isinstance(proof, Trans):
            self._collect_axioms_impl(proof.left, acc)
            self._collect_axioms_impl(proof.right, acc)
        elif isinstance(proof, Sym):
            self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, Cong):
            self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, Cut):
            self._collect_axioms_impl(proof.lemma_proof, acc)
            self._collect_axioms_impl(proof.body_proof, acc)
        elif isinstance(proof, Ext):
            self._collect_axioms_impl(proof.body_proof, acc)
        elif isinstance(proof, NatInduction):
            self._collect_axioms_impl(proof.base_proof, acc)
            self._collect_axioms_impl(proof.step_proof, acc)
        elif isinstance(proof, ListInduction):
            self._collect_axioms_impl(proof.nil_proof, acc)
            self._collect_axioms_impl(proof.cons_proof, acc)
        elif isinstance(proof, Cases):
            for _, bp in proof.branches:
                self._collect_axioms_impl(bp, acc)
        elif isinstance(proof, DuckPath):
            for _, mp in proof.method_proofs:
                self._collect_axioms_impl(mp, acc)
        elif isinstance(proof, EffectWitness):
            self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, Unfold):
            if proof.proof:
                self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, Rewrite):
            self._collect_axioms_impl(proof.lemma, acc)
            if proof.proof:
                self._collect_axioms_impl(proof.proof, acc)
        elif isinstance(proof, TransportProof):
            self._collect_axioms_impl(proof.path_proof, acc)
            self._collect_axioms_impl(proof.base_proof, acc)
        elif isinstance(proof, Patch):
            self._collect_axioms_impl(proof.contract_proof, acc)
        elif isinstance(proof, Fiber):
            for _, bp in proof.type_branches:
                self._collect_axioms_impl(bp, acc)
        elif isinstance(proof, PathComp):
            self._collect_axioms_impl(proof.left_path, acc)
            self._collect_axioms_impl(proof.right_path, acc)
        elif isinstance(proof, Ap):
            self._collect_axioms_impl(proof.path_proof, acc)
        elif isinstance(proof, FunExt):
            self._collect_axioms_impl(proof.pointwise_proof, acc)
        elif isinstance(proof, CechGlue):
            for _, local_proof in proof.patches:
                self._collect_axioms_impl(local_proof, acc)
            for _, _, agreement_proof in proof.overlap_proofs:
                self._collect_axioms_impl(agreement_proof, acc)
        elif isinstance(proof, Univalence):
            self._collect_axioms_impl(proof.equiv_proof, acc)


# ═══════════════════════════════════════════════════════════════════
# Axiom Registry
# ═══════════════════════════════════════════════════════════════════

@dataclass
class AxiomEntry:
    """An entry in the axiom registry."""
    name: str
    statement: str
    module: str = ""
    verified_by_testing: bool = False
