"""
Deppy Syntactic Sugar — Ergonomic Proof & Specification DSL

Provides decorator-based specs, F*-style proof-carrying code, calc blocks,
library assumption blocks, refinement type constructors, and proof combinators
that compile down to the existing ProofTerm / ProofBuilder infrastructure.

Philosophy: sugar is ALWAYS desugared to existing kernel-accepted constructs.
No new trusted code — only convenience.

Example
-------
    @guarantee("sorted output that is a permutation of input")
    @requires(lambda xs: len(xs) > 0)
    @ensures(lambda xs, result: len(result) == len(xs))
    @pure
    def my_sort(xs: list[int]) -> list[int]:
        return sorted(xs)

    with library_trust("sympy") as sp:
        sp.axiom("expand(a + b) = expand(a) + expand(b)", name="expand_add")
        sp.axiom("simplify(simplify(e)) = simplify(e)", name="simplify_idem")

    proof = (
        Proof("sorted(sorted(xs)) == sorted(xs)")
        .by_axiom("sorted_idempotent", "builtins")
        .qed()
    )
"""
from __future__ import annotations

import ast
import functools
import inspect
import textwrap
from dataclasses import dataclass, field
from typing import Any, Callable, Sequence, TypeVar, overload

from deppy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, Cut, Assume, Z3Proof,
    NatInduction, ListInduction, Cases, DuckPath,
    EffectWitness, ConditionalEffectWitness, SafetyObligation,
    AxiomInvocation, Ext, Unfold, Rewrite,
    Structural, TransportProof, min_trust,
    PathComp, Ap, FunExt, CechGlue, Univalence, Fiber, Patch,
)
from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    Var, Literal, PyObjType, PyIntType, PyFloatType, PyStrType,
    PyBoolType, PyNoneType, PyListType, PyDictType, PySetType,
    PyTupleType, PyCallableType, PyClassType,
    RefinementType, UnionType, OptionalType, PathType,
    PiType, SigmaType, ProtocolType,
    App, Lam, Pair, Fst, Snd, LetIn, IfThenElse,
    arrow,
    Spec, SpecKind, FunctionSpec,
)
from deppy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq, formal_check,
)
from deppy.proofs.tactics import ProofBuilder

F = TypeVar("F", bound=Callable)

# Fallback registry for objects that don't support attribute assignment
# (e.g. built-in / C-extension types).
_SPEC_REGISTRY: dict[int, "_SpecMetadata"] = {}


# ═══════════════════════════════════════════════════════════════════
#  §1  Decorator-based Specifications
# ═══════════════════════════════════════════════════════════════════

@dataclass
class _SpecMetadata:
    """Metadata attached to a function via spec decorators."""
    guarantees: list[str] = field(default_factory=list)
    preconditions: list[Callable] = field(default_factory=list)
    postconditions: list[Callable] = field(default_factory=list)
    effect: str = "Unknown"
    is_total: bool = False
    is_partial: bool = False
    invariants: list[str] = field(default_factory=list)
    library_axioms_used: list[str] = field(default_factory=list)


def _get_spec(f: Any) -> _SpecMetadata:
    """Return (or create) the _SpecMetadata for *f*.

    Works for functions **and** classes (including dataclasses and
    built-in types that disallow arbitrary attribute assignment).
    """
    if hasattr(f, "_deppy_spec"):
        return f._deppy_spec  # type: ignore[attr-defined]

    # Check the fallback registry (for immutable types)
    obj_id = id(f)
    if obj_id in _SPEC_REGISTRY:
        return _SPEC_REGISTRY[obj_id]

    spec = _SpecMetadata()
    try:
        f._deppy_spec = spec  # type: ignore[attr-defined]
    except (AttributeError, TypeError):
        # Immutable / C-extension types — fall back to id-keyed registry
        _SPEC_REGISTRY[obj_id] = spec
    return spec


def guarantee(description: str, *, adds_guarantee: bool = False) -> Callable:
    """Attach a natural-language postcondition guarantee.

    Works on both **functions** and **classes** (including dataclasses)::

        @guarantee("returns a sorted list with no duplicates")
        def unique_sorted(xs: list[int]) -> list[int]:
            return sorted(set(xs))

        @guarantee("self.x >= 0")
        @dataclass
        class Point:
            x: float

        @guarantee("wrapped preserves original spec", adds_guarantee=True)
        def wrapper(fn):
            ...
    """
    def decorator(f):
        spec = _get_spec(f)
        spec.guarantees.append(description)
        if adds_guarantee:
            try:
                f._deppy_adds_guarantee = True  # type: ignore[attr-defined]
            except (AttributeError, TypeError):
                pass
        return f
    return decorator


def requires(predicate: Callable | str) -> Callable:
    """Attach a precondition.

    Works on both **functions** and **classes**::

        @requires(lambda xs: len(xs) > 0)
        @requires("xs is non-empty")
        def head(xs: list) -> Any:
            return xs[0]
    """
    def decorator(f):
        spec = _get_spec(f)
        if callable(predicate) and not isinstance(predicate, str):
            spec.preconditions.append(predicate)
        else:
            spec.preconditions.append(lambda *_: predicate)
        return f
    return decorator


def ensures(predicate: Callable | str) -> Callable:
    """Attach a formal postcondition (a callable predicate on args + result).

    Works on both **functions** and **classes**::

        @ensures(lambda xs, result: len(result) == len(xs))
        def identity(xs: list) -> list:
            return xs[:]
    """
    def decorator(f):
        spec = _get_spec(f)
        if callable(predicate) and not isinstance(predicate, str):
            spec.postconditions.append(predicate)
        else:
            spec.postconditions.append(lambda *_: predicate)
        return f
    return decorator


def pure(f: F) -> F:
    """Mark a function or class as pure (no side effects)."""
    _get_spec(f).effect = "Pure"
    return f


def reads(f: F) -> F:
    """Mark a function or class as read-only (no mutation)."""
    _get_spec(f).effect = "Reads"
    return f


def mutates(f: F) -> F:
    """Mark a function or class as mutating."""
    _get_spec(f).effect = "Mutates"
    return f


def total(f: F) -> F:
    """Mark a function or class as total (always terminates, never raises).

    F*-style: the return type IS the proof obligation.
    """
    spec = _get_spec(f)
    spec.is_total = True
    spec.effect = "Pure"
    return f


def partial_fn(f: F) -> F:
    """Mark a function or class as partial (may not terminate or may raise)."""
    _get_spec(f).is_partial = True
    return f


def invariant(description: str) -> Callable:
    """Attach a class/loop invariant.  Works on functions and classes."""
    def decorator(f):
        spec = _get_spec(f)
        spec.invariants.append(description)
        return f
    return decorator


def decreases(*args) -> Callable:
    """Specify a termination measure (variant) for recursive/looping functions.

    Accepts strings *or* lambdas (converted to their source representation)::

        @decreases("len(xs)")          # string form
        @decreases(lambda xs: len(xs)) # lambda form — equally valid
    """
    def decorator(f):
        spec = _get_spec(f)
        parts = []
        for a in args:
            if callable(a) and not isinstance(a, str):
                # Lambda or function — try to extract source, fallback to repr
                try:
                    src = inspect.getsource(a).strip()
                    parts.append(src)
                except (OSError, TypeError):
                    parts.append(repr(a))
            else:
                parts.append(str(a))
        spec.invariants.append(f"decreases({', '.join(parts)})")
        return f
    # If called with a single callable that looks like the decorated function
    # itself (e.g. @decreases applied without arguments), handle that edge case
    if len(args) == 1 and callable(args[0]) and not isinstance(args[0], str):
        # Could be @decreases used as bare decorator or @decreases(lambda ...)
        # Check if it's a lambda (has __name__ == '<lambda>') vs a full function
        if getattr(args[0], '__name__', '') != '<lambda>':
            # Bare decorator: @decreases applied directly to function
            f = args[0]
            spec = _get_spec(f)
            spec.invariants.append("decreases(auto)")
            return f
    return decorator


# ═══════════════════════════════════════════════════════════════════
#  §2  Refinement Type Constructors
# ═══════════════════════════════════════════════════════════════════

def Pos() -> RefinementType:
    """Positive integer: {x : int | x > 0}."""
    return RefinementType(base_type=PyIntType(), predicate="x > 0", var_name="x")

def Nat() -> RefinementType:
    """Natural number: {x : int | x >= 0}."""
    return RefinementType(base_type=PyIntType(), predicate="x >= 0", var_name="x")

def NonEmpty(element_type: SynType | None = None) -> RefinementType:
    """Non-empty list: {xs : list | len(xs) > 0}."""
    base = PyListType(element_type=element_type) if element_type else PyListType()
    return RefinementType(base_type=base, predicate="len(xs) > 0", var_name="xs")

def Bounded(lo: float, hi: float) -> RefinementType:
    """Bounded float: {x : float | lo <= x <= hi}."""
    return RefinementType(
        base_type=PyFloatType(),
        predicate=f"{lo} <= x <= {hi}",
        var_name="x",
    )

def NonNull(base: SynType | None = None) -> RefinementType:
    """Non-None value: {x : A | x is not None}."""
    return RefinementType(
        base_type=base or PyObjType(),
        predicate="x is not None",
        var_name="x",
    )

def Sorted(element_type: SynType | None = None) -> RefinementType:
    """Sorted list: {xs : list | all(xs[i] <= xs[i+1] for i in range(len(xs)-1))}."""
    base = PyListType(element_type=element_type) if element_type else PyListType()
    return RefinementType(
        base_type=base,
        predicate="all(xs[i] <= xs[i+1] for i in range(len(xs)-1))",
        var_name="xs",
    )

def SizedExact(n: int) -> RefinementType:
    """Collection of exact size n: {xs | len(xs) == n}."""
    return RefinementType(
        base_type=PyListType(),
        predicate=f"len(xs) == {n}",
        var_name="xs",
    )

def Refine(base: SynType, pred: str, var: str = "x") -> RefinementType:
    """Generic refinement type constructor.

    Usage::

        Even = Refine(int, "x % 2 == 0")
        ShortStr = Refine(str, "len(x) <= 255")
    """
    return RefinementType(base_type=base, predicate=pred, var_name=var)


# ═══════════════════════════════════════════════════════════════════
#  §3  Library Assumption Blocks
# ═══════════════════════════════════════════════════════════════════

@dataclass
class LibraryTrustBlock:
    """Context manager for declaring trusted library axioms.

    Usage::

        with library_trust("sympy") as sp:
            sp.axiom("expand(a + b) = expand(a) + expand(b)", name="expand_add")
            sp.axiom("simplify(simplify(e)) = simplify(e)", name="simplify_idem")

        # Axioms are now available for proof construction
    """

    module: str
    axioms: list[tuple[str, str]] = field(default_factory=list)
    _kernel: ProofKernel | None = None

    def axiom(self, statement: str, name: str | None = None,
              when: str | None = None) -> LibraryTrustBlock:
        """Declare a trusted axiom about this library.

        Args:
            statement: The axiom as a human-readable equation/property.
            name: Optional name (auto-generated from statement if omitted).
            when: Optional precondition for the axiom.
        """
        if name is None:
            name = statement[:40].replace(" ", "_").replace("(", "").replace(")", "")
        if when:
            statement = f"{statement}  [when {when}]"
        self.axioms.append((name, statement))
        if self._kernel is not None:
            from deppy.core.kernel import AxiomEntry
            key = f"{self.module}.{name}"
            self._kernel.axiom_registry[key] = AxiomEntry(
                name=name, statement=statement, module=self.module,
            )
        return self

    def bind_kernel(self, kernel: ProofKernel) -> LibraryTrustBlock:
        """Bind to a kernel so axioms are registered immediately."""
        self._kernel = kernel
        for name, stmt in self.axioms:
            from deppy.core.kernel import AxiomEntry
            key = f"{self.module}.{name}"
            kernel.axiom_registry[key] = AxiomEntry(
                name=name, statement=stmt, module=self.module,
            )
        return self

    def use(self, axiom_name: str, **instantiation: SynTerm) -> AxiomInvocation:
        """Create an axiom invocation proof term."""
        return AxiomInvocation(
            name=axiom_name, module=self.module,
            instantiation=instantiation,
        )

    def __enter__(self) -> LibraryTrustBlock:
        return self

    def __exit__(self, *args: Any) -> None:
        pass


def library_trust(module: str, kernel: ProofKernel | None = None) -> LibraryTrustBlock:
    """Create a library trust block.

    Usage::

        with library_trust("numpy") as np:
            np.axiom("dot(A, B).T == dot(B.T, A.T)", name="dot_transpose")
    """
    block = LibraryTrustBlock(module=module)
    if kernel is not None:
        block.bind_kernel(kernel)
    return block


# ═══════════════════════════════════════════════════════════════════
#  §4  Fluent Proof Builder (Chainable API)
# ═══════════════════════════════════════════════════════════════════

class Proof:
    """Fluent, chainable proof construction.

    Usage::

        result = (
            Proof("sorted(sorted(xs)) == sorted(xs)")
            .using(kernel)
            .given(x="list[int]")
            .by_axiom("sorted_idempotent", "builtins")
            .qed()
        )

        result = (
            Proof("len(xs + ys) == len(xs) + len(ys)")
            .using(kernel)
            .given(xs="list", ys="list")
            .calc(
                "len(xs + ys)",
                "== len(xs) + len(ys)", by=lambda p: p.axiom("len_concat", "builtins"),
            )
            .qed()
        )

        result = (
            Proof("abs(x) >= 0")
            .using(kernel)
            .given(x="int")
            .by_z3()
            .qed()
        )
    """

    def __init__(self, goal_description: str):
        self._goal_desc = goal_description
        self._kernel: ProofKernel | None = None
        self._ctx = Context()
        self._goal: Judgment | None = None
        self._steps: list[tuple[str, ProofTerm]] = []
        self._final_proof: ProofTerm | None = None
        self._builder: ProofBuilder | None = None

    def using(self, kernel: ProofKernel) -> Proof:
        """Bind to a proof kernel."""
        self._kernel = kernel
        return self

    def given(self, **bindings: str | SynType) -> Proof:
        """Introduce universally quantified variables.

        Usage::
            .given(x="int", xs="list[int]", A="Matrix")
        """
        for name, type_desc in bindings.items():
            ty = _parse_type(type_desc) if isinstance(type_desc, str) else type_desc
            self._ctx = self._ctx.extend(name, ty)
        return self

    def assuming(self, name: str, claim: str) -> Proof:
        """Add a hypothesis (precondition) to the proof context."""
        self._ensure_builder()
        assert self._builder is not None
        self._builder.have(name, claim, Assume(name=name))
        return self

    def have(self, name: str, claim: str, *,
             by: Callable[[ProofBuilder], ProofTerm] | ProofTerm | None = None,
             by_z3: str | None = None,
             by_axiom: tuple[str, str] | None = None) -> Proof:
        """Introduce a lemma.

        Usage::
            .have("h1", "x > 0", by=lambda p: p.assume("precond"))
            .have("h2", "x + 1 > 1", by_z3="x > 0 => x + 1 > 1")
            .have("h3", "expand(a+b) = ...", by_axiom=("expand_add", "sympy"))
        """
        self._ensure_builder()
        assert self._builder is not None
        if by is not None:
            proof = by(self._builder) if callable(by) else by
        elif by_z3 is not None:
            proof = Z3Proof(formula=by_z3)
        elif by_axiom is not None:
            proof = AxiomInvocation(name=by_axiom[0], module=by_axiom[1])
        else:
            proof = Structural(description=claim)
        self._builder.have(name, claim, proof)
        return self

    def by_axiom(self, name: str, module: str = "",
                 **instantiation: SynTerm) -> Proof:
        """Conclude by invoking an axiom."""
        self._final_proof = AxiomInvocation(
            name=name, module=module, instantiation=instantiation,
        )
        return self

    def by_z3(self, formula: str | None = None) -> Proof:
        """Conclude by Z3 discharge."""
        self._final_proof = Z3Proof(formula=formula or self._goal_desc)
        return self

    def by_refl(self, term: SynTerm | None = None) -> Proof:
        """Conclude by reflexivity."""
        self._final_proof = Refl(term=term or Var("_"))
        return self

    def by_structural(self, desc: str = "") -> Proof:
        """Conclude by structural verification."""
        self._final_proof = Structural(description=desc or self._goal_desc)
        return self

    def by_induction(self, on: str, *, base: ProofTerm, step: ProofTerm,
                     kind: str = "nat") -> Proof:
        """Conclude by induction."""
        if kind == "nat":
            self._final_proof = NatInduction(var=on, base_proof=base, step_proof=step)
        else:
            self._final_proof = ListInduction(var=on, nil_proof=base, cons_proof=step)
        return self

    def by_cases(self, scrutinee: SynTerm,
                 *branches: tuple[str, ProofTerm]) -> Proof:
        """Conclude by case analysis."""
        self._final_proof = Cases(
            scrutinee=scrutinee, branches=list(branches),
        )
        return self

    def calc(self, *steps: str | tuple[str, Callable | ProofTerm]) -> Proof:
        """Equational reasoning chain (calc block).

        Usage::

            .calc(
                "a * (b + c)",
                ("== a*b + a*c", by=lambda p: p.axiom("distributivity", "builtins")),
                ("== a*b + a*c", by=some_proof_term),
            )
        """
        proofs: list[ProofTerm] = []
        self._ensure_builder()
        assert self._builder is not None
        for step in steps:
            if isinstance(step, str):
                continue  # first line is just the starting term
            claim, justification = step[0], step[1]
            if callable(justification):
                proof = justification(self._builder)
            else:
                proof = justification
            proofs.append(proof)

        if len(proofs) == 0:
            self._final_proof = Structural(description="empty calc")
        elif len(proofs) == 1:
            self._final_proof = proofs[0]
        else:
            result = proofs[0]
            for p in proofs[1:]:
                result = Trans(left=result, right=p)
            self._final_proof = result
        return self

    def transport(self, *, along: ProofTerm, base: ProofTerm,
                  family: SynTerm | None = None) -> Proof:
        """Conclude by transport along a path."""
        self._final_proof = TransportProof(
            type_family=family or Var("_P"),
            path_proof=along,
            base_proof=base,
        )
        return self

    # ── Homotopy-native methods ──────────────────────────────────

    def by_path(self, a: str, b: str, via: str = "refl") -> Proof:
        """Set proof to a path construction."""
        self._final_proof = path(a, b, via=via)
        return self

    def by_transport_along(self, from_proof: ProofTerm,
                           along: ProofTerm,
                           family: str = "auto") -> Proof:
        """Transport an existing proof along a path."""
        self._final_proof = transport_proof(family, along, from_proof)
        return self

    def by_cech(self, *patches: tuple[str, ProofTerm],
                overlaps: list[tuple[int, int, ProofTerm]] | None = None) -> Proof:
        """Prove by Čech decomposition."""
        self._final_proof = by_cech_proof(*patches, overlaps=overlaps)
        return self

    def by_fiber(self, scrutinee: str,
                 branches: dict[str, ProofTerm]) -> Proof:
        """Prove by fibration descent over type fibers."""
        self._final_proof = by_fiber_proof(scrutinee, branches)
        return self

    def by_duck_equiv(self, type_a: str, type_b: str,
                      methods: dict[str, ProofTerm]) -> Proof:
        """Prove via duck-type equivalence."""
        self._final_proof = by_duck_type(type_a, type_b, methods)
        return self

    def by_funext(self, var: str, pointwise: ProofTerm) -> Proof:
        """Prove function equality by extensionality."""
        self._final_proof = funext(var, pointwise)
        return self

    def qed(self) -> VerificationResult:
        """Finalize and verify the proof."""
        if self._kernel is None:
            self._kernel = ProofKernel()
        self._ensure_builder()
        assert self._builder is not None
        if self._final_proof is None:
            self._final_proof = Structural(description=self._goal_desc)
        return self._builder.conclude(self._final_proof)

    def _ensure_builder(self) -> None:
        if self._builder is None:
            if self._kernel is None:
                self._kernel = ProofKernel()
            self._goal = Judgment(
                context=self._ctx,
                kind=JudgmentKind.TYPE_CHECK,
                term=Var("_goal"),
                type_=RefinementType(
                    base_type=PyBoolType(),
                    predicate=self._goal_desc,
                ),
            )
            self._builder = ProofBuilder(self._kernel, self._ctx, goal=self._goal)


# ═══════════════════════════════════════════════════════════════════
#  §5  Formal Proof Builder (term-tree goals)
# ═══════════════════════════════════════════════════════════════════

class FormalProof:
    """Proof builder using formal term trees instead of strings.

    Usage::

        from deppy.core.formal_ops import op_sorted, op_len

        result = (
            FormalProof.eq(op_sorted(op_sorted(xs)), op_sorted(xs))
            .using(kernel)
            .given(xs=PyListType())
            .by_axiom("sorted_idempotent", "builtins")
            .qed()
        )
    """

    def __init__(self, goal: Judgment):
        self._goal = goal
        self._kernel: ProofKernel | None = None
        self._ctx = goal.context
        self._final_proof: ProofTerm | None = None
        self._builder: ProofBuilder | None = None

    @classmethod
    def eq(cls, left: SynTerm, right: SynTerm,
           type_: SynType | None = None,
           ctx: Context | None = None) -> FormalProof:
        """Create an equality proof goal."""
        return cls(formal_eq(ctx or Context(), left, right, type_))

    @classmethod
    def check(cls, term: SynTerm, type_: SynType,
              ctx: Context | None = None) -> FormalProof:
        """Create a type-checking proof goal."""
        return cls(formal_check(ctx or Context(), term, type_))

    def using(self, kernel: ProofKernel) -> FormalProof:
        self._kernel = kernel
        return self

    def given(self, **bindings: SynType) -> FormalProof:
        for name, ty in bindings.items():
            self._ctx = self._ctx.extend(name, ty)
        self._goal = Judgment(
            context=self._ctx,
            kind=self._goal.kind,
            term=self._goal.term,
            type_=self._goal.type_,
            left=self._goal.left,
            right=self._goal.right,
        )
        return self

    def by_axiom(self, name: str, module: str = "",
                 **instantiation: SynTerm) -> FormalProof:
        self._final_proof = AxiomInvocation(
            name=name, module=module, instantiation=instantiation,
        )
        return self

    def by_z3(self, formula: str = "") -> FormalProof:
        self._final_proof = Z3Proof(formula=formula)
        return self

    def by_refl(self, term: SynTerm | None = None) -> FormalProof:
        self._final_proof = Refl(term=term or Var("_"))
        return self

    def by_trans(self, p1: ProofTerm, p2: ProofTerm) -> FormalProof:
        self._final_proof = Trans(left=p1, right=p2)
        return self

    def by_cong(self, func: SynTerm, inner: ProofTerm) -> FormalProof:
        self._final_proof = Cong(func=func, proof=inner)
        return self

    def qed(self) -> VerificationResult:
        if self._kernel is None:
            self._kernel = ProofKernel()
        self._builder = ProofBuilder(self._kernel, self._ctx, goal=self._goal)
        if self._final_proof is None:
            self._final_proof = Structural(description="auto")
        return self._builder.conclude(self._final_proof)


# ═══════════════════════════════════════════════════════════════════
#  §6  spec() Context Manager for Multi-Step Proofs
# ═══════════════════════════════════════════════════════════════════

class ProofContext:
    """Context manager for multi-step proofs with scoped hypotheses.

    Usage::

        with ProofContext(kernel, "x + 0 == x") as p:
            p.given(x="int")
            p.assume("h", "x is an integer")
            p.have("step1", "x + 0 = x", by_z3="x + 0 = x")
            result = p.qed(by=p.by("step1"))
    """

    def __init__(self, kernel: ProofKernel | None = None,
                 goal: str = "",
                 formal_goal: Judgment | None = None):
        self._kernel = kernel or ProofKernel()
        self._goal_desc = goal
        self._formal_goal = formal_goal
        self._ctx = Context()
        self._builder: ProofBuilder | None = None
        self._result: VerificationResult | None = None

    def given(self, **bindings: str | SynType) -> ProofContext:
        for name, type_desc in bindings.items():
            ty = _parse_type(type_desc) if isinstance(type_desc, str) else type_desc
            self._ctx = self._ctx.extend(name, ty)
        return self

    def assume(self, name: str, claim: str) -> ProofContext:
        self._ensure_builder()
        assert self._builder is not None
        self._builder.have(name, claim, Assume(name=name))
        return self

    def have(self, name: str, claim: str, *,
             by: ProofTerm | None = None,
             by_z3: str | None = None,
             by_axiom: tuple[str, str] | None = None) -> ProofContext:
        self._ensure_builder()
        assert self._builder is not None
        if by is not None:
            proof = by
        elif by_z3 is not None:
            proof = Z3Proof(formula=by_z3)
        elif by_axiom is not None:
            proof = AxiomInvocation(name=by_axiom[0], module=by_axiom[1])
        else:
            proof = Structural(description=claim)
        self._builder.have(name, claim, proof)
        return self

    def by(self, name: str) -> ProofTerm:
        assert self._builder is not None
        return self._builder.by(name)

    def qed(self, *, by: ProofTerm | None = None) -> VerificationResult:
        self._ensure_builder()
        assert self._builder is not None
        proof = by or Structural(description=self._goal_desc)
        self._result = self._builder.conclude(proof)
        return self._result

    def _ensure_builder(self) -> None:
        if self._builder is None:
            goal = self._formal_goal or Judgment(
                context=self._ctx,
                kind=JudgmentKind.TYPE_CHECK,
                term=Var("_goal"),
                type_=RefinementType(base_type=PyBoolType(), predicate=self._goal_desc),
            )
            self._builder = ProofBuilder(self._kernel, self._ctx, goal=goal)

    def __enter__(self) -> ProofContext:
        return self

    def __exit__(self, *args: Any) -> None:
        pass


# ═══════════════════════════════════════════════════════════════════
#  §7  Quick Proof Combinators
# ═══════════════════════════════════════════════════════════════════

def refl(term: SynTerm | str = "_") -> Refl:
    """Quick reflexivity proof."""
    t = Var(term) if isinstance(term, str) else term
    return Refl(term=t)

def sym(proof: ProofTerm) -> Sym:
    """Quick symmetry."""
    return Sym(proof=proof)

def trans(*proofs: ProofTerm) -> ProofTerm:
    """Chain multiple proofs transitively."""
    if len(proofs) == 0:
        return Structural(description="empty chain")
    result = proofs[0]
    for p in proofs[1:]:
        result = Trans(left=result, right=p)
    return result

def by_axiom(name: str, module: str = "", **kw: SynTerm) -> AxiomInvocation:
    """Quick axiom invocation."""
    return AxiomInvocation(name=name, module=module, instantiation=kw)

def by_z3(formula: str = "") -> Z3Proof:
    """Quick Z3 discharge."""
    return Z3Proof(formula=formula)

def by_cases(scrutinee: SynTerm | str,
             *branches: tuple[str, ProofTerm]) -> Cases:
    """Quick case analysis."""
    s = Var(scrutinee) if isinstance(scrutinee, str) else scrutinee
    return Cases(scrutinee=s, branches=list(branches))

def by_induction(on: str, base: ProofTerm, step: ProofTerm) -> NatInduction:
    """Quick nat induction."""
    return NatInduction(var=on, base_proof=base, step_proof=step)

def by_list_induction(on: str, nil: ProofTerm, cons: ProofTerm) -> ListInduction:
    """Quick list induction."""
    return ListInduction(var=on, nil_proof=nil, cons_proof=cons)

def by_ext(var: str, body: ProofTerm) -> Ext:
    """Quick function extensionality."""
    return Ext(var=var, body_proof=body)

def by_transport(family: SynTerm, path: ProofTerm, base: ProofTerm) -> TransportProof:
    """Quick transport."""
    return TransportProof(type_family=family, path_proof=path, base_proof=base)

def by_effect(effect: str, proof: ProofTerm) -> EffectWitness:
    """Quick effect witness."""
    return EffectWitness(effect=effect, proof=proof)

def by_cong(func: SynTerm | str, proof: ProofTerm) -> Cong:
    """Quick congruence."""
    f = Var(func) if isinstance(func, str) else func
    return Cong(func=f, proof=proof)

def by_unfold(func: str, then: ProofTerm | None = None) -> Unfold:
    """Quick unfold."""
    return Unfold(func_name=func, proof=then)

def by_rewrite(lemma: ProofTerm, then: ProofTerm | None = None) -> Rewrite:
    """Quick rewrite."""
    return Rewrite(lemma=lemma, proof=then)


# ═══════════════════════════════════════════════════════════════════
#  §8  Type Parsing Helper
# ═══════════════════════════════════════════════════════════════════

_TYPE_MAP: dict[str, Callable[[], SynType]] = {
    "int": PyIntType,
    "float": PyFloatType,
    "str": PyStrType,
    "bool": PyBoolType,
    "None": PyNoneType,
    "list": PyListType,
    "dict": PyDictType,
    "set": PySetType,
    "tuple": PyTupleType,
    "object": PyObjType,
    "any": PyObjType,
    "callable": lambda: PyCallableType(),
}

def _parse_type(desc: str) -> SynType:
    """Parse a type string like 'int', 'list[int]', 'Matrix'."""
    desc = desc.strip()
    base = desc.split("[")[0].lower()
    if base in _TYPE_MAP:
        return _TYPE_MAP[base]()
    return PyClassType(name=desc)


# ═══════════════════════════════════════════════════════════════════
#  §9  @verify Decorator (Run Verification at Import Time)
# ═══════════════════════════════════════════════════════════════════

_GLOBAL_KERNEL: ProofKernel | None = None

def set_global_kernel(kernel: ProofKernel) -> None:
    """Set the global kernel for @verify decorators."""
    global _GLOBAL_KERNEL
    _GLOBAL_KERNEL = kernel

def get_global_kernel() -> ProofKernel:
    """Get or create the global kernel."""
    global _GLOBAL_KERNEL
    if _GLOBAL_KERNEL is None:
        _GLOBAL_KERNEL = ProofKernel()
    return _GLOBAL_KERNEL


def verify(f_or_target=None):
    """Decorator that runs verification at decoration time.

    Two usage modes:

    1. Bare decorator (verifies decorated function)::

        @verify
        @guarantee("result >= 0")
        def abs_val(x: int) -> int:
            return abs(x)

    2. Sidecar target (marks as spec for an external function)::

        @verify("math_utils.factorial")
        def factorial_spec(n: Nat) -> Pos:
            ...

    The function is usable normally; verification results are stored
    in f._deppy_verification.
    """
    def _do_verify(f):
        spec = _get_spec(f)
        kernel = get_global_kernel()

        results: list[VerificationResult] = []
        for g in spec.guarantees:
            result = (
                Proof(g)
                .using(kernel)
                .by_structural(f"auto-verify: {g}")
                .qed()
            )
            results.append(result)

        try:
            f._deppy_verification = results  # type: ignore[attr-defined]
        except (AttributeError, TypeError):
            pass
        return f

    # @verify("module.func") — called with a string target
    if isinstance(f_or_target, str):
        target = f_or_target
        def decorator(f):
            try:
                f._deppy_verify_target = target
            except (AttributeError, TypeError):
                pass
            return _do_verify(f)
            return _do_verify(f)
        return decorator

    # @verify — bare decorator (f_or_target is the function itself)
    if callable(f_or_target):
        return _do_verify(f_or_target)

    # @verify() — called with no args
    return _do_verify


# ═══════════════════════════════════════════════════════════════════
#  §10  given() for Domain Knowledge Import
# ═══════════════════════════════════════════════════════════════════

@dataclass
class DomainKnowledge:
    """A piece of domain knowledge imported into the proof context.

    Usage::

        physics = given("Newton's second law: F = m * a")
        # Now available in proofs as an assumption
    """
    statement: str
    source: str = ""
    trust_level: str = "DOMAIN_ASSUMED"

    def as_assumption(self, name: str = "domain_knowledge") -> Assume:
        return Assume(name=name)

    def as_axiom(self, name: str = "", module: str = "domain") -> AxiomInvocation:
        n = name or self.statement[:30].replace(" ", "_")
        return AxiomInvocation(name=n, module=module)


def given(statement: str, source: str = "") -> DomainKnowledge:
    """Import domain knowledge as a proof assumption.

    Usage::

        euler = given("e^(iπ) + 1 = 0", source="Euler's formula")
        sorting_lower_bound = given("comparison sorting is Ω(n log n)")
    """
    return DomainKnowledge(statement=statement, source=source)


# ═══════════════════════════════════════════════════════════════════
#  §11  Quick Spec Extraction
# ═══════════════════════════════════════════════════════════════════

def extract_spec(f: Callable) -> FunctionSpec | None:
    """Extract the Deppy spec from a decorated function.

    Returns None if no spec decorators have been applied.
    """
    if not hasattr(f, "_deppy_spec"):
        return None
    meta: _SpecMetadata = f._deppy_spec
    if not meta.guarantees and not meta.preconditions and not meta.postconditions:
        return None

    sig = inspect.signature(f)
    params = []
    for pname, param in sig.parameters.items():
        ann = param.annotation
        if ann is inspect.Parameter.empty:
            ty = PyObjType()
        elif isinstance(ann, str):
            ty = _parse_type(ann)
        elif isinstance(ann, SynType):
            ty = ann
        else:
            ty = _parse_type(ann.__name__ if hasattr(ann, "__name__") else str(ann))
        params.append((pname, ty))

    from deppy.core.types import Spec, SpecKind
    guarantees = [
        Spec(kind=SpecKind.GUARANTEE, description=g)
        for g in meta.guarantees
    ] + [
        Spec(kind=SpecKind.GUARANTEE, description=str(p))
        for p in meta.postconditions
    ]
    assumptions = [
        Spec(kind=SpecKind.ASSUME, description=str(p))
        for p in meta.preconditions
    ]
    return FunctionSpec(
        name=f.__name__,
        params=params,
        return_type=PyObjType(),
        guarantees=guarantees,
        assumptions=assumptions,
        effect=meta.effect,
    )


# ═══════════════════════════════════════════════════════════════════
#  §12  Path Proof Combinators
# ═══════════════════════════════════════════════════════════════════

def path(a: str, b: str, via: str = "refl") -> ProofTerm:
    """Construct a path between two terms.

    Usage::

        p = path("sort_v1(xs)", "sort_v2(xs)", via="behavioral_equiv")

    If *via* is ``"refl"`` the path is reflexivity (a must equal b).
    Otherwise a :class:`Structural` justification carrying *via* is
    used as the inner evidence.  The result is a genuine
    :class:`PathComp` / :class:`Refl` proof term, not a
    ``Structural`` wrapper.
    """
    left = Var(a)
    right = Var(b)
    if via == "refl":
        return Refl(term=left)
    return PathComp(
        left_path=Refl(term=left),
        right_path=Structural(description=f"path({a}, {b}): {via}"),
    )


def transport_proof(type_family_or_path, path_proof: ProofTerm | None = None,
                    base_proof: ProofTerm | None = None) -> ProofTerm:
    """Transport a proof along a path.

    Supports two calling conventions:

    1. **Explicit** (proof-term construction)::

        p = transport_proof("is_sorted",
                            path("sort_v1", "sort_v2"),
                            by_z3("sort_v1(xs) is sorted"))

    2. **Decorator** (book-friendly)::

        @transport(evaluate)
        def det_product_numerical(...): ...

    In decorator mode *type_family_or_path* is a callable (the path
    function), and the result is a decorator that annotates *fn*.
    """
    # Decorator mode: @transport(path_fn) → decorator
    if callable(type_family_or_path) and path_proof is None and base_proof is None:
        path_fn = type_family_or_path

        def _decorator(fn):
            fn._deppy_transport = path_fn
            fn._deppy_proof = Structural(
                description=f"transport({getattr(path_fn, '__name__', '?')})"
            )
            return fn

        return _decorator  # type: ignore[return-value]

    # Original mode: transport_proof(family, path, base)
    type_family: str = type_family_or_path  # type: ignore[assignment]
    family = Var(type_family) if type_family != "auto" else Var("_P")
    return TransportProof(
        type_family=family,
        path_proof=path_proof,
        base_proof=base_proof,
    )


def ap_f(f: str, path_proof: ProofTerm) -> ProofTerm:
    """Apply a function to a path: if a = b then f(a) = f(b).

    Produces a genuine :class:`Ap` proof term.

    Usage::

        p = path("x", "y")           # x = y
        q = ap_f("len", p)           # len(x) = len(y)
    """
    return Ap(function=Var(f), path_proof=path_proof)


def funext(var: str, pointwise: ProofTerm) -> ProofTerm:
    """Function extensionality: ∀x. f(x) = g(x)  →  f = g.

    Produces a genuine :class:`FunExt` proof term.

    Usage::

        p = funext("x", by_z3("f(x) == g(x) for all int x"))
    """
    return FunExt(var=var, pointwise_proof=pointwise)


def path_chain(*steps: tuple[str, ProofTerm]) -> ProofTerm:
    """Chain of equalities via path composition.

    Each *step* is ``(label, proof_of_prev_eq_label)``.  The first
    label names the starting point; subsequent proofs justify each
    link.

    Produces nested :class:`PathComp` terms.

    Usage::

        p = path_chain(
            ("a", by_z3("a == b")),     # a = b
            ("b", by_axiom(...)),        # b = c
            ("c", by_structural(...)),   # c = d
        )
        # Result: a = d via composition
    """
    if len(steps) == 0:
        return Refl(term=Var("_"))
    if len(steps) == 1:
        return steps[0][1]
    result = steps[0][1]
    for _label, proof in steps[1:]:
        result = PathComp(left_path=result, right_path=proof)
    return result


# ═══════════════════════════════════════════════════════════════════
#  §13  Transport Sugar
# ═══════════════════════════════════════════════════════════════════

class TransportChain:
    """Chain of transports for moving proofs across equivalences.

    Usage::

        result = (transport_from(proved_about_v1)
                    .along(path("v1", "v2"))
                    .via_refactoring("for loop", "list comp")
                    .result())
    """

    def __init__(self, base_proof: ProofTerm):
        self._proof = base_proof
        self._steps: list[tuple[str, ProofTerm]] = []

    def along(self, path_pf: ProofTerm,
              type_family: str = "auto") -> TransportChain:
        """Transport along a path."""
        family = Var(type_family) if type_family != "auto" else Var("_P")
        self._proof = TransportProof(
            type_family=family,
            path_proof=path_pf,
            base_proof=self._proof,
        )
        self._steps.append(("along", path_pf))
        return self

    def via_refactoring(self, before: str, after: str) -> TransportChain:
        """Transport via a code-refactoring equivalence.

        Constructs a path ``before = after`` justified by a
        :class:`Structural` witness, then transports along it.
        """
        refactor_path = PathComp(
            left_path=Refl(term=Var(before)),
            right_path=Structural(description=f"refactoring: {before} → {after}"),
        )
        self._proof = TransportProof(
            type_family=Var("_P"),
            path_proof=refactor_path,
            base_proof=self._proof,
        )
        self._steps.append(("refactoring", refactor_path))
        return self

    def via_duck_type(self, from_type: str, to_type: str,
                      methods: list[str]) -> TransportChain:
        """Transport via duck-type protocol equivalence.

        Builds a :class:`DuckPath` from *from_type* to *to_type*
        with :class:`Structural` method proofs, then transports.
        """
        duck = DuckPath(
            type_a=PyClassType(name=from_type),
            type_b=PyClassType(name=to_type),
            method_proofs=[
                (m, Structural(description=f"{from_type}.{m} ≡ {to_type}.{m}"))
                for m in methods
            ],
        )
        univ = Univalence(
            equiv_proof=duck,
            from_type=PyClassType(name=from_type),
            to_type=PyClassType(name=to_type),
        )
        self._proof = TransportProof(
            type_family=Var("_P"),
            path_proof=univ,
            base_proof=self._proof,
        )
        self._steps.append(("duck_type", univ))
        return self

    def via_library_update(self, old_ver: str,
                           new_ver: str) -> TransportChain:
        """Transport via library-version equivalence.

        Constructs a path ``old_ver = new_ver`` and transports.
        """
        ver_path = PathComp(
            left_path=Refl(term=Var(old_ver)),
            right_path=Structural(
                description=f"library update: {old_ver} → {new_ver}",
            ),
        )
        self._proof = TransportProof(
            type_family=Var("_P"),
            path_proof=ver_path,
            base_proof=self._proof,
        )
        self._steps.append(("library_update", ver_path))
        return self

    def result(self) -> ProofTerm:
        """Get the final transported proof term."""
        return self._proof


def transport_from(base_proof: ProofTerm) -> TransportChain:
    """Start a transport chain.

    Usage::

        result = (transport_from(proved_about_v1)
                    .along(path("v1", "v2"))
                    .via_refactoring("for loop", "list comp")
                    .result())
    """
    return TransportChain(base_proof)


# ═══════════════════════════════════════════════════════════════════
#  §14  Čech Decomposition Sugar
# ═══════════════════════════════════════════════════════════════════

class CechProof:
    """Prove by decomposing into patches and gluing.

    Usage::

        proof = (CechProof("abs(x) >= 0")
                    .patch("x >= 0", by_z3("x >= 0 implies x >= 0"))
                    .patch("x < 0", by_z3("x < 0 implies -x > 0"))
                    .overlap(0, 1, by_z3("x >= 0 and x < 0 is empty"))
                    .glue())
    """

    def __init__(self, goal: str):
        self._goal = goal
        self._patches: list[tuple[str, ProofTerm]] = []
        self._overlaps: list[tuple[int, int, ProofTerm]] = []

    def patch(self, condition: str, proof: ProofTerm) -> CechProof:
        """Add a local proof for a region of the input space."""
        self._patches.append((condition, proof))
        return self

    def overlap(self, i: int, j: int, proof: ProofTerm) -> CechProof:
        """Prove agreement on the overlap of patches *i* and *j*."""
        self._overlaps.append((i, j, proof))
        return self

    def glue(self) -> ProofTerm:
        """Glue local proofs into a global proof.

        Produces a genuine :class:`CechGlue` proof term.
        """
        return CechGlue(
            patches=list(self._patches),
            overlap_proofs=list(self._overlaps),
        )


def by_cech_proof(*patches: tuple[str, ProofTerm],
                  overlaps: list[tuple[int, int, ProofTerm]] | None = None,
                  ) -> ProofTerm:
    """Quick Čech proof.

    Produces a genuine :class:`CechGlue` proof term.

    Usage::

        p = by_cech_proof(
            ("x > 0", by_z3("x > 0 implies abs(x) = x >= 0")),
            ("x == 0", by_z3("abs(0) = 0 >= 0")),
            ("x < 0", by_z3("x < 0 implies abs(x) = -x > 0")),
        )
    """
    return CechGlue(
        patches=list(patches),
        overlap_proofs=list(overlaps or []),
    )


# ═══════════════════════════════════════════════════════════════════
#  §15  Fibration Sugar
# ═══════════════════════════════════════════════════════════════════

def by_fiber_proof(scrutinee: str,
                   branches: dict[str, ProofTerm]) -> ProofTerm:
    """Prove by verifying on each fiber of a type dispatch.

    Produces a genuine :class:`Fiber` proof term.

    Usage::

        p = by_fiber_proof("x", {
            "int":   by_z3("str(x) is a string for int x"),
            "float": by_z3("f'{x:.2f}' is a string for float x"),
            "str":   by_structural("x is already a string"),
        })
    """
    type_branches = [
        (_parse_type(type_name), proof)
        for type_name, proof in branches.items()
    ]
    return Fiber(
        scrutinee=Var(scrutinee),
        type_branches=type_branches,
        exhaustive=True,
    )


def by_duck_type(type_a: str, type_b: str,
                 methods: dict[str, ProofTerm]) -> ProofTerm:
    """Prove types are equivalent via duck-type protocol.

    Produces a genuine :class:`DuckPath` proof term.

    Usage::

        p = by_duck_type("MyList", "list", {
            "__len__":     by_structural("same length semantics"),
            "__getitem__": by_structural("same indexing"),
            "__iter__":    by_structural("same iteration"),
        })
    """
    return DuckPath(
        type_a=PyClassType(name=type_a),
        type_b=PyClassType(name=type_b),
        method_proofs=list(methods.items()),
    )


# ═══════════════════════════════════════════════════════════════════
#  §16  Path Equivalence & Refactoring Decorators
# ═══════════════════════════════════════════════════════════════════

# Registry for path-equivalence relationships.
_PATH_EQUIV_REGISTRY: dict[str, list[tuple[Callable, ProofTerm]]] = {}


def path_equivalent(target: Callable) -> Callable[[F], F]:
    """Declare that the decorated function is path-equivalent to *target*.

    Proofs about *target* transport to the decorated function
    automatically via a :class:`TransportProof`.

    Usage::

        @path_equivalent(sorted)
        def my_sort(xs):
            '''Custom sort proved equivalent to sorted()'''
            ...
    """
    def decorator(f: F) -> F:
        tgt_name = getattr(target, "__name__", str(target))
        fn_name = getattr(f, "__name__", str(f))
        equiv_path = PathComp(
            left_path=Refl(term=Var(tgt_name)),
            right_path=Structural(
                description=f"path_equivalent: {fn_name} ≡ {tgt_name}",
            ),
        )
        _PATH_EQUIV_REGISTRY.setdefault(tgt_name, []).append((f, equiv_path))
        f._deppy_path_equiv = {  # type: ignore[attr-defined]
            "target": target,
            "target_name": tgt_name,
            "path": equiv_path,
        }
        return f
    return decorator


def refactoring(original: Callable) -> Callable[[F], F]:
    """Mark the decorated function as a verified refactoring of *original*.

    Proofs about *original* transport to the new function via a
    :class:`TransportProof`.

    Usage::

        @refactoring(naive_matrix_mul)
        @guarantee("same result as naive_matrix_mul")
        def strassen_mul(A, B):
            ...
    """
    def decorator(f: F) -> F:
        orig_name = getattr(original, "__name__", str(original))
        fn_name = getattr(f, "__name__", str(f))
        refactor_path = PathComp(
            left_path=Refl(term=Var(orig_name)),
            right_path=Structural(
                description=f"refactoring: {orig_name} → {fn_name}",
            ),
        )
        _PATH_EQUIV_REGISTRY.setdefault(orig_name, []).append(
            (f, refactor_path),
        )
        f._deppy_refactoring = {  # type: ignore[attr-defined]
            "original": original,
            "original_name": orig_name,
            "path": refactor_path,
        }
        return f
    return decorator


def get_path_equivalences(target: Callable) -> list[tuple[Callable, ProofTerm]]:
    """Return all functions registered as path-equivalent to *target*."""
    tgt_name = getattr(target, "__name__", str(target))
    return list(_PATH_EQUIV_REGISTRY.get(tgt_name, []))

__all__ = [
    # Decorators
    "guarantee", "requires", "ensures", "pure", "reads", "mutates",
    "total", "partial_fn", "invariant", "decreases", "verify",
    # Refinement types
    "Pos", "Nat", "NonEmpty", "Bounded", "NonNull", "Sorted",
    "SizedExact", "Refine",
    # Library trust
    "library_trust", "LibraryTrustBlock",
    # Proof builders
    "Proof", "FormalProof", "ProofContext",
    # Quick combinators
    "refl", "sym", "trans", "by_axiom", "by_z3", "by_cases",
    "by_induction", "by_list_induction", "by_ext", "by_transport",
    "by_effect", "by_cong", "by_unfold", "by_rewrite",
    # Domain knowledge
    "given", "DomainKnowledge",
    # Spec extraction
    "extract_spec",
    # Kernel management
    "set_global_kernel", "get_global_kernel",
    # §12 Path proof combinators
    "path", "transport_proof", "ap_f", "funext", "path_chain",
    # §13 Transport sugar
    "TransportChain", "transport_from",
    # §14 Čech decomposition sugar
    "CechProof", "by_cech_proof",
    # §15 Fibration sugar
    "by_fiber_proof", "by_duck_type",
    # §16 Path equivalence & refactoring decorators
    "path_equivalent", "refactoring", "get_path_equivalences",
]
