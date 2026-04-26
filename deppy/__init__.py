"""
Deppy — Python with Dependent Types

A formal verification system for Python based on cubical homotopy type theory.
"""
from __future__ import annotations

__version__ = "0.1.0"

# ── Public API re-exports ──
# These make ``from deppy import guarantee`` (etc.) work as shown in the
# Deppy tutorial book.  Everything delegates to internal modules.

from deppy.proofs.sugar import (          # noqa: F401  — decorators & DSL
    guarantee, requires, ensures, verify, pure, total,
    decreases, invariant, reads, mutates,
    given, library_trust,
    Proof, ProofBuilder, ProofContext,
    Nat, Pos, NonEmpty, NonNull, Sorted, Bounded, SizedExact,
    refl, sym, trans, path, path_chain, funext,
    transport_proof, transport_from, path_equivalent,
    by_z3, by_axiom, by_cases, by_induction, by_transport,
    by_cech_proof, by_fiber_proof, by_duck_type, by_ext,
    by_list_induction, by_cong, by_rewrite, by_unfold, by_effect,
    formal_check, formal_eq, extract_spec,
    Spec, SpecKind, DomainKnowledge,
    FormalProof, FunctionSpec,
    _get_spec,
)
from deppy.proofs.sugar import Refine as refined          # noqa: F401
from deppy.proofs.sugar import Refine                     # noqa: F401

from deppy.core.kernel import (           # noqa: F401  — proof terms
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, Cut, Assume, Z3Proof, LeanProof,
    NatInduction, ListInduction, Cases, DuckPath,
    ConditionalDuckPath, FiberedLookup,
    EffectWitness, AxiomInvocation, Ext, Unfold, Rewrite,
    Structural, TransportProof, PathComp, Ap, FunExt,
    CechGlue, Univalence, Fiber, Patch,
)

# Convenience aliases used in book examples
assume = requires          # F*-style name
check = invariant          # F*-style name
preserves_spec = guarantee # alias
transforms_spec = guarantee
implements = guarantee
def protocol_spec(cls_or_str=None):
    """Mark a ``typing.Protocol`` class as a Deppy specification.

    Use either form::

        @protocol_spec
        class Renderable(Protocol):
            def render(self) -> str: ...

        @protocol_spec("things that can render to a string")
        class Renderable(Protocol):
            def render(self) -> str: ...

    Verification semantics
    ----------------------
    When a class ``C`` is later checked against ``Renderable`` (e.g.
    via :func:`deppy.check_adherence` or by passing an instance to a
    function annotated ``r: Renderable``), Deppy constructs a real
    :class:`deppy.core.kernel.DuckPath` proof term whose method
    witnesses are the protocol's declared abstract methods.  That
    proof term is what gets fed to the kernel — not just metadata.

    This decorator records:

    * ``cls._deppy_protocol_spec = True`` so downstream tools know
      to treat ``cls`` as a structural-typing spec, not a nominal
      base class;
    * the protocol's declared method *names* on
      ``cls._deppy_protocol_methods`` for fast DuckPath construction;
    * an optional human-readable ``cls._deppy_protocol_description``.
    """
    def _attach(proto_cls, description: str | None) -> type:
        # Collect method names declared on the protocol body (skip
        # dunders other than the iterator/container ones we always
        # treat as user-facing).
        permitted_dunders = {
            "__iter__", "__next__", "__len__", "__getitem__",
            "__setitem__", "__contains__", "__enter__", "__exit__",
            "__call__", "__eq__", "__hash__",
        }
        methods: list[str] = []
        for name in proto_cls.__dict__:
            if name.startswith("_") and name not in permitted_dunders:
                continue
            attr = proto_cls.__dict__[name]
            if callable(attr):
                methods.append(name)
        proto_cls._deppy_protocol_spec = True  # type: ignore[attr-defined]
        proto_cls._deppy_protocol_methods = tuple(methods)  # type: ignore[attr-defined]
        if description:
            proto_cls._deppy_protocol_description = description  # type: ignore[attr-defined]
        # Still attach _SpecMetadata so guarantee()-style tooling
        # can find the protocol if a description was supplied.
        if description:
            _get_spec(proto_cls).guarantees.append(description)
        return proto_cls

    if isinstance(cls_or_str, str):
        description = cls_or_str
        def decorator(cls):
            return _attach(cls, description)
        return decorator
    if isinstance(cls_or_str, type):
        return _attach(cls_or_str, None)
    if cls_or_str is None:
        def decorator2(cls):
            return _attach(cls, None)
        return decorator2
    return cls_or_str
from deppy.lean.compiler import compile_to_lean  # noqa: F401
from deppy.lean.obligations import (  # noqa: F401
    Obligation, ObligationReport, emit_obligations,
)
from deppy.lean.certificate import (  # noqa: F401
    Certificate, CertificateReport, write_certificate,
)

loop_variant = decreases
fuel = decreases
may_diverge = total        # marks intent (opposite semantics — placeholder)
Perm = Trans               # permutation path (alias for book examples)

def uses(*deps):
    """Declare that a lemma or proof uses other lemmas/theorems."""
    def decorator(fn):
        fn._deppy_uses = deps
        return fn
    return decorator

def induction(target):
    """Decorator marking a proof as proceeding by induction on `target`."""
    def decorator(fn):
        fn._deppy_induction_target = target
        return fn
    return decorator

def lemma(fn):
    """Decorator marking a function as a lemma (returns a proof term)."""
    fn._deppy_lemma = True
    return fn


def implies(
    precondition: str,
    postcondition: str,
    *,
    proof: str = "",
    imports: tuple[str, ...] = (),
):
    """Declare an implication property: whenever ``precondition``
    holds at function entry, ``postcondition`` holds at exit (with
    ``result`` bound to the return value).

    Example::

        @implies("x > 0", "result > 0")
        def f(x):
            return x + 1

        @implies("len(xs) > 0", "result is not None")
        def first(xs):
            return xs[0] if xs else None

    The decorator records the property on the function as
    ``fn._deppy_implies``.  The pipeline then:

    1. **Tries to discharge automatically** — for arithmetic-only
       implications it asks Z3 to prove ``precondition ⇒
       postcondition[result := body]``.
    2. **Emits a Lean theorem** in the certificate when Z3 cannot
       discharge the implication.  The certificate's theorem
       statement is generated automatically from the decorator
       arguments and the function's translated body; the proof body
       defaults to ``Deppy.deppy_safe`` (which tries the standard
       automation tactics) and falls back to ``sorry`` only when
       neither tactic nor user-supplied proof is available.
    3. **Accepts a user-supplied proof** via the ``proof=`` keyword:
       a Lean tactic body that closes the implication.  Multiple
       ``@implies`` can stack on a single function.

    The Python-side ``result`` identifier in the postcondition refers
    to the function's return value.  Lean translates it to ``result``
    (a fresh binder bound to the function's body in the theorem).
    """
    def decorator(fn):
        existing = getattr(fn, "_deppy_implies", None)
        if existing is None:
            existing = []
        existing.append({
            "precondition": precondition,
            "postcondition": postcondition,
            "proof": proof,
            "imports": tuple(imports or ()),
        })
        fn._deppy_implies = existing
        return fn
    return decorator


def with_lean_proof(
    *,
    theorem: str,
    proof: str = "",
    for_kind: str = "*",
    imports: tuple[str, ...] = (),
):
    """Attach a Lean 4 proof script that discharges a runtime-safety obligation.

    Use this when the deppy pipeline cannot discharge a particular
    exception source via Z3, the syntactic shortcut, or the builtin
    sidecar — typically because the property requires reasoning Z3
    can't do (induction, list/dict properties, abstract algebra).

    Example::

        @with_lean_proof(
            theorem='''theorem div_safe
                (a b : Int) (h : b ≠ 0) : b ≠ 0''',
            proof="exact h",
            for_kind="ZERO_DIVISION",
        )
        def divide(a, b):
            return a / b

    Parameters
    ----------
    theorem : str
        The Lean theorem statement (single ``theorem ... :
        T_goal`` line, no body).  The kernel appends ``:= by`` and
        the proof script when invoking Lean.  If you write a fully
        self-contained statement that ends in ``:= proof_term``,
        leave ``proof`` empty.
    proof : str
        The proof script body — typically a ``by ...`` block, e.g.
        ``"exact h"`` or ``"omega"`` or a multi-line tactic block.
    for_kind : str
        Which exception kind this proof discharges.  Defaults to
        ``"*"`` (all kinds).  Specific kinds like
        ``"ZERO_DIVISION"`` / ``"KEY_ERROR"`` / ``"INDEX_ERROR"`` /
        ``"VALUE_ERROR"`` make the discharge precise.
    imports : tuple[str, ...]
        Extra Lean ``import`` lines prepended to the file (e.g.
        ``("import Mathlib.Data.List.Basic",)``).

    The decorator is read by :func:`verify_module_safety` (and by the
    CLI's ``deppy check``).  Multiple decorators stack — apply one
    decorator per source kind you need to discharge.
    """
    def decorator(fn):
        existing = getattr(fn, "_deppy_lean_proofs", None)
        if existing is None:
            existing = []
        existing.append((for_kind, theorem, proof, tuple(imports)))
        fn._deppy_lean_proofs = existing
        return fn
    return decorator

def trust_boundary(
    fn=None,
    *,
    args=None,
    kwargs=None,
    expected_return=None,
    expected_properties=None,
):
    """Boundary between verified and unverified code.

    Two forms (matches the deppy book — ``part3/dynamic.html``):

    Decorator form::

        @trust_boundary
        def call_legacy(...):
            ...

        # marks ``call_legacy`` as the seam between verified and
        # untyped code; equivalence proofs that cross this boundary
        # are tagged ``UNTRUSTED`` until upgraded.

    Callable form (runtime check)::

        result = trust_boundary(
            legacy_compute,
            args=(values, scale),
            expected_return=list,           # or list[float], typing.get_origin handled
            expected_properties=[
                "len(result) == len(values)",
                "all(isinstance(x, float) for x in result)",
            ],
        )

    The callable form *invokes* ``fn`` with ``args`` / ``kwargs``,
    then validates:

    1. ``isinstance(result, expected_return_origin)`` — uses
       :func:`typing.get_origin` so generics like ``list[float]``
       reduce to a runtime-checkable origin.
    2. Each ``expected_properties`` entry, evaluated as a Python
       expression in a context with ``result``, the input args (by
       parameter name when introspectable), and the standard
       builtins.  Properties that pass at runtime become evidence
       attached to the returned value via ``__deppy_trust_evidence__``;
       a property that fails raises :class:`ValueError`.

    Returns the call result on success; raises ``ValueError`` /
    ``TypeError`` on failure so calling code can decide whether to
    fall through to an alternate path.
    """
    if fn is None or callable(fn) and args is None and kwargs is None \
            and expected_return is None and expected_properties is None:
        # Decorator form: @trust_boundary or @trust_boundary().
        if fn is None:
            def _decorator(real_fn):
                real_fn._deppy_trust_boundary = True
                return real_fn
            return _decorator
        fn._deppy_trust_boundary = True
        return fn

    # Callable form: actually invoke and validate.
    import typing as _typing

    call_args = tuple(args or ())
    call_kwargs = dict(kwargs or {})
    result = fn(*call_args, **call_kwargs)

    # 1. Return type check.
    if expected_return is not None:
        origin = _typing.get_origin(expected_return) or expected_return
        if isinstance(origin, type) and not isinstance(result, origin):
            raise TypeError(
                f"trust_boundary: {getattr(fn, '__name__', fn)!r} returned "
                f"{type(result).__name__}, expected {expected_return!r}"
            )

    # 2. Property checks.
    evidence: list[str] = []
    if expected_properties:
        import inspect
        eval_ctx: dict = {"result": result}
        try:
            sig = inspect.signature(fn)
            bound = sig.bind_partial(*call_args, **call_kwargs)
            bound.apply_defaults()
            eval_ctx.update(bound.arguments)
        except (TypeError, ValueError):
            for i, val in enumerate(call_args):
                eval_ctx[f"arg{i}"] = val
            eval_ctx.update(call_kwargs)
        for prop in expected_properties:
            try:
                ok = bool(eval(prop, {"__builtins__": __builtins__}, eval_ctx))
            except Exception as e:
                raise ValueError(
                    f"trust_boundary: property {prop!r} raised "
                    f"{type(e).__name__}: {e}"
                )
            if not ok:
                raise ValueError(
                    f"trust_boundary: property {prop!r} did not hold for "
                    f"result={result!r}"
                )
            evidence.append(prop)

    # Try to attach evidence.  Fails silently for immutable types.
    try:
        result.__deppy_trust_evidence__ = tuple(evidence)  # type: ignore[attr-defined]
    except (AttributeError, TypeError):
        pass

    return result

from deppy.equivalence import (  # noqa: F401,E402
    check_equiv, check_inequiv, check_adherence,
    check_spec_equiv, equiv_to_lean,
    EquivResult, EquivMethod, AdherenceResult, SpecEquivResult,
    verify_module, verify_composition, check_module_paths,
    analyze_effects, analyze_call_chain_effects,
    analyze_shared_state, verify_concurrent_safety,
    build_import_graph, verify_import_graph,
    CompositionResult, ModulePathResult, EffectReport,
    SharedStateWarning, ConcurrencyResult, ImportGraph,
)

from deppy.z3_bridge import z3_prove_real_identity  # noqa: F401,E402

# Cubical proof language + five-stage pipeline.
# Names match `deppy.proofs.*` exactly — no aliasing at the top level.
from deppy.proofs.language import (  # noqa: F401,E402
    CodeAxiom, UnfoldError, Goal, Tactic, T,
)
from deppy.proofs.pipeline import (  # noqa: F401,E402
    AxiomRegistry, axiomize,
    Tactics, ProofCertificate, prove_certificate,
    ProofScript, verify_proof_script,
    register_universal_axioms,
)


# ── User-facing HoTT helpers (book examples) ────────────────────────
def duck_path(type_a, type_b, *witnesses, protocol=None):
    """User-facing wrapper for :class:`deppy.core.kernel.DuckPath`.

    Three forms:

    * ``duck_path(A, B)`` — auto-construct from shared methods (uses
      :meth:`DuckPath.auto_construct`).
    * ``duck_path(A, B, ("method_name", proof_term), …)`` — explicit
      method-by-method witnesses.
    * ``duck_path(Protocol, val1, val2)`` — structural-typing form
      from the deppy book: the first arg is a protocol or generic
      type (e.g. ``Iterable[int]``), and the next two are concrete
      values both of which are claimed to inhabit it.  The result
      is a ``DuckPath`` between ``type(val1)`` and ``type(val2)``
      whose protocol is the supplied ``Protocol`` type.

    Returns a kernel :class:`DuckPath` proof term ready to feed to
    :meth:`ProofKernel.verify`.
    """
    from deppy.core.kernel import DuckPath as _DuckPath
    if not witnesses:
        return _DuckPath.auto_construct(type_a, type_b, protocol=protocol)

    # Structural form: duck_path(Protocol, val1, val2).  Detect it by
    # checking whether type_b is *not* a type — a value rather than a
    # class — and exactly one extra positional argument follows.
    if len(witnesses) == 1 and not isinstance(type_b, type):
        proto = type_a
        val1 = type_b
        val2 = witnesses[0]
        cls1 = type(val1)
        cls2 = type(val2)
        return _DuckPath.auto_construct(cls1, cls2, protocol=proto)

    return _DuckPath(type_a=type_a, type_b=type_b,
                     method_proofs=list(witnesses))


def cech_glue(local_proofs, overlap_proofs=None, *, name: str = ""):
    """User-facing wrapper for :class:`deppy.core.kernel.CechGlue`.

    ``local_proofs`` may be either:

    * a list of ``(condition_str, ProofTerm)`` pairs — direct form;
    * a list of bare ``ProofTerm`` objects — synthetic conditions of
      the shape ``"patch_<i>"`` are generated.

    ``overlap_proofs`` is the list of ``(i, j, agreement_proof)``
    tuples witnessing the cocycle condition; defaults to empty.
    """
    from deppy.core.kernel import CechGlue as _CechGlue
    patches: list = []
    for i, lp in enumerate(local_proofs):
        if isinstance(lp, tuple) and len(lp) == 2:
            patches.append(lp)
        else:
            patches.append((f"patch_{i}", lp))
    return _CechGlue(
        patches=patches,
        overlap_proofs=list(overlap_proofs or []),
    )

# Spec-preservation decorators (see deppy/decorators.py).
from deppy.decorators import (  # noqa: F401,E402
    preserves_spec, transforms_spec, SpecPreservationViolation,
    unwrap_decorator_stack, decorator_chain,
)

# Async verification (see deppy/async_verify.py).
from deppy.async_verify import (  # noqa: F401,E402
    async_requires, async_ensures, async_yields, async_invariant,
    terminates, pure as async_pure,
    ContractViolation, TerminationViolation,
)

# Concurrency verification (see deppy/concurrency.py).
from deppy.concurrency import (  # noqa: F401,E402
    Lock, Semaphore, Condition, AtomicCell, atomic_cas,
    spawn, join_all, parallel_safe, lock_inv,
    InvariantViolation, RaceViolation,
)

# Ghost variables (see deppy/ghost.py).
from deppy.ghost import (  # noqa: F401,E402
    Ghost, ghost_var, ghost_update, ghost_set,
    ghost_pts_to, array_pts_to, ghost_assert,
    GhostViolation,
)
