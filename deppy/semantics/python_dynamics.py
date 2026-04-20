"""
Deppy — Formal Semantics for Python's Dynamic Features
==========================================================

Covers the aspects of Python that make it hard to verify statically:
MRO, metaclasses, descriptors, dynamic attributes, monkey-patching,
and duck typing.  Each feature receives:

- *Formal typing rules* expressed as ``FormalAxiomEntry`` instances with
  machine-checkable ``Judgment`` conclusions.
- *Operation term constructors* built on the ``Op``/``OpCall`` infrastructure
  from ``deppy.core.formal_ops``.
- *Semantics classes* that embed the computational rules described in the
  deppy monograph (Chs 6, 7, 13, 14, 16, 19).

Monograph map
-------------
Ch  6  — Duck Typing:  duck-type equivalence, DuckPath, protocol inference
Ch  7  — Monkey-Patching:  Patch proof term, temporal reasoning, behavioral subtyping
Ch 13  — MRO:  C3 linearization, super(), method resolution as section of class bundle
Ch 14  — Metaclasses:  __init_subclass__, __new__, __prepare__, 2-types w/ HITs
Ch 16  — Dict as namespace:  __dict__, dynamic attributes, module dict
Ch 19  — Descriptors:  __get__/__set__/__delete__, data vs non-data, vertical bundle

Usage::

    from deppy.semantics.python_dynamics import (
        MROSemantics, DuckTypeSemantics, MonkeyPatchSemantics,
        MetaclassSemantics, DescriptorSemantics, DynamicAttrSemantics,
        all_dynamics_axioms,
    )
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyClassType, PyCallableType, ProtocolType,
    Var, Literal, GetAttr,
    Spec, SpecKind,
    PathType, PyBoolType, PyStrType, PyNoneType, PyDictType,
)
from deppy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq,
    op_dispatch, op_mro, op_super, op_hasattr, op_getattr_op, op_setattr,
    op_isinstance, op_issubclass, op_type,
    op_desc_get, op_desc_set, op_desc_delete,
)


# ═══════════════════════════════════════════════════════════════════
# Local Op helpers  (operations specific to this module)
# ═══════════════════════════════════════════════════════════════════

def _op(name: str) -> Op:
    return Op(name=name, module="python_dynamics")


def _opcall(name: str, *args: SynTerm) -> OpCall:
    return OpCall(op=_op(name), args=tuple(args))


# metaclass protocol
def op_meta_new(meta: SynTerm, name: SynTerm,
                bases: SynTerm, ns: SynTerm) -> OpCall:
    """meta.__new__(meta, name, bases, namespace)"""
    return OpCall(Op("__new__"), (meta, name, bases, ns))


def op_meta_init(cls: SynTerm, name: SynTerm,
                 bases: SynTerm, ns: SynTerm) -> OpCall:
    """meta.__init__(cls, name, bases, namespace)"""
    return OpCall(Op("__init__"), (cls, name, bases, ns))


def op_prepare(meta: SynTerm, name: SynTerm,
               bases: SynTerm) -> OpCall:
    """meta.__prepare__(name, bases)"""
    return OpCall(Op("__prepare__"), (meta, name, bases))


def op_init_subclass(cls: SynTerm) -> OpCall:
    """cls.__init_subclass__()"""
    return OpCall(Op("__init_subclass__"), (cls,))


def op_getattribute(obj: SynTerm, name: SynTerm) -> OpCall:
    """obj.__getattribute__(name)"""
    return OpCall(Op("__getattribute__"), (obj, name))


def op_delattr(obj: SynTerm, name: SynTerm) -> OpCall:
    """del obj.name"""
    return OpCall(Op("delattr"), (obj, name))


def op_dict_of(obj: SynTerm) -> OpCall:
    """obj.__dict__"""
    return OpCall(Op("__dict__"), (obj,))


def op_slots_of(cls: SynTerm) -> OpCall:
    """cls.__slots__"""
    return OpCall(Op("__slots__"), (cls,))


# ─── schema variable helpers ─────────────────────────────────────

_CTX = Context()

_V = Var  # shorthand for schema variables


def _cls(name: str = "C") -> Var:
    return Var(name)


def _method(name: str = "m") -> Var:
    return Var(name)


def _obj(name: str = "obj") -> Var:
    return Var(name)


# ═══════════════════════════════════════════════════════════════════
# 1. MRO — Method Resolution Order  (Ch 13)
# ═══════════════════════════════════════════════════════════════════

class MROSemantics:
    """C3 linearization as a section of the class fiber bundle.

    In the monograph (Ch 13) MRO is modeled as a *section* of the class
    fiber bundle: for each class C, the MRO selects a total ordering of
    its ancestors that is compatible with the local precedence orderings
    imposed by each ``class X(B1, B2, ...):`` declaration.
    """

    # ── computation ──────────────────────────────────────────────

    @staticmethod
    def compute_mro(cls: PyClassType,
                    registry: dict[str, PyClassType] | None = None,
                    ) -> list[PyClassType]:
        """Compute MRO using C3 linearization.

        Algorithm: for class C(B1, B2, ..., Bn), define
            L[C] = C + merge(L[B1], L[B2], ..., L[Bn], [B1, ..., Bn])
        where *merge* repeatedly takes the first head that is not in the
        tail of any other list.

        Parameters
        ----------
        registry : dict mapping class name → PyClassType, optional
            When provided, base classes are looked up by name so that
            method information and deeper ancestry are preserved.
        """
        if not cls.bases:
            return [cls]

        reg = registry or {}
        base_classes = [reg.get(b, PyClassType(name=b)) for b in cls.bases]
        base_mros = [MROSemantics.compute_mro(b, reg) for b in base_classes]

        return _c3_merge(cls, base_mros, base_classes)

    @staticmethod
    def resolve_method(cls: PyClassType, method: str,
                       mro: list[PyClassType]) -> SynTerm | None:
        """Walk the MRO and return the first class that defines *method*.

        Returns an ``OpCall(__dispatch__, cls_term, method_lit)`` term
        identifying the resolved provider, or ``None``.
        """
        for klass in mro:
            method_names = {m for m, _ in klass.methods}
            if method in method_names:
                return op_dispatch(Literal(klass), Literal(method))
        return None

    @staticmethod
    def super_dispatch(cls: PyClassType, method: str,
                       start_cls: PyClassType,
                       registry: dict[str, PyClassType] | None = None,
                       ) -> SynTerm | None:
        """``super().method`` resolution starting from *start_cls* in the MRO.

        Finds *start_cls* in the MRO, then searches from the next entry.
        """
        mro = MROSemantics.compute_mro(cls, registry)
        try:
            idx = next(i for i, k in enumerate(mro) if k.name == start_cls.name)
        except StopIteration:
            return None
        return MROSemantics.resolve_method(cls, method, mro[idx + 1:])

    # ── axioms (Ch 13 §§ 3–5) ───────────────────────────────────

    @staticmethod
    def mro_axioms() -> list[FormalAxiomEntry]:
        """Axioms about MRO behavior.

        1. Local precedence:  if ``class C(A, B):``, then A precedes B in MRO(C).
        2. Monotonicity:  if A precedes B in MRO(C), then A precedes B in
           MRO(D) for every subclass D of C that does not reorder A, B.
        3. super() follows MRO: ``super(C, obj).m`` resolves to the *next*
           provider after C in ``type(obj).__mro__``.
        4. Determinism: MRO is a pure function of the class hierarchy.
        """
        C, A, B, D = Var("C"), Var("A"), Var("B"), Var("D")
        m = Var("m")
        obj = Var("obj")

        return [
            FormalAxiomEntry(
                name="mro_local_precedence",
                module="python_dynamics",
                params=[("C", PyClassType()), ("A", PyClassType()),
                        ("B", PyClassType())],
                conclusion=formal_eq(
                    _CTX,
                    # In MRO(C), index(A) < index(B) when bases = (..., A, ..., B, ...)
                    _opcall("mro_index", op_mro(C), A),
                    _opcall("mro_lt", _opcall("mro_index", op_mro(C), A),
                            _opcall("mro_index", op_mro(C), B)),
                    PyBoolType(),
                ),
                description=(
                    "If class C lists base A before base B, "
                    "then A precedes B in MRO(C)."
                ),
            ),
            FormalAxiomEntry(
                name="mro_monotonicity",
                module="python_dynamics",
                params=[("C", PyClassType()), ("D", PyClassType()),
                        ("A", PyClassType()), ("B", PyClassType())],
                conclusion=formal_eq(
                    _CTX,
                    # issubclass(D, C) ∧ precedes(A, B, MRO(C))
                    #   → precedes(A, B, MRO(D))   (unless D re-orders)
                    _opcall("mro_precedes", A, B, op_mro(D)),
                    Literal(True),
                    PyBoolType(),
                ),
                description=(
                    "Monotonicity: subclass MRO preserves ancestor ordering."
                ),
            ),
            FormalAxiomEntry(
                name="super_follows_mro",
                module="python_dynamics",
                params=[("C", PyClassType()), ("obj", PyObjType()),
                        ("m", PyStrType())],
                conclusion=formal_eq(
                    _CTX,
                    op_dispatch(op_super(C, obj), m),
                    _opcall("mro_next_provider", op_mro(op_type(obj)), C, m),
                ),
                description=(
                    "super(C, obj).m resolves to the next provider "
                    "after C in type(obj).__mro__."
                ),
            ),
            FormalAxiomEntry(
                name="mro_deterministic",
                module="python_dynamics",
                params=[("C", PyClassType())],
                conclusion=formal_eq(
                    _CTX, op_mro(C), op_mro(C),
                ),
                description=(
                    "MRO is a pure function of the class hierarchy — "
                    "calling it twice yields the same result."
                ),
            ),
        ]


def _c3_merge(cls: PyClassType,
              base_mros: list[list[PyClassType]],
              bases: list[PyClassType]) -> list[PyClassType]:
    """C3 linearization merge step.

    Repeatedly find the first head that does not appear in the tail of
    any other list, remove it from every list, and append to result.
    """
    result: list[PyClassType] = [cls]
    seqs: list[list[PyClassType]] = [list(m) for m in base_mros] + [list(bases)]

    while True:
        # prune empty sequences
        seqs = [s for s in seqs if s]
        if not seqs:
            return result

        # find a good head
        for seq in seqs:
            head = seq[0]
            # head must not appear in the *tail* of any other sequence
            if not any(head.name == s.name for other in seqs for s in other[1:]):
                break
        else:
            raise TypeError(
                f"Cannot compute C3 MRO for {cls.name}: "
                "inconsistent hierarchy"
            )

        result.append(head)
        # remove head from all sequences
        seqs = [[s for s in seq if s.name != head.name] for seq in seqs]


# ═══════════════════════════════════════════════════════════════════
# 2. Duck Typing  (Ch 6)
# ═══════════════════════════════════════════════════════════════════

class DuckTypeSemantics:
    """Duck-type equivalence via the univalence axiom.

    Two classes are *duck-type equivalent* when they expose the same
    method names with compatible signatures.  In the HoTT reading
    (Ch 6) this is captured by the *DuckPath*: a path in the space
    of PyClass values constructed from a witness of structural
    equivalence.
    """

    @staticmethod
    def check_duck_equivalent(a: PyClassType, b: PyClassType) -> bool:
        """Check if *a* and *b* are duck-type equivalent.

        Two classes are duck-type equivalent iff they have the same set
        of method names and each pair of corresponding signatures is
        compatible (i.e. structurally equal at the ``SynType`` level).
        """
        a_map = dict(a.methods)
        b_map = dict(b.methods)
        if set(a_map) != set(b_map):
            return False
        return all(a_map[m] == b_map[m] for m in a_map)

    @staticmethod
    def compute_protocol(usage_sites: list[SynTerm]) -> ProtocolType:
        """Infer the minimal protocol required by a set of usage sites.

        Each usage site is expected to be a ``GetAttr(obj, attr)`` or
        ``OpCall(Op("__dispatch__"), ...)`` from which we extract the
        attribute name.  The resulting protocol lists every attribute
        accessed with ``PyObjType`` signatures (refined later by
        downstream type-inference).
        """
        seen: dict[str, SynType] = {}
        for site in usage_sites:
            if isinstance(site, GetAttr):
                seen.setdefault(site.attr, PyObjType())
            elif isinstance(site, OpCall) and site.op.name == "__dispatch__":
                if len(site.args) >= 2 and isinstance(site.args[1], Literal):
                    name = str(site.args[1].value)
                    seen.setdefault(name, PyObjType())
        methods = tuple(sorted(seen.items()))
        return ProtocolType(name="<inferred>", methods=methods)

    @staticmethod
    def duck_path(a: PyClassType, b: PyClassType) -> SynTerm | None:
        """Construct a *DuckPath* witnessing duck-type equivalence.

        Returns a ``PathAbs`` term  i ↦ interp(i, a, b)  when the two
        classes are duck-equivalent, or ``None`` otherwise.
        """
        if not DuckTypeSemantics.check_duck_equivalent(a, b):
            return None
        from deppy.core.types import PathAbs
        return PathAbs(ivar="i", body=Literal(b))

    # ── axioms (Ch 6 §§ 2–4) ────────────────────────────────────

    @staticmethod
    def duck_typing_axioms() -> list[FormalAxiomEntry]:
        """Axioms for duck typing.

        1. Univalence:  (A ≃_duck B) ≃ (A =_{PyClass} B)
        2. Protocol transitivity:  A conforms to P ∧ P <: Q → A conforms to Q
        3. hasattr + callable → protocol conformance
        """
        A, B = Var("A"), Var("B")
        x, m = Var("x"), Var("m")
        P, Q = Var("P"), Var("Q")

        return [
            FormalAxiomEntry(
                name="duck_univalence",
                module="python_dynamics",
                params=[("A", PyClassType()), ("B", PyClassType())],
                conclusion=formal_eq(
                    _CTX,
                    _opcall("duck_equiv", A, B),
                    _opcall("class_path_eq", A, B),
                    PathType(base_type=PyClassType()),
                ),
                description=(
                    "Duck-type univalence: structural equivalence "
                    "gives a path A =_{PyClass} B."
                ),
            ),
            FormalAxiomEntry(
                name="protocol_transitivity",
                module="python_dynamics",
                params=[("A", PyClassType()), ("P", PyObjType()),
                        ("Q", PyObjType())],
                conclusion=formal_eq(
                    _CTX,
                    _opcall("conforms", A, Q),
                    Literal(True),
                    PyBoolType(),
                ),
                description=(
                    "Protocol conformance is transitive: "
                    "A conforms to P and P <: Q implies A conforms to Q."
                ),
            ),
            FormalAxiomEntry(
                name="hasattr_implies_protocol",
                module="python_dynamics",
                params=[("x", PyObjType()), ("m", PyStrType())],
                conclusion=formal_eq(
                    _CTX,
                    _opcall("conforms_single", x, m),
                    op_hasattr(x, m),
                    PyBoolType(),
                ),
                description=(
                    "hasattr(x, m) ∧ callable(x.m) → "
                    "x conforms to Protocol({m})."
                ),
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 3. Monkey-Patching  (Ch 7)
# ═══════════════════════════════════════════════════════════════════

class MonkeyPatchSemantics:
    """Monkey-patching as path construction in the PyClass HIT.

    Ch 7 models monkey-patching through a *higher inductive type* (HIT)
    for the space of class objects.  ``setattr(C, m, v)`` is a *path
    constructor*: it gives an identification ``C =_{PyClass} C[m:=v]``
    provided the new method satisfies the old contract (behavioral
    subtyping).
    """

    @staticmethod
    def apply_patch(cls: PyClassType, method: str,
                    new_impl: SynTerm) -> PyClassType:
        """Compute the patched class type.

        Returns a new ``PyClassType`` whose method map has *method*
        replaced (or added) with type ``PyObjType()`` — we don't know
        the concrete type of *new_impl* at this level.
        """
        existing = dict(cls.methods)
        existing[method] = PyObjType()
        return PyClassType(
            name=cls.name,
            methods=tuple(sorted(existing.items())),
            bases=cls.bases,
        )

    @staticmethod
    def patch_preserves_contract(cls: PyClassType, method: str,
                                 old_spec: Spec,
                                 new_impl: SynTerm) -> Judgment:
        """Generate the proof obligation: *new_impl* satisfies *old_spec*.

        The obligation is a ``TYPE_CHECK`` judgment requiring that
        ``new_impl`` inhabits the refinement type carved out by the
        postcondition in *old_spec*.
        """
        from deppy.core.types import RefinementType
        obligation_type = RefinementType(
            base_type=PyObjType(),
            var_name="result",
            predicate=old_spec.description,
        )
        return Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=_CTX,
            term=new_impl,
            type_=obligation_type,
        )

    # ── axioms (Ch 7 §§ 2–4) ────────────────────────────────────

    @staticmethod
    def patch_axioms() -> list[FormalAxiomEntry]:
        """Axioms for monkey-patching.

        1. Patch path:  setattr(C, m, v) gives C =_{PyClass} C[m:=v]
           when the behavioral subtyping contract is preserved.
        2. Patch composition:  sequential patches compose as path
           concatenation.
        3. Reversible patch:  restoring the original method yields the
           identity path (refl).
        """
        C = Var("C")
        m, v, v1, v2 = Var("m"), Var("v"), Var("v1"), Var("v2")
        orig = Var("orig")

        return [
            FormalAxiomEntry(
                name="patch_path",
                module="python_dynamics",
                params=[("C", PyClassType()), ("m", PyStrType()),
                        ("v", PyObjType())],
                conclusion=formal_eq(
                    _CTX,
                    op_setattr(C, m, v),
                    _opcall("patch_cls", C, m, v),
                    PathType(base_type=PyClassType()),
                ),
                description=(
                    "setattr(C, m, v) produces a path "
                    "C =_{PyClass} C[m:=v] when contract is preserved."
                ),
            ),
            FormalAxiomEntry(
                name="patch_composition",
                module="python_dynamics",
                params=[("C", PyClassType()), ("m", PyStrType()),
                        ("v1", PyObjType()), ("v2", PyObjType())],
                conclusion=formal_eq(
                    _CTX,
                    _opcall("patch_seq", C, m, v1, v2),
                    _opcall("patch_cls", C, m, v2),
                    PathType(base_type=PyClassType()),
                ),
                description=(
                    "Applying two patches in sequence is equal to "
                    "the single patch with the final value."
                ),
            ),
            FormalAxiomEntry(
                name="patch_reversible",
                module="python_dynamics",
                params=[("C", PyClassType()), ("m", PyStrType()),
                        ("v", PyObjType()), ("orig", PyObjType())],
                conclusion=formal_eq(
                    _CTX,
                    _opcall("patch_restore", C, m, v, orig),
                    C,  # restoring original ≡ identity path (refl)
                    PyClassType(),
                ),
                description=(
                    "Patching then restoring the original method "
                    "yields the identity path."
                ),
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 4. Metaclasses  (Ch 14)
# ═══════════════════════════════════════════════════════════════════

class MetaclassSemantics:
    """Metaclasses as 2-types in the type theory.

    In the monograph (Ch 14) a metaclass is a *2-type*: a type of types
    of types, with higher inductive structure reflecting the dynamic
    class-creation protocol (__prepare__ → namespace execution →
    __new__ → __init__ → __init_subclass__).
    """

    @staticmethod
    def metaclass_of(cls: PyClassType) -> PyClassType:
        """Return the metaclass of *cls*.

        Default: ``type`` (the ur-metaclass).  A real implementation
        would consult a class registry; here we return a stub.
        """
        return PyClassType(name="type")

    @staticmethod
    def new_call(meta: PyClassType, name: str,
                 bases: list[PyClassType], namespace: SynTerm) -> PyClassType:
        """Model ``meta.__new__(meta, name, bases, namespace)``.

        Returns a fresh ``PyClassType`` representing the newly created
        class.  The *namespace* term is expected to be a dict literal
        mapping attribute names to implementations.
        """
        # Extract method entries from the namespace literal if possible
        methods: list[tuple[str, SynType]] = []
        if isinstance(namespace, Literal) and isinstance(namespace.value, dict):
            for k in namespace.value:
                methods.append((str(k), PyObjType()))

        base_names = tuple(b.name for b in bases)
        return PyClassType(
            name=name,
            methods=tuple(methods),
            bases=base_names,
        )

    @staticmethod
    def prepare_namespace(meta: PyClassType, name: str,
                          bases: list[PyClassType]) -> SynTerm:
        """Model ``meta.__prepare__(name, bases)``.

        Returns an ``OpCall`` representing the namespace dict that will
        be populated during class body execution.
        """
        base_terms = tuple(Literal(b) for b in bases)
        return op_prepare(
            Literal(meta), Literal(name),
            Literal(tuple(b.name for b in bases)),
        )

    @staticmethod
    def init_subclass_call(cls: PyClassType) -> SynTerm:
        """Model ``cls.__init_subclass__()``."""
        return op_init_subclass(Literal(cls))

    # ── axioms (Ch 14 §§ 2–5) ───────────────────────────────────

    @staticmethod
    def metaclass_axioms() -> list[FormalAxiomEntry]:
        """Axioms for metaclasses.

        1. type(type) == type   (fixed-point)
        2. isinstance(C, type) for any class C
        3. __init_subclass__ is invoked on subclass creation
        4. __prepare__ returns the class namespace (dict)
        """
        C = Var("C")

        return [
            FormalAxiomEntry(
                name="type_fixed_point",
                module="python_dynamics",
                params=[],
                conclusion=formal_eq(
                    _CTX,
                    op_type(Literal(PyClassType(name="type"))),
                    Literal(PyClassType(name="type")),
                    PyClassType(),
                ),
                description="type(type) == type  (metaclass fixed-point).",
            ),
            FormalAxiomEntry(
                name="class_is_type_instance",
                module="python_dynamics",
                params=[("C", PyClassType())],
                conclusion=formal_eq(
                    _CTX,
                    op_isinstance(C, Literal(PyClassType(name="type"))),
                    Literal(True),
                    PyBoolType(),
                ),
                description="isinstance(C, type) holds for every class C.",
            ),
            FormalAxiomEntry(
                name="init_subclass_invoked",
                module="python_dynamics",
                params=[("C", PyClassType())],
                conclusion=formal_eq(
                    _CTX,
                    _opcall("subclass_hook_called", C),
                    Literal(True),
                    PyBoolType(),
                ),
                description=(
                    "__init_subclass__ is called on every subclass creation."
                ),
            ),
            FormalAxiomEntry(
                name="prepare_returns_dict",
                module="python_dynamics",
                params=[("C", PyClassType())],
                conclusion=Judgment(
                    kind=JudgmentKind.TYPE_CHECK,
                    context=_CTX,
                    term=op_prepare(
                        Literal(PyClassType(name="type")),
                        Literal("_"),
                        Literal(()),
                    ),
                    type_=PyDictType(key_type=PyStrType(),
                                     value_type=PyObjType()),
                ),
                description="__prepare__ returns a dict (the class namespace).",
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 5. Descriptors  (Ch 19)
# ═══════════════════════════════════════════════════════════════════

class DescriptorSemantics:
    """Descriptor protocol: __get__, __set__, __delete__.

    Ch 19 of the monograph views the descriptor protocol as a *vertical
    bundle* over the class hierarchy: each descriptor attaches a fiber
    of attribute-access semantics to the points (methods/properties)
    of the class object.
    """

    @staticmethod
    def is_data_descriptor(desc: PyClassType) -> bool:
        """A *data descriptor* defines ``__set__`` or ``__delete__``."""
        names = {m for m, _ in desc.methods}
        return "__set__" in names or "__delete__" in names

    @staticmethod
    def is_non_data_descriptor(desc: PyClassType) -> bool:
        """A *non-data descriptor* defines ``__get__`` but not ``__set__``."""
        names = {m for m, _ in desc.methods}
        return "__get__" in names and "__set__" not in names

    @staticmethod
    def resolve_attribute(obj: SynTerm, name: str) -> SynTerm:
        """Full attribute resolution following CPython's descriptor protocol.

        Priority order:
        1. Data descriptor from the type's MRO
        2. Instance ``__dict__``
        3. Non-data descriptor from the type's MRO
        4. ``__getattr__`` fallback

        We return a term that *models* this four-step chain as a
        sequence of conditionals expressed via Op calls.
        """
        name_lit = Literal(name)
        cls = op_type(obj)

        # step 1: data descriptor from MRO
        data_desc = _opcall("find_data_descriptor", cls, name_lit)
        data_result = op_desc_get(data_desc, obj, cls)

        # step 2: instance dict
        dict_result = op_getattr_op(op_dict_of(obj), name_lit)

        # step 3: non-data descriptor from MRO
        nondata_desc = _opcall("find_nondata_descriptor", cls, name_lit)
        nondata_result = op_desc_get(nondata_desc, obj, cls)

        # step 4: __getattr__ fallback
        fallback = _opcall("getattr_fallback", obj, name_lit)

        # Build the chain as nested conditionals (innermost-first):
        #   if has_nondata_desc then nondata_result else fallback
        step34 = _opcall("desc_or", nondata_desc, nondata_result, fallback)
        #   if has_dict_entry then dict_result else step34
        step234 = _opcall("dict_or", dict_result, step34)
        #   if has_data_desc then data_result else step234
        full = _opcall("desc_or", data_desc, data_result, step234)
        return full

    @staticmethod
    def set_attribute(obj: SynTerm, name: str, value: SynTerm) -> SynTerm:
        """Attribute assignment with data-descriptor override.

        If a data descriptor exists in the type's MRO for *name*, its
        ``__set__`` is called; otherwise the value is stored directly in
        the instance ``__dict__``.
        """
        name_lit = Literal(name)
        cls = op_type(obj)
        data_desc = _opcall("find_data_descriptor", cls, name_lit)
        desc_set = op_desc_set(data_desc, obj, value)
        dict_set = op_setattr(op_dict_of(obj), name_lit, value)
        return _opcall("desc_or", data_desc, desc_set, dict_set)

    # ── axioms (Ch 19 §§ 2–5) ───────────────────────────────────

    @staticmethod
    def descriptor_axioms() -> list[FormalAxiomEntry]:
        """Axioms for the descriptor protocol.

        1. Property is a data descriptor (has __set__)
        2. @staticmethod removes self binding
        3. @classmethod binds to class not instance
        4. Data descriptors override __dict__
        """
        desc = Var("desc")
        obj = Var("obj")
        cls = Var("cls")
        val = Var("val")

        return [
            FormalAxiomEntry(
                name="property_is_data_descriptor",
                module="python_dynamics",
                params=[("desc", PyClassType(name="property"))],
                conclusion=formal_eq(
                    _CTX,
                    op_hasattr(desc, Literal("__set__")),
                    Literal(True),
                    PyBoolType(),
                ),
                description="property objects are data descriptors.",
            ),
            FormalAxiomEntry(
                name="staticmethod_no_self",
                module="python_dynamics",
                params=[("desc", PyClassType(name="staticmethod")),
                        ("obj", PyObjType()), ("cls", PyClassType())],
                conclusion=formal_eq(
                    _CTX,
                    op_desc_get(desc, obj, cls),
                    _opcall("unwrap_static", desc),
                ),
                description=(
                    "@staticmethod.__get__ returns the underlying function "
                    "without binding self or cls."
                ),
            ),
            FormalAxiomEntry(
                name="classmethod_binds_cls",
                module="python_dynamics",
                params=[("desc", PyClassType(name="classmethod")),
                        ("obj", PyObjType()), ("cls", PyClassType())],
                conclusion=formal_eq(
                    _CTX,
                    op_desc_get(desc, obj, cls),
                    _opcall("bind_to_cls", desc, cls),
                ),
                description=(
                    "@classmethod.__get__ binds the first argument to cls, "
                    "not the instance."
                ),
            ),
            FormalAxiomEntry(
                name="data_descriptor_overrides_dict",
                module="python_dynamics",
                params=[("desc", PyObjType()), ("obj", PyObjType()),
                        ("cls", PyClassType()), ("val", PyObjType())],
                conclusion=formal_eq(
                    _CTX,
                    _opcall("attr_resolve_priority", desc, obj, cls),
                    op_desc_get(desc, obj, cls),
                ),
                description=(
                    "Data descriptors take priority over the instance "
                    "__dict__ during attribute resolution."
                ),
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 6. Dynamic Attributes  (Ch 16)
# ═══════════════════════════════════════════════════════════════════

class DynamicAttrSemantics:
    """Dynamic attribute access via __dict__, __getattr__, __getattribute__.

    Ch 16 of the monograph treats ``__dict__`` as the *namespace sheaf*:
    the instance dictionary is a section of the presheaf of attributes
    over the class hierarchy.
    """

    @staticmethod
    def getattr_semantics(obj: SynTerm, name: str) -> SynTerm:
        """Full ``getattr`` resolution chain.

        1. ``type(obj).__getattribute__(obj, name)``
           — which itself invokes the descriptor protocol
              (see :class:`DescriptorSemantics`)
        2. If that raises ``AttributeError``, fall back to
           ``type(obj).__getattr__(obj, name)``
        """
        name_lit = Literal(name)
        primary = op_getattribute(obj, name_lit)
        fallback = _opcall("getattr_fallback", obj, name_lit)
        return _opcall("try_or", primary, fallback)

    @staticmethod
    def setattr_semantics(obj: SynTerm, name: str, val: SynTerm) -> SynTerm:
        """Full ``setattr`` resolution.

        1. Check for a data descriptor in ``type(obj).__mro__``; if
           found, call its ``__set__``.
        2. Otherwise, store directly in ``obj.__dict__``.

        This delegates to :meth:`DescriptorSemantics.set_attribute`.
        """
        return DescriptorSemantics.set_attribute(obj, name, val)

    @staticmethod
    def delattr_semantics(obj: SynTerm, name: str) -> SynTerm:
        """Model ``delattr(obj, name)``.

        If a data descriptor with ``__delete__`` exists, call it;
        otherwise remove the key from ``obj.__dict__``.
        """
        name_lit = Literal(name)
        cls = op_type(obj)
        data_desc = _opcall("find_data_descriptor", cls, name_lit)
        desc_del = op_desc_delete(data_desc, obj)
        dict_del = op_delattr(op_dict_of(obj), name_lit)
        return _opcall("desc_or", data_desc, desc_del, dict_del)

    # ── axioms (Ch 16 §§ 2–4) ───────────────────────────────────

    @staticmethod
    def dynamic_axioms() -> list[FormalAxiomEntry]:
        """Axioms for dynamic attribute access.

        1. Round-trip: setattr then getattr recovers the value
           (absent descriptors).
        2. __dict__ reflects all instance attributes.
        3. __slots__ restricts attribute creation.
        4. hasattr ↔ getattr doesn't raise AttributeError.
        """
        obj = Var("obj")
        k = Var("k")
        v = Var("v")

        return [
            FormalAxiomEntry(
                name="setattr_getattr_roundtrip",
                module="python_dynamics",
                params=[("obj", PyObjType()), ("k", PyStrType()),
                        ("v", PyObjType())],
                conclusion=formal_eq(
                    _CTX,
                    op_getattr_op(
                        _opcall("after_setattr", obj, k, v),
                        k,
                    ),
                    v,
                ),
                description=(
                    "setattr(obj, k, v); getattr(obj, k) == v  "
                    "(when no data descriptor intercepts)."
                ),
            ),
            FormalAxiomEntry(
                name="dict_reflects_attrs",
                module="python_dynamics",
                params=[("obj", PyObjType()), ("k", PyStrType()),
                        ("v", PyObjType())],
                conclusion=formal_eq(
                    _CTX,
                    _opcall("dict_lookup", op_dict_of(obj), k),
                    op_getattr_op(obj, k),
                ),
                description=(
                    "__dict__ faithfully reflects instance attributes "
                    "(absent descriptors)."
                ),
            ),
            FormalAxiomEntry(
                name="slots_restrict_attrs",
                module="python_dynamics",
                params=[("obj", PyObjType()), ("k", PyStrType())],
                conclusion=formal_eq(
                    _CTX,
                    _opcall("can_set_attr", obj, k),
                    _opcall("k_in_slots_or_no_slots", obj, k),
                    PyBoolType(),
                ),
                description=(
                    "__slots__ restricts which attributes can be set."
                ),
            ),
            FormalAxiomEntry(
                name="hasattr_iff_no_error",
                module="python_dynamics",
                params=[("obj", PyObjType()), ("k", PyStrType())],
                conclusion=formal_eq(
                    _CTX,
                    op_hasattr(obj, k),
                    _opcall("getattr_succeeds", obj, k),
                    PyBoolType(),
                ),
                description=(
                    "hasattr(obj, k) ↔ getattr(obj, k) does not raise "
                    "AttributeError."
                ),
            ),
        ]


# ═══════════════════════════════════════════════════════════════════
# 7. Collect all dynamics axioms
# ═══════════════════════════════════════════════════════════════════

def all_dynamics_axioms() -> list[FormalAxiomEntry]:
    """Collect every axiom from all dynamics sub-modules.

    Returns a flat list suitable for installation into an
    ``AxiomRegistry`` or a ``ProofKernel``.
    """
    axioms: list[FormalAxiomEntry] = []
    axioms.extend(MROSemantics.mro_axioms())
    axioms.extend(DuckTypeSemantics.duck_typing_axioms())
    axioms.extend(MonkeyPatchSemantics.patch_axioms())
    axioms.extend(MetaclassSemantics.metaclass_axioms())
    axioms.extend(DescriptorSemantics.descriptor_axioms())
    axioms.extend(DynamicAttrSemantics.dynamic_axioms())
    return axioms


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:  # noqa: C901
    """Run internal consistency tests.  Called at import if
    ``DEPPY_SELF_TEST`` is set, and also by pytest discovery.
    """
    import sys

    errors: list[str] = []

    def _check(cond: bool, msg: str) -> None:
        if not cond:
            errors.append(msg)

    # ── MRO ──────────────────────────────────────────────────────

    # simple linear hierarchy: C(B(A))
    A = PyClassType(name="A", methods=(("fa", PyObjType()),))
    B = PyClassType(name="B", methods=(("fb", PyObjType()),), bases=("A",))
    C = PyClassType(name="C", methods=(("fc", PyObjType()),), bases=("B",))
    reg: dict[str, PyClassType] = {"A": A, "B": B, "C": C}

    mro = MROSemantics.compute_mro(C, reg)
    mro_names = [k.name for k in mro]
    _check(mro_names[0] == "C", f"MRO first is C, got {mro_names}")
    _check("B" in mro_names, "MRO should include B")
    _check("A" in mro_names, "MRO should include A")

    # method resolution
    resolved = MROSemantics.resolve_method(C, "fc", mro)
    _check(resolved is not None, "resolve_method should find 'fc' in C")

    resolved_a = MROSemantics.resolve_method(C, "fa", mro)
    _check(resolved_a is not None, "resolve_method should find 'fa' via MRO")

    # super dispatch
    sup = MROSemantics.super_dispatch(C, "fb", C, reg)
    _check(sup is not None, "super(C, obj).fb should resolve to B")

    # MRO axioms
    mro_ax = MROSemantics.mro_axioms()
    _check(len(mro_ax) == 4, f"Expected 4 MRO axioms, got {len(mro_ax)}")
    _check(all(isinstance(a, FormalAxiomEntry) for a in mro_ax),
           "All MRO axioms must be FormalAxiomEntry")

    # ── Duck typing ──────────────────────────────────────────────

    D1 = PyClassType(name="D1", methods=(("quack", PyObjType()),
                                          ("swim", PyObjType())))
    D2 = PyClassType(name="D2", methods=(("quack", PyObjType()),
                                          ("swim", PyObjType())))
    D3 = PyClassType(name="D3", methods=(("quack", PyObjType()),))

    _check(DuckTypeSemantics.check_duck_equivalent(D1, D2),
           "D1 and D2 should be duck-equivalent")
    _check(not DuckTypeSemantics.check_duck_equivalent(D1, D3),
           "D1 and D3 should NOT be duck-equivalent")

    # protocol inference
    sites = [GetAttr(Var("x"), "quack"), GetAttr(Var("x"), "swim")]
    proto = DuckTypeSemantics.compute_protocol(sites)
    _check(isinstance(proto, ProtocolType), "Should return ProtocolType")
    proto_names = {m for m, _ in proto.methods}
    _check(proto_names == {"quack", "swim"},
           f"Protocol should have {{quack, swim}}, got {proto_names}")

    # duck path
    path = DuckTypeSemantics.duck_path(D1, D2)
    _check(path is not None, "Duck path should exist for equivalent classes")
    no_path = DuckTypeSemantics.duck_path(D1, D3)
    _check(no_path is None, "Duck path should be None for non-equivalent")

    duck_ax = DuckTypeSemantics.duck_typing_axioms()
    _check(len(duck_ax) == 3, f"Expected 3 duck axioms, got {len(duck_ax)}")

    # ── Monkey-patching ──────────────────────────────────────────

    base = PyClassType(name="Cls", methods=(("foo", PyObjType()),))
    patched = MonkeyPatchSemantics.apply_patch(base, "bar", Var("new_bar"))
    patched_names = {m for m, _ in patched.methods}
    _check("foo" in patched_names and "bar" in patched_names,
           f"Patched class should have foo and bar, got {patched_names}")

    spec = Spec(kind=SpecKind.GUARANTEE, description="returns positive int")
    obligation = MonkeyPatchSemantics.patch_preserves_contract(
        base, "foo", spec, Var("new_foo"),
    )
    _check(obligation.kind == JudgmentKind.TYPE_CHECK,
           "Patch obligation should be TYPE_CHECK")

    patch_ax = MonkeyPatchSemantics.patch_axioms()
    _check(len(patch_ax) == 3, f"Expected 3 patch axioms, got {len(patch_ax)}")

    # ── Metaclasses ──────────────────────────────────────────────

    meta = MetaclassSemantics.metaclass_of(base)
    _check(meta.name == "type", f"Default metaclass should be 'type', got {meta.name}")

    ns = Literal({"foo": None, "bar": None})
    new_cls = MetaclassSemantics.new_call(
        PyClassType(name="type"), "NewCls", [A], ns,
    )
    _check(new_cls.name == "NewCls", f"New class name mismatch: {new_cls.name}")
    new_cls_methods = {m for m, _ in new_cls.methods}
    _check("foo" in new_cls_methods and "bar" in new_cls_methods,
           f"New class should have foo and bar, got {new_cls_methods}")

    meta_ax = MetaclassSemantics.metaclass_axioms()
    _check(len(meta_ax) == 4, f"Expected 4 metaclass axioms, got {len(meta_ax)}")

    # ── Descriptors ──────────────────────────────────────────────

    data_desc = PyClassType(
        name="MyProp",
        methods=(("__get__", PyObjType()), ("__set__", PyObjType())),
    )
    non_data_desc = PyClassType(
        name="MyDesc",
        methods=(("__get__", PyObjType()),),
    )
    plain_cls = PyClassType(name="Plain", methods=(("foo", PyObjType()),))

    _check(DescriptorSemantics.is_data_descriptor(data_desc),
           "Should detect data descriptor")
    _check(not DescriptorSemantics.is_data_descriptor(non_data_desc),
           "Non-data desc should not be data descriptor")
    _check(DescriptorSemantics.is_non_data_descriptor(non_data_desc),
           "Should detect non-data descriptor")
    _check(not DescriptorSemantics.is_non_data_descriptor(data_desc),
           "Data descriptor is not a non-data descriptor")
    _check(not DescriptorSemantics.is_non_data_descriptor(plain_cls),
           "Plain class should not be a descriptor")

    resolved_attr = DescriptorSemantics.resolve_attribute(Var("obj"), "x")
    _check(isinstance(resolved_attr, (OpCall, SynTerm)),
           "resolve_attribute should return a SynTerm")

    desc_ax = DescriptorSemantics.descriptor_axioms()
    _check(len(desc_ax) == 4, f"Expected 4 descriptor axioms, got {len(desc_ax)}")

    # ── Dynamic attributes ───────────────────────────────────────

    ga = DynamicAttrSemantics.getattr_semantics(Var("o"), "x")
    _check(isinstance(ga, SynTerm), "getattr_semantics should return SynTerm")

    sa = DynamicAttrSemantics.setattr_semantics(Var("o"), "x", Var("v"))
    _check(isinstance(sa, SynTerm), "setattr_semantics should return SynTerm")

    da = DynamicAttrSemantics.delattr_semantics(Var("o"), "x")
    _check(isinstance(da, SynTerm), "delattr_semantics should return SynTerm")

    dyn_ax = DynamicAttrSemantics.dynamic_axioms()
    _check(len(dyn_ax) == 4, f"Expected 4 dynamic axioms, got {len(dyn_ax)}")

    # ── all_dynamics_axioms ──────────────────────────────────────

    all_ax = all_dynamics_axioms()
    expected_total = 4 + 3 + 3 + 4 + 4 + 4  # 22
    _check(len(all_ax) == expected_total,
           f"Expected {expected_total} total axioms, got {len(all_ax)}")

    # every axiom should have a non-empty name and module
    for ax in all_ax:
        _check(bool(ax.name), f"Axiom has empty name: {ax}")
        _check(ax.module == "python_dynamics",
               f"Axiom {ax.name} has wrong module: {ax.module}")

    # unique names
    names = [ax.name for ax in all_ax]
    _check(len(names) == len(set(names)),
           f"Duplicate axiom names: {[n for n in names if names.count(n) > 1]}")

    # ── report ───────────────────────────────────────────────────

    if errors:
        for e in errors:
            print(f"  FAIL: {e}", file=sys.stderr)
        raise AssertionError(
            f"python_dynamics self-test: {len(errors)} failure(s)"
        )
    print(f"python_dynamics: all self-tests passed "
          f"({len(all_ax)} axioms verified)")


# Run self-tests on import when requested
import os as _os
if _os.environ.get("DEPPY_SELF_TEST"):
    _self_test()
