"""Operator dispatch with `__r*__` fallback for PSDL.

Python's binary operators dispatch via a *two-stage* protocol:

  1. ``a op b`` calls ``a.__op__(b)``.
  2. If the result is :class:`NotImplemented` (or the method is
     missing), Python calls ``b.__rop__(a)``.
  3. If that also returns :class:`NotImplemented`, raise
     :exc:`TypeError`.

For a *subclass-priority* exception: when ``type(b)`` is a strict
subclass of ``type(a)``, Python calls ``b.__rop__(a)`` *first*.

Cubical interpretation:

  * The dispatch is a :class:`ConditionalDuckPath`:

      ``ConditionalDuckPath(
          condition="hasattr(type(a), '__op__') ∧ "
                    "a.__op__(b) ≠ NotImplemented",
          evidence={"forward":  forward_path,
                    "fallback": rop_fallback_path,
                    "type_error": type_error_fibre},
      )``

    The ``condition`` selects between the forward and reverse
    paths; the ``type_error_fibre`` is the exception fibre that
    fires when both branches return :class:`NotImplemented`.

  * The subclass-priority case is encoded as an outer
    :class:`Fiber` over ``type(b)`` ≺ ``type(a)``.

Soundness gain: a proof that ``a + b == X`` is honest only when
PSDL records *which* of the two methods produced the value.  Without
this, claims about commutative-looking operators on user-defined
types could be unsound (one side defines ``__add__`` non-trivially,
the other returns ``NotImplemented`` and Python falls through).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional


# Python's standard binary operator → dunder pair.
OPERATOR_DUNDERS: dict[str, tuple[str, str]] = {
    "+":   ("__add__",      "__radd__"),
    "-":   ("__sub__",      "__rsub__"),
    "*":   ("__mul__",      "__rmul__"),
    "@":   ("__matmul__",   "__rmatmul__"),
    "/":   ("__truediv__",  "__rtruediv__"),
    "//":  ("__floordiv__", "__rfloordiv__"),
    "%":   ("__mod__",      "__rmod__"),
    "**":  ("__pow__",      "__rpow__"),
    "<<":  ("__lshift__",   "__rlshift__"),
    ">>":  ("__rshift__",   "__rrshift__"),
    "&":   ("__and__",      "__rand__"),
    "|":   ("__or__",       "__ror__"),
    "^":   ("__xor__",      "__rxor__"),
}


@dataclass
class OperatorImpl:
    """Records whether a class defines an op-dunder."""
    cls: str
    op: str
    forward_defined: bool = False   # __op__ implemented (non-trivial)
    reverse_defined: bool = False   # __rop__ implemented (non-trivial)
    inplace_defined: bool = False   # __iop__ implemented


@dataclass
class OperatorRegistry:
    """Tracks per-class operator implementations.

    Looked up by the compiler when emitting binary-op kernel terms;
    if both forward and reverse are defined on the operands, PSDL
    can reason about which path actually fires.
    """
    table: dict[tuple[str, str], OperatorImpl] = field(default_factory=dict)

    def declare(
        self,
        cls: str,
        op: str,
        *,
        forward: bool = False,
        reverse: bool = False,
        inplace: bool = False,
    ) -> OperatorImpl:
        impl = OperatorImpl(
            cls=cls, op=op,
            forward_defined=forward,
            reverse_defined=reverse,
            inplace_defined=inplace,
        )
        self.table[(cls, op)] = impl
        return impl

    def lookup(self, cls: str, op: str) -> Optional[OperatorImpl]:
        return self.table.get((cls, op))

    def has_forward(self, cls: str, op: str) -> bool:
        impl = self.lookup(cls, op)
        return impl is not None and impl.forward_defined

    def has_reverse(self, cls: str, op: str) -> bool:
        impl = self.lookup(cls, op)
        return impl is not None and impl.reverse_defined


# ───────────────────────────────────────────────────────────────────
#  PSDL primitives — emit kernel terms for ``a op b`` dispatch
# ───────────────────────────────────────────────────────────────────

def emit_op_dispatch(
    op: str,
    lhs_repr: str,
    rhs_repr: str,
    *,
    lhs_class: Optional[str] = None,
    rhs_class: Optional[str] = None,
    registry: Optional[OperatorRegistry] = None,
):
    """Emit the kernel artefact for ``lhs op rhs`` dispatch.

    Returns a :class:`ConditionalDuckPath` whose ``condition`` is
    "lhs has a working ``__op__``" and whose ``evidence`` contains:

      * ``"forward"`` → :class:`AxiomInvocation` on ``lhs.__op__``;
      * ``"fallback"`` → :class:`AxiomInvocation` on ``rhs.__rop__``;
      * ``"type_error"`` → :class:`EffectWitness` in the exception
        modality, fired when neither resolves.

    Subclass-priority exception: when ``rhs_class`` is a known
    strict subclass of ``lhs_class``, the fibres swap (rhs goes
    first).  Encoded as an outer :class:`Fiber` over the
    ``issubclass`` test.
    """
    from deppy.core.kernel import (
        ConditionalDuckPath, AxiomInvocation, EffectWitness, Refl,
        Fiber,
    )
    from deppy.core.types import Var, PyObjType

    dunders = OPERATOR_DUNDERS.get(op)
    if dunders is None:
        return Refl(Var(f"_unknown_op_{op}"))
    forward_dunder, reverse_dunder = dunders
    lhs_safe = lhs_repr[:24] or "lhs"
    rhs_safe = rhs_repr[:24] or "rhs"
    forward = AxiomInvocation(
        name=f"{lhs_class or 'lhs'}_{forward_dunder}_{lhs_safe}_{rhs_safe}",
        module="op_dispatch",
    )
    fallback = AxiomInvocation(
        name=f"{rhs_class or 'rhs'}_{reverse_dunder}_{rhs_safe}_{lhs_safe}",
        module="op_dispatch",
    )
    type_error = EffectWitness(
        effect=f"exception:TypeError@op{op}",
        proof=Refl(Var("_neither_dunder_resolved")),
    )
    # The evidence is a Fiber over two branches: forward-succeeds
    # vs falls-through-to-fallback.  Each branch's proof is the
    # corresponding kernel artefact.  ``type_error`` becomes a
    # third branch in the inner Fiber so the kernel sees all three
    # exit paths.
    evidence_fiber = Fiber(
        scrutinee=Var(f"_op_{op}_dispatch"),
        type_branches=[
            (PyObjType(), forward),
            (PyObjType(), fallback),
            (PyObjType(), type_error),
        ],
        exhaustive=True,
    )
    cond_path = ConditionalDuckPath(
        condition=(
            f"hasattr({lhs_class or 'type(lhs)'}, "
            f"{forward_dunder!r}) and "
            f"{lhs_class or 'lhs'}.{forward_dunder}({rhs_safe}) "
            f"is not NotImplemented"
        ),
        evidence=evidence_fiber,
    )
    # Subclass-priority swap: when rhs's class is a strict subclass
    # of lhs's class, Python tries the reverse first.  Encoded as a
    # Fiber over the issubclass test.
    if (
        lhs_class and rhs_class and lhs_class != rhs_class
        and registry is not None
    ):
        return Fiber(
            scrutinee=Var(f"_issubclass_{rhs_class}_of_{lhs_class}"),
            type_branches=[
                # Branch 1: rhs is strict subclass — reverse first.
                (PyObjType(), ConditionalDuckPath(
                    condition=(
                        f"hasattr({rhs_class}, {reverse_dunder!r}) and "
                        f"{rhs_class}.{reverse_dunder}({lhs_safe}) "
                        f"is not NotImplemented"
                    ),
                    evidence=Fiber(
                        scrutinee=Var(f"_op_{op}_subclass_priority"),
                        type_branches=[
                            (PyObjType(), fallback),
                            (PyObjType(), forward),
                            (PyObjType(), type_error),
                        ],
                        exhaustive=True,
                    ),
                )),
                # Branch 2: not a subclass — normal order.
                (PyObjType(), cond_path),
            ],
            exhaustive=True,
        )
    return cond_path


def emit_inplace_op_dispatch(
    op: str,
    lhs_repr: str,
    rhs_repr: str,
    *,
    lhs_class: Optional[str] = None,
    registry: Optional[OperatorRegistry] = None,
):
    """``lhs op= rhs`` dispatch.

    Python first tries ``__iop__`` (in-place); if not defined or
    returns :class:`NotImplemented`, it falls back to the regular
    ``op`` dispatch and rebinds ``lhs``.
    """
    from deppy.core.kernel import ConditionalDuckPath, AxiomInvocation, Refl
    from deppy.core.types import Var
    dunders = OPERATOR_DUNDERS.get(op)
    if dunders is None:
        return Refl(Var(f"_unknown_iop_{op}"))
    forward_dunder, _ = dunders
    inplace_dunder = "__i" + forward_dunder.removeprefix("__")
    inplace_path = AxiomInvocation(
        name=f"{lhs_class or 'lhs'}_{inplace_dunder}",
        module="op_dispatch",
    )
    fallback_to_normal = emit_op_dispatch(
        op, lhs_repr, rhs_repr,
        lhs_class=lhs_class, registry=registry,
    )
    from deppy.core.kernel import Fiber
    from deppy.core.types import PyObjType
    return ConditionalDuckPath(
        condition=(
            f"hasattr({lhs_class or 'type(lhs)'}, "
            f"{inplace_dunder!r})"
        ),
        evidence=Fiber(
            scrutinee=Var(f"_iop_{op}"),
            type_branches=[
                (PyObjType(), inplace_path),
                (PyObjType(), fallback_to_normal),
            ],
            exhaustive=True,
        ),
    )


__all__ = [
    "OPERATOR_DUNDERS",
    "OperatorImpl",
    "OperatorRegistry",
    "emit_op_dispatch",
    "emit_inplace_op_dispatch",
]
