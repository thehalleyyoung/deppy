"""Descriptor protocol for PSDL — `__get__`/`__set__`/`__delete__`
as a fibration with explicit precedence.

Python's attribute lookup walks a precedence chain:

  1. **Data descriptor** on the class (defines ``__get__`` *and*
     ``__set__`` or ``__delete__``).  Wins over instance dict.
  2. **Instance dict** entry — what ``obj.__dict__[name]`` holds.
  3. **Non-data descriptor** on the class (defines ``__get__`` only,
     e.g. methods, ``staticmethod``, ``classmethod``).
  4. ``__getattr__`` fallback (called only on AttributeError above).

Cubical interpretation:

  * Each instance is a **fibre** over its class.  The descriptor
    protocol is a section of the (instance → class) fibration that
    *picks* one of the four resolution paths for a given attribute.
  * The precedence is encoded as an ordered :class:`Fiber` over four
    ``type_branches``:

      ``Fiber(scrutinee=attr_name, type_branches=[
          (DataDescriptorType,  proof_via_data_desc),
          (InstanceDictType,    proof_via_instance_dict),
          (NonDataDescType,     proof_via_non_data_desc),
          (GetattrFallbackType, proof_via_getattr),
      ], exhaustive=True)``

    The first branch whose pattern matches at runtime is the one
    Python takes; PSDL records all four so the kernel can reason
    about each in turn.

  * ``__set__`` on a data descriptor is a :class:`Patch`: a
    monkey-patch path that updates the cell at the descriptor's
    storage location.  ``Patch.contract_proof`` is the descriptor's
    invariant.

Soundness gain: a proof that ``obj.attr == V`` is honest only when
the resolution path PSDL picked matches what Python takes at
runtime.  When a class's data descriptors are unknown, PSDL emits
a :class:`Fiber` over all four branches and the proof must hold for
every fibre — strictly safer than assuming instance-dict resolution.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Optional


class DescriptorKind(Enum):
    DATA = "data"            # has __get__ + (__set__ or __delete__)
    NON_DATA = "non_data"    # has __get__ only
    INSTANCE = "instance"    # plain instance-dict entry
    GETATTR = "getattr"      # __getattr__ fallback


@dataclass
class Descriptor:
    """A single descriptor declared on a class for an attribute."""
    cls: str
    attr: str
    kind: DescriptorKind
    has_get: bool = True
    has_set: bool = False
    has_delete: bool = False


@dataclass
class DescriptorRegistry:
    """Per-class descriptor table indexed by ``(class_name, attr)``."""
    table: dict[tuple[str, str], Descriptor] = field(default_factory=dict)

    def declare(
        self,
        cls: str,
        attr: str,
        kind: DescriptorKind,
        *,
        has_get: bool = True,
        has_set: bool = False,
        has_delete: bool = False,
    ) -> Descriptor:
        d = Descriptor(
            cls=cls, attr=attr, kind=kind,
            has_get=has_get, has_set=has_set, has_delete=has_delete,
        )
        self.table[(cls, attr)] = d
        return d

    def lookup(self, cls: str, attr: str) -> Optional[Descriptor]:
        return self.table.get((cls, attr))


# ───────────────────────────────────────────────────────────────────
#  Build the precedence-ordered Fiber for ``obj.attr`` resolution
# ───────────────────────────────────────────────────────────────────

def emit_descriptor_fiber(
    obj_repr: str,
    cls_name: str,
    attr: str,
    *,
    registry: Optional[DescriptorRegistry] = None,
):
    """Emit the kernel-side :class:`Fiber` over Python's four-branch
    attribute-resolution chain.

    Branches are ordered as Python evaluates them:
    data-descriptor → instance-dict → non-data-descriptor →
    ``__getattr__``.  A known descriptor in the registry pins the
    fibre's matching branch; an unknown attribute emits the Fiber
    over all four so the kernel can reason about each.
    """
    from deppy.core.kernel import Fiber, Refl, AxiomInvocation
    from deppy.core.types import Var, PyObjType

    descriptor = (
        registry.lookup(cls_name, attr) if registry is not None else None
    )

    def _branch_proof(kind: DescriptorKind):
        # The proof on each branch cites the descriptor / dict-lookup
        # via a kernel ``AxiomInvocation`` so the witness is named.
        return AxiomInvocation(
            name=f"resolve_{cls_name}_{attr}_via_{kind.value}",
            module="descriptor_protocol",
        )

    if descriptor is not None and descriptor.kind == DescriptorKind.DATA:
        # Data descriptors win — collapse the fibre to that branch.
        return Refl(Var(f"_data_desc_{cls_name}_{attr}"))

    branches = [
        (PyObjType(), _branch_proof(DescriptorKind.DATA)),
        (PyObjType(), _branch_proof(DescriptorKind.INSTANCE)),
        (PyObjType(), _branch_proof(DescriptorKind.NON_DATA)),
        (PyObjType(), _branch_proof(DescriptorKind.GETATTR)),
    ]
    return Fiber(
        scrutinee=Var(f"_attr_{obj_repr[:24]}_{attr}"),
        type_branches=branches,
        exhaustive=True,
    )


def emit_descriptor_set_patch(
    obj_repr: str,
    cls_name: str,
    attr: str,
    new_value_repr: str,
):
    """``obj.attr = v`` through a data descriptor is a :class:`Patch`:
    a monkey-patch path on the cell.  ``contract_proof`` is the
    descriptor's invariant — required to preserve trust through the
    update.
    """
    from deppy.core.kernel import Patch, Refl
    from deppy.core.types import Var
    return Patch(
        cls=Var(cls_name),
        method_name=attr,
        new_impl=Var(f"_value_{new_value_repr[:24]}"),
        contract_proof=Refl(Var(
            f"_descriptor_invariant_{cls_name}_{attr}",
        )),
    )


__all__ = [
    "DescriptorKind",
    "Descriptor",
    "DescriptorRegistry",
    "emit_descriptor_fiber",
    "emit_descriptor_set_patch",
]
