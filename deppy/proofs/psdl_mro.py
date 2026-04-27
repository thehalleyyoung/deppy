"""MRO / C3 linearization for PSDL — sheaf over inheritance graph.

The C3 linearization of a class's bases gives the *unique* total
order of classes consistent with each parent's order in which Python
walks methods.  In categorical terms:

  * The inheritance graph is a partial order (parent → child).
  * Each class is a **section** over its sub-tree: it provides a
    family of method implementations.
  * Two classes that share a base on overlapping methods must
    **agree** on the implementation — the sheaf's *cocycle
    condition*.
  * Method lookup on an instance is **sheaf restriction** to the
    instance's class along the linearization order.

Cubical interpretation:

  * The MRO is a path in the universe of classes; method lookup
    ``Cls.method`` is a :class:`DuckPath` walking the MRO until a
    matching impl is found.
  * Multiple-inheritance overlap is a :class:`CechGlue`: the local
    impls on each path agree on overlap.
  * The MRO's coherence (no diamond ambiguity) is a
    :class:`Cocycle` at level 1 — every (caller, callee) pair on
    the linearization has a witness of consistent dispatch.
  * ``super().method()`` is :class:`PathComp`: composing the path
    "find this class in MRO" with "step to next class in MRO".

Soundness gain: when a class's MRO is computed eagerly, PSDL
records the path it took.  A subsequent claim about ``obj.method()``
is honest only if the recorded MRO matches what Python's ``mro()``
returns at runtime; PSDL's ``Cocycle`` makes that obligation
explicit.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional


@dataclass
class ClassNode:
    """One class in the inheritance graph."""
    name: str
    bases: list[str] = field(default_factory=list)
    methods: dict[str, str] = field(default_factory=dict)
    # name → impl-locator (e.g. ``"_method_impl_in_<class>"``)


@dataclass
class MROTable:
    """Inheritance graph + lazy C3 linearization cache."""
    classes: dict[str, ClassNode] = field(default_factory=dict)
    _lin_cache: dict[str, list[str]] = field(default_factory=dict)

    def declare(
        self,
        name: str,
        bases: Optional[list[str]] = None,
        methods: Optional[dict[str, str]] = None,
    ) -> ClassNode:
        node = ClassNode(
            name=name,
            bases=list(bases or []),
            methods=dict(methods or {}),
        )
        self.classes[name] = node
        self._lin_cache.pop(name, None)
        return node

    def add_method(self, cls_name: str, attr: str, impl_locator: str) -> None:
        node = self.classes.get(cls_name)
        if node is None:
            node = self.declare(cls_name)
        node.methods[attr] = impl_locator
        self._lin_cache.pop(cls_name, None)

    def linearize(self, cls_name: str) -> list[str]:
        """Compute C3 linearization for ``cls_name``.  Returns the
        ordered list of classes for method lookup; the leftmost
        wins.  Raises ``ValueError`` if no consistent linearization
        exists (the diamond inconsistency case)."""
        if cls_name in self._lin_cache:
            return self._lin_cache[cls_name]
        node = self.classes.get(cls_name)
        if node is None:
            return [cls_name]
        # Standard C3:
        #   L[C] = C ⊕ merge(L[B1], L[B2], …, [B1, B2, …])
        bases = node.bases
        if not bases:
            self._lin_cache[cls_name] = [cls_name]
            return self._lin_cache[cls_name]
        sequences = [self.linearize(b) for b in bases] + [list(bases)]
        merged: list[str] = []
        while any(sequences):
            for s in sequences:
                if not s:
                    continue
                head = s[0]
                # Head must not appear in the tail of any other.
                if not any(head in t[1:] for t in sequences):
                    merged.append(head)
                    for t in sequences:
                        if t and t[0] == head:
                            t.pop(0)
                    break
            else:
                raise ValueError(
                    f"C3 linearization failed for {cls_name}: "
                    f"inconsistent diamond"
                )
            sequences = [s for s in sequences if s]
        result = [cls_name] + merged
        self._lin_cache[cls_name] = result
        return result

    def resolve(self, cls_name: str, attr: str) -> Optional[tuple[str, str]]:
        """Walk the C3 linearization to find the first class that
        defines ``attr``.  Returns ``(defining_class, impl_locator)``
        or None when not found."""
        try:
            order = self.linearize(cls_name)
        except ValueError:
            return None
        for c in order:
            node = self.classes.get(c)
            if node is None:
                continue
            if attr in node.methods:
                return (c, node.methods[attr])
        return None


# ───────────────────────────────────────────────────────────────────
#  PSDL primitives — emit kernel artefacts for MRO walks
# ───────────────────────────────────────────────────────────────────

def emit_mro_dispatch_path(
    table: MROTable, cls_name: str, attr: str,
):
    """Emit a :class:`DuckPath` walking the C3 linearization.

    Each link in the path is one ``method_proofs`` entry: from class
    ``C[i]`` to class ``C[i+1]`` along the linearization, the proof
    is that ``attr`` is *not* defined on ``C[i]``, so dispatch
    proceeds to ``C[i+1]``.  The final entry has the actual impl.
    """
    from deppy.core.kernel import (
        DuckPath, Refl, AxiomInvocation, Structural,
    )
    from deppy.core.types import Var, PyObjType
    try:
        order = table.linearize(cls_name)
    except ValueError:
        return Structural(
            f"MRO C3 inconsistent for {cls_name} (diamond)"
        )
    method_proofs: list[tuple[str, object]] = []
    for c in order:
        node = table.classes.get(c)
        if node is None:
            continue
        if attr in node.methods:
            method_proofs.append((
                f"resolve_{c}.{attr}",
                AxiomInvocation(
                    name=node.methods[attr], module="mro",
                ),
            ))
            break
        method_proofs.append((
            f"skip_{c}.{attr}",
            Refl(Var(f"_no_{attr}_on_{c}")),
        ))
    return DuckPath(
        type_a=PyObjType(),
        type_b=PyObjType(),
        method_proofs=method_proofs,
    )


def emit_mro_cocycle(
    table: MROTable, cls_name: str, shared_methods: list[str],
):
    """Build a :class:`Cocycle` that witnesses MRO consistency.

    Components: for each shared method, the dispatch path through
    ``cls_name``'s linearization.  ``boundary_pairs`` are the
    (caller, callee) pairs in the linearization sequence.
    """
    from deppy.core.kernel import Cocycle, Refl
    from deppy.core.types import Var
    components: list[object] = []
    for m in shared_methods:
        components.append(emit_mro_dispatch_path(table, cls_name, m))
    if not components:
        components.append(Refl(Var(f"_empty_mro_{cls_name}")))
    try:
        order = table.linearize(cls_name)
    except ValueError:
        order = [cls_name]
    boundary_pairs = [(i, i + 1) for i in range(len(order) - 1)]
    return Cocycle(
        level=1,
        components=components,
        boundary_pairs=boundary_pairs,
    )


def emit_super_path(
    table: MROTable, cls_name: str, attr: str,
):
    """``super().method()`` — :class:`PathComp` of "find this class
    in MRO" then "step to next class".
    """
    from deppy.core.kernel import PathComp, AxiomInvocation
    try:
        order = table.linearize(cls_name)
    except ValueError:
        order = [cls_name]
    cur_idx = 0
    if cls_name in order:
        cur_idx = order.index(cls_name)
    next_cls = order[cur_idx + 1] if cur_idx + 1 < len(order) else cls_name
    find_self = AxiomInvocation(
        name=f"mro_position_{cls_name}",
        module="mro",
    )
    step_next = AxiomInvocation(
        name=f"mro_step_{cls_name}_to_{next_cls}",
        module="mro",
    )
    return PathComp(left_path=find_self, right_path=step_next)


__all__ = [
    "ClassNode",
    "MROTable",
    "emit_mro_dispatch_path",
    "emit_mro_cocycle",
    "emit_super_path",
]
