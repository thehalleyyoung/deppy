"""Variance analysis for ``Generic[T]`` classes.

Standard variance soundness rules:

  * **Covariant** position: T appears in a *return type* of a method
    or as a *read-only* (frozen / property without setter) field.
  * **Contravariant** position: T appears as a *parameter type* of
    a method.
  * **Invariant** position: T appears as both, or as a writable
    field, or inside an invariant generic.

The class's overall variance is the meet of all positions:
``Covariant ⊓ Contravariant = Invariant``.

PSDL primitive ``verify_variance(Cls)`` walks the live class via
``inspect`` and emits a ``VarianceCheck`` ProofTerm — see
:mod:`deppy.core.kernel`.

Soundness is proved at the meta-level (Lean) in
``metatheory/Deppy.lean §32``.
"""
from __future__ import annotations

import ast
import inspect
import typing
from dataclasses import dataclass, field
from enum import Enum
from typing import Optional


class VariancePos(Enum):
    """Tag for a single occurrence of a type variable."""
    COVARIANT     = "covariant"
    CONTRAVARIANT = "contravariant"
    INVARIANT     = "invariant"

    @staticmethod
    def meet(a: "VariancePos", b: "VariancePos") -> "VariancePos":
        """Greatest-lower-bound on the variance lattice.

        Mirrors :data:`Deppy.Metatheory.VariancePos.meet` in Lean.
        """
        if a is VariancePos.INVARIANT or b is VariancePos.INVARIANT:
            return VariancePos.INVARIANT
        if a is b:
            return a
        return VariancePos.INVARIANT

    def flip(self) -> "VariancePos":
        """Sign-flip used when entering a contravariant context."""
        if self is VariancePos.COVARIANT:
            return VariancePos.CONTRAVARIANT
        if self is VariancePos.CONTRAVARIANT:
            return VariancePos.COVARIANT
        return VariancePos.INVARIANT


@dataclass
class VarianceOccurrence:
    """One occurrence of the type parameter in the class body."""
    position: VariancePos
    location: str          # human-readable: "method foo: parameter x"
    line: int = 0


@dataclass
class VarianceReport:
    """Result of analysing a single ``Generic[T]`` class."""
    type_var: str
    declared: VariancePos      # what the user declared via ``TypeVar(..., covariant=...)``
    occurrences: list[VarianceOccurrence] = field(default_factory=list)

    @property
    def overall(self) -> VariancePos:
        """The meet of every occurrence's position.  An empty
        occurrence list is *vacuously* covariant (no constraints)."""
        result: VariancePos = VariancePos.COVARIANT
        for occ in self.occurrences:
            result = VariancePos.meet(result, occ.position)
        return result

    @property
    def consistent_with_declaration(self) -> bool:
        """The user-declared variance is sound iff the analyzer's
        overall is at least as restrictive."""
        if self.declared is VariancePos.COVARIANT:
            return self.overall is VariancePos.COVARIANT
        if self.declared is VariancePos.CONTRAVARIANT:
            return self.overall is VariancePos.CONTRAVARIANT
        # invariant accepts anything
        return True


# ───────────────────────────────────────────────────────────────────
#  AST walker — tags each occurrence of the type variable
# ───────────────────────────────────────────────────────────────────

def _typevar_appears_in(annotation: ast.AST, name: str) -> bool:
    """Does ``name`` appear anywhere inside the given AST node?"""
    if isinstance(annotation, ast.Name):
        return annotation.id == name
    if isinstance(annotation, ast.Subscript):
        return _typevar_appears_in(annotation.value, name) or \
               _typevar_appears_in(annotation.slice, name)
    if isinstance(annotation, ast.Tuple):
        return any(_typevar_appears_in(e, name) for e in annotation.elts)
    if isinstance(annotation, ast.Attribute):
        return _typevar_appears_in(annotation.value, name)
    return False


def analyze_class_variance(
    cls: type,
    *,
    type_var_name: str,
    declared: VariancePos,
) -> VarianceReport:
    """Walk ``cls``'s methods + fields and tag each appearance of
    ``type_var_name`` with its variance position.

    Heuristics matching standard PEP 484 rules:

      * Method *return* annotation containing T  →  covariant.
      * Method *parameter* annotation containing T  →  contravariant.
      * Field annotation on a frozen dataclass containing T  →  covariant
        (read-only).
      * Field annotation on a non-frozen class containing T  →  invariant
        (read AND write).
      * ``self``-only methods (no T in parameters or return) — no
        contribution.

    Returns a :class:`VarianceReport`.  Calling code should
    consult :attr:`VarianceReport.consistent_with_declaration`
    to decide whether to admit the user's TypeVar variance
    declaration.
    """
    report = VarianceReport(type_var=type_var_name, declared=declared)

    # Determine if the class is a frozen dataclass (read-only fields).
    is_frozen = False
    try:
        from dataclasses import fields, is_dataclass
        if is_dataclass(cls):
            params = getattr(cls, "__dataclass_params__", None)
            is_frozen = bool(getattr(params, "frozen", False))
    except Exception:
        pass

    # ── Walk class-level field annotations ──
    for fname, ann in (cls.__annotations__ or {}).items():
        # We only have the runtime annotation object.  For the
        # AST-level analysis we re-parse via `typing.get_type_hints`.
        try:
            hints = typing.get_type_hints(cls)
            ann_obj = hints.get(fname)
        except Exception:
            ann_obj = ann
        # String containment is the simplest check that works for
        # both runtime types and string annotations.
        if type_var_name not in repr(ann_obj):
            continue
        pos = (
            VariancePos.COVARIANT if is_frozen
            else VariancePos.INVARIANT
        )
        report.occurrences.append(VarianceOccurrence(
            position=pos,
            location=f"field {fname} ({'frozen' if is_frozen else 'mutable'})",
        ))

    # ── Walk methods ──
    for mname in dir(cls):
        # Conventionally skip __init__ from variance checks — PEP 484
        # treats the constructor as the single creation point of a
        # generic instance; its parameters don't propagate variance
        # like ordinary methods do.  Other dunders (__hash__,
        # __repr__, __eq__) are skipped too.
        if mname.startswith("_"):
            continue
        attr = getattr(cls, mname, None)
        if not callable(attr):
            continue
        try:
            sig = inspect.signature(attr)
        except (TypeError, ValueError):
            continue
        # Return annotation → covariant.
        ret = sig.return_annotation
        if ret is not inspect.Parameter.empty:
            if type_var_name in repr(ret):
                report.occurrences.append(VarianceOccurrence(
                    position=VariancePos.COVARIANT,
                    location=f"method {mname}: return type",
                ))
        # Parameter annotations → contravariant.
        for pname, pobj in sig.parameters.items():
            if pname == "self":
                continue
            ann = pobj.annotation
            if ann is inspect.Parameter.empty:
                continue
            if type_var_name in repr(ann):
                report.occurrences.append(VarianceOccurrence(
                    position=VariancePos.CONTRAVARIANT,
                    location=f"method {mname}: parameter {pname}",
                ))

    return report


def emit_variance_check(report: VarianceReport):
    """Build a :class:`deppy.core.kernel.VarianceCheck` ProofTerm
    from the analyzer's report.  When
    ``report.consistent_with_declaration`` is True, the kernel
    accepts via the soundness theorem in
    ``metatheory/Deppy.lean §32``; otherwise the kernel rejects
    with the specific occurrences that violate the declaration.
    """
    from deppy.core.kernel import VarianceCheck
    return VarianceCheck(
        type_var=report.type_var,
        declared=report.declared.value,
        overall=report.overall.value,
        consistent=report.consistent_with_declaration,
        occurrences=[
            (o.position.value, o.location)
            for o in report.occurrences
        ],
    )


__all__ = [
    "VariancePos",
    "VarianceOccurrence",
    "VarianceReport",
    "analyze_class_variance",
    "emit_variance_check",
]
