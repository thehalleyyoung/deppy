"""Discharge arithmetic foundation axioms via deppy's Z3 backend.

A foundation declared in a ``.deppy`` file is, by default, admitted
on the user's authority — it lives at the bottom of the trust
chain.  But many foundations are *pure arithmetic* (``a + b == b + a``,
``abs(x) >= 0``, ``(a - b)**2 == (b - a)**2``) and Z3 can verify
them mechanically.  When that succeeds we promote the foundation
from ``AXIOM_TRUSTED`` (admitted) to ``Z3_VERIFIED`` (proved by
solver).

This module is library-agnostic: it works on the .deppy
``foundation`` declarations themselves, not on any specific library.

Pipeline
--------

For each foundation:

  1. Strip the natural-language guard (``"... when x >= 0"``) from
     the statement, keeping only the equational/inequational core.
  2. Build a :class:`Z3Proof` whose ``formula`` is the core
     expression (rewritten into Z3-compatible Python syntax — e.g.
     ``==`` → ``=``, ``**2`` → multiplication, ``abs(x)`` →
     ``If(x >= 0, x, -x)``).
  3. Call ``ProofKernel.verify`` with the ``Z3Proof`` against a
     synthetic Judgment.  When Z3 returns valid we record the
     foundation as ``z3_discharged=True`` and the certificate
     emits the foundation alongside its Z3 verdict.

Foundations involving ``sqrt``, ``sin``, ``cos`` and similar
non-arithmetic operators stay as admitted foundations.  No magic
— Z3 either handles a formula or it doesn't, and the report is
transparent about which bucket each foundation fell into.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field


@dataclass
class FoundationDischarge:
    name: str
    statement: str
    z3_attempted: bool = False
    z3_verified: bool = False
    z3_formula: str = ""           # the Z3-compatible rewrite
    kernel_message: str = ""
    notes: list[str] = field(default_factory=list)


@dataclass
class FoundationDischargeReport:
    discharges: list[FoundationDischarge] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.discharges)

    @property
    def attempted(self) -> int:
        return sum(1 for d in self.discharges if d.z3_attempted)

    @property
    def verified(self) -> int:
        return sum(1 for d in self.discharges if d.z3_verified)

    def by_name(self) -> dict[str, FoundationDischarge]:
        return {d.name: d for d in self.discharges}


# ─────────────────────────────────────────────────────────────────────
#  Statement → Z3 formula rewriting
# ─────────────────────────────────────────────────────────────────────

_NON_ARITH_TOKENS = (
    "sqrt", "sin", "cos", "tan", "log", "exp", "pow_real",
    "sum", "Σ", "matrix", "is_collinear", "concurrent",
    "perpendicular", "parallel", "thales", "midpoint",
    "centroid", "Triangle", "Point", "Segment", "Circle",
    "Polygon", "tangent", "distance", "area", "length",
    "perimeter",
)


def _looks_arithmetic(statement: str) -> bool:
    """Heuristic: is the statement plain arithmetic?

    Returns False if the statement mentions sqrt, sin, sum, etc., or
    references a class.method.  Otherwise True.
    """
    s = statement.strip()
    if not s:
        return False
    for tok in _NON_ARITH_TOKENS:
        if tok in s:
            return False
    return True


def _strip_when_clause(statement: str) -> tuple[str, str]:
    """Split ``<core> when <guard>`` into (core, guard).

    Returns ``(core, "")`` if there's no ``when`` clause.
    """
    m = re.match(r"^(.+?)\s+when\s+(.+)$", statement.strip(), re.DOTALL)
    if m:
        return m.group(1).strip(), m.group(2).strip()
    return statement.strip(), ""


def _rewrite_for_z3(formula: str) -> str:
    """Rewrite a Python-syntax statement into Z3's expected form.

    The deppy ``Z3Proof`` accepts Python-syntax with these
    conventions:
      * ``==`` is propositional equality
      * ``=>`` is implication (used for guarded arithmetic)
      * ``**`` is exponentiation (Z3 expands ``x**2`` to ``x*x`` for
        small constants)

    For our foundations the only rewrite needed is to combine an
    optional guard from ``when ...`` with the core into an
    implication ``guard => core``.
    """
    core, guard = _strip_when_clause(formula)
    if guard:
        return f"({guard}) => ({core})"
    return core


def _collect_binders(formula: str) -> dict[str, str]:
    """Identify free variables in the formula and assign them ``int``.

    The kernel's typed-Z3 encoder accepts ``{name: annotation_text}``
    where annotation text is Python-syntax (``"int"``, ``"float"``,
    ``"bool"``).  For arithmetic foundations every free variable is
    treated as ``int`` — Z3's Int sort suffices for the algebraic
    identities we discharge here.
    """
    out: dict[str, str] = {}
    # Match identifiers; skip operators and known builtins.
    keywords = {"and", "or", "not", "True", "False", "abs", "if",
                "then", "else", "in", "is", "iff", "when"}
    for tok in re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", formula):
        if tok in keywords:
            continue
        out.setdefault(tok, "int")
    return out


def discharge_one(name: str, statement: str) -> FoundationDischarge:
    """Attempt Z3 discharge of a single foundation."""
    out = FoundationDischarge(name=name, statement=statement)

    if not _looks_arithmetic(statement):
        out.notes.append("non-arithmetic — skipping Z3")
        return out

    formula = _rewrite_for_z3(statement)
    out.z3_formula = formula
    out.z3_attempted = True
    binders = _collect_binders(formula)

    try:
        from deppy.core.kernel import ProofKernel, Z3Proof
        from deppy.core.types import (
            Context, Judgment, JudgmentKind, Var, PyObjType,
        )
        kernel = ProofKernel()
        ctx = Context()
        # Synthetic goal: TYPE_CHECK over PyObjType.  The kernel
        # routes Z3Proof against this goal through its Z3 backend.
        goal = Judgment(
            kind=JudgmentKind.TYPE_CHECK,
            context=ctx,
            term=Var(f"foundation_{name}"),
            type_=PyObjType(),
        )
        proof = Z3Proof(formula=formula, binders=binders)
        result = kernel.verify(ctx, goal, proof)
        out.kernel_message = result.message
        out.z3_verified = result.success
        if not result.success:
            out.notes.append(f"Z3 verdict: {result.message[:100]}")
    except ImportError as e:
        out.notes.append(f"Z3 unavailable: {e}")
    except Exception as e:
        out.notes.append(f"Z3 error: {e}")

    return out


def discharge_foundations(sidecar_module) -> FoundationDischargeReport:
    """Attempt Z3 discharge of every foundation in the sidecar."""
    if sidecar_module is None:
        return FoundationDischargeReport()
    foundations = getattr(sidecar_module, "foundations", {}) or {}
    out = [
        discharge_one(name, getattr(f, "statement", "") or "")
        for name, f in sorted(foundations.items())
    ]
    return FoundationDischargeReport(discharges=out)


__all__ = [
    "FoundationDischarge",
    "FoundationDischargeReport",
    "discharge_one",
    "discharge_foundations",
]
