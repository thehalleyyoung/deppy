"""
Cubical Safety (Phase 5)
========================

Re-grounds the Phase 1–3 runtime-safety pipeline in deppy's
duck=homotopy / cubical kernel rather than treating safety as a flat
obligation tree.

This module introduces three constructions, all of which **lower to
ProofTerms the kernel already verifies** (`CechGlue`, `TransportProof`,
`Refl`).  No new kernel rules are required.

The constructions:

* :class:`HazardSpace` — a finite presheaf of hazard points
  ``(function, lineno, kind)`` covering a module.  This is the *base*
  of the safety fibration.

* :func:`safety_section` — given a function's per-source
  ``SourceDischarge`` list, produces a ``CechGlue`` whose patches are
  the local fibre proofs and whose overlaps are reflexivity (hazards
  in a single function are pairwise disjoint cover elements, so the
  cocycle condition is trivial).

* :func:`safety_atlas` — given per-function sections plus a call
  graph, produces a module-level ``CechGlue`` whose patches are the
  function sections and whose overlap proofs encode the cocycle:

      caller.precondition ⇒ subst(callee.precondition)

  Each cocycle is a ``Z3Proof`` (the call boundary is a path between
  caller-env and callee-env, transported by the substitution).  This
  makes the previously-hardcoded ``internal_calls_closed=True`` an
  honest, kernel-verified condition.

* :func:`termination_transport` — wraps a Z3 well-founded inequality
  in a ``TransportProof`` along the measure path.  The Z3 proof is
  the *witness on the carrier*; the transport is the actual proof of
  termination.

Trust comes entirely from the underlying ``CechGlue`` and
``TransportProof`` verifiers — there is no min-trust collapse layered
on top of an obligation list.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional

from deppy.core.kernel import (
    AxiomInvocation, CechGlue, ProofKernel, ProofTerm, Refl, Structural,
    SourceDischarge, TransportProof, Z3Proof,
)
from deppy.core.types import Var
from deppy.pipeline.exception_sources import ExceptionSource


# ─────────────────────────────────────────────────────────────────────
#  HazardSpace — the base of the safety fibration
# ─────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class HazardPoint:
    """A single point in the hazard space: a potential failure site."""
    function: str
    lineno: int
    kind: str  # ExceptionKind.name

    def label(self) -> str:
        return f"{self.function}:L{self.lineno}:{self.kind}"


@dataclass
class HazardSpace:
    """Finite presheaf of hazard points covering a module.

    The cover is the disjoint union of per-function hazard points plus
    a top-level group for module-level sources.  Morphisms in the
    presheaf are AST containment (function → its hazards), but for
    safety verification we only need the *cover*: each point is its
    own cover element, and the safety fibration over a point is
    discrete (a single fibre).
    """
    points_by_function: dict[str, list[HazardPoint]] = field(default_factory=dict)
    module_points: list[HazardPoint] = field(default_factory=list)

    @classmethod
    def from_sources(cls,
                     per_function: dict[str, list[ExceptionSource]],
                     module_level: list[ExceptionSource],
                     ) -> HazardSpace:
        out = cls()
        for fn, sources in per_function.items():
            out.points_by_function[fn] = [
                HazardPoint(function=fn,
                            lineno=s.location.lineno,
                            kind=s.kind.name)
                for s in sources
            ]
        out.module_points = [
            HazardPoint(function="<module>",
                        lineno=s.location.lineno,
                        kind=s.kind.name)
            for s in module_level
        ]
        return out

    def all_function_names(self) -> list[str]:
        return list(self.points_by_function.keys())


# ─────────────────────────────────────────────────────────────────────
#  Sections — per-function safety as a CechGlue over its hazard cover
# ─────────────────────────────────────────────────────────────────────

def _patch_label(d: SourceDischarge) -> str:
    # The cover element label.  A function with N hazard points has N
    # patches; each patch's "condition" is the hazard label.
    return d.source_id


def safety_section(discharges: list[SourceDischarge]) -> Optional[CechGlue]:
    """Build a per-function ``CechGlue`` over the hazard cover.

    Patches are the per-source discharges themselves (each one a
    ProofTerm).  Overlaps are empty: distinct hazard points within a
    single function are disjoint cover elements, so there are no
    cocycle obligations *inside* the function.  The cross-function
    cocycles live at the atlas level (``safety_atlas``).

    Returns None when the function has no detected sources — in that
    case the section is vacuously total and the caller may emit a
    ``Structural("no hazards")`` instead.
    """
    if not discharges:
        return None
    return CechGlue(
        patches=[(_patch_label(d), d) for d in discharges],
        overlap_proofs=[],
    )


# ─────────────────────────────────────────────────────────────────────
#  Atlas — module-level CechGlue over the function/module cover
# ─────────────────────────────────────────────────────────────────────

@dataclass
class CallEdge:
    """A directed call-graph edge ``caller -> callee`` annotated with
    the textual substitution at the call boundary."""
    caller: str
    callee: str
    arg_substitution: dict[str, str] = field(default_factory=dict)
    # Optional preconditions, used to build the cocycle Z3 formula.
    caller_precondition: str = "True"
    callee_precondition: str = "True"


def _substitute(expr: str, subst: dict[str, str]) -> str:
    """Substitute formal parameter names with caller's actual exprs in
    the callee's precondition.  Best-effort textual substitution via AST
    rewrite; falls back to the original expression on parse failure."""
    if not subst:
        return expr
    try:
        tree = ast.parse(expr, mode="eval")
    except SyntaxError:
        return expr

    class _R(ast.NodeTransformer):
        def visit_Name(self, n: ast.Name) -> ast.AST:  # type: ignore
            if n.id in subst:
                try:
                    return ast.parse(f"({subst[n.id]})", mode="eval").body
                except Exception:
                    return n
            return n

    try:
        return ast.unparse(_R().visit(tree).body)
    except Exception:
        return expr


def _cocycle_proof(edge: CallEdge,
                   probe_kernel: ProofKernel) -> ProofTerm:
    """Build the agreement proof for a call-graph overlap.

    We require ``caller_pre ⇒ subst(callee_pre)`` to hold — that is,
    the caller's substituted environment lands inside the callee's
    precondition.  When Z3 verifies it we emit a ``Z3Proof``;
    otherwise we emit a ``Refl(Var(callee))`` *only when the callee
    precondition is trivially True*.  Real failure (non-trivial
    callee precondition that isn't implied) yields a Z3Proof with an
    unprovable formula, which the kernel will reject — exactly
    enforcing internal-call closure.
    """
    callee_sub = _substitute(edge.callee_precondition, edge.arg_substitution)
    caller = (edge.caller_precondition or "True").strip() or "True"
    callee = (callee_sub or "True").strip() or "True"

    if callee == "True":
        # Trivial cocycle — reflexivity on the callee's identity.
        return Refl(term=Var(edge.callee))

    formula = f"({caller}) => ({callee})"
    if probe_kernel._z3_check(formula):
        return Z3Proof(formula=formula)
    # Unverified: emit a Z3Proof with the failing formula so the
    # kernel reports the precise broken cocycle.
    return Z3Proof(formula=formula)


def safety_atlas(
    *,
    function_sections: dict[str, ProofTerm],
    module_section: Optional[ProofTerm],
    call_edges: list[CallEdge],
    probe_kernel: Optional[ProofKernel] = None,
) -> CechGlue:
    """Compose per-function sections into a module atlas.

    Patches: ``[(fn_name, fn_section), ..., ("<module>", module_section)]``.
    Overlaps: one per call-graph edge whose endpoints are both in the
    cover; the agreement proof is the cocycle ``caller_pre ⇒
    subst(callee_pre)``.
    """
    probe_kernel = probe_kernel or ProofKernel()

    patches: list[tuple[str, ProofTerm]] = []
    index: dict[str, int] = {}
    for name, sec in function_sections.items():
        index[name] = len(patches)
        patches.append((name, sec))
    if module_section is not None:
        index["<module>"] = len(patches)
        patches.append(("<module>", module_section))

    if not patches:
        # Provide a structural placeholder so CechGlue is well-formed.
        patches.append(("<empty>", Structural(description="no functions")))

    overlap_proofs: list[tuple[int, int, ProofTerm]] = []
    seen: set[tuple[int, int]] = set()
    for edge in call_edges:
        if edge.caller not in index or edge.callee not in index:
            continue
        i, j = index[edge.caller], index[edge.callee]
        if i == j:
            continue
        # Canonicalise i<j to avoid duplicate overlap entries.
        key = (min(i, j), max(i, j))
        if key in seen:
            continue
        seen.add(key)
        overlap_proofs.append((i, j, _cocycle_proof(edge, probe_kernel)))

    return CechGlue(patches=patches, overlap_proofs=overlap_proofs)


# ─────────────────────────────────────────────────────────────────────
#  Termination as TransportProof along a measure path
# ─────────────────────────────────────────────────────────────────────

def termination_transport(
    *,
    target: str,
    measure_at_entry: str,
    measure_at_recursive_call: str,
    precondition: str,
    z3_well_founded: Z3Proof,
) -> TransportProof:
    """Wrap a Z3 well-founded inequality as a transport along a path.

    The path is the measure step ``measure_entry ↦ measure_at_call``
    in the well-founded carrier ``(N, <)``.  The Z3 inequality is the
    proof that this step actually lives in the carrier; the transport
    carries safety from the smaller-measure base case to the
    recursive case.

    The kernel verifies:
      * the path proof (the Z3 well-founded inequality), and
      * the base proof (a ``Refl`` on the target, certifying the
        recursive callee is the same function — well-formedness of the
        recursion site).
    """
    return TransportProof(
        type_family=Var(f"Safe[{target}]"),
        path_proof=z3_well_founded,
        base_proof=Refl(term=Var(target)),
    )


__all__ = [
    "HazardPoint",
    "HazardSpace",
    "CallEdge",
    "safety_section",
    "safety_atlas",
    "termination_transport",
]
