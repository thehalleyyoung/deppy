"""Generic, library-agnostic derivation of Lean proof bodies for
sidecar proofs.

Given a :class:`deppy.proofs.sidecar.SidecarModule`, this module
inspects each :class:`ProofDecl`'s ``by_clause`` and emits a *real*
Lean proof body.  None of the logic here is sympy-specific: the same
infrastructure handles any library that uses the same ``.deppy``
proof DSL.

The trust chain
---------------

The certificate distinguishes three classes of declarations:

  1. **Foundations** (``foundation NAME: "..."``) — generic
     mathematical facts that we admit without further justification
     (e.g., ``sqrt(x)**2 == x`` for ``x ≥ 0``, ``a + b == b + a``).
     Foundations are the *trust surface*: every theorem ultimately
     reduces to one of them.

  2. **Sidecar axioms** (``axiom NAME: "..."`` inside a ``spec``) —
     claims about specific library functions.  An axiom is admitted
     directly when no derivation is supplied.

  3. **Sidecar proofs** (``proof NAME:`` with a non-trivial ``by:``
     clause) — claims that *derive* from foundations and/or axioms.
     The proof body is a real Lean term (Eq.trans / And.intro / rfl /
     Foundation_F.symm.trans), checked by Lean's kernel.  These are
     not citations of axioms with the identical statement.

Recognised ``by:`` forms (also see :func:`emit_proof_body`):

  * ``axiom <NAME>``                            → ``Sidecar_NAME``
  * ``foundation <NAME>``                       → ``Foundation_NAME``
  * ``refl``                                    → ``rfl``
  * ``chain <X1>, <X2>, ...``                   → ``Eq.trans (...) ...``
  * ``composition <X1> & <X2>``                 → ``⟨..., ...⟩``
  * ``rewrite <F> then cite <A>``               → ``Foundation_F.symm.trans Sidecar_A``

Each form emits a proof body that the Lean kernel actually
type-checks against the theorem's stated proposition.  When a form
is not recognised, the body is ``sorry`` (honest non-discharge).

Use of the cubical / cohomological proof theory
-----------------------------------------------

This module *registers* each proof in the ProofClassification:

  * ``CITES_AXIOM``   — proof body is the axiom itself (renaming)
  * ``CITES_FOUNDATION`` — body is a foundation (genuine derivation
    from the trust surface, not from another axiom)
  * ``CHAIN``         — transitive composition (real algebra)
  * ``COMPOSITION``   — conjunction (And.intro of multiple axioms)
  * ``REWRITE_THEN_CITE`` — rewrite + cite (real chain through a
    foundation)
  * ``REFL``          — definitional equality (Lean checks)
  * ``UNRECOGNISED``  — sorry, honestly admitted

The honest accounting from :func:`derive_all` reports counts of each
class so the user can see at a glance which proofs are real
derivations versus axiom restatements.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from enum import Enum


class ProofClassification(Enum):
    CITES_AXIOM = "CITES_AXIOM"
    CITES_FOUNDATION = "CITES_FOUNDATION"
    CHAIN = "CHAIN"
    COMPOSITION = "COMPOSITION"
    REWRITE_THEN_CITE = "REWRITE_THEN_CITE"
    REFL = "REFL"
    UNRECOGNISED = "UNRECOGNISED"


@dataclass
class DerivationResult:
    """Result of deriving a Lean proof body for a single ProofDecl."""
    proof_name: str
    target_name: str
    claim: str
    by_clause: str
    classification: ProofClassification
    lean_body: str          # the proof term, e.g. ``Sidecar_X`` / ``rfl``
    cites_axioms: list[str] = field(default_factory=list)
    cites_foundations: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    @property
    def is_genuinely_derived(self) -> bool:
        """True when the proof body does more than rename an axiom."""
        return self.classification not in (
            ProofClassification.CITES_AXIOM,
            ProofClassification.UNRECOGNISED,
        )


@dataclass
class DerivationReport:
    """Aggregate result of deriving every proof in a sidecar module."""
    results: list[DerivationResult] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.results)

    @property
    def derived_count(self) -> int:
        return sum(1 for r in self.results if r.is_genuinely_derived)

    @property
    def cited_count(self) -> int:
        return sum(
            1 for r in self.results
            if r.classification == ProofClassification.CITES_AXIOM
        )

    @property
    def unrecognised_count(self) -> int:
        return sum(
            1 for r in self.results
            if r.classification == ProofClassification.UNRECOGNISED
        )

    def by_classification(self) -> dict[ProofClassification, int]:
        out: dict[ProofClassification, int] = {}
        for r in self.results:
            out[r.classification] = out.get(r.classification, 0) + 1
        return out


# ─────────────────────────────────────────────────────────────────────
#  Identifier sanitisation (mirrors sidecar_certificate.py)
# ─────────────────────────────────────────────────────────────────────

def _safe_ident(text: str) -> str:
    out = []
    for ch in text or "":
        if ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append("_")
    s = "".join(out) or "anon"
    if s[0].isdigit():
        s = "i" + s
    s = re.sub(r"_+", "_", s)
    return s.strip("_") or "anon"


def _axiom_ident(name: str) -> str:
    return "Sidecar_" + _safe_ident(name)


def _foundation_ident(name: str) -> str:
    return "Foundation_" + _safe_ident(name)


# ─────────────────────────────────────────────────────────────────────
#  Per-proof derivation
# ─────────────────────────────────────────────────────────────────────

def derive_one(
    pdecl,
    *,
    axioms: dict,
    foundations: dict,
) -> DerivationResult:
    """Derive a Lean proof body for a single ProofDecl.

    ``axioms`` is the SidecarModule's axiom map (name → AxiomDecl).
    ``foundations`` is the foundation map (name → FoundationDecl).
    """
    claim = getattr(pdecl, "claim", "") or ""
    by_clause = (getattr(pdecl, "by_clause", "") or "").strip()
    target = getattr(pdecl, "target_name", "") or ""

    # Form: ``foundation <NAME>``
    fname = getattr(pdecl, "foundation_name", "") or ""
    if fname:
        if fname not in foundations:
            return DerivationResult(
                proof_name=claim,
                target_name=target,
                claim=claim,
                by_clause=by_clause,
                classification=ProofClassification.UNRECOGNISED,
                lean_body="sorry",
                notes=[f"foundation '{fname}' not declared"],
            )
        return DerivationResult(
            proof_name=claim,
            target_name=target,
            claim=claim,
            by_clause=by_clause,
            classification=ProofClassification.CITES_FOUNDATION,
            lean_body=_foundation_ident(fname),
            cites_foundations=[fname],
        )

    # Form: ``chain <X1>, <X2>, ...``  — transitive composition.
    chain = list(getattr(pdecl, "chain_axioms", []) or [])
    if chain and by_clause.startswith("chain "):
        unknown = [
            x for x in chain
            if x not in axioms and x not in foundations
        ]
        if unknown:
            return DerivationResult(
                proof_name=claim,
                target_name=target,
                claim=claim,
                by_clause=by_clause,
                classification=ProofClassification.UNRECOGNISED,
                lean_body="sorry",
                notes=[f"chain references undeclared: {unknown}"],
            )
        idents = [
            _foundation_ident(x) if x in foundations else _axiom_ident(x)
            for x in chain
        ]
        # Eq.trans is left-associative: (((t1 t2) t3) t4)...
        body = idents[0]
        for nxt in idents[1:]:
            body = f"(Eq.trans {body} {nxt})"
        return DerivationResult(
            proof_name=claim,
            target_name=target,
            claim=claim,
            by_clause=by_clause,
            classification=ProofClassification.CHAIN,
            lean_body=body,
            cites_axioms=[x for x in chain if x in axioms],
            cites_foundations=[x for x in chain if x in foundations],
        )

    # Form: ``composition <X1> & <X2> & ...`` — conjunction.
    if chain and by_clause.startswith("composition "):
        unknown = [
            x for x in chain
            if x not in axioms and x not in foundations
        ]
        if unknown:
            return DerivationResult(
                proof_name=claim,
                target_name=target,
                claim=claim,
                by_clause=by_clause,
                classification=ProofClassification.UNRECOGNISED,
                lean_body="sorry",
                notes=[f"composition references undeclared: {unknown}"],
            )
        idents = [
            _foundation_ident(x) if x in foundations else _axiom_ident(x)
            for x in chain
        ]
        # And.intro is right-associative for >2: ⟨a, b, c⟩ ≡ ⟨a, ⟨b, c⟩⟩
        body = "⟨" + ", ".join(idents) + "⟩"
        return DerivationResult(
            proof_name=claim,
            target_name=target,
            claim=claim,
            by_clause=by_clause,
            classification=ProofClassification.COMPOSITION,
            lean_body=body,
            cites_axioms=[x for x in chain if x in axioms],
            cites_foundations=[x for x in chain if x in foundations],
        )

    # Form: ``rewrite <F> then cite <A>``.
    rw_with = getattr(pdecl, "rewrite_with", "") or ""
    rw_then = getattr(pdecl, "rewrite_then_cite", "") or ""
    if rw_with and rw_then:
        if rw_with not in foundations:
            return DerivationResult(
                proof_name=claim,
                target_name=target,
                claim=claim,
                by_clause=by_clause,
                classification=ProofClassification.UNRECOGNISED,
                lean_body="sorry",
                notes=[f"rewrite foundation '{rw_with}' not declared"],
            )
        if rw_then not in axioms and rw_then not in foundations:
            return DerivationResult(
                proof_name=claim,
                target_name=target,
                claim=claim,
                by_clause=by_clause,
                classification=ProofClassification.UNRECOGNISED,
                lean_body="sorry",
                notes=[f"rewrite cite '{rw_then}' not declared"],
            )
        f_id = _foundation_ident(rw_with)
        a_id = (
            _foundation_ident(rw_then) if rw_then in foundations
            else _axiom_ident(rw_then)
        )
        body = f"({f_id}.symm.trans {a_id})"
        return DerivationResult(
            proof_name=claim,
            target_name=target,
            claim=claim,
            by_clause=by_clause,
            classification=ProofClassification.REWRITE_THEN_CITE,
            lean_body=body,
            cites_axioms=([rw_then] if rw_then in axioms else []),
            cites_foundations=(
                [rw_with] + ([rw_then] if rw_then in foundations else [])
            ),
        )

    # Form: ``refl``.
    if by_clause == "refl":
        return DerivationResult(
            proof_name=claim,
            target_name=target,
            claim=claim,
            by_clause=by_clause,
            classification=ProofClassification.REFL,
            lean_body="rfl",
        )

    # Form: ``axiom <NAME>``  (citation form — renaming).
    ax_name = getattr(pdecl, "axiom_name", "") or ""
    if ax_name:
        if ax_name not in axioms:
            return DerivationResult(
                proof_name=claim,
                target_name=target,
                claim=claim,
                by_clause=by_clause,
                classification=ProofClassification.UNRECOGNISED,
                lean_body="sorry",
                notes=[f"axiom '{ax_name}' not declared"],
            )
        return DerivationResult(
            proof_name=claim,
            target_name=target,
            claim=claim,
            by_clause=by_clause,
            classification=ProofClassification.CITES_AXIOM,
            lean_body=_axiom_ident(ax_name),
            cites_axioms=[ax_name],
            notes=["renaming: theorem statement equals axiom statement"],
        )

    # Unrecognised form.
    return DerivationResult(
        proof_name=claim,
        target_name=target,
        claim=claim,
        by_clause=by_clause,
        classification=ProofClassification.UNRECOGNISED,
        lean_body="sorry",
        notes=[f"unrecognised by-clause: {by_clause!r}"],
    )


def derive_all(sidecar_module) -> DerivationReport:
    """Derive proof bodies for every proof in a sidecar module."""
    if sidecar_module is None:
        return DerivationReport()
    axioms = getattr(sidecar_module, "axioms", {}) or {}
    foundations = getattr(sidecar_module, "foundations", {}) or {}
    proofs = getattr(sidecar_module, "proofs", []) or []
    out: list[DerivationResult] = []
    for pd in proofs:
        out.append(derive_one(pd, axioms=axioms, foundations=foundations))
    return DerivationReport(results=out)


__all__ = [
    "ProofClassification",
    "DerivationResult",
    "DerivationReport",
    "derive_one",
    "derive_all",
]
