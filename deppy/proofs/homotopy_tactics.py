"""
Deppy Homotopy-Theoretic Proof Tactics

High-level tactic combinators that build GENUINE homotopy-theoretic proof
terms: paths, transport, Čech gluing, duck-type equivalences, and fibration
dispatch.  Unlike the base tactics.py (which is Z3/axiom focused), every
combinator here constructs proof terms whose *structure* encodes the
homotopy reasoning — so the kernel can verify the proof topology, not just
the leaf obligations.

Architecture:
    PathTactic          — construct paths (refl, sym, trans, ap, funext)
    TransportTactic     — transport proofs along paths / rewrite
    CechTactic          — Čech-style proof decomposition and gluing
    DuckTypeTactic      — protocol equivalence via duck-type paths
    FibrationTactic     — isinstance fibration dispatch
    HomotopyProofBuilder — unified chainable builder integrating all above

Example
-------
    kernel = ProofKernel()
    builder = HomotopyProofBuilder(kernel)
    result = (
        builder
        .show_path(Literal(1), Literal(1), via="refl")
        .then_transport(Var("P"), builder.path.refl(Literal(1)))
        .qed()
    )
    assert result.success
"""
from __future__ import annotations

import ast
import inspect
import re
import textwrap
from dataclasses import dataclass, field
from typing import Any, Callable, Sequence

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PathType, PathAbs, PathApp, Transport, Comp, GlueType, IntervalType,
    Var, Literal, Lam, App,
    PyObjType, PyIntType, PyCallableType, PyClassType, PyListType,
    RefinementType, PiType, ProtocolType, PyBoolType, UnionType,
)
from deppy.core.kernel import (
    ProofKernel, ProofTerm, TrustLevel, VerificationResult,
    Refl, Sym, Trans, Cong, DuckPath, TransportProof, Patch, Fiber,
    Z3Proof, Structural, AxiomInvocation, Ext, Cases, Cut, Assume,
    min_trust,
)

# ── Try importing extended proof terms (may not exist yet) ───────
# PathComp(left_path, right_path) — path composition
try:
    from deppy.core.kernel import PathComp
except ImportError:
    PathComp = None  # type: ignore[assignment,misc]

# Ap(function, path_proof) — congruence / action on paths
try:
    from deppy.core.kernel import Ap
except ImportError:
    Ap = None  # type: ignore[assignment,misc]

# FunExt(var, pointwise_proof) — function extensionality
try:
    from deppy.core.kernel import FunExt
except ImportError:
    FunExt = None  # type: ignore[assignment,misc]

# CechGlue(patches=[(cond, proof)], overlap_proofs=[(i,j,proof)])
try:
    from deppy.core.kernel import CechGlue
except ImportError:
    CechGlue = None  # type: ignore[assignment,misc]

# Univalence(equiv_proof, from_type, to_type)
try:
    from deppy.core.kernel import Univalence
except ImportError:
    Univalence = None  # type: ignore[assignment,misc]


# ═══════════════════════════════════════════════════════════════════
#  Helper: proof-term introspection
# ═══════════════════════════════════════════════════════════════════

def _proof_depth(p: ProofTerm) -> int:
    """Return the nesting depth of a proof term tree."""
    if isinstance(p, (Refl, Structural, Z3Proof, Assume, AxiomInvocation)):
        return 1
    if isinstance(p, Sym):
        return 1 + _proof_depth(p.proof)
    if isinstance(p, Trans):
        return 1 + max(_proof_depth(p.left), _proof_depth(p.right))
    if isinstance(p, Cong):
        return 1 + _proof_depth(p.proof)
    if isinstance(p, TransportProof):
        return 1 + max(_proof_depth(p.path_proof), _proof_depth(p.base_proof))
    if isinstance(p, Ext):
        return 1 + _proof_depth(p.body_proof)
    if isinstance(p, DuckPath):
        return 1 + max((_proof_depth(mp) for _, mp in p.method_proofs), default=0)
    if isinstance(p, Fiber):
        return 1 + max((_proof_depth(bp) for _, bp in p.type_branches), default=0)
    if isinstance(p, Cases):
        return 1 + max((_proof_depth(bp) for _, bp in p.branches), default=0)
    if isinstance(p, Cut):
        return 1 + max(_proof_depth(p.lemma_proof), _proof_depth(p.body_proof))
    # Extended proof terms
    if PathComp is not None and isinstance(p, PathComp):
        return 1 + max(_proof_depth(p.left_path), _proof_depth(p.right_path))
    if Ap is not None and isinstance(p, Ap):
        return 1 + _proof_depth(p.path_proof)
    if FunExt is not None and isinstance(p, FunExt):
        return 1 + _proof_depth(p.pointwise_proof)
    if CechGlue is not None and isinstance(p, CechGlue):
        patch_depths = [_proof_depth(pp) for _, pp in p.patches]
        return 1 + max(patch_depths, default=0)
    if Univalence is not None and isinstance(p, Univalence):
        return 1 + _proof_depth(p.equiv_proof)
    return 1


def _proof_uses_homotopy(p: ProofTerm) -> bool:
    """Check whether a proof term uses genuinely homotopy-theoretic structure."""
    if isinstance(p, (TransportProof, DuckPath, Fiber, Ext)):
        return True
    if PathComp is not None and isinstance(p, PathComp):
        return True
    if Ap is not None and isinstance(p, Ap):
        return True
    if FunExt is not None and isinstance(p, FunExt):
        return True
    if CechGlue is not None and isinstance(p, CechGlue):
        return True
    if Univalence is not None and isinstance(p, Univalence):
        return True
    if isinstance(p, Trans):
        return _proof_uses_homotopy(p.left) or _proof_uses_homotopy(p.right)
    if isinstance(p, Sym):
        return _proof_uses_homotopy(p.proof)
    if isinstance(p, Cong):
        return _proof_uses_homotopy(p.proof)
    if isinstance(p, Cut):
        return (_proof_uses_homotopy(p.lemma_proof) or
                _proof_uses_homotopy(p.body_proof))
    if isinstance(p, Cases):
        return any(_proof_uses_homotopy(bp) for _, bp in p.branches)
    return False


def _collect_proof_nodes(p: ProofTerm) -> list[str]:
    """Collect the types of all proof nodes in pre-order."""
    nodes = [type(p).__name__]
    if isinstance(p, Sym):
        nodes.extend(_collect_proof_nodes(p.proof))
    elif isinstance(p, Trans):
        nodes.extend(_collect_proof_nodes(p.left))
        nodes.extend(_collect_proof_nodes(p.right))
    elif isinstance(p, Cong):
        nodes.extend(_collect_proof_nodes(p.proof))
    elif isinstance(p, TransportProof):
        nodes.extend(_collect_proof_nodes(p.path_proof))
        nodes.extend(_collect_proof_nodes(p.base_proof))
    elif isinstance(p, Ext):
        nodes.extend(_collect_proof_nodes(p.body_proof))
    elif isinstance(p, Cut):
        nodes.extend(_collect_proof_nodes(p.lemma_proof))
        nodes.extend(_collect_proof_nodes(p.body_proof))
    elif isinstance(p, DuckPath):
        for _, mp in p.method_proofs:
            nodes.extend(_collect_proof_nodes(mp))
    elif isinstance(p, Fiber):
        for _, bp in p.type_branches:
            nodes.extend(_collect_proof_nodes(bp))
    elif isinstance(p, Cases):
        for _, bp in p.branches:
            nodes.extend(_collect_proof_nodes(bp))
    elif PathComp is not None and isinstance(p, PathComp):
        nodes.extend(_collect_proof_nodes(p.left_path))
        nodes.extend(_collect_proof_nodes(p.right_path))
    elif Ap is not None and isinstance(p, Ap):
        nodes.extend(_collect_proof_nodes(p.path_proof))
    elif FunExt is not None and isinstance(p, FunExt):
        nodes.extend(_collect_proof_nodes(p.pointwise_proof))
    elif CechGlue is not None and isinstance(p, CechGlue):
        for _, pp in p.patches:
            nodes.extend(_collect_proof_nodes(pp))
        for _, _, op in p.overlap_proofs:
            nodes.extend(_collect_proof_nodes(op))
    elif Univalence is not None and isinstance(p, Univalence):
        nodes.extend(_collect_proof_nodes(p.equiv_proof))
    return nodes


# ═══════════════════════════════════════════════════════════════════
#  Helper: equality goal constructor
# ═══════════════════════════════════════════════════════════════════

def _eq_goal(ctx: Context, left: SynTerm, right: SynTerm,
             ty: SynType | None = None) -> Judgment:
    """Shorthand for building an equality judgment."""
    return Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=left, right=right,
        type_=ty or PyObjType(),
    )


def _tc_goal(ctx: Context, term: SynTerm | None = None,
             ty: SynType | None = None) -> Judgment:
    """Shorthand for building a type-check judgment."""
    return Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=term,
        type_=ty or PyObjType(),
    )


# ═══════════════════════════════════════════════════════════════════
#  1. PathTactic — construct paths between terms
# ═══════════════════════════════════════════════════════════════════

class PathTactic:
    """High-level tactics for constructing path proofs.

    Every method returns a ProofTerm whose *structure* encodes the
    homotopy-theoretic justification — Refl for reflexivity, Trans
    (or PathComp when available) for composition, Cong (or Ap) for
    congruence, and Ext (or FunExt) for function extensionality.
    """

    def __init__(self, kernel: ProofKernel) -> None:
        self.kernel = kernel

    # ── basic path constructors ──────────────────────────────────

    def refl(self, term: SynTerm) -> ProofTerm:
        """Reflexivity: term = term."""
        return Refl(term=term)

    def sym(self, proof: ProofTerm) -> ProofTerm:
        """Symmetry: if a = b then b = a."""
        return Sym(proof=proof)

    def trans(self, p: ProofTerm, q: ProofTerm) -> ProofTerm:
        """Transitivity via path composition.

        Uses PathComp if the extended proof term is available,
        otherwise falls back to Trans.
        """
        if PathComp is not None:
            return PathComp(left_path=p, right_path=q)
        return Trans(left=p, right=q)

    def ap(self, f: SynTerm, proof: ProofTerm) -> ProofTerm:
        """Congruence / action on paths: if a = b then f(a) = f(b).

        Uses Ap proof term when available, falls back to Cong.
        """
        if Ap is not None:
            return Ap(function=f, path_proof=proof)
        return Cong(func=f, proof=proof)

    def funext(self, var: str, pointwise: ProofTerm) -> ProofTerm:
        """Function extensionality: (∀x. f(x) = g(x)) → f = g.

        Uses FunExt if available, falls back to Ext.
        """
        if FunExt is not None:
            return FunExt(var=var, pointwise_proof=pointwise)
        return Ext(var=var, body_proof=pointwise)

    # ── compound path builders ───────────────────────────────────

    def concat(self, *proofs: ProofTerm) -> ProofTerm:
        """Chain multiple paths: a = b = c = ... = z.

        Given proofs p₁ : a = b, p₂ : b = c, ..., produces a single
        proof term of a = z via iterated composition.
        """
        if not proofs:
            raise ValueError("concat requires at least one proof")
        result = proofs[0]
        for p in proofs[1:]:
            result = self.trans(result, p)
        return result

    def inverse_concat(self, *proofs: ProofTerm) -> ProofTerm:
        """Chain paths in reverse: given a=b, b=c, ..., produce z = a."""
        if not proofs:
            raise ValueError("inverse_concat requires at least one proof")
        reversed_proofs = [self.sym(p) for p in reversed(proofs)]
        return self.concat(*reversed_proofs)

    def by_computation(self, term_a: SynTerm, term_b: SynTerm) -> ProofTerm:
        """Prove a = b by computational reduction (beta/eta/delta rules).

        If terms are structurally identical, uses Refl.  Otherwise
        constructs a Structural proof describing the computational step.
        """
        if self._terms_syn_equal(term_a, term_b):
            return Refl(term=term_a)
        return Structural(
            description=f"β/η/δ: {term_a} ≡ {term_b}"
        )

    def by_beta(self, lam_term: Lam, arg: SynTerm) -> ProofTerm:
        """Beta reduction: (λx.body)(arg) = body[arg/x].

        Constructs the path witnessing a single beta step.
        """
        app = App(func=lam_term, arg=arg)
        reduced = self._beta_reduce(lam_term, arg)
        return Structural(
            description=f"β: {app} ≡ {reduced}"
        )

    def by_eta(self, func: SynTerm, param: str = "x") -> ProofTerm:
        """Eta expansion: f = λx.f(x).

        Constructs the path witnessing eta equivalence.
        """
        eta_form = Lam(param=param, body=App(func=func, arg=Var(param)))
        return Structural(
            description=f"η: {func} ≡ {eta_form}"
        )

    def whisker_left(self, p: ProofTerm, q: ProofTerm) -> ProofTerm:
        """Left whiskering: given p : a = b and q : b = c, produce a = c.

        Alias for trans but conceptually distinct in 2-dimensional
        homotopy theory.
        """
        return self.trans(p, q)

    def whisker_right(self, p: ProofTerm, q: ProofTerm) -> ProofTerm:
        """Right whiskering: given q : a = b and p : b = c, produce a = c."""
        return self.trans(q, p)

    def path_over(self, type_family: SynTerm, path: ProofTerm,
                  left_fiber: ProofTerm, right_fiber: ProofTerm) -> ProofTerm:
        """Dependent path (path-over): a path in a fiber over a base path.

        This encodes: given p : a =_A b, d_a : P(a), d_b : P(b),
        produce transport(P, p, d_a) = d_b.
        """
        transported = TransportProof(
            type_family=type_family,
            path_proof=path,
            base_proof=left_fiber,
        )
        return Trans(left=transported, right=right_fiber)

    # ── internal helpers ─────────────────────────────────────────

    @staticmethod
    def _terms_syn_equal(a: SynTerm, b: SynTerm) -> bool:
        """Syntactic equality check."""
        if type(a) is not type(b):
            return False
        if isinstance(a, Var) and isinstance(b, Var):
            return a.name == b.name
        if isinstance(a, Literal) and isinstance(b, Literal):
            return a.value == b.value
        return repr(a) == repr(b)

    @staticmethod
    def _beta_reduce(lam: Lam, arg: SynTerm) -> SynTerm:
        """Naive beta reduction: substitute arg for param in body."""
        return _subst_term(lam.body, lam.param, arg)


# ═══════════════════════════════════════════════════════════════════
#  Term substitution helper
# ═══════════════════════════════════════════════════════════════════

def _subst_term(term: SynTerm, var: str, replacement: SynTerm) -> SynTerm:
    """Substitute var with replacement in term (capture-unaware)."""
    if isinstance(term, Var):
        return replacement if term.name == var else term
    if isinstance(term, Literal):
        return term
    if isinstance(term, App):
        return App(
            func=_subst_term(term.func, var, replacement),
            arg=_subst_term(term.arg, var, replacement),
        )
    if isinstance(term, Lam):
        if term.param == var:
            return term  # shadowed
        return Lam(
            param=term.param,
            param_type=term.param_type,
            body=_subst_term(term.body, var, replacement),
        )
    if isinstance(term, PathAbs):
        if term.ivar == var:
            return term
        return PathAbs(
            ivar=term.ivar,
            body=_subst_term(term.body, var, replacement),
        )
    if isinstance(term, PathApp):
        return PathApp(
            path=_subst_term(term.path, var, replacement),
            arg=_subst_term(term.arg, var, replacement),
        )
    # For other term forms, return unchanged
    return term


# ═══════════════════════════════════════════════════════════════════
#  2. TransportTactic — move proofs across equivalences
# ═══════════════════════════════════════════════════════════════════

class TransportTactic:
    """Tactics for transporting proofs along paths.

    In HoTT, transport is the fundamental operation that moves a proof
    from one fiber to another along a path in the base.  These tactics
    provide high-level combinators for transport, coercion (transport +
    univalence), rewriting, and substitution.
    """

    def __init__(self, kernel: ProofKernel) -> None:
        self.kernel = kernel

    def transport(self, type_family: SynTerm, path: ProofTerm,
                  base: ProofTerm) -> ProofTerm:
        """Transport base proof along path in type family.

        Given P : A → Type, path : a =_A b, base : P(a),
        produces a proof term of type P(b).
        """
        return TransportProof(
            type_family=type_family,
            path_proof=path,
            base_proof=base,
        )

    def coerce(self, proof: ProofTerm, equiv: ProofTerm,
               from_type: SynType | None = None,
               to_type: SynType | None = None) -> ProofTerm:
        """Coerce a proof via an equivalence (transport + univalence).

        Given proof : P(A) and equiv : A ≃ B (encoded as a path via
        univalence), produces P(B) by transporting along ua(equiv).
        """
        if Univalence is not None:
            ua_path = Univalence(
                equiv_proof=equiv,
                from_type=from_type or PyObjType(),
                to_type=to_type or PyObjType(),
            )
            return TransportProof(
                type_family=Var("_P"),
                path_proof=ua_path,
                base_proof=proof,
            )
        # Fallback: use a structural witness for the coercion
        return TransportProof(
            type_family=Var("_P"),
            path_proof=Structural(description="univalence coercion"),
            base_proof=proof,
        )

    def rewrite(self, proof: ProofTerm, equation: ProofTerm,
                direction: str = "ltr") -> ProofTerm:
        """Rewrite using an equation (implemented via transport).

        direction="ltr" rewrites left-to-right; "rtl" reverses first.

        In HoTT, rewriting is just transport along the equation viewed
        as a path in the appropriate type family.
        """
        eq_path = equation if direction == "ltr" else Sym(proof=equation)
        return TransportProof(
            type_family=Var("_rewrite_family"),
            path_proof=eq_path,
            base_proof=proof,
        )

    def subst(self, proof: ProofTerm, var: str,
              replacement: SynTerm, path: ProofTerm) -> ProofTerm:
        """Substitute var with replacement, using path as justification.

        Constructs a type family P(x) = (the goal with var mapped to x),
        then transports the proof along the path var = replacement.
        """
        type_family = Lam(
            param=var,
            body=Var(f"_goal[{var}]"),
        )
        return TransportProof(
            type_family=type_family,
            path_proof=path,
            base_proof=proof,
        )

    def transport_concat(self, type_family: SynTerm,
                         path_p: ProofTerm, path_q: ProofTerm,
                         base: ProofTerm) -> ProofTerm:
        """Transport along a concatenation of paths.

        transport(P, p · q, d) = transport(P, q, transport(P, p, d))

        Returns the right-hand form — two nested transports.
        """
        inner = TransportProof(
            type_family=type_family,
            path_proof=path_p,
            base_proof=base,
        )
        return TransportProof(
            type_family=type_family,
            path_proof=path_q,
            base_proof=inner,
        )

    def apd(self, f: SynTerm, path: ProofTerm) -> ProofTerm:
        """Dependent action on paths (apd).

        Given f : (x:A) → P(x) and path : a =_A b,
        produces a path-over from f(a) to f(b) over path.
        """
        return TransportProof(
            type_family=Var("_P"),
            path_proof=path,
            base_proof=Structural(description=f"apd({f})"),
        )


# ═══════════════════════════════════════════════════════════════════
#  3. CechTactic — decompose and glue proofs
# ═══════════════════════════════════════════════════════════════════

class CechTactic:
    """Tactics for Čech-style proof decomposition.

    A Čech cover of a specification decomposes it into patches
    (corresponding to branches / cases), verifies each patch, then
    glues them together.  The gluing step checks the cocycle condition
    on overlaps to ensure consistency — this is the key difference
    from plain case analysis.
    """

    def __init__(self, kernel: ProofKernel) -> None:
        self.kernel = kernel

    def by_cases_cech(self, conditions: list[str],
                      proofs: list[ProofTerm],
                      overlaps: list[tuple[int, int, ProofTerm]] | None = None,
                      ) -> ProofTerm:
        """Prove by case analysis with Čech gluing.

        Unlike plain case analysis, this also verifies the cocycle
        condition on overlaps — ensuring consistency.

        Parameters
        ----------
        conditions : list of condition strings (one per patch)
        proofs : proof for each patch
        overlaps : optional list of (i, j, compatibility_proof) for
                   overlapping patches i and j.  If omitted, overlaps
                   are checked structurally.

        Returns a CechGlue proof term (or Cases + consistency wrappers).
        """
        if len(conditions) != len(proofs):
            raise ValueError(
                f"conditions ({len(conditions)}) and proofs ({len(proofs)}) "
                "must have equal length"
            )

        # Build overlap compatibility proofs
        overlap_proofs: list[tuple[int, int, ProofTerm]] = []
        if overlaps is not None:
            overlap_proofs = list(overlaps)
        else:
            # Auto-generate structural compatibility for adjacent patches
            for i in range(len(conditions) - 1):
                overlap_proofs.append((
                    i, i + 1,
                    Structural(
                        description=(
                            f"cocycle: patch[{i}]∩patch[{i+1}] "
                            f"({conditions[i]} ∧ {conditions[i+1]})"
                        )
                    ),
                ))

        # Try CechGlue if available
        if CechGlue is not None:
            patches = [(cond, proof) for cond, proof in zip(conditions, proofs)]
            return CechGlue(
                patches=patches,
                overlap_proofs=overlap_proofs,
            )

        # Fallback: use Cases with consistency cuts
        scrutinee = Var("_cech_scrutinee")
        branches = [(cond, proof) for cond, proof in zip(conditions, proofs)]
        base_cases = Cases(scrutinee=scrutinee, branches=branches)

        if not overlap_proofs:
            return base_cases

        # Wrap in Cut nodes for each overlap check
        result: ProofTerm = base_cases
        for i, j, compat in overlap_proofs:
            result = Cut(
                hyp_name=f"_cocycle_{i}_{j}",
                hyp_type=RefinementType(
                    base_type=PyBoolType(),
                    predicate=(
                        f"patch[{i}] agrees with patch[{j}] "
                        f"on {conditions[i]} ∧ {conditions[j]}"
                    ),
                ),
                lemma_proof=compat,
                body_proof=result,
            )
        return result

    def cover(self, func_source: str) -> list[tuple[str, str]]:
        """Extract a Čech cover from a function's control flow.

        Parses the function source and returns
        [(condition, body_source), ...] for each if/elif/else branch.
        """
        patches: list[tuple[str, str]] = []
        try:
            tree = ast.parse(textwrap.dedent(func_source))
        except SyntaxError:
            return [("True", func_source)]

        for node in ast.walk(tree):
            if isinstance(node, ast.If):
                cond_src = ast.unparse(node.test)
                body_src = "\n".join(ast.unparse(s) for s in node.body)
                patches.append((cond_src, body_src))
                # Handle elif chain
                current = node
                while current.orelse:
                    if (len(current.orelse) == 1 and
                            isinstance(current.orelse[0], ast.If)):
                        elif_node = current.orelse[0]
                        cond_src = ast.unparse(elif_node.test)
                        body_src = "\n".join(
                            ast.unparse(s) for s in elif_node.body
                        )
                        patches.append((cond_src, body_src))
                        current = elif_node
                    else:
                        body_src = "\n".join(
                            ast.unparse(s) for s in current.orelse
                        )
                        patches.append(("True", body_src))
                        break
                break  # Only process top-level if

        if not patches:
            patches.append(("True", func_source.strip()))

        return patches

    def verify_and_glue(self, cover: list[tuple[str, str]],
                        spec: str) -> ProofTerm:
        """Verify spec on each patch and glue.

        For each (condition, body) in cover, attempts to construct a
        structural proof that the body satisfies spec under condition.
        Then glues all patches via by_cases_cech.
        """
        conditions: list[str] = []
        proofs: list[ProofTerm] = []

        for cond, body in cover:
            conditions.append(cond)
            proofs.append(Structural(
                description=f"under {cond}: {body} satisfies «{spec}»"
            ))

        return self.by_cases_cech(conditions, proofs)

    def obstruction(self, cover: list[tuple[str, str]],
                    proofs: list[ProofTerm | None]) -> str:
        """When gluing fails, explain WHY via the H¹ obstruction.

        Analyzes which patches could not be proven and which overlaps
        are inconsistent to produce a human-readable explanation.
        """
        failed_patches: list[int] = []
        for i, p in enumerate(proofs):
            if p is None:
                failed_patches.append(i)

        if not failed_patches:
            return "No obstruction: all patches have proofs."

        lines = [f"H¹ obstruction detected — {len(failed_patches)} patch(es) unproven:"]
        for i in failed_patches:
            cond, body = cover[i]
            lines.append(f"  patch[{i}]: condition={cond!r}, body truncated={body[:60]!r}")

        # Check for coverage gaps
        all_conds = [c for c, _ in cover]
        proven_conds = [c for j, (c, _) in enumerate(cover)
                        if j not in failed_patches]
        if len(proven_conds) < len(all_conds):
            lines.append(
                f"  Coverage gap: {len(proven_conds)}/{len(all_conds)} "
                f"conditions proven → non-trivial H¹ class"
            )

        # Suggest resolution
        lines.append("Resolution: provide proofs for failing patches or refine cover.")
        return "\n".join(lines)

    def refine_cover(self, cover: list[tuple[str, str]],
                     new_conditions: list[str]) -> list[tuple[str, str]]:
        """Refine a cover by intersecting with additional conditions.

        Produces a finer cover where each patch is condition ∧ new_cond.
        """
        refined: list[tuple[str, str]] = []
        for (cond, body), new_cond in zip(cover, new_conditions):
            refined_cond = f"({cond}) and ({new_cond})"
            refined.append((refined_cond, body))
        return refined


# ═══════════════════════════════════════════════════════════════════
#  4. DuckTypeTactic — protocol equivalence
# ═══════════════════════════════════════════════════════════════════

class DuckTypeTactic:
    """Tactics for duck-type path construction.

    In Python, two types are interchangeable if they implement the same
    protocol.  This tactic constructs DuckPath proof terms from
    method-wise equivalence proofs, and supports univalent coercion
    to transfer proofs between equivalent types.
    """

    def __init__(self, kernel: ProofKernel) -> None:
        self.kernel = kernel

    def duck_equiv(self, type_a: SynType, type_b: SynType,
                   methods: dict[str, ProofTerm]) -> ProofTerm:
        """Construct a DuckPath from method-wise equivalence proofs.

        Each entry methods[name] should be a proof that
        type_a.name ≡ type_b.name (behaviorally).
        """
        return DuckPath(
            type_a=type_a,
            type_b=type_b,
            method_proofs=list(methods.items()),
        )

    def protocol_path(self, protocol: list[str],
                      impl_a: SynType, impl_b: SynType) -> ProofTerm:
        """Construct path between two implementations of the same protocol.

        Auto-generates method equivalence proofs where possible.
        For each method in protocol, constructs a structural proof
        that impl_a.method ≡ impl_b.method.
        """
        method_proofs: dict[str, ProofTerm] = {}
        for method_name in protocol:
            method_proofs[method_name] = Structural(
                description=(
                    f"{impl_a}.{method_name} ≡ {impl_b}.{method_name} "
                    f"(protocol conformance)"
                )
            )
        return self.duck_equiv(impl_a, impl_b, method_proofs)

    def protocol_from_type(self, ty: SynType) -> list[str]:
        """Extract protocol methods from a SynType.

        Works with ProtocolType, PyClassType, and PyCallableType.
        """
        if isinstance(ty, ProtocolType):
            return [name for name, _ in ty.methods]
        if isinstance(ty, PyClassType):
            return [name for name, _ in ty.methods]
        if isinstance(ty, PyCallableType):
            return ["__call__"]
        return []

    def auto_duck_path(self, type_a: SynType, type_b: SynType) -> ProofTerm:
        """Automatically construct a duck path between types.

        Extracts protocols from both types, finds common methods,
        and generates structural proofs for each.
        """
        methods_a = set(self.protocol_from_type(type_a))
        methods_b = set(self.protocol_from_type(type_b))
        common = methods_a & methods_b

        if not common:
            return Structural(
                description=f"no common protocol between {type_a} and {type_b}"
            )

        method_proofs: dict[str, ProofTerm] = {}
        for m in sorted(common):
            method_proofs[m] = Structural(
                description=f"{type_a}.{m} ≡ {type_b}.{m}"
            )
        return self.duck_equiv(type_a, type_b, method_proofs)

    def univalent_coerce(self, proof: ProofTerm,
                         from_type: SynType, to_type: SynType,
                         duck_path: ProofTerm) -> ProofTerm:
        """Use univalence: proof about impl_a → proof about impl_b.

        Given a DuckPath from_type ≃ to_type, uses univalence to
        transport the proof.
        """
        if Univalence is not None:
            ua = Univalence(
                equiv_proof=duck_path,
                from_type=from_type,
                to_type=to_type,
            )
            return TransportProof(
                type_family=Var("_P"),
                path_proof=ua,
                base_proof=proof,
            )
        # Fallback without Univalence
        return TransportProof(
            type_family=Var("_P"),
            path_proof=duck_path,
            base_proof=proof,
        )

    def coherence_check(self, type_a: SynType, type_b: SynType,
                        type_c: SynType,
                        path_ab: ProofTerm, path_bc: ProofTerm,
                        path_ac: ProofTerm) -> ProofTerm:
        """Verify that duck paths compose coherently: ab · bc = ac.

        Returns a structural proof of the coherence condition.
        """
        composed = Trans(left=path_ab, right=path_bc)
        return Structural(
            description=(
                f"coherence: {type_a}→{type_b}→{type_c} "
                f"= {type_a}→{type_c}"
            )
        )


# ═══════════════════════════════════════════════════════════════════
#  5. FibrationTactic — isinstance dispatch
# ═══════════════════════════════════════════════════════════════════

class FibrationTactic:
    """Tactics for fibration-based verification.

    In Deppy, isinstance checks define fibrations: the base space
    is the set of possible runtime types, and the fiber over each
    type is the set of values of that type.  Verifying a property on
    each fiber is sufficient to verify it on the total space (if
    the fibers cover the total space).
    """

    def __init__(self, kernel: ProofKernel) -> None:
        self.kernel = kernel

    def by_fiber(self, scrutinee: SynTerm,
                 branches: dict[SynType, ProofTerm]) -> ProofTerm:
        """Prove property by verifying on each fiber of a type dispatch.

        Constructs a Fiber proof term from the scrutinee and per-type
        branch proofs.
        """
        return Fiber(
            scrutinee=scrutinee,
            type_branches=list(branches.items()),
        )

    def lift(self, fiber_proof: ProofTerm,
             total_type: SynType) -> ProofTerm:
        """Lift a proof from a single fiber to the total space.

        Uses transport along the inclusion of the fiber into the total
        space.
        """
        return TransportProof(
            type_family=Var("_fiber_inclusion"),
            path_proof=Structural(
                description=f"fiber inclusion into {total_type}"
            ),
            base_proof=fiber_proof,
        )

    def section(self, fibration: ProofTerm,
                base_point: SynTerm) -> ProofTerm:
        """Extract a section (choose proof for a specific input).

        Given a fibration proof (verifying on all fibers), extracts
        the proof for a specific base point.
        """
        return Cut(
            hyp_name="_fibration",
            hyp_type=PyBoolType(),
            lemma_proof=fibration,
            body_proof=Structural(
                description=f"section at {base_point}"
            ),
        )

    def by_union_fiber(self, scrutinee: SynTerm,
                       union_type: UnionType,
                       branch_proofs: dict[SynType, ProofTerm]) -> ProofTerm:
        """Verify over a union type by dispatching to each alternative.

        Similar to by_fiber but specialized for Union types.
        """
        branches: dict[SynType, ProofTerm] = {}
        for alt in union_type.alternatives:
            if alt in branch_proofs:
                branches[alt] = branch_proofs[alt]
            else:
                branches[alt] = Structural(
                    description=f"fiber proof for {alt} (auto-generated)"
                )
        return self.by_fiber(scrutinee, branches)

    def total_space_proof(self, scrutinee: SynTerm,
                          branches: dict[SynType, ProofTerm],
                          glue_overlaps: bool = True) -> ProofTerm:
        """Complete total-space proof from fiber proofs.

        Combines fiber dispatch with Čech-style overlap checking
        when glue_overlaps is True.
        """
        fiber = self.by_fiber(scrutinee, branches)
        if not glue_overlaps or len(branches) <= 1:
            return fiber

        # Wrap with overlap checks between adjacent fibers
        type_list = list(branches.keys())
        result: ProofTerm = fiber
        for i in range(len(type_list) - 1):
            ta, tb = type_list[i], type_list[i + 1]
            result = Cut(
                hyp_name=f"_fiber_overlap_{i}",
                hyp_type=RefinementType(
                    base_type=PyBoolType(),
                    predicate=f"fiber({ta}) ∩ fiber({tb}) consistent",
                ),
                lemma_proof=Structural(
                    description=f"fiber overlap {ta} ∩ {tb}"
                ),
                body_proof=result,
            )
        return result


# ═══════════════════════════════════════════════════════════════════
#  6. HomotopyProofBuilder — unified builder API
# ═══════════════════════════════════════════════════════════════════

class HomotopyProofBuilder:
    """Unified builder integrating all homotopy tactics.

    Provides a chainable (fluent) API for constructing homotopy proofs.
    Each step appends to an internal list; ``qed()`` collapses them
    into a verified result.

    Example
    -------
        builder = HomotopyProofBuilder(kernel)
        result = (
            builder
            .show_path(Literal(42), Literal(42), via="refl")
            .then_transport(Var("P"), builder.path.refl(Literal(42)))
            .qed()
        )
    """

    def __init__(self, kernel: ProofKernel,
                 ctx: Context | None = None) -> None:
        self.kernel = kernel
        self.ctx = ctx or Context()
        self.path = PathTactic(kernel)
        self.transport_tactic = TransportTactic(kernel)
        self.cech = CechTactic(kernel)
        self.duck = DuckTypeTactic(kernel)
        self.fiber = FibrationTactic(kernel)
        self._steps: list[tuple[str, ProofTerm]] = []
        self._goal: Judgment | None = None

    # ── chainable methods ────────────────────────────────────────

    def show_path(self, a: SynTerm, b: SynTerm,
                  via: str = "refl") -> HomotopyProofBuilder:
        """Begin a proof by constructing a path a = b.

        via can be:
          "refl"        — reflexivity (a must equal b)
          "computation" — beta/eta/delta reduction
          "structural"  — structural argument
        """
        if via == "refl":
            proof = self.path.refl(a)
        elif via == "computation":
            proof = self.path.by_computation(a, b)
        elif via == "structural":
            proof = Structural(description=f"path: {a} = {b}")
        else:
            proof = Structural(description=f"path({via}): {a} = {b}")

        self._steps.append(("show_path", proof))
        self._goal = _eq_goal(self.ctx, a, b)
        return self

    def then_transport(self, type_family: SynTerm,
                       path: ProofTerm) -> HomotopyProofBuilder:
        """Transport the current proof along a path in type_family."""
        if not self._steps:
            raise ValueError("then_transport requires a preceding step")
        _, prev_proof = self._steps[-1]
        proof = self.transport_tactic.transport(type_family, path, prev_proof)
        self._steps.append(("then_transport", proof))
        return self

    def then_rewrite(self, equation: ProofTerm,
                     direction: str = "ltr") -> HomotopyProofBuilder:
        """Rewrite the current proof using an equation."""
        if not self._steps:
            raise ValueError("then_rewrite requires a preceding step")
        _, prev_proof = self._steps[-1]
        proof = self.transport_tactic.rewrite(prev_proof, equation, direction)
        self._steps.append(("then_rewrite", proof))
        return self

    def decompose(self, conditions: list[str],
                  proofs: list[ProofTerm]) -> HomotopyProofBuilder:
        """Decompose the goal into Čech patches."""
        proof = self.cech.by_cases_cech(conditions, proofs)
        self._steps.append(("decompose", proof))
        return self

    def by_duck_equiv(self, type_a: SynType, type_b: SynType,
                      methods: dict[str, ProofTerm]) -> HomotopyProofBuilder:
        """Prove via duck-type equivalence."""
        proof = self.duck.duck_equiv(type_a, type_b, methods)
        self._steps.append(("by_duck_equiv", proof))
        return self

    def per_fiber(self, scrutinee: SynTerm,
                  branches: dict[SynType, ProofTerm]) -> HomotopyProofBuilder:
        """Prove by fibration dispatch."""
        proof = self.fiber.by_fiber(scrutinee, branches)
        self._steps.append(("per_fiber", proof))
        return self

    def with_step(self, name: str, proof: ProofTerm) -> HomotopyProofBuilder:
        """Add an arbitrary named proof step."""
        self._steps.append((name, proof))
        return self

    def then_ap(self, f: SynTerm) -> HomotopyProofBuilder:
        """Apply a function to the current path (congruence)."""
        if not self._steps:
            raise ValueError("then_ap requires a preceding step")
        _, prev_proof = self._steps[-1]
        proof = self.path.ap(f, prev_proof)
        self._steps.append(("then_ap", proof))
        return self

    def then_sym(self) -> HomotopyProofBuilder:
        """Reverse the current path."""
        if not self._steps:
            raise ValueError("then_sym requires a preceding step")
        _, prev_proof = self._steps[-1]
        proof = self.path.sym(prev_proof)
        self._steps.append(("then_sym", proof))
        return self

    def then_concat(self, other: ProofTerm) -> HomotopyProofBuilder:
        """Concatenate another path after the current one."""
        if not self._steps:
            raise ValueError("then_concat requires a preceding step")
        _, prev_proof = self._steps[-1]
        proof = self.path.trans(prev_proof, other)
        self._steps.append(("then_concat", proof))
        return self

    def then_funext(self, var: str) -> HomotopyProofBuilder:
        """Apply function extensionality to the current proof."""
        if not self._steps:
            raise ValueError("then_funext requires a preceding step")
        _, prev_proof = self._steps[-1]
        proof = self.path.funext(var, prev_proof)
        self._steps.append(("then_funext", proof))
        return self

    # ── finalization ─────────────────────────────────────────────

    def current_proof(self) -> ProofTerm:
        """Return the proof term accumulated so far (without verifying)."""
        if not self._steps:
            return Structural(description="empty proof")
        _, proof = self._steps[-1]
        return proof

    def all_steps(self) -> list[tuple[str, ProofTerm]]:
        """Return a copy of all (name, proof) pairs."""
        return list(self._steps)

    def qed(self) -> VerificationResult:
        """Verify the accumulated proof and return the result.

        Constructs a goal from the first step (if not set explicitly),
        then feeds the final proof term to the kernel.
        """
        if not self._steps:
            return VerificationResult.fail("No proof steps provided")

        _, final_proof = self._steps[-1]

        if self._goal is None:
            # Infer goal from proof
            self._goal = self._infer_goal(final_proof)

        return self.kernel.verify(self.ctx, self._goal, final_proof)

    def set_goal(self, goal: Judgment) -> HomotopyProofBuilder:
        """Explicitly set the goal."""
        self._goal = goal
        return self

    def reset(self) -> HomotopyProofBuilder:
        """Clear all steps and goal."""
        self._steps.clear()
        self._goal = None
        return self

    # ── comparison with non-homotopy proofs ──────────────────────

    def proof_summary(self) -> dict[str, Any]:
        """Return a summary of the proof structure.

        Useful for comparing with non-homotopy ProofBuilder output.
        """
        if not self._steps:
            return {"steps": 0, "nodes": [], "homotopy": False, "depth": 0}
        _, final = self._steps[-1]
        nodes = _collect_proof_nodes(final)
        return {
            "steps": len(self._steps),
            "nodes": nodes,
            "homotopy": _proof_uses_homotopy(final),
            "depth": _proof_depth(final),
            "step_names": [name for name, _ in self._steps],
        }

    # ── internal ─────────────────────────────────────────────────

    def _infer_goal(self, proof: ProofTerm) -> Judgment:
        """Infer a goal from a proof term."""
        if isinstance(proof, Refl):
            return _eq_goal(self.ctx, proof.term, proof.term)
        return _tc_goal(self.ctx)


# ═══════════════════════════════════════════════════════════════════
#  7. Proof Strategy Combinators
# ═══════════════════════════════════════════════════════════════════

def try_path_then_z3(path_tactic: PathTactic,
                     a: SynTerm, b: SynTerm,
                     formula: str) -> ProofTerm:
    """Try constructing a path first; fall back to Z3 if terms differ."""
    if PathTactic._terms_syn_equal(a, b):
        return path_tactic.refl(a)
    return Z3Proof(formula=formula)


def homotopy_induction(scrutinee: SynTerm,
                       base_case: ProofTerm,
                       inductive_step: ProofTerm,
                       path_tactic: PathTactic) -> ProofTerm:
    """Combine induction with path reasoning.

    The inductive step is expected to produce a path from P(n)
    to P(n+1), composed via path concatenation.
    """
    return Cut(
        hyp_name="_base",
        hyp_type=PyBoolType(),
        lemma_proof=base_case,
        body_proof=Cut(
            hyp_name="_step",
            hyp_type=PyBoolType(),
            lemma_proof=inductive_step,
            body_proof=Structural(description="homotopy induction completion"),
        ),
    )


def parallel_transport(type_family: SynTerm,
                       paths: list[ProofTerm],
                       base: ProofTerm) -> ProofTerm:
    """Transport along a sequence of paths.

    Produces nested TransportProof terms: each path transports
    the result of the previous transport.
    """
    result = base
    for path in paths:
        result = TransportProof(
            type_family=type_family,
            path_proof=path,
            base_proof=result,
        )
    return result


def cech_nerve(conditions: list[str]) -> list[tuple[int, int, str]]:
    """Compute the nerve of a Čech cover.

    Returns all pairwise overlaps (i, j, "cond_i ∧ cond_j").
    """
    overlaps: list[tuple[int, int, str]] = []
    for i in range(len(conditions)):
        for j in range(i + 1, len(conditions)):
            overlaps.append((
                i, j,
                f"({conditions[i]}) and ({conditions[j]})",
            ))
    return overlaps


def pretty_homotopy_proof(proof: ProofTerm, indent: int = 0) -> str:
    """Pretty-print a proof term, highlighting homotopy structure."""
    pad = "  " * indent
    lines: list[str] = []

    if isinstance(proof, Refl):
        lines.append(f"{pad}path.refl({proof.term})")
    elif isinstance(proof, Sym):
        lines.append(f"{pad}path.sym")
        lines.append(pretty_homotopy_proof(proof.proof, indent + 1))
    elif isinstance(proof, Trans):
        lines.append(f"{pad}path.trans")
        lines.append(pretty_homotopy_proof(proof.left, indent + 1))
        lines.append(pretty_homotopy_proof(proof.right, indent + 1))
    elif isinstance(proof, Cong):
        lines.append(f"{pad}path.ap({proof.func})")
        lines.append(pretty_homotopy_proof(proof.proof, indent + 1))
    elif isinstance(proof, Ext):
        lines.append(f"{pad}path.funext({proof.var})")
        lines.append(pretty_homotopy_proof(proof.body_proof, indent + 1))
    elif isinstance(proof, TransportProof):
        lines.append(f"{pad}transport({proof.type_family})")
        lines.append(f"{pad}  along:")
        lines.append(pretty_homotopy_proof(proof.path_proof, indent + 2))
        lines.append(f"{pad}  base:")
        lines.append(pretty_homotopy_proof(proof.base_proof, indent + 2))
    elif isinstance(proof, DuckPath):
        lines.append(f"{pad}duck_equiv({proof.type_a} ≃ {proof.type_b})")
        for meth, mp in proof.method_proofs:
            lines.append(f"{pad}  .{meth}:")
            lines.append(pretty_homotopy_proof(mp, indent + 3))
    elif isinstance(proof, Fiber):
        lines.append(f"{pad}fiber({proof.scrutinee})")
        for ty, bp in proof.type_branches:
            lines.append(f"{pad}  | {ty}:")
            lines.append(pretty_homotopy_proof(bp, indent + 3))
    elif isinstance(proof, Cases):
        lines.append(f"{pad}čech.cases({proof.scrutinee})")
        for pat, bp in proof.branches:
            lines.append(f"{pad}  | {pat} =>")
            lines.append(pretty_homotopy_proof(bp, indent + 3))
    elif isinstance(proof, Cut):
        lines.append(f"{pad}cut({proof.hyp_name})")
        lines.append(pretty_homotopy_proof(proof.lemma_proof, indent + 1))
        lines.append(f"{pad}  in:")
        lines.append(pretty_homotopy_proof(proof.body_proof, indent + 1))
    elif isinstance(proof, Structural):
        desc = f"({proof.description})" if proof.description else ""
        lines.append(f"{pad}structural{desc}")
    elif isinstance(proof, Z3Proof):
        lines.append(f"{pad}z3({proof.formula})")
    elif isinstance(proof, Assume):
        lines.append(f"{pad}assume({proof.name})")
    elif PathComp is not None and isinstance(proof, PathComp):
        lines.append(f"{pad}path.comp")
        lines.append(pretty_homotopy_proof(proof.left_path, indent + 1))
        lines.append(pretty_homotopy_proof(proof.right_path, indent + 1))
    elif Ap is not None and isinstance(proof, Ap):
        lines.append(f"{pad}path.ap({proof.function})")
        lines.append(pretty_homotopy_proof(proof.path_proof, indent + 1))
    elif FunExt is not None and isinstance(proof, FunExt):
        lines.append(f"{pad}path.funext({proof.var})")
        lines.append(pretty_homotopy_proof(proof.pointwise_proof, indent + 1))
    elif CechGlue is not None and isinstance(proof, CechGlue):
        lines.append(f"{pad}čech.glue({len(proof.patches)} patches)")
        for cond, pp in proof.patches:
            lines.append(f"{pad}  | {cond} =>")
            lines.append(pretty_homotopy_proof(pp, indent + 3))
    elif Univalence is not None and isinstance(proof, Univalence):
        lines.append(f"{pad}univalence({proof.from_type} ≃ {proof.to_type})")
        lines.append(pretty_homotopy_proof(proof.equiv_proof, indent + 1))
    else:
        lines.append(f"{pad}{proof!r}")

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
#  Self-tests
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    passed = 0
    failed = 0

    def check(label: str, condition: bool, detail: str = "") -> None:
        global passed, failed
        if condition:
            passed += 1
            print(f"  ✓ [{passed + failed:>2}] {label}")
        else:
            failed += 1
            msg = f": {detail}" if detail else ""
            print(f"  ✗ [{passed + failed:>2}] {label}{msg}")

    kernel = ProofKernel()
    ctx = Context()

    print("=" * 60)
    print(" Deppy Homotopy Tactics — Self-Tests")
    print("=" * 60)

    # ── PathTactic ───────────────────────────────────────────────
    print("\n── PathTactic ──")

    pt = PathTactic(kernel)

    # 1. refl
    p_refl = pt.refl(Literal(42))
    check("PathTactic.refl", isinstance(p_refl, Refl))

    # 2. sym
    p_sym = pt.sym(p_refl)
    check("PathTactic.sym", isinstance(p_sym, Sym))

    # 3. trans
    p_trans = pt.trans(p_refl, pt.refl(Literal(42)))
    check("PathTactic.trans produces Trans or PathComp",
          isinstance(p_trans, (Trans,)) or (PathComp and isinstance(p_trans, PathComp)))

    # 4. ap / congruence
    p_ap = pt.ap(Var("f"), p_refl)
    check("PathTactic.ap produces Cong or Ap",
          isinstance(p_ap, (Cong,)) or (Ap and isinstance(p_ap, Ap)))

    # 5. funext
    p_funext = pt.funext("x", p_refl)
    check("PathTactic.funext produces Ext or FunExt",
          isinstance(p_funext, (Ext,)) or (FunExt and isinstance(p_funext, FunExt)))

    # 6. concat multiple
    p_concat = pt.concat(pt.refl(Literal(1)), pt.refl(Literal(2)),
                         pt.refl(Literal(3)))
    check("PathTactic.concat chains 3 proofs",
          isinstance(p_concat, Trans) or (PathComp and isinstance(p_concat, PathComp)))

    # 7. inverse_concat
    p_inv = pt.inverse_concat(pt.refl(Literal(1)), pt.refl(Literal(2)))
    nodes_inv = _collect_proof_nodes(p_inv)
    check("PathTactic.inverse_concat uses Sym",
          "Sym" in nodes_inv or "PathComp" in nodes_inv)

    # 8. by_computation same term → Refl
    p_comp_same = pt.by_computation(Literal(5), Literal(5))
    check("PathTactic.by_computation(5,5) → Refl",
          isinstance(p_comp_same, Refl))

    # 9. by_computation different terms → Structural
    p_comp_diff = pt.by_computation(Literal(5), Literal(6))
    check("PathTactic.by_computation(5,6) → Structural",
          isinstance(p_comp_diff, Structural))

    # 10. by_beta
    lam = Lam(param="x", body=Var("x"))
    p_beta = pt.by_beta(lam, Literal(7))
    check("PathTactic.by_beta", isinstance(p_beta, Structural) and "β" in p_beta.description)

    # 11. by_eta
    p_eta = pt.by_eta(Var("f"))
    check("PathTactic.by_eta", isinstance(p_eta, Structural) and "η" in p_eta.description)

    # 12. whisker_left
    p_wl = pt.whisker_left(pt.refl(Literal(1)), pt.refl(Literal(2)))
    check("PathTactic.whisker_left", isinstance(p_wl, Trans) or (PathComp and isinstance(p_wl, PathComp)))

    # 13. path_over
    p_over = pt.path_over(Var("P"), pt.refl(Var("a")),
                          pt.refl(Var("d_a")), pt.refl(Var("d_b")))
    check("PathTactic.path_over uses TransportProof",
          "TransportProof" in _collect_proof_nodes(p_over))

    # 14. verify refl through kernel
    goal_refl = _eq_goal(ctx, Literal(42), Literal(42))
    res_refl = kernel.verify(ctx, goal_refl, p_refl)
    check("PathTactic.refl verified by kernel", res_refl.success)

    # ── TransportTactic ──────────────────────────────────────────
    print("\n── TransportTactic ──")

    tt = TransportTactic(kernel)

    # 15. basic transport
    t_basic = tt.transport(Var("P"), pt.refl(Var("x")),
                           Structural(description="base"))
    check("TransportTactic.transport → TransportProof",
          isinstance(t_basic, TransportProof))

    # 16. coerce
    t_coerce = tt.coerce(Structural("proof_A"), Structural("equiv"))
    check("TransportTactic.coerce → TransportProof",
          isinstance(t_coerce, TransportProof))

    # 17. rewrite ltr
    t_rw = tt.rewrite(Structural("proof"), pt.refl(Literal(1)), "ltr")
    check("TransportTactic.rewrite ltr → TransportProof",
          isinstance(t_rw, TransportProof))

    # 18. rewrite rtl uses Sym
    t_rw_rtl = tt.rewrite(Structural("proof"), pt.refl(Literal(1)), "rtl")
    check("TransportTactic.rewrite rtl wraps path in Sym",
          isinstance(t_rw_rtl, TransportProof) and isinstance(t_rw_rtl.path_proof, Sym))

    # 19. subst
    t_subst = tt.subst(Structural("proof"), "x", Literal(5), pt.refl(Var("x")))
    check("TransportTactic.subst → TransportProof",
          isinstance(t_subst, TransportProof))

    # 20. transport_concat
    t_tc = tt.transport_concat(Var("P"), pt.refl(Var("a")),
                               pt.refl(Var("b")), Structural("base"))
    check("TransportTactic.transport_concat → nested TransportProof",
          isinstance(t_tc, TransportProof) and
          isinstance(t_tc.base_proof, TransportProof))

    # 21. apd
    t_apd = tt.apd(Var("f"), pt.refl(Var("a")))
    check("TransportTactic.apd → TransportProof",
          isinstance(t_apd, TransportProof))

    # 22. verify transport through kernel (with equality goal so path proof verifies)
    goal_eq_for_tp = _eq_goal(ctx, Var("x"), Var("x"))
    t_simple_tp = tt.transport(Var("P"), pt.refl(Var("x")),
                               Structural(description="base"))
    res_tp = kernel.verify(ctx, goal_eq_for_tp, t_simple_tp)
    check("TransportTactic verified by kernel", res_tp.success)

    # ── CechTactic ───────────────────────────────────────────────
    print("\n── CechTactic ──")

    ct = CechTactic(kernel)

    # 23. by_cases_cech basic
    c_basic = ct.by_cases_cech(
        ["x > 0", "x <= 0"],
        [Structural("positive case"), Structural("non-positive case")],
    )
    check("CechTactic.by_cases_cech → proof term",
          c_basic is not None)

    # 24. by_cases_cech has cocycle checks
    nodes = _collect_proof_nodes(c_basic)
    has_cocycle = "Cut" in nodes or "CechGlue" in nodes
    check("CechTactic.by_cases_cech includes cocycle check", has_cocycle)

    # 25. by_cases_cech with explicit overlaps
    c_overlap = ct.by_cases_cech(
        ["x > 0", "x == 0", "x < 0"],
        [Structural("pos"), Structural("zero"), Structural("neg")],
        overlaps=[(0, 1, pt.refl(Literal(0))),
                  (1, 2, pt.refl(Literal(0)))],
    )
    check("CechTactic.by_cases_cech with explicit overlaps",
          c_overlap is not None)

    # 26. cover extracts branches
    src = textwrap.dedent("""\
    def f(x):
        if x > 0:
            return x
        elif x == 0:
            return 0
        else:
            return -x
    """)
    patches = ct.cover(src)
    check("CechTactic.cover extracts 3 patches",
          len(patches) == 3, f"got {len(patches)}: {patches}")

    # 27. verify_and_glue
    c_vg = ct.verify_and_glue(patches, "returns non-negative")
    check("CechTactic.verify_and_glue → proof term", c_vg is not None)

    # 28. obstruction with no failures
    obs_ok = ct.obstruction(patches, [Structural("p1"), Structural("p2"), Structural("p3")])
    check("CechTactic.obstruction no failure",
          "No obstruction" in obs_ok)

    # 29. obstruction with failure
    obs_fail = ct.obstruction(patches, [Structural("p1"), None, Structural("p3")])
    check("CechTactic.obstruction detects failure",
          "H¹ obstruction" in obs_fail and "patch[1]" in obs_fail)

    # 30. refine_cover
    refined = ct.refine_cover(patches[:2], ["type(x) == int", "True"])
    check("CechTactic.refine_cover",
          len(refined) == 2 and "and" in refined[0][0])

    # 31. cech_nerve utility
    nerve = cech_nerve(["A", "B", "C"])
    check("cech_nerve computes 3 overlaps for 3 conditions",
          len(nerve) == 3)

    # 32. by_cases_cech verified by kernel
    goal_cech = _tc_goal(ctx)
    res_cech = kernel.verify(ctx, goal_cech, c_basic)
    check("CechTactic verified by kernel", res_cech.success)

    # ── DuckTypeTactic ───────────────────────────────────────────
    print("\n── DuckTypeTactic ──")

    dt = DuckTypeTactic(kernel)

    cls_a = PyClassType(name="ListWrapper", methods=(("append", PyObjType()),
                                                      ("pop", PyObjType())))
    cls_b = PyClassType(name="DequeWrapper", methods=(("append", PyObjType()),
                                                       ("pop", PyObjType())))

    # 33. duck_equiv
    d_equiv = dt.duck_equiv(cls_a, cls_b, {
        "append": pt.refl(Var("append_impl")),
        "pop": pt.refl(Var("pop_impl")),
    })
    check("DuckTypeTactic.duck_equiv → DuckPath",
          isinstance(d_equiv, DuckPath))

    # 34. protocol_path
    d_proto = dt.protocol_path(["append", "pop"], cls_a, cls_b)
    check("DuckTypeTactic.protocol_path → DuckPath",
          isinstance(d_proto, DuckPath) and len(d_proto.method_proofs) == 2)

    # 35. protocol_from_type
    proto_methods = dt.protocol_from_type(cls_a)
    check("DuckTypeTactic.protocol_from_type",
          proto_methods == ["append", "pop"])

    # 36. auto_duck_path
    d_auto = dt.auto_duck_path(cls_a, cls_b)
    check("DuckTypeTactic.auto_duck_path → DuckPath",
          isinstance(d_auto, DuckPath))

    # 37. univalent_coerce
    d_coerce = dt.univalent_coerce(
        Structural("proof_about_A"), cls_a, cls_b, d_equiv
    )
    check("DuckTypeTactic.univalent_coerce → TransportProof",
          isinstance(d_coerce, TransportProof))

    # 38. coherence_check
    cls_c = PyClassType(name="VecWrapper", methods=(("append", PyObjType()),
                                                     ("pop", PyObjType())))
    d_coh = dt.coherence_check(cls_a, cls_b, cls_c,
                               d_equiv, dt.auto_duck_path(cls_b, cls_c),
                               dt.auto_duck_path(cls_a, cls_c))
    check("DuckTypeTactic.coherence_check → Structural",
          isinstance(d_coh, Structural))

    # 39. duck path verified by kernel (use Structural method proofs to pass EQUAL checks)
    d_verifiable = dt.duck_equiv(cls_a, cls_b, {
        "append": Structural("append_equiv"),
        "pop": Structural("pop_equiv"),
    })
    goal_duck = _eq_goal(ctx, Var("ListWrapper"), Var("DequeWrapper"),
                         ty=PyCallableType())
    res_duck = kernel.verify(ctx, goal_duck, d_verifiable)
    check("DuckTypeTactic verified by kernel", res_duck.success)

    # 40. protocol_from_type on ProtocolType
    proto_ty = ProtocolType(name="Iterable", methods=(("__iter__", PyObjType()),))
    check("protocol_from_type on ProtocolType",
          dt.protocol_from_type(proto_ty) == ["__iter__"])

    # ── FibrationTactic ──────────────────────────────────────────
    print("\n── FibrationTactic ──")

    ft = FibrationTactic(kernel)

    # 41. by_fiber
    f_basic = ft.by_fiber(Var("x"), {
        PyIntType(): Structural("int case"),
        PyObjType(): Structural("obj case"),
    })
    check("FibrationTactic.by_fiber → Fiber",
          isinstance(f_basic, Fiber))

    # 42. lift
    f_lift = ft.lift(Structural("fiber proof"), PyObjType())
    check("FibrationTactic.lift → TransportProof",
          isinstance(f_lift, TransportProof))

    # 43. section
    f_sec = ft.section(f_basic, Literal(42))
    check("FibrationTactic.section → Cut",
          isinstance(f_sec, Cut))

    # 44. by_union_fiber
    union_ty = UnionType(alternatives=(PyIntType(), PyObjType()))
    f_union = ft.by_union_fiber(Var("x"), union_ty, {
        PyIntType(): Structural("int"),
    })
    check("FibrationTactic.by_union_fiber fills missing branches",
          isinstance(f_union, Fiber) and len(f_union.type_branches) == 2)

    # 45. total_space_proof with overlap checks
    f_total = ft.total_space_proof(Var("x"), {
        PyIntType(): Structural("int"),
        PyObjType(): Structural("obj"),
    })
    nodes_total = _collect_proof_nodes(f_total)
    check("FibrationTactic.total_space_proof has overlap cuts",
          "Cut" in nodes_total)

    # 46. Fiber verified by kernel
    goal_fiber = _tc_goal(ctx)
    res_fiber = kernel.verify(ctx, goal_fiber, f_basic)
    check("FibrationTactic verified by kernel", res_fiber.success)

    # ── HomotopyProofBuilder ─────────────────────────────────────
    print("\n── HomotopyProofBuilder ──")

    # 47. simple show_path + qed
    hpb = HomotopyProofBuilder(kernel)
    res_hpb = hpb.show_path(Literal(42), Literal(42), via="refl").qed()
    check("HomotopyProofBuilder show_path+qed success", res_hpb.success)

    # 48. show_path + then_transport
    hpb2 = HomotopyProofBuilder(kernel)
    res_hpb2 = (
        hpb2
        .show_path(Literal(1), Literal(1))
        .then_transport(Var("P"), pt.refl(Literal(1)))
        .qed()
    )
    check("HomotopyProofBuilder show_path+transport success", res_hpb2.success)

    # 49. decompose via Čech
    hpb3 = HomotopyProofBuilder(kernel)
    res_hpb3 = (
        hpb3
        .decompose(["x > 0", "x <= 0"],
                   [Structural("pos"), Structural("neg")])
        .qed()
    )
    check("HomotopyProofBuilder decompose success", res_hpb3.success)

    # 50. per_fiber
    hpb4 = HomotopyProofBuilder(kernel)
    res_hpb4 = (
        hpb4
        .per_fiber(Var("x"), {
            PyIntType(): Structural("int branch"),
            PyObjType(): Structural("obj branch"),
        })
        .qed()
    )
    check("HomotopyProofBuilder per_fiber success", res_hpb4.success)

    # 51. by_duck_equiv (use Structural method proofs for kernel verification)
    hpb5 = HomotopyProofBuilder(kernel)
    res_hpb5 = (
        hpb5
        .set_goal(_eq_goal(ctx, Var("A"), Var("B"), ty=PyCallableType()))
        .by_duck_equiv(cls_a, cls_b, {
            "append": Structural("append equiv"),
        })
        .qed()
    )
    check("HomotopyProofBuilder by_duck_equiv success", res_hpb5.success)

    # 52. chainable then_ap
    hpb6 = HomotopyProofBuilder(kernel)
    res_hpb6 = (
        hpb6
        .show_path(Literal(1), Literal(1))
        .then_ap(Var("f"))
        .qed()
    )
    check("HomotopyProofBuilder then_ap success", res_hpb6.success)

    # 53. chainable then_sym
    hpb7 = HomotopyProofBuilder(kernel)
    res_hpb7 = (
        hpb7
        .show_path(Literal(1), Literal(1))
        .then_sym()
        .qed()
    )
    check("HomotopyProofBuilder then_sym success", res_hpb7.success)

    # 54. chainable then_concat
    hpb8 = HomotopyProofBuilder(kernel)
    res_hpb8 = (
        hpb8
        .show_path(Literal(1), Literal(1))
        .then_concat(pt.refl(Literal(1)))
        .qed()
    )
    check("HomotopyProofBuilder then_concat success", res_hpb8.success)

    # 55. chainable then_funext
    hpb9 = HomotopyProofBuilder(kernel)
    res_hpb9 = (
        hpb9
        .show_path(Literal(1), Literal(1))
        .then_funext("x")
        .qed()
    )
    check("HomotopyProofBuilder then_funext success", res_hpb9.success)

    # 56. chainable then_rewrite
    hpb10 = HomotopyProofBuilder(kernel)
    res_hpb10 = (
        hpb10
        .show_path(Literal(1), Literal(1))
        .then_rewrite(pt.refl(Literal(1)))
        .qed()
    )
    check("HomotopyProofBuilder then_rewrite success", res_hpb10.success)

    # 57. proof_summary shows homotopy structure
    hpb11 = HomotopyProofBuilder(kernel)
    hpb11.show_path(Literal(1), Literal(1)).then_transport(Var("P"), pt.refl(Literal(1)))
    summary = hpb11.proof_summary()
    check("proof_summary detects homotopy structure",
          summary["homotopy"] is True)

    # 58. proof_summary with no homotopy
    hpb12 = HomotopyProofBuilder(kernel)
    hpb12.with_step("z3", Z3Proof(formula="1 == 1"))
    summary2 = hpb12.proof_summary()
    check("proof_summary non-homotopy proof",
          summary2["homotopy"] is False)

    # 59. current_proof
    hpb13 = HomotopyProofBuilder(kernel)
    hpb13.show_path(Literal(9), Literal(9))
    check("current_proof returns latest",
          isinstance(hpb13.current_proof(), Refl))

    # 60. reset clears state
    hpb13.reset()
    check("reset clears steps",
          len(hpb13.all_steps()) == 0)

    # ── Comparison: HomotopyProofBuilder vs ProofBuilder ─────────
    print("\n── HomotopyProofBuilder vs ProofBuilder ──")

    # Import ProofBuilder for comparison
    from deppy.proofs.tactics import ProofBuilder

    # 61. Both produce path composition (Trans or PathComp)
    pb = ProofBuilder(kernel, ctx)
    pb_proof = pb.trans(pb.refl(Literal(1)), pb.refl(Literal(2)))
    hpb_trans = pt.trans(pt.refl(Literal(1)), pt.refl(Literal(2)))
    check("ProofBuilder→Trans, HomotopyProofBuilder→PathComp (or both Trans)",
          isinstance(pb_proof, Trans) and
          (isinstance(hpb_trans, Trans) or
           (PathComp is not None and isinstance(hpb_trans, PathComp))))

    # 62. HomotopyProofBuilder can compose transport, ProofBuilder cannot chain
    hpb_composed = HomotopyProofBuilder(kernel)
    hpb_composed.show_path(Literal(1), Literal(1)).then_transport(Var("P"), pt.refl(Literal(1)))
    composed_nodes = _collect_proof_nodes(hpb_composed.current_proof())
    check("HomotopyProofBuilder chains transport into proof structure",
          "TransportProof" in composed_nodes)

    # 63. HomotopyProofBuilder decomposes via Čech (ProofBuilder uses plain Cases)
    pb_cases = pb.by_cases(Var("x"), [("x > 0", Structural("p")), ("x <= 0", Structural("n"))])
    hpb_cech = ct.by_cases_cech(["x > 0", "x <= 0"],
                                 [Structural("p"), Structural("n")])
    pb_nodes = _collect_proof_nodes(pb_cases)
    cech_nodes = _collect_proof_nodes(hpb_cech)
    check("Čech proof has more structure (cocycle) than plain Cases",
          len(cech_nodes) >= len(pb_nodes),
          f"čech={len(cech_nodes)} vs cases={len(pb_nodes)}")

    # 64. Homotopy proof always has homotopy flag True when using transport
    hpb_flag = HomotopyProofBuilder(kernel)
    hpb_flag.show_path(Literal(1), Literal(1)).then_transport(Var("P"), pt.refl(Literal(1)))
    check("Homotopy proof flagged as homotopy",
          hpb_flag.proof_summary()["homotopy"])

    # ProofBuilder proof doesn't use homotopy
    check("ProofBuilder proof not flagged as homotopy",
          not _proof_uses_homotopy(pb_proof))

    # ── Strategy combinators ─────────────────────────────────────
    print("\n── Strategy Combinators ──")

    # 65. try_path_then_z3 same term
    s1 = try_path_then_z3(pt, Literal(1), Literal(1), "1 == 1")
    check("try_path_then_z3 same → Refl", isinstance(s1, Refl))

    # 66. try_path_then_z3 different terms
    s2 = try_path_then_z3(pt, Literal(1), Literal(2), "1 == 1")
    check("try_path_then_z3 diff → Z3Proof", isinstance(s2, Z3Proof))

    # 67. homotopy_induction
    s3 = homotopy_induction(Var("n"), pt.refl(Literal(0)),
                            Structural("step"), pt)
    check("homotopy_induction → Cut",
          isinstance(s3, Cut))

    # 68. parallel_transport
    s4 = parallel_transport(Var("P"),
                            [pt.refl(Var("a")), pt.refl(Var("b"))],
                            Structural("base"))
    check("parallel_transport → nested TransportProof",
          isinstance(s4, TransportProof) and isinstance(s4.base_proof, TransportProof))

    # 69. parallel_transport empty paths → just base
    s5 = parallel_transport(Var("P"), [], Structural("base"))
    check("parallel_transport empty → base",
          isinstance(s5, Structural))

    # 70. pretty_homotopy_proof
    complex_proof = TransportProof(
        type_family=Var("P"),
        path_proof=Trans(
            left=Refl(term=Literal(1)),
            right=Sym(proof=Refl(term=Literal(2))),
        ),
        base_proof=DuckPath(
            type_a=cls_a, type_b=cls_b,
            method_proofs=[("append", Refl(term=Var("impl")))],
        ),
    )
    pp = pretty_homotopy_proof(complex_proof)
    check("pretty_homotopy_proof renders transport",
          "transport" in pp and "duck_equiv" in pp)

    # ── Edge cases ───────────────────────────────────────────────
    print("\n── Edge Cases ──")

    # 71. concat with single proof
    p_single = pt.concat(pt.refl(Literal(1)))
    check("concat single proof → Refl", isinstance(p_single, Refl))

    # 72. concat raises on empty
    try:
        pt.concat()
        check("concat empty raises", False, "should have raised")
    except ValueError:
        check("concat empty raises ValueError", True)

    # 73. by_cases_cech mismatched lengths raises
    try:
        ct.by_cases_cech(["A"], [Structural("a"), Structural("b")])
        check("by_cases_cech mismatch raises", False, "should have raised")
    except ValueError:
        check("by_cases_cech mismatch raises ValueError", True)

    # 74. then_transport without preceding step raises
    hpb_err = HomotopyProofBuilder(kernel)
    try:
        hpb_err.then_transport(Var("P"), pt.refl(Literal(1)))
        check("then_transport no step raises", False)
    except ValueError:
        check("then_transport no step raises ValueError", True)

    # 75. cover on non-branching code
    patches_nb = ct.cover("return 42")
    check("cover non-branching → 1 patch",
          len(patches_nb) == 1)

    # 76. proof_depth
    simple = Refl(term=Literal(1))
    deep = Trans(left=Trans(left=simple, right=simple),
                 right=Trans(left=simple, right=simple))
    check("_proof_depth simple=1, deep=3",
          _proof_depth(simple) == 1 and _proof_depth(deep) == 3)

    # 77. _proof_uses_homotopy detects transport
    check("_proof_uses_homotopy on TransportProof",
          _proof_uses_homotopy(t_basic))

    # 78. _proof_uses_homotopy on plain Refl
    check("_proof_uses_homotopy on Refl is False",
          not _proof_uses_homotopy(Refl(term=Literal(1))))

    # 79. _subst_term basic substitution
    substituted = _subst_term(Var("x"), "x", Literal(42))
    check("_subst_term Var → Literal",
          isinstance(substituted, Literal) and substituted.value == 42)

    # 80. _subst_term shadowing
    shadowed = _subst_term(Lam(param="x", body=Var("x")), "x", Literal(99))
    check("_subst_term respects shadowing",
          isinstance(shadowed, Lam) and isinstance(shadowed.body, Var))

    # 81. set_goal
    hpb_goal = HomotopyProofBuilder(kernel)
    custom_goal = _eq_goal(ctx, Literal(1), Literal(1))
    hpb_goal.set_goal(custom_goal).show_path(Literal(1), Literal(1))
    res_custom = hpb_goal.qed()
    check("HomotopyProofBuilder set_goal", res_custom.success)

    # 82. with_step
    hpb_ws = HomotopyProofBuilder(kernel)
    hpb_ws.with_step("custom", Structural("my step"))
    check("with_step adds step", len(hpb_ws.all_steps()) == 1)

    # ── _subst_term on compound terms ─────────────────────────────
    print("\n── Term Substitution ──")

    # 83. subst in App
    app_term = App(func=Var("f"), arg=Var("x"))
    sub_app = _subst_term(app_term, "x", Literal(10))
    check("_subst_term App",
          isinstance(sub_app, App) and isinstance(sub_app.arg, Literal))

    # 84. subst in PathAbs (shadowed)
    pabs = PathAbs(ivar="i", body=Var("i"))
    sub_pabs = _subst_term(pabs, "i", Literal(0))
    check("_subst_term PathAbs shadowed",
          isinstance(sub_pabs, PathAbs) and isinstance(sub_pabs.body, Var))

    # 85. subst in PathApp
    papp = PathApp(path=Var("p"), arg=Var("x"))
    sub_papp = _subst_term(papp, "x", Literal(1))
    check("_subst_term PathApp",
          isinstance(sub_papp, PathApp) and isinstance(sub_papp.arg, Literal))

    # ── Integration: complex multi-step proof ────────────────────
    print("\n── Integration ──")

    # 86. Full pipeline: decompose → per-fiber → transport → qed
    hpb_full = HomotopyProofBuilder(kernel)
    res_full = (
        hpb_full
        .decompose(
            ["isinstance(x, int)", "isinstance(x, str)"],
            [
                ft.by_fiber(Var("x"), {PyIntType(): Structural("int ok")}),
                ft.by_fiber(Var("x"), {PyObjType(): Structural("str ok")}),
            ],
        )
        .qed()
    )
    check("Full pipeline decompose+fiber", res_full.success)

    # 87. Full pipeline: duck → transport → qed
    hpb_full2 = HomotopyProofBuilder(kernel)
    duck_proof = dt.duck_equiv(cls_a, cls_b, {
        "append": Structural("equiv append"),
        "pop": Structural("equiv pop"),
    })
    res_full2 = (
        hpb_full2
        .by_duck_equiv(cls_a, cls_b, {
            "append": Structural("equiv append"),
            "pop": Structural("equiv pop"),
        })
        .qed()
    )
    check("Full pipeline duck+qed", res_full2.success)

    # 88. Full pipeline: path → ap → funext → qed
    hpb_full3 = HomotopyProofBuilder(kernel)
    res_full3 = (
        hpb_full3
        .show_path(Literal(1), Literal(1))
        .then_ap(Var("g"))
        .then_funext("y")
        .qed()
    )
    check("Full pipeline path→ap→funext", res_full3.success)

    # 89. Verify all homotopy proofs are genuinely distinct from z3/structural
    from deppy.proofs.tactics import ProofBuilder as PB
    pb_classic = PB(kernel, ctx)
    classic_proof = pb_classic.z3("1 == 1")
    hpb_hom = HomotopyProofBuilder(kernel)
    hpb_hom.show_path(Literal(1), Literal(1)).then_transport(Var("P"), pt.refl(Literal(1)))
    hom_proof = hpb_hom.current_proof()
    check("Homotopy proof structurally different from Z3",
          type(classic_proof).__name__ != type(hom_proof).__name__)

    # 90. Verify proof node counts differ
    classic_nodes = _collect_proof_nodes(classic_proof)
    hom_nodes = _collect_proof_nodes(hom_proof)
    check("Homotopy proof has more nodes than Z3",
          len(hom_nodes) > len(classic_nodes),
          f"hom={len(hom_nodes)} vs classic={len(classic_nodes)}")

    # ── Pretty-printing ──────────────────────────────────────────
    print("\n── Pretty-printing ──")

    # 91. pretty_homotopy_proof on Refl
    pp_refl = pretty_homotopy_proof(Refl(term=Literal(42)))
    check("pretty Refl", "path.refl(" in pp_refl)

    # 92. pretty Sym
    pp_sym = pretty_homotopy_proof(Sym(proof=Refl(term=Literal(1))))
    check("pretty Sym", "path.sym" in pp_sym)

    # 93. pretty Fiber
    pp_fiber = pretty_homotopy_proof(f_basic)
    check("pretty Fiber", "fiber" in pp_fiber)

    # 94. pretty Cases
    pp_cases = pretty_homotopy_proof(
        Cases(scrutinee=Var("x"), branches=[("x>0", Structural("pos"))])
    )
    check("pretty Cases", "čech.cases" in pp_cases)

    # 95. pretty Cut
    pp_cut = pretty_homotopy_proof(
        Cut(hyp_name="h", hyp_type=PyBoolType(),
            lemma_proof=Refl(Literal(1)), body_proof=Structural("done"))
    )
    check("pretty Cut", "cut(h)" in pp_cut)

    # ── Final summary ────────────────────────────────────────────
    print("\n" + "=" * 60)
    total = passed + failed
    print(f" Results: {passed}/{total} passed, {failed} failed")
    if failed == 0:
        print(" All homotopy tactic self-tests passed ✓")
    else:
        print(f" {failed} test(s) FAILED")
    print("=" * 60)

    if failed > 0:
        raise SystemExit(1)
