"""Audit fix #2 — verify the kernel actually enforces structural
conditions on Cocycle / KanFill / HigherPath proof terms.

Each test constructs a deliberately-broken proof term and verifies
that the kernel rejects it with the expected error code.  This is
the regression test for the cheat fix: before the audit, the
kernel accepted *any* proof term of these shapes regardless of
whether the structural data was consistent.
"""
from __future__ import annotations

from deppy.core.kernel import (
    Cocycle,
    Context,
    HigherPath,
    Judgment,
    JudgmentKind,
    KanFill,
    ProofKernel,
    Refl,
    Var,
)
from deppy.core.types import PyObjType


def _Triv():
    """A trivially-valid proof term: ``Refl(x) : x = x``."""
    return Refl(term=Var("x"))


def _kernel_and_goal():
    """A goal that ``Refl(Var('x')) : x = x`` proves trivially,
    so per-component verification of structural tests succeeds and
    the kernel reaches the boundary-pair / endpoint checks where the
    structural error codes fire."""
    kernel = ProofKernel()
    ctx = Context()
    x = Var("x")
    goal = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=x,
        right=x,
        type_=PyObjType(),
    )
    return kernel, ctx, goal


# ─────────────────────────────────────────────────────────────────────
#  Cocycle structural invariants
# ─────────────────────────────────────────────────────────────────────


class TestCocycleStructure:
    def test_empty_components_rejected(self):
        kernel, ctx, goal = _kernel_and_goal()
        proof = Cocycle(level=0, components=[])
        r = kernel.verify(ctx, goal, proof)
        assert not r.success
        assert "E007b" in (r.error_code or "")

    def test_invalid_level_rejected(self):
        kernel, ctx, goal = _kernel_and_goal()
        proof = Cocycle(level=-1, components=[_Triv()])
        r = kernel.verify(ctx, goal, proof)
        assert not r.success
        assert "E007a" in (r.error_code or "")

    def test_boundary_pair_out_of_range_rejected(self):
        kernel, ctx, goal = _kernel_and_goal()
        # 2 components, but boundary pair references index 5.
        proof = Cocycle(
            level=0,
            components=[_Triv(), _Triv()],
            boundary_pairs=[(0, 5)],
            overlap_proofs={(0, 5): _Triv()},
        )
        r = kernel.verify(ctx, goal, proof)
        assert not r.success
        assert "E007d" in (r.error_code or "")

    def test_missing_overlap_proof_rejected(self):
        kernel, ctx, goal = _kernel_and_goal()
        # Boundary pair declared but no overlap proof.
        proof = Cocycle(
            level=0,
            components=[_Triv(), _Triv()],
            boundary_pairs=[(0, 1)],
            overlap_proofs={},  # <-- missing!
        )
        r = kernel.verify(ctx, goal, proof)
        assert not r.success
        assert "E007e" in (r.error_code or "")

    def test_well_formed_cocycle_accepted(self):
        kernel, ctx, goal = _kernel_and_goal()
        proof = Cocycle(
            level=0,
            components=[_Triv(), _Triv()],
            boundary_pairs=[(0, 1)],
            overlap_proofs={(0, 1): _Triv()},
        )
        r = kernel.verify(ctx, goal, proof)
        assert r.success

    def test_single_component_unstructured_keeps_kernel_trust(self):
        # A *single*-component cocycle is trivially coherent — no
        # overlap proofs are meaningful — so trust stays at KERNEL.
        kernel, ctx, goal = _kernel_and_goal()
        proof = Cocycle(level=0, components=[_Triv()])
        r = kernel.verify(ctx, goal, proof)
        assert r.success
        # Single-component case: full trust preserved.
        from deppy.core.kernel import TrustLevel
        assert r.trust_level == TrustLevel.KERNEL
        assert "trivially coherent" in r.message

    def test_multi_component_unstructured_downgrades_trust(self):
        # Audit fix (round 2): a multi-component cocycle without
        # ``boundary_pairs`` gets its trust downgraded to
        # STRUCTURAL_CHAIN so callers gating on ``trust_level``
        # can see the structure wasn't verified.  Before the fix
        # this returned KERNEL trust, masking the missing check.
        kernel, ctx, goal = _kernel_and_goal()
        proof = Cocycle(
            level=0,
            components=[_Triv(), _Triv()],
            # No boundary_pairs.
        )
        r = kernel.verify(ctx, goal, proof)
        assert r.success
        from deppy.core.kernel import TrustLevel
        # Downgraded — not KERNEL anymore.
        assert r.trust_level == TrustLevel.STRUCTURAL_CHAIN
        assert "structurally unchecked" in r.message
        assert "trust downgraded" in r.message


# ─────────────────────────────────────────────────────────────────────
#  KanFill structural invariants
# ─────────────────────────────────────────────────────────────────────


class TestKanFillStructure:
    def test_well_formed_kan_fill_does_not_trigger_structure_error(self):
        kernel, ctx, goal = _kernel_and_goal()
        a, b, c = Var("a"), Var("b"), Var("c")
        proof = KanFill(
            dimension=2,
            faces=[Refl(term=a), Refl(term=b)],
            face_endpoints=[(a, b), (b, c)],
            missing_face_label="missing",
        )
        r = kernel.verify(ctx, goal, proof)
        # The structural-error codes (E009c/d) should NOT appear.
        if not r.success:
            assert "E009c" not in (r.error_code or "")
            assert "E009d" not in (r.error_code or "")


# ─────────────────────────────────────────────────────────────────────
#  HigherPath structural invariants
# ─────────────────────────────────────────────────────────────────────


class TestHigherPathStructure:
    def test_invalid_endpoint_index_rejected(self):
        kernel, ctx, goal = _kernel_and_goal()
        # 2 vertices but endpoint references vertex index 99.
        proof = HigherPath(
            dimension=1,
            vertices=[Var("a"), Var("b")],
            boundary_proofs=[_Triv()],
            boundary_endpoints=[(0, 99)],
        )
        r = kernel.verify(ctx, goal, proof)
        assert not r.success
        # E010d/e/f are the structural codes.
        code = r.error_code or ""
        assert any(c in code for c in ("E010d", "E010e", "E010f"))

    def test_degenerate_endpoint_rejected(self):
        kernel, ctx, goal = _kernel_and_goal()
        # endpoint (0, 0) is degenerate (start == end).
        proof = HigherPath(
            dimension=1,
            vertices=[Var("a"), Var("b")],
            boundary_proofs=[_Triv()],
            boundary_endpoints=[(0, 0)],
        )
        r = kernel.verify(ctx, goal, proof)
        assert not r.success
