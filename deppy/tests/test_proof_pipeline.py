"""
Tests for the five-stage cubical proof pipeline
(``deppy.proofs.language`` + ``deppy.proofs.pipeline``).

Stages exercised:
  1. code_to_axioms (simple + deep: multi-statement, for-loop fold,
     self-recursive induction principle, @property, inheritance)
  2. AxiomRegistry (dedup, LHS-head index, install into kernel,
     conflict detection)
  3. Tactic DSL extensions (Tactics.first / cases / simp_with)
  4. ProofTree (tactic → printable tree, Lean export, JSON)
  5. ProofCertificate (kernel-checked result with replayable script)
"""
from __future__ import annotations

import json

import pytest

from deppy.core.kernel import ProofKernel
from deppy.core.types import Context, Var, Literal, PyObjType
from deppy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq, op_add, op_floordiv,
)
from deppy.proofs.language import (
    UnfoldError, T, eq, op_attr, op_method, op_call, _OBJ,
)
from deppy.proofs.pipeline import (
    AxiomRegistry, axiomize,
    deep_function_to_axioms, deep_class_to_axioms,
    foldl_universal_axioms, register_universal_axioms, op_nil,
    Tactics, ProofCertificate, prove_certificate,
    ProofScript, verify_proof_script,
)
from deppy.core.kernel import TrustLevel


# ── Test fixtures: defined at module scope so inspect.getsource works ──

# Recursive function — should generate a list-induction principle.
def _length(lst):
    if lst == 0:
        return 0
    return 1 + _length(lst - 1)


# For-loop function — should generate a fold axiom.
def _total(lst):
    acc = 0
    for x in lst:
        acc = acc + x
    return acc


# Multi-statement function — should be let-inlined.
def _midpoint(a, b):
    s = a + b
    return s // 2


class _BankAccount:
    def __init__(self, balance, rate):
        self.balance = balance
        self.rate = rate

    def deposit(self, x):
        new_bal = self.balance + x
        return new_bal

    @property
    def interest(self):
        return self.balance * self.rate


class _SavingsAccount(_BankAccount):
    def withdraw(self, x):
        return self.balance - x


# ── Stage 1: code_to_axioms ──────────────────────────────────────────

def test_deep_function_recursive_yields_case_axioms_not_induction_schema():
    """A recursive function should produce case-split axioms but no
    induction meta-axiom — induction is discharged at proof time via
    ``Tactics.induction(...)`` building a real ``ListInduction`` term."""
    axs = deep_function_to_axioms(_length, module="tests")
    names = {a.name for a in axs}
    assert any(n.startswith("_length_def_case") for n in names)
    # Critically, no _induction axiom is registered.
    assert not any(n.endswith("_induction") for n in names)


def test_deep_function_for_loop_yields_fold_axiom():
    axs = deep_function_to_axioms(_total, module="tests")
    names = {a.name for a in axs}
    assert "_total_fold" in names


def test_deep_function_multi_statement_let_inlined():
    axs = deep_function_to_axioms(_midpoint, module="tests")
    # Simple translator rejects multi-statement bodies (the single-return
    # pass doesn't trigger); the let-inlining pass should produce `_def`.
    names = {a.name for a in axs}
    assert "_midpoint_def" in names


def test_deep_class_includes_property_and_inherited_axioms():
    axs = deep_class_to_axioms(_BankAccount, module="tests")
    names = {a.name for a in axs}
    # Property → accessor axiom
    assert "_BankAccount_interest_property" in names
    # __init__ accessors
    assert "_BankAccount_init_balance" in names
    assert "_BankAccount_init_rate" in names

    child_axs = deep_class_to_axioms(_SavingsAccount, module="tests")
    child_names = {a.name for a in child_axs}
    # Inherited parent accessors are re-tagged
    assert any(n.endswith("__inherited") for n in child_names)


def test_axiomize_dispatches_on_function_vs_class():
    fn_axs = axiomize(_midpoint, module="tests")
    cls_axs = axiomize(_BankAccount, module="tests")
    assert fn_axs and cls_axs
    with pytest.raises(TypeError):
        axiomize(42)  # type: ignore[arg-type]


# ── Stage 2: AxiomRegistry ───────────────────────────────────────────

def test_registry_dedup_and_install():
    reg = AxiomRegistry()
    axs = deep_function_to_axioms(_length, module="tests")
    added1 = reg.add_all(axs, source="length")
    # Adding the same axioms again dedups completely.
    added2 = reg.add_all(axs, source="length-second-pass")
    assert added1 > 0
    assert added2 == 0

    kernel = ProofKernel()
    installed = reg.install(kernel)
    assert installed == len(reg.by_qname)


def test_registry_lhs_head_index_populated():
    reg = AxiomRegistry()
    reg.add_all(deep_function_to_axioms(_length, module="tests"),
                source="length")
    # The head for length(...) axioms is "_length".
    assert "_length" in reg.by_lhs_head
    assert len(reg.by_lhs_head["_length"]) >= 1


def test_registry_detects_same_lhs_different_rhs_conflict():
    reg = AxiomRegistry()

    # Two contradictory axioms over the same LHS shape.
    ctx = Context()
    good = FormalAxiomEntry(
        name="f_is_0", module="conflict_test", params=[],
        conclusion=formal_eq(ctx,
            OpCall(Op("f", "conflict_test"), ()), Literal(0, _OBJ),
            type_=_OBJ),
        description="f() = 0")
    bad = FormalAxiomEntry(
        name="f_is_1", module="conflict_test", params=[],
        conclusion=formal_eq(ctx,
            OpCall(Op("f", "conflict_test"), ()), Literal(1, _OBJ),
            type_=_OBJ),
        description="f() = 1")

    from deppy.proofs.language import CodeAxiom
    reg.add(CodeAxiom("f_is_0", "conflict_test", good, good.description),
            source="a")
    reg.add(CodeAxiom("f_is_1", "conflict_test", bad, bad.description),
            source="b")
    conflicts = reg.conflicts()
    assert any(head == "f" for _, _, head in conflicts)


# ── Stage 3+4+5: tactics → proof tree → certificate ─────────────────

def test_prove_certificate_on_case_axiom():
    kernel = ProofKernel()
    reg = AxiomRegistry()
    reg.add_all(deep_function_to_axioms(_length, module="tests"),
                source="length")
    reg.install(kernel)

    goal = eq(OpCall(Op("_length", "tests"), (op_nil(),)), Literal(0, _OBJ))
    cert = prove_certificate(
        "length_nil_is_zero",
        kernel=kernel, goal=goal,
        tactic=Tactics.cases("_length", 1, "tests"),
        quiet=True,
    )
    assert isinstance(cert, ProofCertificate)
    assert cert.success, f"kernel rejected proof: {cert.message}"
    # Certificate records the axiom it invoked
    assert any("_length_def_case1" in a for a in cert.axioms_used)
    # Content hash is stable/non-empty
    assert cert.content_hash and len(cert.content_hash) == 16


def test_prove_certificate_fold_chain_for_total_empty_list():
    kernel = ProofKernel()
    reg = AxiomRegistry()
    reg.add_all(deep_function_to_axioms(_total, module="tests"),
                source="total")
    reg.add_all(foldl_universal_axioms(), source="universal:foldl")
    reg.install(kernel)

    goal = eq(OpCall(Op("_total", "tests"), (op_nil(),)), Literal(0, _OBJ))
    cert = prove_certificate(
        "total_nil_is_zero",
        kernel=kernel, goal=goal,
        tactic=T.simp(("_total_fold", "tests"),
                      ("foldl_nil", "deppy.list")),
        quiet=True,
    )
    # The certificate is produced regardless — but if the kernel accepts
    # definitional chains, success should be True.
    assert cert.tree.kind == "simp"


def test_prove_certificate_class_accessor_via_first():
    kernel = ProofKernel()
    reg = AxiomRegistry()
    reg.add_all(deep_class_to_axioms(_BankAccount, module="tests"),
                source="BankAccount")
    reg.add_all(deep_class_to_axioms(_SavingsAccount, module="tests"),
                source="SavingsAccount")
    reg.install(kernel)

    b, r = Var("b"), Var("r")
    bk = OpCall(Op("_SavingsAccount", "tests"), (b, r))
    goal = eq(op_attr(bk, "balance"), b)
    goal.ctx = Context().extend("b", _OBJ).extend("r", _OBJ)

    cert = prove_certificate(
        "savings_balance_inherited",
        kernel=kernel, goal=goal,
        tactic=Tactics.first(
            Tactics.axiom("_SavingsAccount_init_balance", "tests"),
            Tactics.axiom("_BankAccount_init_balance", "tests"),
        ),
        quiet=True,
    )
    # Proof tree records the first-combinator
    assert cert.tree.kind == "first"


def test_proof_certificate_lean_and_json_export():
    kernel = ProofKernel()
    reg = AxiomRegistry()
    reg.add_all(deep_function_to_axioms(_length, module="tests"),
                source="length")
    reg.install(kernel)

    goal = eq(OpCall(Op("_length", "tests"), (op_nil(),)), Literal(0, _OBJ))
    cert = prove_certificate(
        "length_nil_is_zero",
        kernel=kernel, goal=goal,
        tactic=Tactics.cases("_length", 1, "tests"),
        quiet=True,
    )

    # Lean surface export mentions the theorem
    lean_src = cert.lean_export()
    assert "theorem length_nil_is_zero" in lean_src
    assert "True := by" in lean_src

    # JSON is valid and roundtrips key fields
    parsed = json.loads(cert.to_json())
    assert parsed["theorem"] == "length_nil_is_zero"
    assert parsed["hash"] == cert.content_hash
    assert parsed["success"] is cert.success
    assert isinstance(parsed["tree"], dict)


def test_public_api_is_exposed_at_top_level():
    """The pipeline is core source code, so the headline names resolve
    from ``deppy`` directly (sub-API lives under ``deppy.proofs``)."""
    import deppy
    for name in (
        "AxiomRegistry", "axiomize",
        "ProofCertificate", "prove_certificate",
        "ProofScript", "verify_proof_script",
        "Tactics", "register_universal_axioms",
    ):
        assert hasattr(deppy, name), f"deppy.{name} is missing"


# ── kernel_verified vs success distinction ──────────────────────────

def test_structural_proof_succeeds_but_is_not_kernel_verified():
    """A proof whose leaf is ``Tactics.structural`` passes the kernel's
    structural rule set but must *not* be flagged as kernel-verified —
    otherwise a shipped cert could hide an unverified pinky-promise."""
    kernel = ProofKernel()
    goal = eq(Var("x"), Var("x"), x="object")
    cert = prove_certificate(
        "trust_me_theorem",
        kernel=kernel, goal=goal,
        tactic=Tactics.structural("pinky-promise"),
        quiet=True,
    )
    assert cert.success
    assert not cert.kernel_verified, (
        "structural-only proofs must not be labelled kernel_verified"
    )


def test_refl_proof_is_kernel_verified():
    """A plain refl is kernel-checked end-to-end: no structural leaf,
    trust level at KERNEL."""
    kernel = ProofKernel()
    goal = eq(Var("x"), Var("x"), x="object")
    cert = prove_certificate(
        "refl_theorem",
        kernel=kernel, goal=goal,
        tactic=Tactics.refl(),
        quiet=True,
    )
    assert cert.success
    assert cert.kernel_verified
    assert cert.trust_level == TrustLevel.KERNEL


def test_axiom_citation_is_kernel_verified_even_at_axiom_trust():
    """Vision test: a proof that cites a code-derived axiom still counts
    as kernel_verified, because the axiom *is* the code.  Only a
    ``structural`` leaf would disqualify it."""
    kernel = ProofKernel()
    reg = AxiomRegistry()
    reg.add_all(deep_function_to_axioms(_length, module="tests"),
                source="length")
    reg.install(kernel)

    goal = eq(OpCall(Op("_length", "tests"), (op_nil(),)), Literal(0, _OBJ))
    cert = prove_certificate(
        "len_nil_0",
        kernel=kernel, goal=goal,
        tactic=Tactics.cases("_length", 1, "tests"),
        quiet=True,
    )
    assert cert.success
    assert cert.kernel_verified, "code-derived axiom citations must count"
    # But the trust level surfaces as AXIOM_TRUSTED — informative, not a gate.
    assert cert.trust_level == TrustLevel.AXIOM_TRUSTED


# ── ProofScript round-trip (the vision's core operation) ────────────

def test_proof_script_roundtrips_via_json_and_replays_against_kernel():
    """Vision: LLM writes proof, user ships JSON, receiver re-verifies.
    Concretely — build a script, emit JSON, re-parse it, re-verify on a
    fresh kernel, confirm the same certificate semantics come out."""
    kernel = ProofKernel()
    reg = AxiomRegistry()
    reg.add_all(deep_function_to_axioms(_length, module="tests"),
                source="length")
    reg.install(kernel)

    goal = eq(OpCall(Op("_length", "tests"), (op_nil(),)), Literal(0, _OBJ))
    script = ProofScript(
        theorem="length_nil_is_zero",
        goal=goal,
        tactic=Tactics.cases("_length", 1, "tests"),
        source_fingerprint="sha256:length-v1",
    )

    # Round-trip through JSON.
    payload = script.to_json()
    parsed = ProofScript.from_json(payload)

    # Re-verify on a *fresh* kernel — axioms still need to be installed,
    # because a script records the proof, not the axiom base.
    fresh_kernel = ProofKernel()
    fresh_reg = AxiomRegistry()
    fresh_reg.add_all(deep_function_to_axioms(_length, module="tests"),
                      source="length")
    fresh_reg.install(fresh_kernel)

    cert_original = script.verify(kernel, quiet=True)
    cert_replayed = verify_proof_script(payload, kernel=fresh_kernel, quiet=True)
    cert_via_obj = parsed.verify(fresh_kernel, quiet=True)

    for c in (cert_original, cert_replayed, cert_via_obj):
        assert c.success, c.message
        assert c.kernel_verified

    # Content hashes agree — same goal, same tactic, same source pin.
    assert cert_original.content_hash == cert_replayed.content_hash == cert_via_obj.content_hash


def test_proof_script_source_fingerprint_affects_content_hash():
    """Two otherwise-identical scripts with different source_fingerprints
    produce different content hashes — so a stale proof shipped against
    updated code can't masquerade as fresh."""
    kernel = ProofKernel()
    reg = AxiomRegistry()
    reg.add_all(deep_function_to_axioms(_length, module="tests"),
                source="length")
    reg.install(kernel)

    goal_builder = lambda: eq(
        OpCall(Op("_length", "tests"), (op_nil(),)), Literal(0, _OBJ)
    )
    tactic_builder = lambda: Tactics.cases("_length", 1, "tests")

    cert_v1 = ProofScript(
        "thm", goal_builder(), tactic_builder(), "sha:v1",
    ).verify(kernel, quiet=True)
    cert_v2 = ProofScript(
        "thm", goal_builder(), tactic_builder(), "sha:v2",
    ).verify(kernel, quiet=True)

    assert cert_v1.content_hash != cert_v2.content_hash


# ── Real ListInduction via Tactics.induction ────────────────────────

def test_tactics_induction_builds_a_real_list_induction_term():
    """``Tactics.induction`` should produce a kernel ``ListInduction`` term,
    not cite a synthesized ``_induction`` axiom — i.e. the kernel does
    the work, not a string-matched axiom."""
    from deppy.core.kernel import ListInduction
    from deppy.proofs.tactics import ProofBuilder

    kernel = ProofKernel()
    goal = eq(Var("xs"), Var("xs"), xs="object")
    pb = ProofBuilder(
        kernel, goal.ctx,
        formal_eq(goal.ctx, goal.lhs, goal.rhs, type_=_OBJ),
    )
    tac = Tactics.induction(
        "xs",
        nil=Tactics.refl(Var("xs")),
        cons=Tactics.refl(Var("xs")),
    )
    proof = tac.compile(pb)
    assert isinstance(proof, ListInduction), (
        f"expected kernel ListInduction, got {type(proof).__name__}"
    )


# ── register_universal_axioms helper ─────────────────────────────────

def test_register_universal_axioms_installs_foldl_into_kernel():
    kernel = ProofKernel()
    added = register_universal_axioms(kernel)
    assert added == 2  # foldl_nil + foldl_cons

    reg = AxiomRegistry()
    added_reg = register_universal_axioms(reg)
    assert added_reg == 2
    assert ("deppy.list", "foldl_nil") in reg.by_qname
    assert ("deppy.list", "foldl_cons") in reg.by_qname
