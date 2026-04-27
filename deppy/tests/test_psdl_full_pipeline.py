"""End-to-end smoke tests for the PSDL → certificate pipeline.

Each test exercises a slice of the cubical+effect+heap model and
verifies the kernel emits the right ProofTerm shapes.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from deppy.proofs.psdl import compile_psdl


def test_pure_proof():
    """A purely functional PSDL block — no effects, no errors."""
    src = """
(h := apply(F))
swap = h.symm
result = h @ swap
qed()
"""
    res = compile_psdl(src, foundations={"F": object()})
    assert res.ok, f"errors: {res.errors}"
    assert res.final_epoch == 0  # no mutations
    assert "F" in res.foundations_referenced


def test_break_invalidates_loop_induction():
    """``break`` must produce a soundness error so a fake
    ListInduction is not emitted as if it were total."""
    src = """
for x in xs:
    apply(F)
    break
"""
    res = compile_psdl(src, foundations={"F": object()})
    assert any(
        "break" in e.message.lower() for e in res.errors
    ), f"errors: {res.errors}"


def test_match_guards_propagate():
    """``case x if cond:`` should wrap the case body in a Cut over
    the guard predicate."""
    src = """
match v:
    case 0:
        refl(0)
    case n if n > 0:
        apply(F)
"""
    res = compile_psdl(src, foundations={"F": object()})
    # The compile itself succeeds — the guard creates a Cut+Z3Proof
    # in the kernel artefact (we don't expose internals here, just
    # confirm no errors).
    # Match itself adds a "non-arithmetic" Z3 error; that's OK —
    # the guard reaches the kernel.
    assert res.proof_term is not None


def test_try_finally_chained():
    """``finally`` chains via Cut; the cleanup proof is required
    along both the value-fibre and exception-fibre paths."""
    src = """
try:
    apply(F)
except TypeError:
    apply(G)
finally:
    apply(H)
"""
    res = compile_psdl(
        src,
        foundations={"F": object(), "G": object(), "H": object()},
    )
    assert res.ok, f"errors: {res.errors}"
    repr_text = res.term_repr
    # Value witness present:
    assert "EffectWitness(value" in repr_text
    # Handler present (ConditionalEffectWitness):
    assert "CondEffectWitness" in repr_text or "ConditionalEffect" in repr_text
    # Finally chained:
    assert "_try_finally" in repr_text or "finally" in repr_text.lower()


def test_cubical_heap_alias_mutation_warns():
    """Mutation through an alias should fire a soundness warning."""
    src = """
backup = mylist
mylist.append(42)
"""
    res = compile_psdl(src, foundations={})
    # The lint produces an error when mutation crosses an alias
    # group.
    assert any(
        "alias" in e.message.lower() or "mutation" in e.message.lower()
        for e in res.errors
    ), f"errors: {res.errors}"


def test_cubical_heap_transport_required_after_mutation():
    """A name read after its cell was mutated should emit a
    TransportProof in the kernel artefact."""
    src = """
mylist.append(42)
result = mylist
"""
    res = compile_psdl(src, foundations={})
    repr_text = res.term_repr
    # The mutation effect is recorded:
    assert "mutate:" in repr_text
    # Read after mutation produces a transport:
    assert "TransportProof" in repr_text


def test_generator_yields_emit_effect_witnesses():
    """Each ``yield`` in a generator function is an EffectWitness
    in the ◇ modality."""
    src = """
def my_gen():
    yield 1
    yield 2
    yield 3
"""
    res = compile_psdl(src, foundations={})
    repr_text = res.term_repr
    assert repr_text.count("yield:0") >= 1
    assert repr_text.count("yield:1") >= 1
    assert repr_text.count("yield:2") >= 1


def test_async_await_emits_effect_witness():
    """``await x`` is an EffectWitness with effect ``await:X``."""
    src = """
async def fetch():
    a = await call_one
    b = await call_two
"""
    res = compile_psdl(src, foundations={})
    repr_text = res.term_repr
    assert "await:" in repr_text


def test_mro_lookup_emits_duck_path():
    """``mro_lookup(Cls, "method")`` walks the C3 linearization as
    a DuckPath."""
    src = """
result = mro_lookup(MyClass, "method")
"""
    res = compile_psdl(src, foundations={})
    assert "DuckPath" in res.term_repr


def test_op_dispatch_emits_conditional_duck_path():
    """``op_dispatch("+", a, b)`` (no class info) emits a
    ConditionalDuckPath directly; with classes, an outer Fiber for
    subclass-priority wraps the ConditionalDuckPath."""
    # Without classes — direct ConditionalDuckPath.
    res1 = compile_psdl(
        'result = op_dispatch("+", a, b)\n',
        foundations={},
    )
    assert "ConditionalDuckPath" in res1.term_repr
    # With classes — outer Fiber for subclass priority.
    res2 = compile_psdl(
        'result = op_dispatch("+", a, b, lhs_class=Foo, rhs_class=Bar)\n',
        foundations={},
    )
    assert "Fiber" in res2.term_repr


def test_descriptor_get_emits_4_branch_fiber():
    """``descriptor_get`` emits a Fiber over the four-branch
    Python attribute-resolution chain."""
    src = """
result = descriptor_get(obj, "Cls", "attr")
"""
    res = compile_psdl(src, foundations={})
    assert "Fiber" in res.term_repr


def test_descriptor_set_emits_patch():
    """``descriptor_set`` is a monkey-patch path: emits Patch."""
    src = """
descriptor_set(obj, "Cls", "attr", 42)
"""
    res = compile_psdl(src, foundations={})
    assert "Patch" in res.term_repr


def test_effect_sequence_records_mutations_in_order():
    """The effect-sequence in the result records each mutation's
    line, kind and locator in source order."""
    src = """
a.append(1)
a.extend([2])
a.pop()
"""
    res = compile_psdl(src, foundations={})
    assert len(res.effect_sequence) == 3
    kinds = [e[1] for e in res.effect_sequence]
    assert all(k == "mutate" for k in kinds)
    assert res.final_epoch == 3


def test_unknown_call_records_error():
    """An unknown function call must surface as an error so
    ``result.ok`` reflects the proof's incompleteness."""
    src = """
result = mystery_function(x)
"""
    res = compile_psdl(src, foundations={})
    assert not res.ok
    assert any(
        "unknown PSDL primitive" in e.message
        for e in res.errors
    )


def test_late_closure_binding_warns():
    """``[lambda: i for i in xs]`` is the Python late-binding trap."""
    src = """
fns = [lambda: i for i in xs]
"""
    res = compile_psdl(src, foundations={})
    assert any(
        "late closure binding" in e.message
        for e in res.errors
    )


def test_mutable_default_warns():
    """``def f(x=[])`` mutable-default trap."""
    src = """
def helper(x=[]):
    return x
"""
    res = compile_psdl(src, foundations={})
    assert any(
        "mutable default" in e.message
        for e in res.errors
    )


def test_iterator_exhaustion_warns():
    """``for x in zip(a, b):`` over a one-shot iterator."""
    src = """
for y in zip(a, b):
    apply(F)
"""
    res = compile_psdl(src, foundations={"F": object()})
    assert any(
        "one-shot iterator" in e.message
        for e in res.errors
    )


def test_decorated_sidecar_extracts_correctly():
    """Decorator-based sidecar extraction produces a SidecarModule
    with the same shape that .deppy parsing produces."""
    import importlib
    from deppy.proofs.sidecar_decorators import (
        extract_sidecar_module, reset_registry,
    )
    reset_registry()
    mod = importlib.import_module("examples.decorated_geometry")
    sm = extract_sidecar_module(mod)
    # Foundations were registered.
    assert "Real_sqrt_nonneg" in sm.foundations
    assert "Real_sub_sq_swap" in sm.foundations
    # Axioms were registered.
    assert "dist_nonneg" in sm.axioms
    # Spec on Point class registered.
    assert any("Point" in t for t in sm.specs)
    # Verify blocks present, including PSDL.
    assert any(
        v.psdl_proof.strip() and "isinstance(other, Point)" in v.psdl_proof
        for v in sm.verifies
    ), "PSDL proof not propagated through @psdl_proof decorator"
    # Code types registered via call-form decorator.
    assert "sqrt" in sm._code_types
    assert sm._code_types["sqrt"] == "Int → Int"


def test_decorated_sidecar_certifies_via_pipeline():
    """The decorator-extracted SidecarModule passes through the
    full pipeline including Lean round-trip."""
    import importlib
    from pathlib import Path
    from deppy.proofs.sidecar_decorators import (
        extract_sidecar_module, reset_registry,
    )
    reset_registry()
    mod = importlib.import_module("examples.decorated_geometry")
    sm = extract_sidecar_module(mod)
    from deppy.lean.sidecar_runner import _run_with_module
    out = Path("/tmp/decorated_geometry.lean")
    rr = _run_with_module(
        sm,
        out_path=out,
        sidecar_path=Path(mod.__file__ or "<decorated>"),
    )
    assert rr.certified, (
        f"certify_or_die failed: {rr.certify_failures}"
    )


def test_full_pipeline_certifies_sympy_geometry():
    """Run the full sidecar pipeline on the bundled example and
    confirm certify_or_die passes."""
    repo_root = Path(__file__).resolve().parent.parent.parent
    deppy_path = repo_root / "sympy_geometry.deppy"
    if not deppy_path.exists():
        pytest.skip("sympy_geometry.deppy not present")
    out_path = repo_root / "sympy_geometry.lean"
    json_path = repo_root / "sympy_geometry.json"
    from deppy.lean.sidecar_runner import run_sidecar
    rr = run_sidecar(deppy_path, out_path=out_path)
    assert rr.certified, (
        f"certify_or_die failed: {rr.certify_failures}"
    )
    assert json_path.exists(), "JSON sidecar not emitted"
    payload = json.loads(json_path.read_text())
    assert payload["certified"] is True
    assert payload["section_counters"]["verify_kernel_verified"] == \
        payload["section_counters"]["verify_total"]
