from __future__ import annotations

from deppy.hybrid.core.intent_bridge import IntentBridge
from deppy.hybrid.lean_translation.lean_emitter import LeanClaim, LeanEmitter
from deppy.hybrid.research.verified_foundations import BootstrapVerification
from deppy.hybrid.zero_change.implicit_presheaf import ImplicitPresheafExtractor


def test_intent_bridge_extracts_structural_claim() -> None:
    res = IntentBridge().from_text("Function must return a non-empty list.")
    assert res.structural.predicates
    assert res.hybrid_type.intent.text


def test_implicit_presheaf_extracts_sections() -> None:
    src = (
        'def f(x: int) -> int:\n'
        '    """Return positive result."""\n'
        "    assert x >= 0\n"
        "    return x + 1\n"
    )
    model = ImplicitPresheafExtractor().extract_source(src)
    assert len(model.sections) == 1
    assert model.sections[0].structural_hints


def test_lean_emitter_renders_theorem() -> None:
    emitter = LeanEmitter()
    artifact = emitter.emit_claims(
        [LeanClaim(name="demo_theorem", proposition="True", source="test")]
    )
    text = artifact.to_text()
    assert "theorem demo_theorem" in text


def test_verified_foundations_bootstrap_runs() -> None:
    report = BootstrapVerification.run()
    assert report["metrics"]["total"] >= 1

