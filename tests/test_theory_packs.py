from __future__ import annotations

import os
import sys
from dataclasses import asdict

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

from deppy.core._protocols import SiteKind
from deppy.theory_packs import (
    TheoryPackConfigurationError,
    available_theory_packs,
    load_theory_pack,
    verify_loaded_pack,
)
from deppy.theory_packs.models import AxiomSpec, TheoryPackSpec, VerificationCase
from deppy.theory_packs.numpy_pack import build_numpy_pack_spec
from deppy.theory_packs.verifier import TheoryPackVerifier


def test_available_theory_packs_contains_builtin_specs() -> None:
    assert available_theory_packs() == ("numpy", "pandas", "torch")


def test_unknown_pack_name_raises_configuration_error() -> None:
    with pytest.raises(TheoryPackConfigurationError):
        load_theory_pack("not-a-pack")


def test_model_round_trip_is_json_like() -> None:
    case = VerificationCase(name="example", operation="reshape", payload={"shape": [2, 3]}, expected={"size": 6})
    axiom = AxiomSpec(
        name="shape-law",
        library="numpy",
        version_range=">=1.0",
        site_kinds=(SiteKind.TENSOR_SHAPE,),
        verification_cases=(case,),
    )
    spec = TheoryPackSpec(
        name="demo",
        library="numpy",
        version_range=">=1.0",
        site_kinds=(SiteKind.TENSOR_SHAPE,),
        delegate_pack_names=("tensor_shape",),
        axioms=(axiom,),
    )

    encoded = asdict(spec)

    assert encoded["name"] == "demo"
    assert encoded["axioms"][0]["verification_cases"][0]["payload"]["shape"] == [2, 3]


def test_load_numpy_pack_uses_existing_registry_and_verifies_runtime() -> None:
    report = load_theory_pack("numpy")

    assert report.loaded is True
    assert report.spec.name == "numpy"
    assert report.pack.handles_kind(SiteKind.TENSOR_SHAPE)
    assert report.verification.available is True
    assert report.verification.library_version is not None
    assert report.verification.verified_count >= 1


def test_verify_pack_marks_cases_skipped_when_library_is_unavailable(monkeypatch: pytest.MonkeyPatch) -> None:
    spec = build_numpy_pack_spec()
    verifier = TheoryPackVerifier()

    def _boom(name: str):
        raise ImportError(f"missing {name}")

    monkeypatch.setattr("deppy.theory_packs.verifier.importlib.import_module", _boom)
    report = verifier.verify_pack_spec(spec)

    assert report.available is False
    assert report.skipped_count == sum(len(axiom.verification_cases) for axiom in spec.axioms)
    assert report.verification_status == "unavailable"


def test_verify_loaded_pack_function_accepts_spec() -> None:
    report = verify_loaded_pack(build_numpy_pack_spec())
    assert report.pack_name == "numpy"
    assert report.available is True


def test_verify_loaded_pack_accepts_loaded_report() -> None:
    loaded = load_theory_pack("numpy")
    report = verify_loaded_pack(loaded)
    assert report.pack_name == "numpy"
    assert report.available is True
