from __future__ import annotations

from typing import Dict

from deppy.library_theories import ComposedPack, TheoryPackBase, get_default_registry
from deppy.library_theories.pack_registry import PackRegistryImpl
from deppy.library_theories.pytorch import TorchShapePack

from .models import PackLoadReport, TheoryPackSpec, VerificationReport
from .numpy_pack import build_numpy_pack_spec
from .pandas_pack import build_pandas_pack_spec
from .torch_pack import build_torch_pack_spec
from .verifier import TheoryPackVerifier


class TheoryPackConfigurationError(ValueError):
    """Raised when a pack name/spec cannot be loaded correctly."""


_PACK_BUILDERS = {
    "numpy": build_numpy_pack_spec,
    "pandas": build_pandas_pack_spec,
    "torch": build_torch_pack_spec,
}
_RUNTIME_PACKS = {
    "torch_shape": TorchShapePack,
}
_REGISTERED_SPECS: Dict[str, TheoryPackSpec] = {}
_LOADED_REPORTS: Dict[str, PackLoadReport] = {}


def register_pack_spec(spec: TheoryPackSpec) -> TheoryPackSpec:
    if not spec.name:
        raise TheoryPackConfigurationError("pack spec name must be non-empty")
    _REGISTERED_SPECS[spec.name] = spec
    return spec


def available_theory_packs() -> tuple[str, ...]:
    _ensure_default_specs()
    return tuple(sorted(_REGISTERED_SPECS))


def load_theory_pack(
    name: str,
    *,
    registry: PackRegistryImpl | None = None,
    verify: bool = True,
    verifier: TheoryPackVerifier | None = None,
) -> PackLoadReport:
    _ensure_default_specs()
    spec = _REGISTERED_SPECS.get(name)
    if spec is None:
        raise TheoryPackConfigurationError(f"unknown theory pack: {name}")

    active_registry = registry or get_default_registry()
    _ensure_runtime_packs(spec, active_registry)
    delegates = []
    missing = []
    for delegate_name in spec.delegate_pack_names:
        pack = active_registry.get_pack(delegate_name)
        if pack is None:
            missing.append(delegate_name)
        else:
            delegates.append(pack)
    if missing:
        raise TheoryPackConfigurationError(
            f"pack {name!r} could not resolve delegate packs: {', '.join(missing)}"
        )

    resolved_pack: TheoryPackBase
    if len(delegates) == 1:
        resolved_pack = delegates[0]
    else:
        resolved_pack = ComposedPack(delegates)

    if verify:
        verification = (verifier or TheoryPackVerifier()).verify_pack_spec(spec)
    else:
        verification = VerificationReport(
            pack_name=spec.name,
            library=spec.library,
            available=True,
            library_version=None,
            axiom_results=(),
            trusted_axioms=(),
            warnings=("runtime verification skipped by caller",),
        )
    warnings = tuple(dict.fromkeys((*verification.warnings,)))
    report = PackLoadReport(
        spec=spec,
        pack=resolved_pack,
        loaded=True,
        verification=verification,
        warnings=warnings,
    )
    _LOADED_REPORTS[name] = report
    return report


def get_loaded_pack_report(name: str) -> PackLoadReport | None:
    return _LOADED_REPORTS.get(name)


def _ensure_default_specs() -> None:
    if _REGISTERED_SPECS:
        return
    for builder in _PACK_BUILDERS.values():
        register_pack_spec(builder())


def _ensure_runtime_packs(spec: TheoryPackSpec, registry: PackRegistryImpl) -> None:
    for delegate_name in spec.delegate_pack_names:
        if registry.get_pack(delegate_name) is not None:
            continue
        builder = _RUNTIME_PACKS.get(delegate_name)
        if builder is None:
            continue
        registry.register(builder())
