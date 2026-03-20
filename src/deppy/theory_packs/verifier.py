from __future__ import annotations

import importlib
import importlib.metadata
from typing import Callable

from .models import (
    AxiomSpec,
    AxiomVerificationResult,
    PackLoadReport,
    TheoryPackSpec,
    VerificationCase,
    VerificationReport,
)


class TheoryPackVerifier:
    """Run runtime pack verification against the currently installed library."""

    def verify_pack_spec(self, spec: TheoryPackSpec) -> VerificationReport:
        try:
            module = importlib.import_module(spec.library)
        except Exception as exc:
            skipped = tuple(
                AxiomVerificationResult(
                    axiom_name=axiom.name,
                    case_name=case.name,
                    status="skipped",
                    message=f"{spec.library} unavailable: {exc}",
                )
                for axiom in spec.axioms
                for case in axiom.verification_cases
            )
            return VerificationReport(
                pack_name=spec.name,
                library=spec.library,
                available=False,
                library_version=None,
                axiom_results=skipped,
                trusted_axioms=(),
                warnings=(f"{spec.library} is not installed; runtime axioms were skipped",),
            )

        version = self._library_version(spec.library, module)
        verifier = _case_verifier_for(spec.name)
        results = []
        trusted_axioms = []
        warnings = []
        for axiom in spec.axioms:
            axiom_ok = True
            for case in axiom.verification_cases:
                try:
                    passed, message = verifier(axiom, case, module)
                except Exception as exc:
                    passed = False
                    message = f"verification raised {type(exc).__name__}: {exc}"
                status = "verified" if passed else "failed"
                results.append(
                    AxiomVerificationResult(
                        axiom_name=axiom.name,
                        case_name=case.name,
                        status=status,
                        message=message,
                    )
                )
                if not passed:
                    axiom_ok = False
            if axiom_ok and axiom.verification_cases:
                trusted_axioms.append(axiom.name)
            elif not axiom_ok:
                warnings.append(f"axiom {axiom.name!r} did not fully verify against installed {spec.library}")

        return VerificationReport(
            pack_name=spec.name,
            library=spec.library,
            available=True,
            library_version=version,
            axiom_results=tuple(results),
            trusted_axioms=tuple(trusted_axioms),
            warnings=tuple(warnings),
        )

    def _library_version(self, library: str, module: object) -> str | None:
        try:
            return importlib.metadata.version(library)
        except Exception:
            return getattr(module, "__version__", None)


def verify_pack_spec(spec: TheoryPackSpec) -> VerificationReport:
    return TheoryPackVerifier().verify_pack_spec(spec)


def verify_loaded_pack(
    pack: str | TheoryPackSpec | PackLoadReport,
) -> VerificationReport:
    if isinstance(pack, TheoryPackSpec):
        return verify_pack_spec(pack)
    if isinstance(pack, PackLoadReport):
        return verify_pack_spec(pack.spec)
    if isinstance(pack, str):
        from .registry_bridge import get_loaded_pack_report

        report = get_loaded_pack_report(pack)
        if report is None:
            raise ValueError(f"pack {pack!r} has not been loaded")
        return verify_pack_spec(report.spec)
    raise TypeError("pack must be a pack name, TheoryPackSpec, or PackLoadReport")


def _case_verifier_for(pack_name: str) -> Callable[[AxiomSpec, VerificationCase, object], tuple[bool, str]]:
    if pack_name == "numpy":
        from .numpy_pack import verify_numpy_axiom_case

        return verify_numpy_axiom_case
    if pack_name == "pandas":
        from .pandas_pack import verify_pandas_axiom_case

        return verify_pandas_axiom_case
    if pack_name == "torch":
        from .torch_pack import verify_torch_axiom_case

        return verify_torch_axiom_case
    raise ValueError(f"unsupported theory pack verifier: {pack_name}")
