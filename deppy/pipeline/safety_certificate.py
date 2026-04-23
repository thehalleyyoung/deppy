"""
Deppy Pipeline — Module Safety Certificate (Gap 12)

A serializable, content-addressed certificate that records the result of a
``verify_module_safety()`` run.  Certificates are designed to be:

* **Reproducible** — pinned to a SHA-256 hash of the source.
* **Auditable** — list every per-function trust level, the obligations
  discharged, the kernel proof identifier, and (if available) the Lean
  theorem name plus its source.
* **Portable** — round-trip through JSON without loss.
* **Composable** — multiple module certificates can be aggregated into a
  package-level certificate carrying the minimum trust across modules.

Typical usage::

    verdict = verify_module_safety(src, sidecar_specs=specs, emit_lean=True)
    cert = certificate_from_verdict(verdict, src)
    Path("mymod.deppy-cert.json").write_text(cert.to_json())

    # Later (potentially in another process):
    loaded = ModuleSafetyCertificate.from_json(text)
    assert loaded.matches_source(src)         # SHA still aligns
    assert loaded.aggregate_trust >= TrustLevel.Z3_PROVEN
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field, asdict
from typing import Any, Optional

from deppy.core.kernel import (
    TrustLevel, ProofKernel, ConditionalEffectWitness, SemanticSafetyWitness,
    SourceDischarge, Z3Proof, AxiomInvocation, Structural, Assume,
    ModuleSafetyComposition,
)
from deppy.core.types import Context, Judgment, JudgmentKind, Var, PyObjType
from deppy.lean.lean_runner import check_lean_module_source
from deppy.pipeline.safety_pipeline import SafetyVerdict


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


@dataclass
class FunctionCertificate:
    """Per-function audit entry."""
    name: str
    is_safe: bool
    trust: str                       # TrustLevel.name
    coverage_ratio: float
    obligations: list[str] = field(default_factory=list)
    addressed: list[str] = field(default_factory=list)
    unaddressed: list[str] = field(default_factory=list)
    counterexamples: list[dict] = field(default_factory=list)
    proof_payload: Optional[dict[str, Any]] = None
    lean_theorem: Optional[str] = None
    lean_source: Optional[str] = None

    def to_dict(self) -> dict:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: dict) -> "FunctionCertificate":
        return cls(**d)


@dataclass
class ModuleSafetyCertificate:
    """An auditable, serializable module safety certificate."""
    module_path: str
    source_sha256: str
    aggregate_trust: str             # TrustLevel.name
    is_safe: bool
    overall_coverage: float
    functions: list[FunctionCertificate] = field(default_factory=list)
    module_proof_payload: Optional[dict[str, Any]] = None
    lean_checked: bool = False
    lean_module_source: Optional[str] = None
    notes: list[str] = field(default_factory=list)
    deppy_version: str = "0.1"
    schema_version: int = 1

    @property
    def trust_level(self) -> TrustLevel:
        return TrustLevel[self.aggregate_trust]

    def matches_source(self, source: str) -> bool:
        return _sha256(source) == self.source_sha256

    def to_dict(self) -> dict:
        return {
            "schema_version": self.schema_version,
            "deppy_version": self.deppy_version,
            "module_path": self.module_path,
            "source_sha256": self.source_sha256,
            "aggregate_trust": self.aggregate_trust,
            "is_safe": self.is_safe,
            "overall_coverage": self.overall_coverage,
            "module_proof_payload": self.module_proof_payload,
            "lean_checked": self.lean_checked,
            "lean_module_source": self.lean_module_source,
            "notes": list(self.notes),
            "functions": [f.to_dict() for f in self.functions],
        }

    def to_json(self, *, indent: int = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent, sort_keys=True)

    @classmethod
    def from_dict(cls, d: dict) -> "ModuleSafetyCertificate":
        fns = [FunctionCertificate.from_dict(f) for f in d.get("functions", [])]
        return cls(
            module_path=d["module_path"],
            source_sha256=d["source_sha256"],
            aggregate_trust=d["aggregate_trust"],
            is_safe=d["is_safe"],
            overall_coverage=d.get("overall_coverage", 0.0),
            functions=fns,
            module_proof_payload=d.get("module_proof_payload"),
            lean_checked=bool(d.get("lean_checked", False)),
            lean_module_source=d.get("lean_module_source"),
            notes=list(d.get("notes", [])),
            deppy_version=d.get("deppy_version", "0.1"),
            schema_version=d.get("schema_version", 1),
        )

    @classmethod
    def from_json(cls, text: str) -> "ModuleSafetyCertificate":
        return cls.from_dict(json.loads(text))


def certificate_from_verdict(
    verdict: SafetyVerdict,
    source: str,
) -> ModuleSafetyCertificate:
    """Build a certificate from a ``SafetyVerdict`` and its source text."""
    fns: list[FunctionCertificate] = []
    for fn_name, fv in verdict.functions.items():
        spec = verdict.merged_specs.get(fn_name)
        obligations = list(getattr(spec, "exception_free_when", []) or []) \
            if spec else []
        fns.append(FunctionCertificate(
            name=fn_name,
            is_safe=fv.is_safe,
            trust=fv.trust.name,
            coverage_ratio=fv.coverage_ratio,
            obligations=obligations,
            addressed=list(fv.addressed),
            unaddressed=list(fv.unaddressed),
            counterexamples=[{
                "source_id": c.source_id,
                "inputs": dict(c.inputs),
                "exception_type": c.exception_type,
                "message": c.message,
                "source": c.source,
            } for c in fv.counterexamples],
            proof_payload=fv.proof_payload,
            lean_theorem=f"safe_{fn_name}" if fv.lean_proof else None,
            lean_source=fv.lean_proof,
        ))
    overall = verdict.coverage.overall_coverage if verdict.coverage else 0.0
    return ModuleSafetyCertificate(
        module_path=verdict.module_path,
        source_sha256=_sha256(source),
        aggregate_trust=verdict.aggregate_trust.name,
        is_safe=verdict.is_safe,
        overall_coverage=overall,
        functions=fns,
        module_proof_payload=verdict.module_proof_payload,
        lean_checked=verdict.lean_checked,
        lean_module_source=verdict.lean_module_source,
        notes=list(verdict.notes),
    )


@dataclass
class RecheckReport:
    ok: bool
    source_hash_ok: bool
    kernel_ok: bool
    lean_ok: bool
    notes: list[str] = field(default_factory=list)


def _deserialize_atomic_proof(payload: dict[str, Any]):
    kind = payload.get("kind")
    if kind == "Z3Proof":
        return Z3Proof(formula=payload["formula"])
    if kind == "AxiomInvocation":
        return AxiomInvocation(name=payload["name"], module=payload.get("module", ""))
    if kind == "Structural":
        return Structural(description=payload.get("description", ""))
    if kind == "Assume":
        return Assume(name=payload.get("name", "assume"))
    raise ValueError(f"unsupported proof payload: {kind}")


def _deserialize_source_discharge(payload: dict[str, Any]) -> SourceDischarge:
    return SourceDischarge(
        source_id=payload["source_id"],
        failure_kind=payload["failure_kind"],
        safety_predicate=payload["safety_predicate"],
        note=payload.get("note", ""),
        inner=_deserialize_atomic_proof(payload["inner"]),
    )


def _deserialize_conditional_witness(payload: dict[str, Any]) -> ConditionalEffectWitness:
    sem = payload["semantic"]
    sem_w = SemanticSafetyWitness(
        target=sem["target"],
        precondition=sem["precondition"],
        is_total_escape=bool(sem.get("is_total_escape", False)),
        discharges=[_deserialize_source_discharge(d)
                    for d in sem.get("discharges", [])],
    )
    return ConditionalEffectWitness(
        precondition=payload["precondition"],
        effect=payload["effect"],
        proof=sem_w,
        target=payload["target"],
    )


def recheck_certificate(
    cert: ModuleSafetyCertificate,
    source: str,
) -> RecheckReport:
    """Replay embedded proof payloads and optional Lean source."""
    notes: list[str] = []
    source_hash_ok = cert.matches_source(source)
    if not source_hash_ok:
        notes.append("source hash mismatch")

    kernel = ProofKernel()
    ctx = Context()
    goal = Judgment(
        kind=JudgmentKind.TYPE_CHECK,
        context=ctx,
        term=Var("safety"),
        type_=PyObjType(),
    )
    kernel_ok = True
    try:
        fn_witnesses = {}
        for f in cert.functions:
            if not f.proof_payload:
                continue
            fn_witnesses[f.name] = _deserialize_conditional_witness(f.proof_payload)
        module_payload = cert.module_proof_payload or {}
        module_discharges = [
            _deserialize_source_discharge(d)
            for d in module_payload.get("module_discharges", [])
        ]
        composition = ModuleSafetyComposition(
            module_path=cert.module_path,
            function_witnesses=fn_witnesses,
            module_discharges=module_discharges,
            internal_calls_closed=bool(module_payload.get("internal_calls_closed", True)),
        )
        kernel_result = kernel.verify(ctx, goal, composition)
        kernel_ok = bool(kernel_result.success)
        if not kernel_ok:
            notes.append(kernel_result.message)
    except Exception as e:
        kernel_ok = False
        notes.append(f"kernel replay failed: {e}")

    lean_ok = True
    if cert.lean_module_source:
        lean_result = check_lean_module_source(cert.lean_module_source)
        lean_ok = bool(lean_result.ok)
        if not lean_ok:
            notes.append((lean_result.stderr or lean_result.stdout).strip())

    return RecheckReport(
        ok=source_hash_ok and kernel_ok and lean_ok,
        source_hash_ok=source_hash_ok,
        kernel_ok=kernel_ok,
        lean_ok=lean_ok,
        notes=notes,
    )


@dataclass
class PackageSafetyCertificate:
    """Aggregate certificate across multiple modules."""
    package: str
    modules: list[ModuleSafetyCertificate] = field(default_factory=list)
    schema_version: int = 1

    @property
    def aggregate_trust(self) -> TrustLevel:
        if not self.modules:
            return TrustLevel.UNTRUSTED
        return min((m.trust_level for m in self.modules),
                   key=lambda t: t.value)

    @property
    def is_safe(self) -> bool:
        return bool(self.modules) and all(m.is_safe for m in self.modules)

    def to_dict(self) -> dict:
        return {
            "schema_version": self.schema_version,
            "package": self.package,
            "aggregate_trust": self.aggregate_trust.name,
            "is_safe": self.is_safe,
            "modules": [m.to_dict() for m in self.modules],
        }

    def to_json(self, *, indent: int = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent, sort_keys=True)

    @classmethod
    def from_dict(cls, d: dict) -> "PackageSafetyCertificate":
        return cls(
            package=d["package"],
            modules=[ModuleSafetyCertificate.from_dict(m)
                     for m in d.get("modules", [])],
            schema_version=d.get("schema_version", 1),
        )

    @classmethod
    def from_json(cls, text: str) -> "PackageSafetyCertificate":
        return cls.from_dict(json.loads(text))


__all__ = [
    "FunctionCertificate",
    "ModuleSafetyCertificate",
    "PackageSafetyCertificate",
    "RecheckReport",
    "certificate_from_verdict",
    "recheck_certificate",
]
