"""Codegen plan extraction from expanded hybrid type structures.

This module converts expansion trees (Σ/Π/refinement/identity information)
into reusable, serializable planning artifacts for downstream generation and
verification.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple


@dataclass
class PlanModule:
    """Single module artifact extracted from an expanded decomposition."""

    name: str
    path: str
    summary: str
    responsibilities: List[str] = field(default_factory=list)
    depends_on: List[str] = field(default_factory=list)
    exports: List[str] = field(default_factory=list)
    imports: List[str] = field(default_factory=list)
    estimated_loc: int = 120
    sigma_width: int = 1
    pi_arity: int = 1
    constraints: List[Dict[str, Any]] = field(default_factory=list)
    test_obligations: List[str] = field(default_factory=list)
    class_specs: List[Dict[str, Any]] = field(default_factory=list)
    function_specs: List[Dict[str, Any]] = field(default_factory=list)
    ideation_lenses: List[Dict[str, Any]] = field(default_factory=list)
    ideation_benefit: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "path": self.path,
            "summary": self.summary,
            "responsibilities": list(self.responsibilities),
            "depends_on": list(self.depends_on),
            "exports": list(self.exports),
            "imports": list(self.imports),
            "estimated_loc": self.estimated_loc,
            "sigma_width": self.sigma_width,
            "pi_arity": self.pi_arity,
            "constraints": list(self.constraints),
            "test_obligations": list(self.test_obligations),
            "class_specs": list(self.class_specs),
            "function_specs": list(self.function_specs),
            "ideation_lenses": list(self.ideation_lenses),
            "ideation_benefit": dict(self.ideation_benefit),
        }


@dataclass
class PlanInterface:
    """Identity/compatibility obligation for shared APIs."""

    name: str
    provider: str
    consumer: str
    provider_type: str
    consumer_type: str
    obligation: str

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "provider": self.provider,
            "consumer": self.consumer,
            "provider_type": self.provider_type,
            "consumer_type": self.consumer_type,
            "obligation": self.obligation,
        }


@dataclass
class PhasePlan:
    """Topological generation phase produced from Σ dependencies."""

    index: int
    module_names: List[str]
    gate_checks: List[str]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "index": self.index,
            "module_names": list(self.module_names),
            "gate_checks": list(self.gate_checks),
        }


@dataclass
class CodeGenPlan:
    """Reusable compiler artifact for generation, testing, and verification."""

    spec: str
    target_loc: int
    modules: List[PlanModule] = field(default_factory=list)
    interfaces: List[PlanInterface] = field(default_factory=list)
    constraints: List[Dict[str, Any]] = field(default_factory=list)
    tests: List[Dict[str, Any]] = field(default_factory=list)
    phases: List[PhasePlan] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)

    @classmethod
    def compile(
        cls,
        *,
        spec: str,
        target_loc: int,
        nodes: Sequence[Dict[str, Any]],
        interfaces: Sequence[Dict[str, Any]],
        constraints: Sequence[Dict[str, Any]],
        metadata: Optional[Dict[str, Any]] = None,
    ) -> "CodeGenPlan":
        """Compile a normalized expansion result into a stable plan shape."""
        modules: List[PlanModule] = []
        tests: List[Dict[str, Any]] = []

        for node in nodes:
            module = PlanModule(
                name=str(node.get("name", "module")),
                path=str(node.get("path") or cls._default_module_path(node)),
                summary=str(node.get("summary", "")),
                responsibilities=list(node.get("responsibilities", [])),
                depends_on=list(node.get("depends_on", [])),
                exports=list(node.get("exports", [])),
                imports=list(node.get("imports", [])),
                estimated_loc=int(node.get("estimated_loc", 120)),
                sigma_width=int(node.get("sigma_width", 1)),
                pi_arity=int(node.get("pi_arity", 1)),
                constraints=list(node.get("constraints", [])),
                test_obligations=list(node.get("test_obligations", [])),
                class_specs=list(node.get("class_specs", [])),
                function_specs=list(node.get("function_specs", [])),
                ideation_lenses=list(node.get("ideation_lenses", [])),
                ideation_benefit=dict(node.get("ideation_benefit", {})),
            )
            modules.append(module)

            for idx, obligation in enumerate(module.test_obligations):
                tests.append(
                    {
                        "name": f"test_{module.name}_{idx + 1}",
                        "module": module.name,
                        "kind": "refinement",
                        "assertion": obligation,
                    }
                )

        iface_objs = [
            PlanInterface(
                name=str(i.get("name", "shared_api")),
                provider=str(i.get("provider", "")),
                consumer=str(i.get("consumer", "")),
                provider_type=str(i.get("provider_type", "Any")),
                consumer_type=str(i.get("consumer_type", "Any")),
                obligation=str(i.get("obligation", "types must agree on overlap")),
            )
            for i in interfaces
        ]

        phases = cls._build_phases(modules)

        return cls(
            spec=spec,
            target_loc=target_loc,
            modules=modules,
            interfaces=iface_objs,
            constraints=list(constraints),
            tests=tests,
            phases=phases,
            metadata=dict(metadata or {}),
        )

    @staticmethod
    def _default_module_path(node: Dict[str, Any]) -> str:
        name = str(node.get("name", "module")).replace("-", "_").lower()
        return f"generated/{name}.py"

    @staticmethod
    def _build_phases(modules: Sequence[PlanModule]) -> List[PhasePlan]:
        """Create generation phases from dependency ordering."""
        remaining = {m.name: set(m.depends_on) for m in modules}
        all_names = set(remaining.keys())
        done: set[str] = set()
        phases: List[PhasePlan] = []
        phase_idx = 1

        while len(done) < len(all_names):
            ready = sorted(
                name
                for name, deps in remaining.items()
                if name not in done and deps.issubset(done)
            )
            if not ready:
                # Cycle fallback: force progress with lexicographic pick.
                ready = [sorted(name for name in all_names if name not in done)[0]]

            gate = ["structural-check", "interface-check"]
            if phase_idx > 1:
                gate.append("integration-check")

            phases.append(PhasePlan(index=phase_idx, module_names=ready, gate_checks=gate))
            done.update(ready)
            phase_idx += 1

        return phases

    def to_dict(self) -> Dict[str, Any]:
        return {
            "spec": self.spec,
            "target_loc": self.target_loc,
            "modules": [m.to_dict() for m in self.modules],
            "interfaces": [i.to_dict() for i in self.interfaces],
            "constraints": list(self.constraints),
            "tests": list(self.tests),
            "phases": [p.to_dict() for p in self.phases],
            "metadata": dict(self.metadata),
        }

    def module_names(self) -> List[str]:
        return [m.name for m in self.modules]

    def iter_contracts(self) -> Iterable[Tuple[str, Dict[str, Any]]]:
        for module in self.modules:
            yield module.name, {
                "exports": list(module.exports),
                "imports": list(module.imports),
                "constraints": list(module.constraints),
            }
