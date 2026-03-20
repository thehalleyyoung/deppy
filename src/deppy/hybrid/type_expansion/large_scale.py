"""Large-scale orchestration for Pillar 10 type expansion."""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple

from .expander import TypeExpander


@dataclass
class LargeScaleReport:
    """Aggregated report for multi-component expansion."""

    component_count: int
    module_count: int
    total_estimated_loc: int
    per_component: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    global_plan: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "component_count": self.component_count,
            "module_count": self.module_count,
            "total_estimated_loc": self.total_estimated_loc,
            "per_component": dict(self.per_component),
            "global_plan": dict(self.global_plan),
        }


class LargeScaleGenerator:
    """Expands large projects by partitioning and merging component plans."""

    def __init__(
        self,
        *,
        expander: Optional[TypeExpander] = None,
        default_target_loc: int = 50000,
    ) -> None:
        self.expander = expander or TypeExpander()
        self.default_target_loc = default_target_loc

    def generate(
        self,
        project_spec: Dict[str, Any] | str,
        *,
        oracle_fn: Optional[Callable[..., Any]] = None,
        target_loc: Optional[int] = None,
    ) -> Dict[str, Any]:
        """Generate a practical merged expansion plan for many components."""
        normalized = self._normalize_project_spec(project_spec)
        components = normalized["components"]
        total_target = int(target_loc or normalized.get("target_loc") or self.default_target_loc)
        budgets = self._allocate_budgets(components, total_target)

        per_component: Dict[str, Dict[str, Any]] = {}
        global_modules: List[Dict[str, Any]] = []
        global_interfaces: List[Dict[str, Any]] = []
        global_constraints: List[Dict[str, Any]] = []
        global_tree_children: List[Dict[str, Any]] = []

        for name, spec_payload in components:
            plan = self.expander.expand(
                spec_payload,
                oracle_fn=oracle_fn,
                target_loc=budgets[name],
            )
            per_component[name] = plan

            # Namespace modules to avoid collisions during merge.
            for module in plan.get("modules", []):
                cloned = dict(module)
                original = str(cloned.get("name", "module"))
                namespaced = f"{name}__{original}"
                cloned["name"] = namespaced
                cloned["depends_on"] = [
                    f"{name}__{dep}" if "__" not in str(dep) else str(dep)
                    for dep in cloned.get("depends_on", [])
                ]
                global_modules.append(cloned)

            for iface in plan.get("interfaces", []):
                cloned_iface = dict(iface)
                cloned_iface["provider"] = f"{name}__{iface.get('provider', '')}"
                cloned_iface["consumer"] = f"{name}__{iface.get('consumer', '')}"
                global_interfaces.append(cloned_iface)

            global_constraints.extend(plan.get("constraints", []))
            expanded_type = plan.get("expanded_type", {})
            component_tree = (
                expanded_type.get("elaboration_tree")
                if isinstance(expanded_type, dict)
                else None
            )
            if isinstance(component_tree, dict):
                global_tree_children.append(
                    self._namespace_tree(component_tree, name, root_label=f"{name}__cover")
                )
            else:
                global_tree_children.append(self._fallback_component_tree(name, plan))

        cross_component = self._infer_cross_component_interfaces(global_modules)
        global_interfaces.extend(cross_component)

        global_plan = {
            "spec": normalized["spec"],
            "target_loc": total_target,
            "modules": global_modules,
            "interfaces": global_interfaces,
            "constraints": global_constraints,
            "phases": self._build_global_phases(global_modules),
            "elaboration_tree": {
                "name": f"{self._slug(normalized['spec'])}_global_cover",
                "kind": "global_grothendieck_cover",
                "summary": normalized["spec"],
                "target_loc": total_target,
                "algebraic_geometry_view": (
                    "Treat the full build as a cover of component charts whose "
                    "leaf sections descend to executable modules after gluing."
                ),
                "children": global_tree_children,
            },
            "metadata": {
                "component_budgets": budgets,
                "cross_component_interfaces": len(cross_component),
            },
        }

        report = LargeScaleReport(
            component_count=len(components),
            module_count=len(global_modules),
            total_estimated_loc=sum(int(m.get("estimated_loc", 0)) for m in global_modules),
            per_component=per_component,
            global_plan=global_plan,
        )
        return report.to_dict()

    def _normalize_project_spec(self, project_spec: Dict[str, Any] | str) -> Dict[str, Any]:
        if isinstance(project_spec, str):
            return {
                "spec": project_spec,
                "components": [("core", {"spec": project_spec})],
            }

        if not isinstance(project_spec, dict):
            raise TypeError("project_spec must be a str or dict")

        spec = str(project_spec.get("spec") or project_spec.get("name") or "project")
        raw_components = project_spec.get("components")

        if isinstance(raw_components, dict):
            components = [
                (str(name), {"spec": str(text)})
                for name, text in raw_components.items()
            ]
        elif isinstance(raw_components, list):
            components = []
            for idx, item in enumerate(raw_components):
                if isinstance(item, dict):
                    name = str(item.get("name") or f"component_{idx + 1}")
                    payload = dict(item)
                    payload["spec"] = str(item.get("spec") or item.get("description") or name)
                    components.append((name, payload))
                else:
                    components.append((f"component_{idx + 1}", {"spec": str(item)}))
        else:
            components = [("core", {"spec": spec})]

        if not components:
            components = [("core", {"spec": spec})]

        return {
            "spec": spec,
            "target_loc": project_spec.get("target_loc"),
            "components": components,
        }

    def _allocate_budgets(
        self,
        components: Sequence[Tuple[str, Dict[str, Any]]],
        total_target: int,
    ) -> Dict[str, int]:
        weights: Dict[str, int] = {}
        for name, payload in components:
            text = str(payload.get("spec", ""))
            token_count = max(8, len(text.split()))
            complexity_bonus = 0
            lower = text.lower()
            for marker in ("distributed", "realtime", "secure", "consistency", "fault", "stream"):
                if marker in lower:
                    complexity_bonus += 4
            weights[name] = token_count + complexity_bonus

        total_weight = max(1, sum(weights.values()))
        allocation: Dict[str, int] = {}
        for name, _ in components:
            allocation[name] = max(800, int(total_target * (weights[name] / total_weight)))
        return allocation

    def _infer_cross_component_interfaces(
        self,
        modules: Sequence[Dict[str, Any]],
    ) -> List[Dict[str, Any]]:
        """Infer pragmatic cross-component interfaces from shared API verbs."""
        provider_by_export: Dict[str, str] = {}
        for module in modules:
            for exported in module.get("exports", []):
                provider_by_export.setdefault(str(exported), str(module.get("name", "")))

        interfaces: List[Dict[str, Any]] = []
        for module in modules:
            imports = [str(v) for v in module.get("imports", [])]
            for imported in imports:
                provider = provider_by_export.get(imported)
                consumer = str(module.get("name", ""))
                if not provider or provider == consumer:
                    continue
                interfaces.append(
                    {
                        "name": imported,
                        "provider": provider,
                        "consumer": consumer,
                        "provider_type": "Callable[..., dict]",
                        "consumer_type": "Callable[..., dict]",
                        "obligation": f"Id_API({provider}.{imported}, {consumer}.{imported})",
                    }
                )
        return interfaces

    def _build_global_phases(self, modules: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
        done: set[str] = set()
        module_map = {str(m.get("name", "")): m for m in modules}
        phases: List[Dict[str, Any]] = []
        idx = 1

        while len(done) < len(module_map):
            ready = sorted(
                name
                for name, mod in module_map.items()
                if name not in done
                and set(str(d) for d in mod.get("depends_on", [])).issubset(done)
            )
            if not ready:
                ready = [sorted(name for name in module_map if name not in done)[0]]

            phases.append(
                {
                    "index": idx,
                    "module_names": ready,
                    "gate_checks": ["coverage", "coherence", "feasibility"],
                }
            )
            done.update(ready)
            idx += 1

        return phases

    def _namespace_tree(
        self,
        tree: Dict[str, Any],
        prefix: str,
        *,
        root_label: str,
    ) -> Dict[str, Any]:
        renamed = dict(tree)
        renamed["name"] = root_label
        renamed["summary"] = tree.get("summary", prefix)
        children = tree.get("children", [])
        renamed["children"] = [
            self._namespace_tree_child(child, prefix)
            for child in children
            if isinstance(child, dict)
        ]
        return renamed

    def _namespace_tree_child(self, node: Dict[str, Any], prefix: str) -> Dict[str, Any]:
        renamed = dict(node)
        name = str(node.get("name", "module"))
        renamed["name"] = f"{prefix}__{name}" if "__" not in name else name
        renamed["depends_on"] = [
            f"{prefix}__{dep}" if "__" not in str(dep) else str(dep)
            for dep in node.get("depends_on", [])
        ]
        renamed["children"] = [
            self._namespace_tree_child(child, prefix)
            for child in node.get("children", [])
            if isinstance(child, dict)
        ]
        return renamed

    def _fallback_component_tree(self, prefix: str, plan: Dict[str, Any]) -> Dict[str, Any]:
        return {
            "name": f"{prefix}__cover",
            "kind": "component_cover",
            "summary": prefix,
            "children": [
                {
                    "name": str(module.get("name", f"{prefix}__module")),
                    "kind": "local_section",
                    "summary": str(module.get("summary", module.get("name", prefix))),
                    "depends_on": [str(dep) for dep in module.get("depends_on", [])],
                    "children": [],
                }
                for module in plan.get("modules", [])
            ],
        }

    @staticmethod
    def _slug(text: str) -> str:
        cleaned = "".join(ch.lower() if ch.isalnum() else "_" for ch in text)
        while "__" in cleaned:
            cleaned = cleaned.replace("__", "_")
        return cleaned.strip("_") or "project"
