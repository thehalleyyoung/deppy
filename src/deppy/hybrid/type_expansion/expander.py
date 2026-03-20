"""Hybrid type expansion engine (Pillar 10 first pass).

Converts NL/project specs into typed decomposition plans using a practical,
heuristic expansion loop:
- Σ-expansion: component/module decomposition
- Π-expansion: API contract extraction
- refinement expansion: constraint/test obligations
- identity expansion: interface compatibility obligations
"""
from __future__ import annotations

import math
import re
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence

from .codegen_plan import CodeGenPlan


_WORD_RE = re.compile(r"[A-Za-z][A-Za-z0-9_\-]+")
_SENTENCE_RE = re.compile(r"[^.!?\n]+")
_STOPWORDS = {
    "a",
    "an",
    "and",
    "are",
    "as",
    "at",
    "be",
    "build",
    "component",
    "constraints",
    "cover",
    "data",
    "description",
    "ensure",
    "formal",
    "for",
    "from",
    "global",
    "guided",
    "idea",
    "ideation",
    "input",
    "integration",
    "into",
    "layer",
    "local",
    "mathematical",
    "module",
    "must",
    "obligations",
    "of",
    "on",
    "or",
    "overlap",
    "project",
    "responsible",
    "role",
    "service",
    "site",
    "spec",
    "structured",
    "system",
    "that",
    "the",
    "their",
    "this",
    "through",
    "use",
    "with",
    "cross",
    "domain",
    "represented",
    "theory",
    "engineering",
    "verification",
    "area",
}
_AG_LABELS = (
    "chart",
    "section",
    "fiber",
    "atlas",
    "descent",
    "cocycle",
    "sheaf",
)
_STRUCTURAL_LABELS = (
    "model",
    "transport",
    "invariant",
    "proof",
    "state",
    "contract",
    "policy",
    "audit",
)
_ROLE_HINTS = {
    "domain_model": ["schema", "invariant", "entity", "state"],
    "application_service": ["workflow", "policy", "coordination", "validation"],
    "api": ["boundary", "request", "transport", "contract"],
    "persistence": ["storage", "ledger", "snapshot", "state"],
    "observability": ["audit", "trace", "metrics", "alerts"],
}


@dataclass
class ExpansionNode:
    """Intermediate Σ-node for expansion and normalization."""

    name: str
    summary: str
    estimated_loc: int
    responsibilities: List[str] = field(default_factory=list)
    depends_on: List[str] = field(default_factory=list)
    exports: List[str] = field(default_factory=list)
    imports: List[str] = field(default_factory=list)
    constraints: List[Dict[str, Any]] = field(default_factory=list)
    test_obligations: List[str] = field(default_factory=list)
    class_specs: List[Dict[str, Any]] = field(default_factory=list)
    function_specs: List[Dict[str, Any]] = field(default_factory=list)
    sigma_width: int = 1
    pi_arity: int = 1
    depth: int = 0
    chart_kind: str = "chart"
    cover_label: str = ""
    children: List["ExpansionNode"] = field(default_factory=list)
    ideation_lenses: List[Dict[str, Any]] = field(default_factory=list)
    ideation_benefit: Dict[str, Any] = field(default_factory=dict)

    def to_plan_node(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "summary": self.summary,
            "estimated_loc": self.estimated_loc,
            "responsibilities": list(self.responsibilities),
            "depends_on": list(self.depends_on),
            "exports": list(self.exports),
            "imports": list(self.imports),
            "constraints": list(self.constraints),
            "test_obligations": list(self.test_obligations),
            "class_specs": list(self.class_specs),
            "function_specs": list(self.function_specs),
            "sigma_width": self.sigma_width,
            "pi_arity": self.pi_arity,
            "depth": self.depth,
            "chart_kind": self.chart_kind,
            "cover_label": self.cover_label or self.name.replace("_", " "),
            "ideation_lenses": list(self.ideation_lenses),
            "ideation_benefit": dict(self.ideation_benefit),
            "path": f"generated/{self.name.lower().replace('-', '_')}.py",
        }

    def to_tree(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "summary": self.summary,
            "estimated_loc": self.estimated_loc,
            "kind": self.chart_kind,
            "cover_label": self.cover_label or self.name.replace("_", " "),
            "responsibilities": list(self.responsibilities),
            "depends_on": list(self.depends_on),
            "depth": self.depth,
            "ideation_lenses": list(self.ideation_lenses),
            "children": [child.to_tree() for child in self.children],
        }


class TypeExpander:
    """Expands user specs into parseable code generation plans."""

    def __init__(
        self,
        *,
        atomic_loc: int = 300,
        max_pi_arity: int = 5,
        max_depth: int = 7,
    ) -> None:
        self.atomic_loc = atomic_loc
        self.max_pi_arity = max_pi_arity
        self.max_depth = max_depth

    def expand(
        self,
        spec: str | Dict[str, Any],
        *,
        oracle_fn: Optional[Callable[..., Any]] = None,
        target_loc: int = 50000,
    ) -> Dict[str, Any]:
        """Run first-pass Pillar 10 expansion and compile a codegen plan."""
        normalized = self._normalize_spec(spec)
        root_claims = self._extract_claims(normalized)

        seed_components = self._sigma_seed_components(
            claims=root_claims,
            target_loc=target_loc,
            oracle_fn=oracle_fn,
            spec_payload=spec if isinstance(spec, dict) else None,
        )
        elaborated_roots = [self._expand_node(seed) for seed in seed_components]
        nodes = self._collect_atomic_nodes(elaborated_roots)

        for node in nodes:
            pi_items = self._pi_expand(node)
            node.exports = [item["name"] for item in pi_items]
            node.function_specs = self._function_specs(node, pi_items)
            node.class_specs = self._class_specs(node)
            node.pi_arity = max((item["arity"] for item in pi_items), default=1)
            node.constraints = self._refinement_expand(node, normalized)
            node.test_obligations = [
                c["expression"]
                for c in node.constraints
                if c.get("kind") in {"refinement", "postcondition"}
            ]

        interfaces = self._identity_expand(nodes)
        constraints = self._collect_constraints(nodes, interfaces)
        h1_dimension = self._estimate_h1(nodes, interfaces)

        codegen = CodeGenPlan.compile(
            spec=normalized,
            target_loc=target_loc,
            nodes=[n.to_plan_node() for n in nodes],
            interfaces=interfaces,
            constraints=constraints,
            metadata={
                "h1_dimension": h1_dimension,
                "atomic_loc": self.atomic_loc,
                "claims": root_claims,
            },
        )
        plan = codegen.to_dict()
        plan["expanded_type"] = {
            "sigma_modules": [n.name for n in nodes],
            "h1_dimension": h1_dimension,
            "atomic": all(n.estimated_loc <= self.atomic_loc for n in nodes),
            "leaf_order": [n.name for n in nodes],
            "elaboration_tree": self._build_elaboration_tree(
                normalized,
                elaborated_roots,
                h1_dimension=h1_dimension,
                target_loc=target_loc,
            ),
        }
        return plan

    def _normalize_spec(self, spec: str | Dict[str, Any]) -> str:
        if isinstance(spec, str):
            return spec.strip()
        if isinstance(spec, dict):
            if "spec" in spec and isinstance(spec["spec"], str):
                return spec["spec"].strip()
            parts: List[str] = []
            for key in ("name", "goal", "description"):
                value = spec.get(key)
                if isinstance(value, str) and value.strip():
                    parts.append(value.strip())
            requirements = spec.get("requirements")
            if isinstance(requirements, list):
                parts.extend(str(req).strip() for req in requirements if str(req).strip())
            if parts:
                return ". ".join(parts)
        raise TypeError("spec must be str or dict containing textual fields")

    def _extract_claims(self, spec: str) -> List[str]:
        claims = [s.strip() for s in _SENTENCE_RE.findall(spec) if s.strip()]
        return claims or [spec]

    def _sigma_seed_components(
        self,
        *,
        claims: Sequence[str],
        target_loc: int,
        oracle_fn: Optional[Callable[..., Any]],
        spec_payload: Optional[Dict[str, Any]] = None,
    ) -> List[ExpansionNode]:
        baseline = [
            "domain_model",
            "application_service",
            "api",
            "persistence",
            "observability",
        ]
        if target_loc <= 2000:
            baseline = ["core", "api", "tests"]

        oracle_names: List[str] = []
        if oracle_fn is not None:
            maybe = oracle_fn(
                "sigma_expand",
                {
                    "claims": list(claims),
                    "target_loc": target_loc,
                    "max_components": 12,
                },
            )
            if isinstance(maybe, dict) and isinstance(maybe.get("components"), list):
                oracle_names = [str(c).strip() for c in maybe["components"] if str(c).strip()]

        names = oracle_names or baseline
        estimate = max(80, target_loc // max(1, len(names)))
        nodes: List[ExpansionNode] = []
        ideation_lenses = self._extract_ideation_lenses(spec_payload)
        ideation_benefit = self._extract_ideation_benefit(spec_payload)

        for idx, name in enumerate(names):
            claim = claims[idx % len(claims)] if claims else ""
            nodes.append(
                ExpansionNode(
                    name=self._slug(name),
                    summary=claim,
                    estimated_loc=estimate,
                    responsibilities=[claim] if claim else [],
                    sigma_width=max(1, len(names)),
                    chart_kind=self._chart_kind(self._slug(name), depth=0, index=idx),
                    cover_label=self._slug(name).replace("_", " "),
                    ideation_lenses=ideation_lenses[:8],
                    ideation_benefit=ideation_benefit,
                )
            )

        self._infer_dependencies(nodes, claims)
        return nodes

    def _expand_node(self, node: ExpansionNode) -> ExpansionNode:
        if node.estimated_loc <= self.atomic_loc or node.depth >= self.max_depth:
            node.sigma_width = 1
            if not node.cover_label:
                node.cover_label = node.name.replace("_", " ")
            return node

        parts = max(2, math.ceil(node.estimated_loc / self.atomic_loc))
        per_part = max(60, node.estimated_loc // parts)
        child_names = self._semantic_child_names(node, parts)
        children: List[ExpansionNode] = []
        for i, child_name in enumerate(child_names):
            child = ExpansionNode(
                name=child_name,
                summary=node.summary,
                estimated_loc=per_part,
                responsibilities=(
                    node.responsibilities[i::parts] or list(node.responsibilities)
                ),
                depends_on=list(node.depends_on),
                depth=node.depth + 1,
                sigma_width=parts,
                chart_kind=self._chart_kind(child_name, depth=node.depth + 1, index=i),
                cover_label=child_name.replace("_", " "),
                ideation_lenses=list(node.ideation_lenses),
                ideation_benefit=dict(node.ideation_benefit),
            )
            children.append(self._expand_node(child))
        node.children = children
        return node

    def _collect_atomic_nodes(self, roots: Sequence[ExpansionNode]) -> List[ExpansionNode]:
        atomic: List[ExpansionNode] = []

        def _visit(node: ExpansionNode) -> None:
            if not node.children:
                atomic.append(node)
                return
            for child in node.children:
                _visit(child)

        for root in roots:
            _visit(root)
        self._infer_linear_dependency_order(atomic)
        return atomic

    def _pi_expand(self, node: ExpansionNode) -> List[Dict[str, Any]]:
        apis: List[Dict[str, Any]] = []
        duties = node.responsibilities or [node.summary or node.name]
        for idx, duty in enumerate(duties, start=1):
            words = _WORD_RE.findall(duty.lower())
            verb = words[0] if words else "handle"
            noun = words[1] if len(words) > 1 else f"item_{idx}"
            arity = min(self.max_pi_arity, max(1, len(words) // 3))
            apis.append(
                {
                    "name": f"{verb}_{noun}",
                    "arity": arity,
                    "signature": f"({', '.join(f'arg{i}: Any' for i in range(1, arity + 1))}) -> dict",
                }
            )
        return apis

    def _function_specs(
        self,
        node: ExpansionNode,
        apis: Sequence[Dict[str, Any]],
    ) -> List[Dict[str, Any]]:
        specs: List[Dict[str, Any]] = []
        context = self._structured_lens_context(node)
        for item in apis[: min(6, len(apis))]:
            specs.append(
                {
                    "name": str(item.get("name", "run_module")),
                    "signature": str(item.get("signature", "() -> dict")),
                    "purpose": (
                        node.responsibilities[0]
                        if node.responsibilities
                        else node.summary or f"Operate the {node.name} module."
                    ),
                    "invariants": context["invariants"],
                    "transport_maps": context["transport_maps"],
                    "theorem_schema": context["theorem_names"][:1],
                    "canonical_equation": context["equations"][:1],
                    "certification_target": context["certification_targets"][:1],
                }
            )
        if not specs:
            specs.append(
                {
                    "name": f"run_{node.name}",
                    "signature": "() -> dict",
                    "purpose": node.summary or f"Operate the {node.name} module.",
                    "invariants": context["invariants"],
                    "transport_maps": context["transport_maps"],
                    "theorem_schema": context["theorem_names"][:1],
                    "canonical_equation": context["equations"][:1],
                    "certification_target": context["certification_targets"][:1],
                }
            )
        return specs

    def _class_specs(self, node: ExpansionNode) -> List[Dict[str, Any]]:
        prefix = self._camel_case(node.name)
        context = self._structured_lens_context(node)
        return [
            {
                "name": f"{prefix}Section",
                "role": "Typed local-section carrier for the module's mathematical local models.",
                "fields": [
                    "local_models: Dict[str, Any]",
                    "invariant_witnesses: Dict[str, Any]",
                    "metadata: Dict[str, Any]",
                ],
                "invariants": context["invariants"],
                "local_models": context["local_models"],
                "certification_targets": context["certification_targets"],
            },
            {
                "name": f"{prefix}Transport",
                "role": "Typed orchestrator for admissible transports and gluing maps.",
                "fields": [
                    "dependencies: List[str]",
                    "transport_rules: Dict[str, Any]",
                    "proof_obligations: List[str]",
                ],
                "invariants": context["invariants"],
                "transport_maps": context["transport_maps"],
                "theorem_schema": context["theorem_names"][:1],
                "canonical_equation": context["equations"][:1],
                "certification_targets": context["certification_targets"],
            },
        ]

    def _refinement_expand(self, node: ExpansionNode, spec: str) -> List[Dict[str, Any]]:
        constraints: List[Dict[str, Any]] = []
        text = f"{spec} {' '.join(node.responsibilities)}".lower()

        triggers = {
            "non-negative": "x >= 0",
            "positive": "x > 0",
            "at least": "x >= min_value",
            "at most": "x <= max_value",
            "must": "precondition_holds",
            "ensure": "postcondition_holds",
            "unique": "is_unique(x)",
            "sorted": "is_sorted(x)",
        }

        for key, expr in triggers.items():
            if key in text:
                constraints.append(
                    {
                        "kind": "refinement" if key not in {"must", "ensure"} else "postcondition",
                        "module": node.name,
                        "expression": expr,
                    }
                )

        if not constraints:
            constraints.append(
                {
                    "kind": "refinement",
                    "module": node.name,
                    "expression": "inputs_are_valid",
                }
            )
        return constraints

    def _identity_expand(self, nodes: Sequence[ExpansionNode]) -> List[Dict[str, Any]]:
        providers: Dict[str, str] = {}
        interfaces: List[Dict[str, Any]] = []

        for node in nodes:
            for exported in node.exports:
                providers.setdefault(exported, node.name)

        for node in nodes:
            node.imports = []
            for dep in node.depends_on:
                dep_node = next((n for n in nodes if n.name == dep), None)
                if dep_node and dep_node.exports:
                    node.imports.extend(dep_node.exports[:2])
            for imported in node.imports:
                provider = providers.get(imported)
                if not provider:
                    continue
                interfaces.append(
                    {
                        "name": imported,
                        "provider": provider,
                        "consumer": node.name,
                        "provider_type": "Callable[..., dict]",
                        "consumer_type": "Callable[..., dict]",
                        "obligation": f"Id_API({provider}.{imported}, {node.name}.{imported})",
                    }
                )

        return interfaces

    def _collect_constraints(
        self,
        nodes: Sequence[ExpansionNode],
        interfaces: Sequence[Dict[str, Any]],
    ) -> List[Dict[str, Any]]:
        constraints: List[Dict[str, Any]] = []
        for node in nodes:
            constraints.extend(node.constraints)
            constraints.append(
                {
                    "kind": "size",
                    "module": node.name,
                    "expression": f"estimated_loc({node.name}) <= {self.atomic_loc}",
                }
            )
        for interface in interfaces:
            constraints.append(
                {
                    "kind": "identity",
                    "module": interface.get("consumer", ""),
                    "expression": interface.get("obligation", "types compatible"),
                }
            )
        return constraints

    def _estimate_h1(
        self,
        nodes: Sequence[ExpansionNode],
        interfaces: Sequence[Dict[str, Any]],
    ) -> int:
        unresolved_imports = 0
        exports = {exp for n in nodes for exp in n.exports}
        for node in nodes:
            unresolved_imports += sum(1 for imp in node.imports if imp not in exports)

        expected_edges = sum(len(node.depends_on) for node in nodes)
        observed_edges = len({(i["provider"], i["consumer"]) for i in interfaces})
        gaps = max(0, expected_edges - observed_edges)
        return unresolved_imports + gaps

    def _infer_dependencies(self, nodes: Sequence[ExpansionNode], claims: Sequence[str]) -> None:
        lower_claims = [claim.lower() for claim in claims]
        by_name = {n.name: n for n in nodes}

        keyword_links = {
            "api": ["application_service", "domain_model"],
            "persistence": ["domain_model"],
            "observability": ["api", "application_service"],
            "tests": ["api", "core"],
        }

        for node in nodes:
            deps = list(keyword_links.get(node.name, []))
            text = " ".join(lower_claims)
            if "auth" in text and node.name == "api":
                deps.append("domain_model")
            node.depends_on = [d for d in deps if d in by_name and d != node.name]

    def _infer_linear_dependency_order(self, nodes: Sequence[ExpansionNode]) -> None:
        ordered = sorted(nodes, key=lambda n: n.name)
        for idx, node in enumerate(ordered):
            if node.depends_on:
                continue
            if idx > 0:
                prev = ordered[idx - 1].name
                if prev != node.name:
                    node.depends_on = [prev]

    @staticmethod
    def _slug(name: str) -> str:
        words = re.findall(r"[A-Za-z0-9]+", name.lower())
        return "_".join(words) or "module"

    def _semantic_child_names(self, node: ExpansionNode, parts: int) -> List[str]:
        pool = self._semantic_fragments(node)
        label_pool = self._label_pool(node)
        names: List[str] = []
        seen: set[str] = set()
        offset = sum(ord(ch) for ch in node.name) % max(1, len(pool))
        for index in range(parts):
            fragment = pool[(offset + index) % len(pool)]
            suffix_label = label_pool[(node.depth + index) % len(label_pool)]
            candidate = self._slug(f"{node.name}_{fragment}_{suffix_label}")
            suffix = 2
            while candidate in seen:
                candidate = self._slug(f"{node.name}_{fragment}_{suffix_label}_{suffix}")
                suffix += 1
            seen.add(candidate)
            names.append(candidate)
        return names

    def _semantic_fragments(self, node: ExpansionNode) -> List[str]:
        base_tokens = {
            token
            for token in self._slug(node.name).split("_")
            if token
        }
        ideation_fragments = self._ideation_fragments(node, base_tokens)
        raw_words = _WORD_RE.findall(" ".join([node.summary, *node.responsibilities]).lower())
        words = [self._slug(word) for word in raw_words]
        fragments: List[str] = []
        for index, word in enumerate(words):
            if (
                len(word) < 4
                or word in _STOPWORDS
                or word in base_tokens
                or word.isdigit()
            ):
                continue
            if index + 1 < len(words):
                partner = words[index + 1]
                if (
                    len(partner) >= 4
                    and partner not in _STOPWORDS
                    and partner not in base_tokens
                    and partner != word
                ):
                    fragments.append(f"{word}_{partner}")
            fragments.append(word)

        ordered: List[str] = []
        seen: set[str] = set()
        for fragment in ideation_fragments:
            if fragment not in seen:
                seen.add(fragment)
                ordered.append(fragment)
        for fragment in fragments:
            if fragment not in seen:
                seen.add(fragment)
                ordered.append(fragment)
        if not ideation_fragments:
            for role_name, hints in _ROLE_HINTS.items():
                if role_name in node.name:
                    for hint in hints:
                        if hint not in seen:
                            seen.add(hint)
                            ordered.append(hint)
        if ordered:
            return ordered
        fallback = [token for token in self._slug(node.name).split("_") if token and token != "part"]
        return fallback or ["typed"]

    def _ideation_fragments(
        self,
        node: ExpansionNode,
        base_tokens: set[str],
    ) -> List[str]:
        fragments: List[str] = []
        math_area_lenses = [
            lens
            for lens in node.ideation_lenses
            if isinstance(lens, dict) and str(lens.get("kind", "")) == "math_area"
        ]
        active_lenses = (
            math_area_lenses
            if math_area_lenses
            else [
                lens
                for lens in node.ideation_lenses
                if isinstance(lens, dict)
                and str(lens.get("kind", "")) in {"deep_analogy", "registry_domain"}
            ]
        )
        for lens in active_lenses:
            kind = str(lens.get("kind", ""))
            source_parts: List[str] = []
            if kind == "math_area":
                area_name = self._slug(str(lens.get("source_area", "")))
                if area_name and area_name not in base_tokens:
                    fragments.append(area_name)
                source_parts.extend(
                    [
                        str(lens.get("source_area", "")),
                        " ".join(str(item) for item in lens.get("local_models", [])[:4]),
                        " ".join(str(item) for item in lens.get("transport_maps", [])[:4]),
                        " ".join(str(item) for item in lens.get("invariants", [])[:4]),
                        " ".join(
                            str(item.get("name", ""))
                            for item in lens.get("theorem_schemas", [])[:2]
                            if isinstance(item, dict)
                        ),
                        " ".join(
                            str(item.get("meaning", ""))
                            for item in lens.get("canonical_equations", [])[:2]
                            if isinstance(item, dict)
                        ),
                    ]
                )
            else:
                source_parts.extend([str(lens.get("label", "")), str(lens.get("typed_role", ""))])
            words = [self._slug(word) for word in _WORD_RE.findall(" ".join(source_parts).lower())]
            filtered = [
                word
                for word in words
                if len(word) >= 4
                and word not in _STOPWORDS
                and word not in _AG_LABELS
                and word not in base_tokens
                and not word.isdigit()
            ]
            for index, word in enumerate(filtered[:8]):
                if index + 1 < len(filtered):
                    partner = filtered[index + 1]
                    if partner != word:
                        fragments.append(f"{word}_{partner}")
                fragments.append(word)

        ordered: List[str] = []
        seen: set[str] = set()
        for fragment in fragments:
            if fragment not in seen:
                seen.add(fragment)
                ordered.append(fragment)
        return ordered

    def _label_pool(self, node: ExpansionNode) -> List[str]:
        if self._ag_context_enabled(node):
            return list(_AG_LABELS)
        labels: List[str] = []
        for lens in node.ideation_lenses:
            if not isinstance(lens, dict):
                continue
            if str(lens.get("kind", "")) != "math_area":
                continue
            labels.extend(
                self._slug(item)
                for item in lens.get("local_models", [])[:3]
                if self._slug(item) not in _STOPWORDS and self._slug(item) not in _AG_LABELS
            )
            labels.extend(
                self._slug(item)
                for item in lens.get("transport_maps", [])[:3]
                if self._slug(item) not in _STOPWORDS and self._slug(item) not in _AG_LABELS
            )
            labels.extend(
                self._slug(item)
                for item in lens.get("invariants", [])[:3]
                if self._slug(item) not in _STOPWORDS and self._slug(item) not in _AG_LABELS
            )
        ordered: List[str] = []
        seen: set[str] = set()
        for label in labels:
            if label and label not in seen:
                seen.add(label)
                ordered.append(label)
        return ordered or list(_STRUCTURAL_LABELS)

    def _ag_context_enabled(self, node: ExpansionNode) -> bool:
        for lens in node.ideation_lenses:
            if not isinstance(lens, dict):
                continue
            if str(lens.get("kind", "")) == "registry_domain" and str(lens.get("label", "")) == "algebraic_geometry":
                return True
            if str(lens.get("kind", "")) != "math_area":
                continue
            source_text = " ".join(
                str(part).lower()
                for part in (
                    lens.get("source_area", ""),
                    lens.get("category", ""),
                    lens.get("family", ""),
                )
            )
            if any(token in source_text for token in ("algebraic", "geometry", "sheaf", "cohomology", "scheme")):
                return True
        return False

    def _chart_kind(self, name: str, *, depth: int, index: int) -> str:
        lowered = name.lower()
        if "domain_model" in lowered:
            return "schema_model"
        if "application_service" in lowered:
            return "workflow_transport"
        if "api" in lowered:
            return "boundary_contract"
        if "persistence" in lowered:
            return "storage_state"
        if "observability" in lowered:
            return "audit_trace"
        return self._label_pool(
            ExpansionNode(name=name, summary=name, estimated_loc=self.atomic_loc, depth=depth)
        )[(depth + index) % len(self._label_pool(
            ExpansionNode(name=name, summary=name, estimated_loc=self.atomic_loc, depth=depth)
        ))]

    def _build_elaboration_tree(
        self,
        spec: str,
        roots: Sequence[ExpansionNode],
        *,
        h1_dimension: int,
        target_loc: int,
    ) -> Dict[str, Any]:
        root_name = self._slug(" ".join(_WORD_RE.findall(spec)[:4]) or "project")
        return {
            "name": f"{root_name}_cover",
            "kind": "grothendieck_cover",
            "summary": spec,
            "target_loc": target_loc,
            "h1_dimension": h1_dimension,
            "algebraic_geometry_view": (
                "Model the elaboration as a rooted cover whose child charts refine "
                "the parent claim until the leaves become code-generating local sections."
            ),
            "ideation_lenses": [
                lens
                for root in roots
                for lens in root.ideation_lenses[:4]
            ],
            "children": [node.to_tree() for node in roots],
        }

    @staticmethod
    def _extract_ideation_lenses(spec_payload: Optional[Dict[str, Any]]) -> List[Dict[str, Any]]:
        if not isinstance(spec_payload, dict):
            return []
        lenses = spec_payload.get("ideation_lenses", [])
        if not isinstance(lenses, list):
            return []
        return [dict(lens) for lens in lenses if isinstance(lens, dict)]

    @staticmethod
    def _extract_ideation_benefit(spec_payload: Optional[Dict[str, Any]]) -> Dict[str, Any]:
        if not isinstance(spec_payload, dict):
            return {}
        benefit = spec_payload.get("ideation_benefit", {})
        if not isinstance(benefit, dict):
            return {}
        return dict(benefit)

    @staticmethod
    def _camel_case(name: str) -> str:
        parts = [part for part in name.replace("-", "_").split("_") if part]
        return "".join(part[:1].upper() + part[1:] for part in parts) or "Module"

    def _lens_terms(self, node: ExpansionNode, *, limit: int) -> List[str]:
        terms: List[str] = []
        for lens in node.ideation_lenses:
            if not isinstance(lens, dict):
                continue
            for key in ("source_area", "local_models", "transport_maps", "invariants"):
                value = lens.get(key)
                if isinstance(value, list):
                    terms.extend(str(item) for item in value if str(item).strip())
                elif isinstance(value, str) and value.strip():
                    terms.append(value)
        ordered: List[str] = []
        seen: set[str] = set()
        for term in terms:
            if term not in seen:
                seen.add(term)
                ordered.append(term)
            if len(ordered) >= limit:
                break
        return ordered

    def _structured_lens_context(self, node: ExpansionNode) -> Dict[str, List[str]]:
        local_models: List[str] = []
        transport_maps: List[str] = []
        invariants: List[str] = []
        theorem_names: List[str] = []
        equations: List[str] = []
        certification_targets: List[str] = []
        for lens in node.ideation_lenses:
            if not isinstance(lens, dict):
                continue
            local_models.extend(
                str(item) for item in lens.get("local_models", []) if str(item).strip()
            )
            transport_maps.extend(
                str(item) for item in lens.get("transport_maps", []) if str(item).strip()
            )
            invariants.extend(
                str(item) for item in lens.get("invariants", []) if str(item).strip()
            )
            for theorem in lens.get("theorem_schemas", []):
                if isinstance(theorem, dict) and str(theorem.get("name", "")).strip():
                    theorem_names.append(str(theorem.get("name", "")))
            for equation in lens.get("canonical_equations", []):
                if isinstance(equation, dict) and str(equation.get("latex", "")).strip():
                    equations.append(str(equation.get("latex", "")))
            certification_targets.extend(
                str(item)
                for item in lens.get("certification_targets", [])
                if str(item).strip()
            )

        def _dedupe(items: List[str], limit: int) -> List[str]:
            ordered: List[str] = []
            seen: set[str] = set()
            for item in items:
                if item not in seen:
                    seen.add(item)
                    ordered.append(item)
                if len(ordered) >= limit:
                    break
            return ordered

        invariants_out = _dedupe(invariants, 4)
        if not invariants_out:
            invariants_out = self._lens_terms(node, limit=4)
        return {
            "local_models": _dedupe(local_models, 4),
            "transport_maps": _dedupe(transport_maps, 4),
            "invariants": invariants_out,
            "theorem_names": _dedupe(theorem_names, 3),
            "equations": _dedupe(equations, 3),
            "certification_targets": _dedupe(certification_targets, 3),
        }
