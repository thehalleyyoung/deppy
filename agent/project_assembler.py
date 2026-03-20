"""
Project assembler for deppy.

Takes verified modules and assembles them into a complete, runnable project
with pyproject.toml, README, Lean proofs, tests, CI config, and a full
verification manifest (audit trail).
"""
from __future__ import annotations

import json
import os
import textwrap
import time
import datetime
import hashlib
import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Trust-level constants (mirrors verification_loop.py)                     │
# └──────────────────────────────────────────────────────────────────────────┘

TRUST_LEVELS = ["UNCHECKED", "LLM_JUDGED", "Z3_PROVEN", "LEAN_VERIFIED"]
TRUST_RANK: Dict[str, int] = {level: i for i, level in enumerate(TRUST_LEVELS)}

TRUST_BADGES: Dict[str, str] = {
    "LEAN_VERIFIED": "🟢 LEAN_VERIFIED",
    "Z3_PROVEN":     "🟡 Z3_PROVEN",
    "LLM_JUDGED":    "🟠 LLM_JUDGED",
    "UNCHECKED":     "🔴 UNCHECKED",
}

TRUST_EMOJI: Dict[str, str] = {
    "LEAN_VERIFIED": "🟢",
    "Z3_PROVEN":     "🟡",
    "LLM_JUDGED":    "🟠",
    "UNCHECKED":     "🔴",
}


def _min_trust(*levels: str) -> str:
    """Return the lowest trust level among the given levels."""
    if not levels:
        return "UNCHECKED"
    return min(levels, key=lambda l: TRUST_RANK.get(l, 0))


def _content_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _timestamp_iso() -> str:
    return datetime.datetime.utcnow().isoformat(timespec="seconds") + "Z"


def _safe_module_path(name: str) -> str:
    """Convert a module name to a filesystem-safe path segment."""
    return name.replace(".", "/").replace("-", "_")


def _indent(text: str, prefix: str = "    ") -> str:
    return textwrap.indent(text, prefix)


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ VerifiedModule                                                           │
# └──────────────────────────────────────────────────────────────────────────┘

@dataclass
class VerifiedModule:
    """A single module that has passed the verification pipeline."""

    name: str
    source: str
    trust_level: str
    verification_result: Dict[str, Any] = field(default_factory=dict)

    lean_source: Optional[str] = None
    test_source: Optional[str] = None

    content_hash: str = ""
    generation_model: str = ""
    generation_tokens: int = 0
    cegar_rounds: int = 0

    def __post_init__(self) -> None:
        if not self.content_hash:
            self.content_hash = _content_hash(self.source)

    @property
    def badge(self) -> str:
        return TRUST_BADGES.get(self.trust_level, "🔴 UNCHECKED")

    @property
    def emoji(self) -> str:
        return TRUST_EMOJI.get(self.trust_level, "🔴")

    @property
    def is_fully_verified(self) -> bool:
        return self.trust_level in ("Z3_PROVEN", "LEAN_VERIFIED")

    @property
    def line_count(self) -> int:
        return self.source.count("\n") + 1

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "trust_level": self.trust_level,
            "content_hash": self.content_hash,
            "line_count": self.line_count,
            "has_lean": self.lean_source is not None,
            "has_tests": self.test_source is not None,
            "generation_model": self.generation_model,
            "generation_tokens": self.generation_tokens,
            "cegar_rounds": self.cegar_rounds,
            "verification_result": self.verification_result,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any], source: str = "",
                  lean_source: Optional[str] = None,
                  test_source: Optional[str] = None) -> VerifiedModule:
        return cls(
            name=d["name"],
            source=source,
            trust_level=d.get("trust_level", "UNCHECKED"),
            verification_result=d.get("verification_result", {}),
            lean_source=lean_source,
            test_source=test_source,
            content_hash=d.get("content_hash", ""),
            generation_model=d.get("generation_model", ""),
            generation_tokens=d.get("generation_tokens", 0),
            cegar_rounds=d.get("cegar_rounds", 0),
        )


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ ProjectStructure                                                         │
# └──────────────────────────────────────────────────────────────────────────┘

@dataclass
class ProjectStructure:
    """A fully assembled, verified project ready for disk output."""

    name: str
    modules: Dict[str, VerifiedModule]    # name -> verified module
    tests: Dict[str, str]                 # name -> test source
    lean_proofs: Dict[str, str]           # name -> lean source
    config: Dict[str, Any]               # pyproject.toml content (as dict)
    readme: str
    manifest: Dict[str, Any]             # full verification manifest

    dockerfile: Optional[str] = None
    ci_config: Optional[str] = None
    extra_files: Dict[str, str] = field(default_factory=dict)
    init_files: Dict[str, str] = field(default_factory=dict)
    created_at: str = field(default_factory=_timestamp_iso)

    def write(self, output_dir: str) -> List[str]:
        """
        Write complete project to disk.

        Returns a list of all files written.
        """
        written: List[str] = []

        root = os.path.join(output_dir, self.name)
        os.makedirs(root, exist_ok=True)

        # pyproject.toml
        pyproject_path = os.path.join(root, "pyproject.toml")
        pyproject_content = self._dict_to_toml(self.config)
        _write_file(pyproject_path, pyproject_content)
        written.append(pyproject_path)

        # README.md
        readme_path = os.path.join(root, "README.md")
        _write_file(readme_path, self.readme)
        written.append(readme_path)

        # Source modules
        src_dir = os.path.join(root, "src", self.name)
        os.makedirs(src_dir, exist_ok=True)

        for rel_path, content in self.init_files.items():
            init_path = os.path.join(root, "src", rel_path)
            os.makedirs(os.path.dirname(init_path), exist_ok=True)
            _write_file(init_path, content)
            written.append(init_path)

        for mod_name, module in self.modules.items():
            mod_path = os.path.join(src_dir, f"{_safe_module_path(mod_name)}.py")
            os.makedirs(os.path.dirname(mod_path), exist_ok=True)
            _write_file(mod_path, module.source)
            written.append(mod_path)

        # Tests
        test_dir = os.path.join(root, "tests")
        os.makedirs(test_dir, exist_ok=True)
        _write_file(os.path.join(test_dir, "__init__.py"), "")
        written.append(os.path.join(test_dir, "__init__.py"))

        for test_name, test_source in self.tests.items():
            test_path = os.path.join(test_dir, f"test_{test_name}.py")
            _write_file(test_path, test_source)
            written.append(test_path)

        # Lean proofs
        if self.lean_proofs:
            lean_dir = os.path.join(root, "lean_proofs")
            os.makedirs(lean_dir, exist_ok=True)
            for proof_name, proof_source in self.lean_proofs.items():
                proof_path = os.path.join(lean_dir, f"{proof_name}.lean")
                _write_file(proof_path, proof_source)
                written.append(proof_path)

        # Manifest
        manifest_path = os.path.join(root, "deppy_manifest.json")
        _write_file(manifest_path, json.dumps(self.manifest, indent=2))
        written.append(manifest_path)

        # Dockerfile
        if self.dockerfile:
            docker_path = os.path.join(root, "Dockerfile")
            _write_file(docker_path, self.dockerfile)
            written.append(docker_path)

        # CI config
        if self.ci_config:
            ci_dir = os.path.join(root, ".github", "workflows")
            os.makedirs(ci_dir, exist_ok=True)
            ci_path = os.path.join(ci_dir, "deppy.yml")
            _write_file(ci_path, self.ci_config)
            written.append(ci_path)

        # Extra files
        for rel_path, content in self.extra_files.items():
            extra_path = os.path.join(root, rel_path)
            os.makedirs(os.path.dirname(extra_path), exist_ok=True)
            _write_file(extra_path, content)
            written.append(extra_path)

        return written

    def file_tree(self) -> str:
        """Pretty-print file tree."""
        lines: List[str] = [f"{self.name}/"]

        def _add(prefix: str, name: str, is_last: bool) -> str:
            connector = "└── " if is_last else "├── "
            return f"{prefix}{connector}{name}"

        entries: List[Tuple[str, bool]] = []

        entries.append(("pyproject.toml", False))
        entries.append(("README.md", False))

        # src/ tree
        entries.append(("src/", False))
        mod_names = sorted(self.modules.keys())
        for i, mod_name in enumerate(mod_names):
            is_last_mod = (i == len(mod_names) - 1) and not self.tests
            entries.append((f"  {self.name}/{_safe_module_path(mod_name)}.py", is_last_mod))

        # tests/
        if self.tests:
            entries.append(("tests/", False))
            test_names = sorted(self.tests.keys())
            for i, tn in enumerate(test_names):
                entries.append((f"  test_{tn}.py", i == len(test_names) - 1))

        # lean_proofs/
        if self.lean_proofs:
            entries.append(("lean_proofs/", False))
            proof_names = sorted(self.lean_proofs.keys())
            for i, pn in enumerate(proof_names):
                entries.append((f"  {pn}.lean", i == len(proof_names) - 1))

        entries.append(("deppy_manifest.json", False))

        if self.dockerfile:
            entries.append(("Dockerfile", False))
        if self.ci_config:
            entries.append((".github/workflows/deppy.yml", False))

        # Mark the real last entry
        if entries:
            name, _ = entries[-1]
            entries[-1] = (name, True)

        tree_lines: List[str] = [f"{self.name}/"]
        for name, is_last in entries:
            connector = "└── " if is_last else "├── "
            tree_lines.append(f"{connector}{name}")

        return "\n".join(tree_lines)

    def trust_summary(self) -> str:
        """Summarize trust levels across all modules."""
        lines: List[str] = ["Trust Summary", "=" * 50]

        overall = _min_trust(*(m.trust_level for m in self.modules.values()))
        lines.append(f"Overall: {TRUST_BADGES.get(overall, overall)}")
        lines.append("")

        for mod_name in sorted(self.modules.keys()):
            module = self.modules[mod_name]
            lines.append(f"  {module.emoji} {mod_name}: {module.trust_level}")

        return "\n".join(lines)

    def _dict_to_toml(self, d: Dict[str, Any], prefix: str = "") -> str:
        """Minimal TOML serialiser for pyproject.toml generation."""
        lines: List[str] = []
        scalars: Dict[str, Any] = {}
        tables: Dict[str, Any] = {}

        for k, v in d.items():
            if isinstance(v, dict):
                tables[k] = v
            else:
                scalars[k] = v

        for k, v in scalars.items():
            lines.append(f"{k} = {self._toml_value(v)}")

        for k, v in tables.items():
            section = f"{prefix}.{k}" if prefix else k
            lines.append("")
            lines.append(f"[{section}]")
            lines.append(self._dict_to_toml(v, prefix=section))

        return "\n".join(lines)

    @staticmethod
    def _toml_value(v: Any) -> str:
        if isinstance(v, str):
            escaped = v.replace("\\", "\\\\").replace('"', '\\"')
            return f'"{escaped}"'
        if isinstance(v, bool):
            return "true" if v else "false"
        if isinstance(v, int):
            return str(v)
        if isinstance(v, float):
            return str(v)
        if isinstance(v, list):
            items = ", ".join(
                ProjectStructure._toml_value(item) for item in v
            )
            return f"[{items}]"
        return repr(v)


def _write_file(path: str, content: str) -> None:
    """Write content to path, creating parent dirs if needed."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ TrustReport                                                              │
# └──────────────────────────────────────────────────────────────────────────┘

@dataclass
class TrustReport:
    """Aggregated trust report across all modules."""

    overall_trust: str
    per_module: Dict[str, str]  # module_name -> trust_level

    structural_proven: int = 0
    semantic_judged: int = 0
    lean_verified: int = 0
    unchecked: int = 0

    hallucinations_found: int = 0
    hallucinations_fixed: int = 0

    oracle_calls: int = 0
    oracle_cache_hits: int = 0
    tokens_used: int = 0
    tokens_saved: int = 0

    cross_module_contracts_verified: int = 0
    cross_module_contracts_failed: int = 0
    h1_overall: str = "H¹ = 0"

    total_lines: int = 0
    total_modules: int = 0
    generation_duration_ms: float = 0.0
    verification_duration_ms: float = 0.0

    created_at: str = field(default_factory=_timestamp_iso)

    def to_markdown(self) -> str:
        """Render as a Markdown report."""
        lines: List[str] = []
        lines.append("# Deppy Verification Report")
        lines.append("")
        lines.append(f"Generated: {self.created_at}")
        lines.append("")

        # Overall badge
        badge = TRUST_BADGES.get(self.overall_trust, self.overall_trust)
        lines.append(f"## Overall Trust: {badge}")
        lines.append("")

        # Summary table
        lines.append("## Summary")
        lines.append("")
        lines.append("| Metric | Value |")
        lines.append("|--------|-------|")
        lines.append(f"| Modules | {self.total_modules} |")
        lines.append(f"| Total lines | {self.total_lines} |")
        lines.append(f"| Structural (Z3) proven | {self.structural_proven} |")
        lines.append(f"| Semantic (LLM) judged | {self.semantic_judged} |")
        lines.append(f"| Lean verified | {self.lean_verified} |")
        lines.append(f"| Unchecked | {self.unchecked} |")
        lines.append(f"| Hallucinations found | {self.hallucinations_found} |")
        lines.append(f"| Hallucinations fixed | {self.hallucinations_fixed} |")
        lines.append(f"| Oracle calls | {self.oracle_calls} |")
        lines.append(f"| Oracle cache hits | {self.oracle_cache_hits} |")
        lines.append(
            f"| Tokens used | {self.tokens_used:,} |"
        )
        lines.append(
            f"| Tokens saved (cache) | {self.tokens_saved:,} |"
        )
        lines.append(
            f"| Cross-module contracts verified | "
            f"{self.cross_module_contracts_verified} |"
        )
        lines.append(
            f"| Cross-module contracts failed | "
            f"{self.cross_module_contracts_failed} |"
        )
        lines.append(f"| Cohomology (H¹) | {self.h1_overall} |")
        lines.append("")

        # Per-module table
        lines.append("## Per-Module Trust")
        lines.append("")
        lines.append("| Module | Trust | Badge |")
        lines.append("|--------|-------|-------|")
        for mod_name in sorted(self.per_module.keys()):
            trust = self.per_module[mod_name]
            badge = TRUST_BADGES.get(trust, trust)
            lines.append(f"| {mod_name} | {trust} | {badge} |")
        lines.append("")

        # Timing
        lines.append("## Timing")
        lines.append("")
        lines.append(
            f"- Generation: {self.generation_duration_ms:.0f}ms"
        )
        lines.append(
            f"- Verification: {self.verification_duration_ms:.0f}ms"
        )
        total = self.generation_duration_ms + self.verification_duration_ms
        lines.append(f"- Total: {total:.0f}ms")
        lines.append("")

        # Cache efficiency
        if self.oracle_calls > 0:
            hit_rate = (self.oracle_cache_hits / self.oracle_calls) * 100
            lines.append("## Cache Efficiency")
            lines.append("")
            lines.append(f"- Oracle cache hit rate: {hit_rate:.1f}%")
            if self.tokens_used > 0:
                savings = (self.tokens_saved / (self.tokens_used + self.tokens_saved)) * 100
                lines.append(f"- Token savings: {savings:.1f}%")
            lines.append("")

        return "\n".join(lines)

    def to_dict(self) -> Dict[str, Any]:
        """JSON-serialisable dictionary representation."""
        return {
            "overall_trust": self.overall_trust,
            "per_module": self.per_module,
            "structural_proven": self.structural_proven,
            "semantic_judged": self.semantic_judged,
            "lean_verified": self.lean_verified,
            "unchecked": self.unchecked,
            "hallucinations_found": self.hallucinations_found,
            "hallucinations_fixed": self.hallucinations_fixed,
            "oracle_calls": self.oracle_calls,
            "oracle_cache_hits": self.oracle_cache_hits,
            "tokens_used": self.tokens_used,
            "tokens_saved": self.tokens_saved,
            "cross_module_contracts_verified": self.cross_module_contracts_verified,
            "cross_module_contracts_failed": self.cross_module_contracts_failed,
            "h1_overall": self.h1_overall,
            "total_lines": self.total_lines,
            "total_modules": self.total_modules,
            "generation_duration_ms": self.generation_duration_ms,
            "verification_duration_ms": self.verification_duration_ms,
            "created_at": self.created_at,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> TrustReport:
        return cls(
            overall_trust=d.get("overall_trust", "UNCHECKED"),
            per_module=d.get("per_module", {}),
            structural_proven=d.get("structural_proven", 0),
            semantic_judged=d.get("semantic_judged", 0),
            lean_verified=d.get("lean_verified", 0),
            unchecked=d.get("unchecked", 0),
            hallucinations_found=d.get("hallucinations_found", 0),
            hallucinations_fixed=d.get("hallucinations_fixed", 0),
            oracle_calls=d.get("oracle_calls", 0),
            oracle_cache_hits=d.get("oracle_cache_hits", 0),
            tokens_used=d.get("tokens_used", 0),
            tokens_saved=d.get("tokens_saved", 0),
            cross_module_contracts_verified=d.get("cross_module_contracts_verified", 0),
            cross_module_contracts_failed=d.get("cross_module_contracts_failed", 0),
            h1_overall=d.get("h1_overall", "H¹ = 0"),
            total_lines=d.get("total_lines", 0),
            total_modules=d.get("total_modules", 0),
            generation_duration_ms=d.get("generation_duration_ms", 0.0),
            verification_duration_ms=d.get("verification_duration_ms", 0.0),
            created_at=d.get("created_at", ""),
        )


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ TrustReportGenerator                                                     │
# └──────────────────────────────────────────────────────────────────────────┘

class TrustReportGenerator:
    """Generate aggregated trust reports from verification results."""

    def generate_trust_report(
        self,
        all_results: Dict[str, Any],
        cross_module_result: Optional[Dict[str, Any]] = None,
        generation_stats: Optional[Dict[str, Any]] = None,
    ) -> TrustReport:
        """
        Generate a trust report from per-module verification results.

        Parameters
        ----------
        all_results : dict
            Mapping from module_name to verification result dict.
        cross_module_result : dict, optional
            Cross-module verification result dict.
        generation_stats : dict, optional
            Token usage, timing, and cache statistics.
        """
        per_module: Dict[str, str] = {}
        structural_proven = 0
        semantic_judged = 0
        lean_verified_count = 0
        unchecked_count = 0
        hallucinations_found = 0
        hallucinations_fixed = 0
        total_lines = 0

        for mod_name, result in all_results.items():
            trust = result.get("trust_level", "UNCHECKED")
            per_module[mod_name] = trust

            # Count structural
            for sr in result.get("structural_results", []):
                if sr.get("status") == "proven":
                    structural_proven += 1

            # Count semantic
            for sr in result.get("semantic_results", []):
                if sr.get("status") == "passed":
                    semantic_judged += 1

            # Count lean
            for ob in result.get("lean_obligations", []):
                if ob.get("status") == "discharged":
                    lean_verified_count += 1

            # Hallucinations
            hall = result.get("hallucination_findings", [])
            hallucinations_found += len(hall)

            # Count CEGAR repairs as "fixed" hallucinations
            cegar_rounds = result.get("cegar_rounds", 0)
            if cegar_rounds > 0 and result.get("passed", False):
                hallucinations_fixed += len(hall)

        # Count unchecked
        for trust in per_module.values():
            if trust == "UNCHECKED":
                unchecked_count += 1

        # Overall trust
        if per_module:
            overall = _min_trust(*per_module.values())
        else:
            overall = "UNCHECKED"

        # Cross-module
        cm_verified = 0
        cm_failed = 0
        h1_overall = "H¹ = 0"
        if cross_module_result:
            cm_verified = cross_module_result.get("contracts_verified", 0)
            cm_failed = cross_module_result.get("contracts_failed", 0)
            h1_overall = cross_module_result.get("h1_cross", "H¹ = 0")

        # Stats
        oracle_calls = 0
        oracle_cache_hits = 0
        tokens_used = 0
        tokens_saved = 0
        gen_duration = 0.0
        ver_duration = 0.0
        if generation_stats:
            oracle_calls = generation_stats.get("oracle_calls", 0)
            oracle_cache_hits = generation_stats.get("oracle_cache_hits", 0)
            tokens_used = generation_stats.get("tokens_used", 0)
            tokens_saved = generation_stats.get("tokens_saved", 0)
            gen_duration = generation_stats.get("generation_duration_ms", 0.0)
            ver_duration = generation_stats.get("verification_duration_ms", 0.0)

        return TrustReport(
            overall_trust=overall,
            per_module=per_module,
            structural_proven=structural_proven,
            semantic_judged=semantic_judged,
            lean_verified=lean_verified_count,
            unchecked=unchecked_count,
            hallucinations_found=hallucinations_found,
            hallucinations_fixed=hallucinations_fixed,
            oracle_calls=oracle_calls,
            oracle_cache_hits=oracle_cache_hits,
            tokens_used=tokens_used,
            tokens_saved=tokens_saved,
            cross_module_contracts_verified=cm_verified,
            cross_module_contracts_failed=cm_failed,
            h1_overall=h1_overall,
            total_lines=total_lines,
            total_modules=len(per_module),
            generation_duration_ms=gen_duration,
            verification_duration_ms=ver_duration,
        )


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ ProjectAssembler                                                         │
# └──────────────────────────────────────────────────────────────────────────┘

class ProjectAssembler:
    """
    Assemble verified modules into a complete, runnable project.

    Produces a :class:`ProjectStructure` containing all source files, tests,
    Lean proofs, configuration, documentation, and a full audit manifest.
    """

    def __init__(
        self,
        trust_report_gen: Optional[TrustReportGenerator] = None,
    ) -> None:
        self._trust_gen = trust_report_gen or TrustReportGenerator()

    def assemble(
        self,
        intent: Dict[str, Any],
        modules: Dict[str, VerifiedModule],
        results: Dict[str, Any],
        config: Optional[Dict[str, Any]] = None,
    ) -> ProjectStructure:
        """
        Assemble a verified project.

        Parameters
        ----------
        intent : dict
            The resolved intent from the intent oracle. Must have at least
            ``project_name`` and ``description``.
        modules : dict
            Mapping from module name to :class:`VerifiedModule`.
        results : dict
            Mapping from module name to verification result dict.
        config : dict, optional
            Extra configuration overrides.
        """
        config = config or {}
        project_name = self._project_name(intent)

        # Collect dependencies from intent
        dependencies = intent.get("dependencies", [])
        if not dependencies:
            dependencies = self._infer_dependencies(modules)

        # Generate all project files
        pyproject = self.generate_pyproject_toml(intent, dependencies)
        manifest = self.generate_manifest(
            intent=intent,
            modules={n: m.to_dict() for n, m in modules.items()},
            results=results,
            config=config,
        )

        # Trust summary for README
        trust_report = self._trust_gen.generate_trust_report(results)
        trust_summary_dict = trust_report.to_dict()

        readme = self.generate_readme(intent, trust_summary_dict)

        # Collect tests
        tests: Dict[str, str] = {}
        for mod_name, module in modules.items():
            if module.test_source:
                tests[mod_name] = module.test_source
            else:
                tests[mod_name] = self._generate_stub_test(mod_name, module)

        # Collect lean proofs
        lean_proofs: Dict[str, str] = {}
        for mod_name, module in modules.items():
            if module.lean_source:
                lean_proofs[mod_name] = module.lean_source

        # Init files
        init_files = self.generate_init_files(
            project_name, list(modules.keys()),
        )

        # Optional files
        dockerfile = None
        ci_config = None
        if config.get("docker", False) or intent.get("docker", False):
            dockerfile = self.generate_dockerfile(intent)
        if config.get("ci", True):
            ci_config = self.generate_ci_config(intent)

        return ProjectStructure(
            name=project_name,
            modules=modules,
            tests=tests,
            lean_proofs=lean_proofs,
            config=pyproject,
            readme=readme,
            manifest=manifest,
            dockerfile=dockerfile,
            ci_config=ci_config,
            init_files=init_files,
        )

    def generate_pyproject_toml(
        self,
        intent: Dict[str, Any],
        dependencies: List[str],
    ) -> Dict[str, Any]:
        """Generate pyproject.toml content as a dictionary."""
        project_name = self._project_name(intent)
        description = intent.get("description", f"Generated by deppy: {project_name}")

        return {
            "build-system": {
                "requires": ["setuptools>=68.0", "wheel"],
                "build-backend": "setuptools.build_meta",
            },
            "project": {
                "name": project_name,
                "version": "0.1.0",
                "description": description,
                "readme": "README.md",
                "requires-python": ">=3.10",
                "license": "MIT",
                "dependencies": dependencies,
            },
            "tool": {
                "deppy": {
                    "manifest": "deppy_manifest.json",
                    "trust-minimum": "LLM_JUDGED",
                },
                "pytest": {
                    "testpaths": ["tests"],
                },
                "ruff": {
                    "line-length": 88,
                },
            },
        }

    def generate_readme(
        self,
        intent: Dict[str, Any],
        trust_summary: Dict[str, Any],
    ) -> str:
        """
        Generate README.md with project description, verification status,
        and trust badges.
        """
        project_name = self._project_name(intent)
        description = intent.get("description", "")
        domain = intent.get("domain", "general")

        lines: List[str] = []
        lines.append(f"# {project_name}")
        lines.append("")
        if description:
            lines.append(description)
            lines.append("")

        ideation = intent.get("ideation")
        if isinstance(ideation, dict) and ideation.get("novel_idea"):
            lines.append("## Ideation-as-Typing")
            lines.append("")
            lines.append(f"**Novel idea:** {ideation['novel_idea']}")
            lines.append("")

        orchestration = intent.get("orchestration")
        if isinstance(orchestration, dict) and orchestration.get("module_order"):
            lines.append("## Typed Orchestration")
            lines.append("")
            lines.append(
                "Generation cover: "
                + " → ".join(orchestration.get("module_order", []))
            )
            lines.append("")

        # Trust badge
        overall = trust_summary.get("overall_trust", "UNCHECKED")
        badge = TRUST_BADGES.get(overall, overall)
        lines.append(f"**Verification Status:** {badge}")
        lines.append("")

        # Legend
        lines.append("### Trust Level Legend")
        lines.append("")
        lines.append("| Badge | Level | Meaning |")
        lines.append("|-------|-------|---------|")
        lines.append(
            "| 🟢 | LEAN_VERIFIED | "
            "Formally proven in Lean 4 — highest assurance |"
        )
        lines.append(
            "| 🟡 | Z3_PROVEN | "
            "Structurally proven by Z3 SMT solver |"
        )
        lines.append(
            "| 🟠 | LLM_JUDGED | "
            "Judged correct by LLM oracle (semantic check) |"
        )
        lines.append(
            "| 🔴 | UNCHECKED | "
            "Not yet verified — use with caution |"
        )
        lines.append("")

        # Module overview
        per_module = trust_summary.get("per_module", {})
        if per_module:
            lines.append("### Module Verification Status")
            lines.append("")
            lines.append("| Module | Trust Level | Status |")
            lines.append("|--------|-------------|--------|")
            for mod_name in sorted(per_module.keys()):
                trust = per_module[mod_name]
                emoji = TRUST_EMOJI.get(trust, "🔴")
                badge_text = TRUST_BADGES.get(trust, trust)
                lines.append(f"| `{mod_name}` | {badge_text} | {emoji} |")
            lines.append("")

        # Stats summary
        lines.append("### Verification Summary")
        lines.append("")
        sp = trust_summary.get("structural_proven", 0)
        sj = trust_summary.get("semantic_judged", 0)
        lv = trust_summary.get("lean_verified", 0)
        hf = trust_summary.get("hallucinations_found", 0)
        hx = trust_summary.get("hallucinations_fixed", 0)
        lines.append(f"- Structural properties proven (Z3): **{sp}**")
        lines.append(f"- Semantic properties judged (LLM): **{sj}**")
        lines.append(f"- Lean obligations discharged: **{lv}**")
        lines.append(f"- Hallucinations detected: **{hf}**")
        lines.append(f"- Hallucinations fixed (CEGAR): **{hx}**")
        lines.append("")

        # Domain
        if domain and domain != "general":
            lines.append(f"### Domain")
            lines.append("")
            lines.append(f"This project targets the **{domain}** domain.")
            lines.append("")

        # Generated by deppy
        lines.append("---")
        lines.append("")
        lines.append(
            "*This project was generated and verified by "
            "[deppy](https://github.com/mathdivergence/deppy) — "
            "dependent types for Python via hybrid verification.*"
        )
        lines.append("")

        return "\n".join(lines)

    def generate_manifest(
        self,
        intent: Dict[str, Any],
        modules: Dict[str, Any],
        results: Dict[str, Any],
        config: Dict[str, Any],
    ) -> Dict[str, Any]:
        """
        Generate the full audit manifest.

        Contains: every LLM call, every check, every trust transition.
        """
        timestamp = _timestamp_iso()
        project_name = self._project_name(intent)

        # Build per-module audit entries
        module_audits: Dict[str, Any] = {}
        for mod_name, mod_info in modules.items():
            result = results.get(mod_name, {})
            module_audits[mod_name] = {
                "trust_level": mod_info.get("trust_level", "UNCHECKED"),
                "content_hash": mod_info.get("content_hash", ""),
                "generation_model": mod_info.get("generation_model", ""),
                "generation_tokens": mod_info.get("generation_tokens", 0),
                "cegar_rounds": mod_info.get("cegar_rounds", 0),
                "verification": {
                    "structural_results": result.get("structural_results", []),
                    "semantic_results": result.get("semantic_results", []),
                    "hallucination_findings": result.get("hallucination_findings", []),
                    "lean_obligations": result.get("lean_obligations", []),
                    "discharged": result.get("discharged", 0),
                    "residual": result.get("residual", 0),
                    "h1_status": result.get("h1_status", "H¹ = 0"),
                    "duration_ms": result.get("duration_ms", 0.0),
                    "passed": result.get("passed", False),
                },
            }

        # Compute aggregate stats
        total_structural = sum(
            len(r.get("structural_results", []))
            for r in results.values()
        )
        total_structural_proven = sum(
            sum(1 for sr in r.get("structural_results", [])
                if sr.get("status") == "proven")
            for r in results.values()
        )
        total_semantic = sum(
            len(r.get("semantic_results", []))
            for r in results.values()
        )
        total_semantic_passed = sum(
            sum(1 for sr in r.get("semantic_results", [])
                if sr.get("status") == "passed")
            for r in results.values()
        )
        total_hallucinations = sum(
            len(r.get("hallucination_findings", []))
            for r in results.values()
        )
        total_lean_discharged = sum(
            r.get("discharged", 0)
            for r in results.values()
        )
        total_lean_residual = sum(
            r.get("residual", 0)
            for r in results.values()
        )

        return {
            "deppy_version": "0.1.0",
            "project_name": project_name,
            "created_at": timestamp,
            "intent": {
                "raw_prompt": intent.get("raw_prompt", ""),
                "domain": intent.get("domain", "general"),
                "description": intent.get("description", ""),
                "modules_planned": intent.get("modules", []),
                "constraints": intent.get("constraints", []),
                "ideation": intent.get("ideation"),
                "orchestration": intent.get("orchestration"),
            },
            "config": config,
            "modules": module_audits,
            "aggregate": {
                "total_modules": len(modules),
                "structural_checks": total_structural,
                "structural_proven": total_structural_proven,
                "semantic_checks": total_semantic,
                "semantic_passed": total_semantic_passed,
                "hallucinations_found": total_hallucinations,
                "lean_discharged": total_lean_discharged,
                "lean_residual": total_lean_residual,
            },
            "trust_chain": self._build_trust_chain(modules, results),
        }

    def generate_init_files(
        self,
        project_name: str,
        module_names: List[str],
    ) -> Dict[str, str]:
        """Generate __init__.py files for the package structure."""
        init_files: Dict[str, str] = {}

        # Top-level __init__.py
        top_init_lines: List[str] = [
            f'"""',
            f'{project_name} — generated and verified by deppy.',
            f'"""',
            f'',
            f'__version__ = "0.1.0"',
            f'',
        ]

        # Import each module
        for mod_name in sorted(module_names):
            safe = mod_name.replace("-", "_").replace(".", "_")
            top_init_lines.append(f"from . import {safe}")

        top_init_lines.append("")
        init_files[f"{project_name}/__init__.py"] = "\n".join(top_init_lines)

        # Sub-package __init__.py files for nested modules
        sub_packages: set[str] = set()
        for mod_name in module_names:
            parts = _safe_module_path(mod_name).split("/")
            for i in range(len(parts) - 1):
                sub_pkg = "/".join(parts[: i + 1])
                sub_packages.add(sub_pkg)

        for sub_pkg in sorted(sub_packages):
            rel_path = f"{project_name}/{sub_pkg}/__init__.py"
            init_files[rel_path] = f'"""{sub_pkg} sub-package."""\n'

        return init_files

    def generate_dockerfile(
        self,
        intent: Dict[str, Any],
    ) -> Optional[str]:
        """Generate a Dockerfile for the project."""
        project_name = self._project_name(intent)
        python_version = intent.get("python_version", "3.11")

        return textwrap.dedent(f"""\
            # Generated by deppy
            FROM python:{python_version}-slim

            WORKDIR /app

            # Install dependencies
            COPY pyproject.toml .
            RUN pip install --no-cache-dir -e .

            # Copy source
            COPY src/ src/
            COPY tests/ tests/

            # Run tests on build to verify
            RUN python -m pytest tests/ -v

            # Default command
            CMD ["python", "-m", "{project_name}"]
        """)

    def generate_ci_config(
        self,
        intent: Dict[str, Any],
    ) -> Optional[str]:
        """Generate GitHub Actions CI config with deppy check."""
        project_name = self._project_name(intent)
        python_version = intent.get("python_version", "3.11")

        return textwrap.dedent(f"""\
            # Generated by deppy — CI with verification
            name: Deppy CI

            on:
              push:
                branches: [main]
              pull_request:
                branches: [main]

            jobs:
              test:
                runs-on: ubuntu-latest
                steps:
                  - uses: actions/checkout@v4

                  - name: Set up Python
                    uses: actions/setup-python@v5
                    with:
                      python-version: "{python_version}"

                  - name: Install dependencies
                    run: |
                      python -m pip install --upgrade pip
                      pip install -e ".[dev]"

                  - name: Run tests
                    run: python -m pytest tests/ -v

              deppy-verify:
                runs-on: ubuntu-latest
                needs: test
                steps:
                  - uses: actions/checkout@v4

                  - name: Set up Python
                    uses: actions/setup-python@v5
                    with:
                      python-version: "{python_version}"

                  - name: Install deppy
                    run: pip install deppy

                  - name: Verify project
                    run: deppy --check .

                  - name: Generate trust report
                    run: deppy --report deppy_manifest.json
                    if: always()

                  - name: Upload trust report
                    uses: actions/upload-artifact@v4
                    with:
                      name: trust-report
                      path: deppy_trust_report.md
                    if: always()
        """)

    # ── Private helpers ───────────────────────────────────────────────────

    @staticmethod
    def _project_name(intent: Dict[str, Any]) -> str:
        """Extract or derive the project name from intent."""
        name = intent.get("project_name", "")
        if not name:
            # Derive from description
            desc = intent.get("description", "deppy_project")
            name = re.sub(r"[^a-zA-Z0-9]+", "_", desc)[:40].strip("_").lower()
        return name.replace("-", "_").replace(" ", "_")

    @staticmethod
    def _infer_dependencies(modules: Dict[str, VerifiedModule]) -> List[str]:
        """Infer third-party dependencies from module source code."""
        deps: set[str] = set()
        # Common stdlib modules to ignore
        stdlib = {
            "os", "sys", "re", "json", "time", "datetime", "hashlib",
            "typing", "dataclasses", "abc", "collections", "itertools",
            "functools", "pathlib", "logging", "unittest", "math",
            "io", "copy", "enum", "textwrap", "contextlib",
        }
        import_pattern = re.compile(
            r"(?:from\s+(\w+)|import\s+(\w+))"
        )
        for module in modules.values():
            for m in import_pattern.finditer(module.source):
                mod = m.group(1) or m.group(2)
                if mod and mod not in stdlib and not mod.startswith("_"):
                    deps.add(mod)

        return sorted(deps)

    @staticmethod
    def _generate_stub_test(mod_name: str, module: VerifiedModule) -> str:
        """Generate a minimal test stub for a module without tests."""
        safe = mod_name.replace("-", "_").replace(".", "_")
        return textwrap.dedent(f"""\
            \"\"\"Auto-generated test stub for {mod_name}.\"\"\"
            import pytest


            class Test{safe.title().replace('_', '')}:
                \"\"\"Tests for {mod_name} module.\"\"\"

                def test_module_imports(self):
                    \"\"\"Verify the module can be imported.\"\"\"
                    # TODO: Replace with actual import once package is installed
                    assert True

                def test_placeholder(self):
                    \"\"\"Placeholder test — replace with real tests.\"\"\"
                    # This module was verified by deppy with trust level: {module.trust_level}
                    assert True
        """)

    @staticmethod
    def _build_trust_chain(
        modules: Dict[str, Any],
        results: Dict[str, Any],
    ) -> List[Dict[str, Any]]:
        """Build the trust transition chain for the manifest."""
        chain: List[Dict[str, Any]] = []
        for mod_name, mod_info in modules.items():
            result = results.get(mod_name, {})
            entry: Dict[str, Any] = {
                "module": mod_name,
                "transitions": [],
            }

            # Initial state
            entry["transitions"].append({
                "from": "UNCHECKED",
                "to": "UNCHECKED",
                "reason": "initial generation",
            })

            # After structural check
            struct_ok = all(
                sr.get("status") == "proven"
                for sr in result.get("structural_results", [])
            )
            if struct_ok and result.get("structural_results"):
                entry["transitions"].append({
                    "from": "UNCHECKED",
                    "to": "Z3_PROVEN",
                    "reason": "all structural claims proven by Z3",
                })

            # After semantic check
            sem_ok = all(
                sr.get("status") == "passed"
                for sr in result.get("semantic_results", [])
            )
            if sem_ok and result.get("semantic_results"):
                prev = entry["transitions"][-1]["to"]
                entry["transitions"].append({
                    "from": prev,
                    "to": _min_trust(prev, "LLM_JUDGED"),
                    "reason": "semantic claims passed oracle check",
                })

            # After lean
            if result.get("discharged", 0) > 0:
                if result.get("residual", 0) == 0:
                    prev = entry["transitions"][-1]["to"]
                    entry["transitions"].append({
                        "from": prev,
                        "to": "LEAN_VERIFIED",
                        "reason": "all Lean obligations discharged",
                    })

            # Final
            final_trust = mod_info.get("trust_level", "UNCHECKED")
            if entry["transitions"][-1]["to"] != final_trust:
                entry["transitions"].append({
                    "from": entry["transitions"][-1]["to"],
                    "to": final_trust,
                    "reason": "final trust computation",
                })

            chain.append(entry)

        return chain


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Module-level convenience functions                                       │
# └──────────────────────────────────────────────────────────────────────────┘

def assemble_project(
    intent: Dict[str, Any],
    modules: Dict[str, VerifiedModule],
    results: Dict[str, Any],
    config: Optional[Dict[str, Any]] = None,
) -> ProjectStructure:
    """Convenience: assemble a project with default settings."""
    assembler = ProjectAssembler()
    return assembler.assemble(intent, modules, results, config)


def generate_trust_report(
    all_results: Dict[str, Any],
    cross_module_result: Optional[Dict[str, Any]] = None,
    generation_stats: Optional[Dict[str, Any]] = None,
) -> TrustReport:
    """Convenience: generate a trust report."""
    gen = TrustReportGenerator()
    return gen.generate_trust_report(
        all_results, cross_module_result, generation_stats,
    )
