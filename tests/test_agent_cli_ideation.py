from __future__ import annotations

import json
import os
import re
from io import StringIO

from deppy.hybrid.ideation.math_ontology_loader import (
    all_math_areas,
    all_math_terms,
    ontology_path,
    ontology_summary,
)
from agent.cli import AgentCLI, CLIConfig, CopilotCLIInterface
from agent.orchestrator import OrchestratorConfig
from agent.verification_loop import VerificationConfig, VerificationLoop


class _FakeLLM:
    def __init__(self) -> None:
        self.last_prompt = ""
        self.prompts: list[str] = []
        self.responses: list[str] = []

    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        self.last_prompt = prompt
        self.prompts.append(prompt)
        if self.responses:
            return self.responses.pop(0)
        return "# generated\n"

    def complete_json(
        self,
        prompt: str,
        schema,
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ):
        raise RuntimeError("not used")


class _EmptyJSONLLM:
    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        raise RuntimeError("not used")

    def complete_json(
        self,
        prompt: str,
        schema,
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ):
        return {}


class _FailingLLM:
    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        raise RuntimeError("generation failed")

    def complete_json(
        self,
        prompt: str,
        schema,
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ):
        raise RuntimeError("not used")


class _GuidedSelectionLLM:
    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        raise RuntimeError("not used")

    def complete_json(
        self,
        prompt: str,
        schema,
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ):
        return {
            "registry_domains": [
                "machine_learning",
                "formal_verification",
                "category_theory",
                "software_engineering",
            ],
            "math_areas": [
                "stochastic calculus",
                "financial mathematics",
                "Bayesian statistics",
                "control dynamical systems",
            ],
            "reasoning": [
                "The problem is driven by uncertainty, decision-making, and implementation constraints.",
                "These areas are more testable in the deppy framework than a default AG/DTT-only lens.",
            ],
            "idea_strength": 0.82,
            "math_area_strengths": [
                {
                    "area": "stochastic calculus",
                    "score": 0.88,
                    "rationale": "Best fit for modeling price evolution and uncertainty.",
                },
                {
                    "area": "financial mathematics",
                    "score": 0.86,
                    "rationale": "Strong alignment with risk and execution constraints.",
                },
            ],
        }


class _ShallowCopilotLLM(CopilotCLIInterface):
    def __init__(self) -> None:
        super().__init__(model="copilot", executable="/usr/bin/copilot", timeout_seconds=5)
        self.calls = 0
        self.prompts: list[str] = []

    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        del prompt, max_tokens, temperature
        self.calls += 1
        return '"""shallow"""\n\ndef helper() -> int:\n    return 1\n'

    def write_module_file(
        self,
        prompt: str,
        target_path: str,
    ) -> str:
        self.calls += 1
        self.prompts.append(prompt)
        os.makedirs(os.path.dirname(target_path), exist_ok=True)
        source = '"""shallow"""\n\ndef helper() -> int:\n    return 1\n'
        with open(target_path, "w", encoding="utf-8") as handle:
            handle.write(source)
        return source

    def write_module_files(
        self,
        prompt: str,
        target_paths: list[str],
    ) -> dict[str, str]:
        self.calls += 1
        self.prompts.append(prompt)
        results: dict[str, str] = {}
        for target_path in target_paths:
            os.makedirs(os.path.dirname(target_path), exist_ok=True)
            source = (
                '"""phase module"""\n\n'
                "from __future__ import annotations\n\n"
                "def phase_entry(payload: dict[str, object]) -> dict[str, object]:\n"
                f"    return {{'path': {target_path!r}, 'payload': payload}}\n"
            )
            with open(target_path, "w", encoding="utf-8") as handle:
                handle.write(source)
            results[os.path.abspath(target_path)] = source
        return results

    def complete_json(
        self,
        prompt: str,
        schema,
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ):
        raise RuntimeError("not used")


class _FakeProgress:
    def __init__(self) -> None:
        self.messages: list[str] = []

    def info(self, message: str) -> None:
        self.messages.append(message)

    def warning(self, message: str) -> None:
        self.messages.append(message)


def test_agent_cli_parses_ideation_and_orchestration_flags() -> None:
    cli = AgentCLI(
        args=[
            "--ideation",
            "--orchestration",
            "build a verified trading system",
        ]
    )

    config = cli.parse_args()

    assert config.ideation is True
    assert config.orchestration is True
    assert config.prompt == "build a verified trading system"


def test_agent_cli_parses_full_flag() -> None:
    cli = AgentCLI(args=["--full", "build a large verified system"])

    config = cli.parse_args()

    assert config.full is True
    assert config.prompt == "build a large verified system"


def test_enrich_intent_adds_trading_ideation_and_orchestration() -> None:
    cli = AgentCLI()
    cli._config = CLIConfig(
        prompt="build a verified trading system",
        ideation=True,
        orchestration=True,
        verbose=False,
    )
    cli._progress = _FakeProgress()

    intent = {
        "raw_prompt": "build a verified trading system",
        "project_name": "verified_trading",
        "description": "build a verified trading system",
        "domain": "trading",
        "modules": ["main"],
        "constraints": [],
        "dependencies": [],
    }

    enriched = cli._enrich_intent("build a verified trading system", intent)

    assert "ideation" in enriched
    assert "orchestration" in enriched
    assert enriched["ideation"]["novel_idea"]
    assert enriched["ideation"]["novel_idea_structured"]["ag_view"]
    assert enriched["ideation"]["math_area_count_considered"] == 500
    assert enriched["ideation"]["math_term_count_considered"] >= 1000
    assert "signal_geometry" in enriched["modules"]
    assert "strategy_kernel" in enriched["modules"]
    assert enriched["orchestration"]["gluing_obligations"]
    assert enriched["orchestration"]["type_elaboration_tree"]["name"] == "trading_system_cover"


def test_generate_module_prompt_includes_ideation_and_orchestration_context() -> None:
    cli = AgentCLI()
    fake = _FakeLLM()
    fake.responses = ['"""module"""\n\ndef helper() -> int:\n    return 1\n']
    cli._llm = fake

    intent = {
        "description": "verified trading system",
        "domain": "trading",
        "constraints": ["Novel idea requirement: coherent signal sheaf"],
        "module_roles": {
            "signal_geometry": "ideation site: turn local signals into a gluable global section",
        },
        "ideation": {
            "novel_idea": "Treat market regimes as a Grothendieck cover.",
            "deep_analogies": ["Analogy(type_theory↔algebraic_geometry)"],
        },
        "orchestration": {
            "module_order": ["market_data", "signal_geometry", "strategy_kernel"],
            "overlaps": [
                {
                    "left": "market_data",
                    "right": "signal_geometry",
                    "obligation": "signals preserve normalization invariants",
                }
            ],
            "gluing_obligations": ["Global section condition: H¹ = 0"],
        },
        "full_expansion": {
            "modules": [
                {
                    "name": "signal_geometry",
                    "summary": "signal geometry",
                    "depends_on": ["market_data"],
                    "exports": ["compute_signal_geometry"],
                    "imports": ["load_market_data"],
                    "responsibilities": ["turn local signals into a gluable global section"],
                    "estimated_loc": 180,
                    "test_obligations": ["preserve normalization invariants"],
                    "class_specs": [
                        {
                            "name": "SignalGeometryState",
                            "role": "Typed state carrier",
                            "fields": ["payload: Dict[str, Any]"],
                            "invariants": ["gluing", "normalization"],
                        }
                    ],
                    "function_specs": [
                        {
                            "name": "compute_signal_geometry",
                            "signature": "(series: list[float]) -> dict[str, float]",
                            "purpose": "Construct a gluable signal section.",
                            "invariants": ["gluing", "normalization"],
                        }
                    ],
                }
            ]
        },
    }

    cli._generate_module(intent, "signal_geometry")

    prompt = cli._llm.prompts[0]
    assert "Novel idea to realize" in prompt
    assert "Typed orchestration requirements" in prompt
    assert "signal_geometry" in prompt
    assert "H¹ = 0" in prompt
    assert "Desired classes:" in prompt
    assert "Desired functions:" in prompt
    assert "SignalGeometryState" in prompt
    assert "compute_signal_geometry" in prompt
    assert "Inspect other files in the current directory for this module's obligations" in prompt
    assert "Shared signature context:" in prompt


def test_module_plan_carries_typed_surface_specs_from_full_expansion() -> None:
    cli = AgentCLI()
    intent = {
        "full_expansion": {
            "modules": [
                {
                    "name": "risk_engine",
                    "summary": "risk engine",
                    "depends_on": ["strategy_kernel"],
                    "exports": ["evaluate_risk"],
                    "imports": ["propose_strategy"],
                    "responsibilities": ["enforce leverage and drawdown invariants"],
                    "estimated_loc": 220,
                    "test_obligations": ["leverage bound", "drawdown bound"],
                    "class_specs": [
                        {"name": "RiskEngineState", "role": "Typed state carrier"}
                    ],
                    "function_specs": [
                        {
                            "name": "evaluate_risk",
                            "signature": "(proposal: dict[str, float]) -> dict[str, float]",
                            "purpose": "Admit only risk-safe proposals.",
                        }
                    ],
                }
            ]
        }
    }

    module_plan = cli._module_plan(intent, "risk_engine")

    assert module_plan["class_specs"][0]["name"] == "RiskEngineState"
    assert module_plan["function_specs"][0]["name"] == "evaluate_risk"


def test_module_plan_collects_signature_context_from_full_expansion() -> None:
    cli = AgentCLI()
    intent = {
        "full_expansion": {
            "global_plan": {
                "modules": [
                    {
                        "name": "market_data",
                        "summary": "market data",
                        "depends_on": [],
                        "exports": ["load_market_data"],
                        "imports": [],
                        "function_specs": [
                            {
                                "name": "load_market_data",
                                "signature": "(series: list[float], window: int) -> dict[str, float]",
                                "purpose": "Load market data.",
                            }
                        ],
                    },
                    {
                        "name": "signal_geometry",
                        "summary": "signal geometry",
                        "depends_on": ["market_data"],
                        "exports": ["compute_signal_geometry"],
                        "imports": ["load_market_data"],
                        "function_specs": [
                            {
                                "name": "compute_signal_geometry",
                                "signature": "(series: list[float]) -> dict[str, float]",
                                "purpose": "Compute signals.",
                            }
                        ],
                    },
                ],
                "phases": [
                    {"index": 1, "module_names": ["market_data"], "gate_checks": []},
                    {"index": 2, "module_names": ["signal_geometry"], "gate_checks": []},
                ],
            }
        }
    }

    module_plan = cli._module_plan(intent, "signal_geometry")

    signature_context = module_plan["signature_context"]
    assert signature_context["phase_index"] == 2
    assert signature_context["phase_modules"] == ["signal_geometry"]
    assert signature_context["import_contracts"][0]["import_name"] == "load_market_data"
    assert signature_context["import_contracts"][0]["provider"] == "market_data"
    assert signature_context["import_contracts"][0]["param_names"] == ["series", "window"]


def test_resolve_intent_normalizes_empty_llm_payload_for_trading_prompt() -> None:
    cli = AgentCLI()
    cli._llm = _EmptyJSONLLM()

    intent = cli._resolve_intent(
        "build a verified trading system that discovers a novel market idea and proves the risk-critical core"
    )

    assert intent["domain"] == "trading"
    assert "market_data" in intent["modules"]
    assert "risk_engine" in intent["modules"]
    assert any("novel idea" in constraint.lower() for constraint in intent["constraints"])
    assert any("risk" in constraint.lower() for constraint in intent["constraints"])


def test_apply_orchestration_keeps_authoritative_cover_for_trading() -> None:
    cli = AgentCLI()
    cli._config = CLIConfig(prompt="build a verified trading system", orchestration=True)
    cli._progress = _FakeProgress()

    intent = {
        "description": "verified trading system",
        "domain": "trading",
        "modules": ["market_data_ingestion", "backtesting", "proof_artifacts"],
        "constraints": [],
    }

    enriched = cli._apply_orchestration("build a verified trading system", intent)

    assert enriched["modules"] == [
        "market_data",
        "signal_geometry",
        "strategy_kernel",
        "risk_engine",
        "execution",
        "portfolio",
        "compliance",
        "main",
    ]
    assert "market_data_ingestion" in enriched["orchestration"]["expanded_candidates"]
    assert enriched["orchestration"]["type_elaboration_tree"]["name"] == "trading_system_cover"
    assert AgentCLI._leaf_modules_from_tree(enriched["orchestration"]["type_elaboration_tree"]) == [
        "market_data",
        "signal_geometry",
        "strategy_kernel",
        "risk_engine",
        "execution",
        "portfolio",
        "compliance",
        "main",
    ]


def test_generate_module_refines_shallow_draft() -> None:
    cli = AgentCLI()
    fake = _FakeLLM()
    fake.responses = [
        "def x() -> int:\n    return 1\n",
        '"""Expanded module."""\n\nfrom dataclasses import dataclass\nfrom typing import Dict\n\n\n@dataclass\nclass Item:\n    value: int\n    label: str\n\n\n@dataclass\nclass Result:\n    payload: Dict[str, int]\n    ok: bool\n\n\ndef build_item() -> Item:\n    return Item(value=1, label="seed")\n\n\ndef validate_item(item: Item) -> bool:\n    return item.value >= 0 and bool(item.label)\n\n\ndef summarize_item(item: Item) -> dict[str, int]:\n    return {"value": item.value, "label_length": len(item.label)}\n\n\ndef normalize_value(value: int) -> int:\n    return max(0, value)\n\n\ndef enrich_item(item: Item, extra: int) -> Item:\n    return Item(value=item.value + extra, label=item.label + "_expanded")\n\n\ndef compute_metrics(item: Item) -> Dict[str, int]:\n    return {"value": item.value, "label_length": len(item.label), "double": item.value * 2}\n\n\ndef run_pipeline(value: int) -> Result:\n    item = build_item()\n    adjusted = enrich_item(item, normalize_value(value))\n    if not validate_item(adjusted):\n        raise ValueError("invalid item")\n    payload = summarize_item(adjusted)\n    payload.update(compute_metrics(adjusted))\n    return Result(payload=payload, ok=True)\n',
    ]
    cli._llm = fake

    intent = {
        "description": "example system",
        "domain": "general",
        "constraints": ["must be robust"],
        "modules": ["main"],
        "module_roles": {"main": "global section"},
        "orchestration": {"module_order": ["main"], "overlaps": [], "gluing_obligations": []},
    }

    artifact = cli._generate_module(intent, "main")

    assert "Expanded module." in artifact["source"]
    assert "run_pipeline" in artifact["source"]


def test_generate_module_falls_back_to_scaffold_on_llm_failure() -> None:
    cli = AgentCLI()
    cli._llm = _FailingLLM()

    intent = {
        "description": "example system",
        "domain": "general",
        "constraints": ["must be robust"],
        "modules": ["main"],
        "module_roles": {"main": "global section"},
        "orchestration": {"module_order": ["main"], "overlaps": [], "gluing_obligations": []},
    }

    artifact = cli._generate_module(intent, "main")

    assert "Autonomous typed scaffold" in artifact["source"]
    assert "class MainSection" in artifact["source"]
    assert "class MainTransport" in artifact["source"]
    assert "class MainService" in artifact["source"]
    assert "build_main" in artifact["source"]


def test_generate_module_summarizes_large_full_mode_module_order() -> None:
    cli = AgentCLI()
    fake = _FakeLLM()
    fake.responses = ['"""module"""\n\ndef helper() -> int:\n    return 1\n']
    cli._llm = fake

    module_order = [f"module_{index}" for index in range(40)]
    target = "module_20"
    intent = {
        "description": "example system",
        "domain": "general",
        "constraints": ["must be robust"],
        "modules": module_order,
        "full_mode": True,
        "module_roles": {target: "typed target module"},
        "full_expansion": {
            "global_plan": {
                "modules": [
                    {
                        "name": target,
                        "summary": "Target module summary",
                        "responsibilities": ["implement the target module"],
                        "depends_on": ["module_19"],
                        "exports": ["build_module_20"],
                        "imports": ["dataclasses"],
                        "estimated_loc": 240,
                        "test_obligations": ["preserve typed invariants"],
                    }
                ]
            }
        },
        "orchestration": {
            "module_order": module_order,
            "overlaps": [],
            "gluing_obligations": [],
        },
    }

    cli._generate_module(intent, target)

    prompt = fake.prompts[0]
    assert "Module order context:" in prompt
    assert "40 total modules" in prompt
    assert "module_18 -> module_19 -> module_20 -> module_21 -> module_22" in prompt
    assert str(module_order) not in prompt


def test_generate_module_limits_full_mode_refinements_for_copilot_backend(tmp_path) -> None:
    cli = AgentCLI()
    llm = _ShallowCopilotLLM()
    cli._llm = llm
    cli._config = CLIConfig(output_dir=str(tmp_path))

    intent = {
        "description": "example system",
        "domain": "general",
        "constraints": ["must be robust"],
        "modules": ["main"],
        "full_mode": True,
        "module_roles": {"main": "typed target module"},
        "orchestration": {"module_order": ["main"], "overlaps": [], "gluing_obligations": []},
    }

    artifact = cli._generate_module(intent, "main")

    assert "Autonomous typed scaffold" in artifact["source"]
    assert llm.calls == 1
    assert llm.prompts
    assert "You may take as many turns as needed" in llm.prompts[0]
    assert "Inspect other files in the current directory for this module's obligations" in llm.prompts[0]


def test_generate_phase_modules_batches_files_for_copilot(tmp_path) -> None:
    cli = AgentCLI()
    llm = _ShallowCopilotLLM()
    cli._llm = llm
    cli._config = CLIConfig(output_dir=str(tmp_path))

    intent = {
        "description": "example system",
        "domain": "general",
        "full_expansion": {
            "global_plan": {
                "modules": [
                    {
                        "name": "alpha",
                        "summary": "alpha module",
                        "depends_on": [],
                        "exports": ["build_alpha"],
                        "imports": [],
                        "function_specs": [
                            {
                                "name": "build_alpha",
                                "signature": "(context: dict[str, object]) -> dict[str, object]",
                                "purpose": "Build alpha.",
                            }
                        ],
                    },
                    {
                        "name": "beta",
                        "summary": "beta module",
                        "depends_on": [],
                        "exports": ["build_beta"],
                        "imports": ["build_alpha"],
                        "function_specs": [
                            {
                                "name": "build_beta",
                                "signature": "(context: dict[str, object]) -> dict[str, object]",
                                "purpose": "Build beta.",
                            }
                        ],
                    },
                ],
                "phases": [
                    {"index": 1, "module_names": ["alpha", "beta"], "gate_checks": []},
                ],
            }
        },
    }

    artifacts = cli._generate_phase_modules(intent, ["alpha", "beta"])

    assert set(artifacts.keys()) == {"alpha", "beta"}
    assert llm.calls == 1
    assert "Phase modules: alpha, beta" in llm.prompts[0]
    assert "Shared phase signature registry:" in llm.prompts[0]
    assert "shared imported/exported functions use the same names" in llm.prompts[0]


def test_progress_display_reports_generation_and_verification_timings() -> None:
    output = StringIO()
    from agent.cli import ProgressDisplay

    display = ProgressDisplay(output=output, verbose=True, use_color=False)
    display.module_start("main", 1, 1, pattern="typed core")
    display.verification_start("main")
    display.module_done("main", "Z3_PROVEN")

    rendered = output.getvalue()
    assert "Generation time:" in rendered
    assert "Verification time:" in rendered
    assert "Total module time:" in rendered


def test_copilot_backend_uses_repair_budget_for_strict_or_lean_runs() -> None:
    cli = AgentCLI()
    cli._config = CLIConfig(prompt="example", full=True, max_iterations=5)
    cli._llm = _ShallowCopilotLLM()

    assert cli._cegar_round_budget() == 1

    cli._config = CLIConfig(prompt="example", full=True, max_iterations=5, strict=True)
    assert cli._cegar_round_budget() == 2

    cli._config = CLIConfig(prompt="example", full=True, max_iterations=5, lean=True)
    assert cli._cegar_round_budget() == 2


def test_write_generation_prompts_exports_markdown(tmp_path) -> None:
    AgentCLI._write_generation_prompts(
        str(tmp_path),
        {
            "main": {
                "generation_prompt": "Write a complete Python module named 'main'.",
            }
        },
    )

    prompt_path = tmp_path / "prompts" / "main.generation_prompt.md"

    assert prompt_path.exists()
    contents = prompt_path.read_text(encoding="utf-8")
    assert "# Generation prompt for `main`" in contents
    assert "Write a complete Python module named 'main'." in contents


def test_write_ideation_report_exports_mathjax_html(tmp_path) -> None:
    intent = {
        "description": "verified trading system",
        "domain": "trading",
        "ideation": {
            "novel_idea": "Use sheaf-style regime gluing.",
            "domains": ["formal_verification", "machine_learning"],
            "unified_insights": ["Signals can be glued across local regime charts."],
            "deep_analogies": ["Analogy(type_theory↔algebraic_geometry)"],
            "selected_math_areas": ["robust statistics"],
            "selected_math_area_details": [
                {
                    "name": "robust statistics",
                    "summary": "Handle outliers while preserving stable estimates.",
                    "category": "statistics",
                    "family": "inference",
                    "bridge_domains": ["machine_learning"],
                    "key_invariants": ["bounded influence"],
                    "canonical_equations": [
                        {
                            "latex": r"\hat{\theta} = \arg\min_\theta \sum_i \rho(x_i - \theta)",
                            "meaning": "Robust estimator objective.",
                        }
                    ],
                }
            ],
            "novel_idea_structured": {
                "headline": "robust-regime-gluing",
                "thesis": "Use robust local charts and glue only coherent sections.",
                "proof_target": "Preserve leverage and drawdown invariants.",
            },
            "selection_strategy": {
                "mode": "llm_guided",
                "baseline_domains": ["software_engineering"],
                "guided_domains": ["formal_verification", "machine_learning"],
            },
            "benefit_evaluation": {
                "baseline_score": 3,
                "guided_score": 7,
                "score_delta": 4,
                "validated_delta": 1,
                "deep_analogies_delta": 1,
                "novel_connections_delta": 2,
                "h1_improvement": 1,
                "framework_certificate": "LLM-guided selection improved deppy ideation metrics over the typical baseline.",
            },
            "scalar_valued_typing": {
                "overall": 0.91,
                "llm_belief": 0.84,
                "math_model": 0.97,
                "label": "scalar-valued typing",
                "definition": "Scores the fit of the elaboration.",
                "scoring_rule": r"\sigma = 0.4 \cdot b + 0.6 \cdot m",
                "area_strengths": [
                    {
                        "area": "robust statistics",
                        "overall": 0.93,
                        "score": 0.93,
                        "rationale": "Supports noisy market regimes.",
                    }
                ],
            },
        },
    }

    AgentCLI._write_ideation_report(str(tmp_path), intent, {"main": {"source": "print('ok')\n"}})

    report_path = tmp_path / "ideation_improvements_report.html"
    contents = report_path.read_text(encoding="utf-8")
    assert report_path.exists()
    assert "MathJax" in contents
    assert "LLM-guided selection improved deppy ideation metrics" in contents
    assert r"\Delta_{score}" in contents
    assert "robust statistics" in contents


def test_generate_module_writes_prompt_markdown_immediately(tmp_path) -> None:
    cli = AgentCLI()
    fake = _FakeLLM()
    fake.responses = ['"""module"""\n\ndef helper() -> int:\n    return 1\n']
    cli._llm = fake
    cli._config = CLIConfig(output_dir=str(tmp_path))

    intent = {
        "project_name": "market",
        "description": "build a verified trading system",
        "domain": "trading",
        "constraints": ["must be robust"],
        "modules": ["main"],
        "module_roles": {"main": "global section"},
        "orchestration": {"module_order": ["main"], "overlaps": [], "gluing_obligations": []},
    }

    cli._generate_module(intent, "main")

    project_root = tmp_path / "market"
    prompt_path = project_root / "prompts" / "main.generation_prompt.md"
    assert prompt_path.exists()

    report_path = project_root / "ideation_improvements_report.html"
    assert report_path.exists()
    report = report_path.read_text(encoding="utf-8")
    assert "This report summarizes how ideation changed the generated system" in report
    assert "Write a complete Python module named 'main'." in prompt_path.read_text(encoding="utf-8")

    source_path = project_root / "generated_modules" / "main.py"
    assert source_path.exists()
    assert source_path.read_text(encoding="utf-8").strip()

    snapshot_path = project_root / "generation_record_sources" / "main.py"
    assert snapshot_path.exists()
    assert snapshot_path.read_text(encoding="utf-8") == source_path.read_text(encoding="utf-8")

    record_path = project_root / "generation_records" / "main.json"
    assert record_path.exists()
    record = json.loads(record_path.read_text(encoding="utf-8"))
    assert record["module_name"] == "main"
    assert record["stage"] == "generated"
    assert record["source_path"] == "generated_modules/main.py"
    assert record["source_snapshot_path"] == "generation_record_sources/main.py"
    assert record["prompt_path"] == "prompts/main.generation_prompt.md"


def test_module_generation_pattern_prefers_module_specific_plan_details() -> None:
    cli = AgentCLI()
    intent = {
        "description": "A research-to-execution trading platform that discovers a novel market hypothesis from historical and live data.",
        "full_expansion": {
            "modules": [
                {
                    "name": "market_data__domain_model_research_to_execution_trading_random_variables",
                    "summary": "A research-to-execution trading platform that discovers a novel market hypothesis from historical and live data.",
                    "responsibilities": [
                        "model random variables for market observations and research hypotheses",
                    ],
                    "class_specs": [
                        {
                            "name": "MarketDataSection",
                            "local_models": ["random variables", "stochastic processes"],
                        }
                    ],
                    "function_specs": [
                        {
                            "name": "build_market_data",
                            "purpose": "Construct market-data distributions for hypothesis testing.",
                            "invariants": ["martingale admissibility"],
                        }
                    ],
                }
            ]
        },
    }

    pattern = cli._module_generation_pattern(
        intent,
        "market_data__domain_model_research_to_execution_trading_random_variables",
    )

    assert "random variables" in pattern.lower()
    assert "research-to-execution trading platform" not in pattern.lower()


def test_generate_module_truncates_large_overlap_obligation_sets() -> None:
    cli = AgentCLI()
    fake = _FakeLLM()
    fake.responses = ['"""module"""\n\ndef helper() -> int:\n    return 1\n']
    cli._llm = fake

    overlaps = [
        {"left": "module_20", "right": f"module_{index}", "obligation": f"obligation_{index}"}
        for index in range(12)
    ]
    intent = {
        "description": "example system",
        "domain": "general",
        "constraints": ["must be robust"],
        "modules": ["module_20"],
        "full_mode": True,
        "module_roles": {"module_20": "typed target module"},
        "full_expansion": {
            "global_plan": {
                "modules": [
                    {
                        "name": "module_20",
                        "summary": "Target module summary",
                        "responsibilities": ["implement the target module"],
                        "depends_on": ["module_19"],
                        "exports": ["build_module_20"],
                        "imports": ["dataclasses"],
                        "estimated_loc": 240,
                        "test_obligations": ["preserve typed invariants"],
                    }
                ]
            }
        },
        "orchestration": {
            "module_order": ["module_19", "module_20", "module_21"],
            "overlaps": overlaps,
            "gluing_obligations": [],
        },
    }

    cli._generate_module(intent, "module_20")

    prompt = fake.prompts[0]
    assert "obligation_0" in prompt
    assert "obligation_5" in prompt
    assert "obligation_6" not in prompt
    assert "... (6 more)" in prompt


def test_scaffold_fallback_passes_strict_verification_without_high_hallucinations() -> None:
    cli = AgentCLI()
    cli._llm = _FailingLLM()

    intent = {
        "description": "example system",
        "domain": "general",
        "constraints": ["must be robust"],
        "modules": ["main"],
        "module_roles": {"main": "global section"},
        "orchestration": {"module_order": ["main"], "overlaps": [], "gluing_obligations": []},
    }

    artifact = cli._generate_module(intent, "main")
    result = VerificationLoop(
        VerificationConfig(emit_lean=True, strict_mode=True)
    ).verify(artifact["source"], "main")

    assert result.passed is True
    assert all(item["status"] == "proven" for item in result.structural_results)
    assert not [item for item in result.hallucination_findings if item["severity"] == "high"]


def test_agent_timeout_defaults_are_unbounded() -> None:
    verification = VerificationConfig()
    orchestrator = OrchestratorConfig()

    assert verification.z3_timeout_ms is None
    assert verification.lean_timeout_s is None
    assert orchestrator.z3_timeout_ms is None
    assert orchestrator.timeout_seconds is None


def test_full_mode_expands_cover_domain_agnostically() -> None:
    cli = AgentCLI()
    cli._config = CLIConfig(full=True, verbose=False)

    intent = {
        "description": "Build a large distributed control plane with typed orchestration.",
        "domain": "distributed systems",
        "modules": ["ingress", "scheduler", "storage", "main"],
        "constraints": ["Must preserve consistency across service boundaries."],
        "module_roles": {
            "ingress": "accept and normalize incoming requests",
            "scheduler": "coordinate background work",
            "storage": "persist and retrieve durable state",
            "main": "glue the local sites into a runnable system",
        },
        "orchestration": {
            "module_order": ["ingress", "scheduler", "storage", "main"],
            "overlaps": [
                {
                    "left": "ingress",
                    "right": "scheduler",
                    "obligation": "request normalization must agree with scheduling contracts",
                }
            ],
            "gluing_obligations": ["Global section condition: H¹ = 0"],
        },
    }

    enriched = cli._apply_full_mode("Build a large distributed control plane.", intent)

    assert enriched["full_mode"] is True
    assert enriched["target_loc"] == 50000
    assert len(enriched["modules"]) > len(intent["modules"])
    assert enriched["orchestration"]["module_budget"] >= len(enriched["modules"])
    assert enriched["orchestration"]["type_elaboration_tree"]["kind"] == "global_grothendieck_cover"
    assert all(not re.search(r"_part\d+$", module) for module in enriched["modules"])


def test_apply_ideation_emits_structured_novelty_packet_in_verbose_mode() -> None:
    cli = AgentCLI()
    cli._config = CLIConfig(prompt="build a verified trading system", ideation=True, verbose=True)
    cli._progress = _FakeProgress()

    intent = {
        "raw_prompt": "build a verified trading system",
        "project_name": "verified_trading",
        "description": "build a verified trading system",
        "domain": "trading",
        "modules": ["main"],
        "constraints": [],
        "dependencies": [],
    }

    enriched = cli._apply_ideation("build a verified trading system", intent)

    assert enriched["ideation"]["novel_idea_structured"]["proof_target"]
    assert "Scalar-valued typing" in enriched["ideation"]["novel_idea_structured"]["scalar_valued_typing"]
    assert enriched["ideation"]["math_ontology_summary"]["area_count"] == 500
    assert any(message == "Novel idea packet:" for message in cli._progress.messages)


def test_apply_ideation_uses_llm_guided_selection_and_reports_benefit() -> None:
    cli = AgentCLI()
    cli._llm = _GuidedSelectionLLM()
    cli._config = CLIConfig(prompt="build a verified trading system", ideation=True, verbose=False)
    cli._progress = _FakeProgress()

    intent = {
        "raw_prompt": "build a verified trading system",
        "project_name": "verified_trading",
        "description": "build a verified trading system",
        "domain": "trading",
        "modules": ["main"],
        "constraints": [],
        "dependencies": [],
    }

    enriched = cli._apply_ideation("build a verified trading system", intent)

    selection = enriched["ideation"]["selection_strategy"]
    benefit = enriched["ideation"]["benefit_evaluation"]
    scalar = enriched["ideation"]["scalar_valued_typing"]
    assert selection["mode"] == "llm_guided"
    assert "machine_learning" in selection["guided_domains"]
    assert "software_engineering" in selection["guided_domains"]
    assert "stochastic calculus" in selection["guided_math_areas"]
    assert "framework_certificate" in benefit
    assert scalar["label"] == "scalar-valued typing"
    assert "type elaboration" in scalar["definition"]
    assert 0.0 <= scalar["overall"] <= 1.0
    assert 0.0 <= scalar["llm_belief"] <= 1.0
    assert 0.0 <= scalar["math_model"] <= 1.0
    assert scalar["area_strengths"]


def test_type_expansion_receives_translated_ideation_lenses() -> None:
    cli = AgentCLI()
    cli._llm = _GuidedSelectionLLM()
    cli._config = CLIConfig(
        prompt="build a verified trading system",
        ideation=True,
        orchestration=True,
        full=True,
        verbose=False,
    )
    cli._progress = _FakeProgress()

    intent = {
        "raw_prompt": "build a verified trading system",
        "project_name": "verified_trading",
        "description": "build a verified trading system",
        "domain": "trading",
        "modules": ["market_data", "signal_geometry", "strategy_kernel", "risk_engine", "execution", "portfolio", "compliance", "main"],
        "constraints": [],
        "dependencies": [],
        "module_roles": {
            "market_data": "input site",
            "signal_geometry": "signal site",
            "strategy_kernel": "strategy site",
            "risk_engine": "risk site",
            "execution": "execution site",
            "portfolio": "portfolio site",
            "compliance": "compliance site",
            "main": "global section",
        },
        "orchestration": {
            "module_order": ["market_data", "signal_geometry", "strategy_kernel", "risk_engine", "execution", "portfolio", "compliance", "main"],
            "overlaps": [],
            "gluing_obligations": [],
        },
    }

    enriched = cli._apply_ideation("build a verified trading system", intent)
    enriched = cli._apply_full_mode("build a verified trading system", enriched)

    global_plan = enriched["full_expansion"]["global_plan"]
    assert enriched["ideation"]["selected_math_area_details"]
    assert any(module.get("ideation_lenses") for module in global_plan["modules"])
    math_lens = next(
        lens
        for lens in global_plan["elaboration_tree"]["children"][0]["children"][0]["ideation_lenses"]
        if lens.get("kind") == "math_area"
    )
    scalar_lens = next(
        lens
        for lens in global_plan["elaboration_tree"]["children"][0]["children"][0]["ideation_lenses"]
        if lens.get("kind") == "scalar_valued_typing"
    )
    assert math_lens["local_models"]
    assert math_lens["transport_maps"]
    assert math_lens["theorem_schemas"]
    assert math_lens["canonical_equations"]
    assert math_lens["certification_targets"]
    assert 0.0 <= math_lens["scalar_weight"] <= 1.0
    assert scalar_lens["label"] == "scalar-valued typing"
    assert scalar_lens["score_formula"]
    assert 0.0 <= scalar_lens["scalar_weight"] <= 1.0
    assert any(module.get("class_specs") for module in global_plan["modules"])
    assert any(module.get("function_specs") for module in global_plan["modules"])
    assert any(
        isinstance(module.get("ideation_benefit", {}).get("scalar_valued_typing", {}), dict)
        and module.get("ideation_benefit", {}).get("scalar_valued_typing", {}).get("overall") is not None
        for module in global_plan["modules"]
    )
    assert any(
        spec.get("theorem_schema") or spec.get("canonical_equation")
        for module in global_plan["modules"]
        for spec in module.get("function_specs", [])
    )
    assert any(
        any(token in module["name"] for token in ("stochastic_calculus", "bayesian_statistics", "financial_mathematics"))
        for module in global_plan["modules"]
    )
    assert not all(
        module["name"].endswith(("_chart", "_section", "_fiber", "_atlas", "_descent", "_sheaf"))
        for module in global_plan["modules"]
    )
    assert any(
        any(token in module["name"] for token in ("stochastic", "bayesian", "control", "rough"))
        for module in global_plan["modules"]
    )


def test_math_ontology_stores_500_areas_and_thousands_of_terms() -> None:
    summary = ontology_summary()
    assert len(all_math_areas()) == 500
    assert len(all_math_terms()) >= 1500
    assert summary["area_count"] == 500
    assert summary["term_count"] == len(all_math_terms())
    assert sum(1 for _ in ontology_path().open("r", encoding="utf-8")) >= 50000


def test_ideation_domains_use_registry_and_math_ontology() -> None:
    cli = AgentCLI()

    domains = cli._ideation_domains(
        {
            "domain": "trading",
            "description": "build a verified trading system that searches over all domains of math",
        },
        "build a verified trading system that searches over all domains of math",
    )

    assert "category_theory" in domains
    assert "formal_verification" in domains
    assert domains[0] != "type_theory"


def test_sanitize_python_source_rejects_assistant_status_updates() -> None:
    cleaned = AgentCLI._sanitize_python_source(
        "Fixed `src/deppy/compliance.py`.\n\n"
        "I changed the dataclasses and validated with `pytest -q`.\n"
    )

    assert cleaned.strip() == ""
