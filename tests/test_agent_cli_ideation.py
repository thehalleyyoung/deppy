from __future__ import annotations

import re

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

    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        del prompt, max_tokens, temperature
        self.calls += 1
        return '"""shallow"""\n\ndef helper() -> int:\n    return 1\n'

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


def test_generate_module_limits_full_mode_refinements_for_copilot_backend() -> None:
    cli = AgentCLI()
    llm = _ShallowCopilotLLM()
    cli._llm = llm

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


def test_copilot_backend_uses_single_cegar_round_budget() -> None:
    cli = AgentCLI()
    cli._config = CLIConfig(prompt="example", full=True, max_iterations=5)
    cli._llm = _ShallowCopilotLLM()

    assert cli._cegar_round_budget() == 1


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
