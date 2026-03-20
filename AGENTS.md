# AGENTS.md — Agent Configuration for OpenAI Codex / OpenClaw / Any Agent

## deppy: Hybrid Dependent Algebraic-Geometric Type System

### Agent Skills

This project provides an autonomous agent that generates **formally verified Python code** from natural language prompts. The agent uses:

1. **Hybrid Dependent Types** — every value has a type with structural (Z3-decidable) and semantic (LLM-oracle-judgeable) components
2. **Algebraic Geometry** — bugs are Čech cohomology classes, intent-implementation gaps are H¹ obstructions
3. **Controlled Oracle** — LLM outputs are wrapped in an oracle monad T_O with tracked trust levels
4. **Anti-Hallucination** — LLM outputs are type-checked; hallucination = type inhabitation failure
5. **Lean Proofs** — structural properties compile to machine-checked Lean 4 theorems

### Available Commands

```bash
# Generate a verified project from NL prompt
python3 agent/cli.py "write me a financial trading app"

# Verify an existing Python file
python3 -m deppy.hybrid.pipeline.cli verify myfile.py

# Run anti-hallucination check on LLM output
python3 -m deppy.hybrid.pipeline.cli check myfile.py

# Translate Python to Lean
python3 -m deppy.hybrid.pipeline.cli translate myfile.py

# Run the test suite
PYTHONPATH=src python3 -m pytest tests/test_hybrid/ -v
```

### Agent Integration Points

When using this project as a tool in another agent system:

```python
# 1. Create the deppy agent
from agent.orchestrator import DeppyAgent, AgentConfig
agent = DeppyAgent(llm_fn=your_llm_function, config=AgentConfig())

# 2. Generate a verified project
result = agent.run("your natural language prompt here")

# 3. Access the verified code
for module_name, module in result.project.modules.items():
    print(f"{module_name}: trust={module.trust_level}")
    print(module.source)

# 4. Access the verification report
print(result.trust_report.to_markdown())

# 5. Access Lean proofs
for name, lean_src in result.project.lean_proofs.items():
    print(f"--- {name}.lean ---")
    print(lean_src)
```

### Surface Syntax (use in all generated code)

```python
from deppy.hybrid import guarantee, spec, hole, assume, check, given

@guarantee("returns a sorted list with no duplicates")
def unique_sorted(lst: list[int]) -> list[int]:
    deduped = hole("remove duplicates from lst")
    return sorted(deduped)
```

### Trust Levels (ordered)
- `LEAN_VERIFIED` — machine-checked proof (highest)
- `Z3_PROVEN` — SMT solver proof
- `RUNTIME_CHECKED` — passed dynamic tests
- `LLM_JUDGED` — oracle says correct
- `ASSUMED` — assumed without evidence
- `UNTRUSTED` — no verification
- `CONTRADICTED` — evidence of falsehood (lowest)
