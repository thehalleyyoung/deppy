"""
deppy agent: Autonomous verified software generation.

Usage:
    from agent import DeppyAgent, AgentConfig
    
    agent = DeppyAgent(llm_fn=my_llm, config=AgentConfig())
    result = agent.run("write me a financial trading app")
    result.project.write("./output")

Or from CLI:
    deppy "write me a financial trading app"
"""

from __future__ import annotations

# Re-export public API
# (Use lazy imports to avoid circular deps)

def create_agent(llm_fn=None, **kwargs):
    """Create a DeppyAgent with sensible defaults."""
    from agent.orchestrator import DeppyAgent, AgentConfig
    config = AgentConfig(**kwargs)
    return DeppyAgent(llm_fn=llm_fn, config=config)

def run(prompt: str, llm_fn=None, **kwargs):
    """One-shot: run the agent on a prompt."""
    agent = create_agent(llm_fn=llm_fn, **kwargs)
    return agent.run(prompt)

__all__ = ["create_agent", "run"]
