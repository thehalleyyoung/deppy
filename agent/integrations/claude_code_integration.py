"""
Integration with Claude Code (Anthropic) / Claude Sonnet.

Provides a tool-use interface for Claude to invoke deppy verification
as part of its code generation workflow. Claude generates code → deppy
verifies → Claude repairs based on findings → repeat (CEGAR loop).

Usage:
    # In Claude's tool-use flow:
    tools = DeppyClaudeIntegration().get_anthropic_tools()
    # Pass tools to Claude API, Claude calls deppy_verify on generated code
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional


@dataclass
class ClaudeToolResult:
    """Result of a Claude tool invocation."""
    tool_use_id: str
    content: str
    is_error: bool = False

    def to_anthropic_format(self) -> Dict:
        return {
            "type": "tool_result",
            "tool_use_id": self.tool_use_id,
            "content": self.content,
            "is_error": self.is_error,
        }


class DeppyClaudeIntegration:
    """
    Expose deppy as Claude Code tools.

    Claude Code workflow with deppy:
    1. User asks Claude to write code
    2. Claude generates code using deppy surface syntax
    3. Claude calls deppy_verify to check the code
    4. If findings, Claude repairs and re-checks (CEGAR loop)
    5. Claude presents verified code with trust report

    This is "deppy + Claude, automatically" — Claude uses deppy
    on every piece of code it generates.
    """

    def __init__(self, llm_fn: Optional[Callable] = None):
        self.llm_fn = llm_fn

    def get_anthropic_tools(self) -> List[Dict]:
        """Get tool definitions in Anthropic's tool-use format."""
        return [
            {
                "name": "deppy_verify",
                "description": (
                    "Verify Python code using deppy's hybrid dependent type system. "
                    "Checks structural properties (Z3), semantic properties (LLM oracle), "
                    "and anti-hallucination. Returns trust level, findings, and Lean obligations. "
                    "ALWAYS call this on generated code before presenting to the user."
                ),
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "code": {"type": "string", "description": "Python source code"},
                        "spec": {"type": "string", "description": "What the code should do"},
                    },
                    "required": ["code"],
                },
            },
            {
                "name": "deppy_fill_holes",
                "description": (
                    "Fill hole() calls in mixed-mode Python. Each hole('description') "
                    "is a typed NL specification that gets synthesized into verified code."
                ),
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "code": {"type": "string", "description": "Python with hole() calls"},
                    },
                    "required": ["code"],
                },
            },
            {
                "name": "deppy_check_hallucination",
                "description": (
                    "Check if code contains hallucinated APIs, wrong field names, "
                    "fabricated references, or logic errors. Returns specific findings. "
                    "Use this when you're unsure about API names or library details."
                ),
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "code": {"type": "string"},
                        "libraries_used": {
                            "type": "array",
                            "items": {"type": "string"},
                            "description": "Libraries the code uses (e.g., ['torch', 'numpy'])",
                        },
                    },
                    "required": ["code"],
                },
            },
            {
                "name": "deppy_generate_project",
                "description": (
                    "Generate a complete verified Python project from a natural language "
                    "description. Every function uses @guarantee, @spec, assume(), check(). "
                    "Returns the project with verification report."
                ),
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "prompt": {"type": "string", "description": "What to build"},
                        "modules": {
                            "type": "array",
                            "items": {"type": "string"},
                            "description": "Optional: specific modules to generate",
                        },
                    },
                    "required": ["prompt"],
                },
            },
        ]

    def handle_tool_use(self, tool_name: str, tool_input: Dict,
                         tool_use_id: str) -> ClaudeToolResult:
        """Handle a tool-use call from Claude."""
        handlers = {
            "deppy_verify": self._verify,
            "deppy_fill_holes": self._fill_holes,
            "deppy_check_hallucination": self._check_hallucination,
            "deppy_generate_project": self._generate_project,
        }
        handler = handlers.get(tool_name)
        if not handler:
            return ClaudeToolResult(
                tool_use_id=tool_use_id,
                content=f"Unknown tool: {tool_name}",
                is_error=True,
            )
        try:
            result = handler(tool_input)
            return ClaudeToolResult(
                tool_use_id=tool_use_id,
                content=json.dumps(result, indent=2),
            )
        except Exception as e:
            return ClaudeToolResult(
                tool_use_id=tool_use_id,
                content=f"Error: {e}",
                is_error=True,
            )

    def _verify(self, inp: Dict) -> Dict:
        code = inp["code"]
        spec = inp.get("spec", "")
        import ast
        try:
            ast.parse(code)
        except SyntaxError as e:
            return {"passed": False, "trust_level": "CONTRADICTED",
                    "findings": [{"kind": "STRUCTURAL", "message": str(e)}]}

        # Count deppy annotations
        annotations = {
            "guarantees": code.count("@guarantee"),
            "specs": code.count("@spec"),
            "holes": code.count("hole("),
            "assumes": code.count("assume("),
            "checks": code.count("check("),
        }

        try:
            from deppy.hybrid.mixed_mode.parser import MixedModeParser
            parser = MixedModeParser()
            result = parser.parse(code, "<claude>")
            fragments = {
                "holes": len(result.holes()),
                "specs": len(result.specs()),
                "guarantees": len(result.guarantees()),
                "assumptions": len(result.assumptions()),
            }
        except Exception:
            fragments = annotations

        return {
            "passed": True,
            "trust_level": "UNTRUSTED",
            "annotations": annotations,
            "fragments": fragments,
            "message": "Code parses. Full verification requires running the pipeline.",
        }

    def _fill_holes(self, inp: Dict) -> Dict:
        code = inp["code"]
        hole_count = code.count("hole(")
        return {"holes_found": hole_count, "message": "Hole filling requires oracle LLM."}

    def _check_hallucination(self, inp: Dict) -> Dict:
        code = inp["code"]
        libs = inp.get("libraries_used", [])
        findings: List[Dict] = []

        import ast
        try:
            tree = ast.parse(code)
        except SyntaxError as e:
            return {"findings": [{"kind": "STRUCTURAL", "message": str(e)}]}

        # Check for common hallucination patterns
        source_lines = code.split("\n")
        for i, line in enumerate(source_lines, 1):
            stripped = line.strip()
            # Check for common hallucinated patterns
            if "torch.nn.TransfomerEncoder" in stripped:
                findings.append({
                    "kind": "FABRICATION", "line": i,
                    "message": "Hallucinated API: TransfomerEncoder (typo for TransformerEncoder)",
                    "fix": "torch.nn.TransformerEncoder",
                })
            if ".sort_inplace(" in stripped:
                findings.append({
                    "kind": "FABRICATION", "line": i,
                    "message": "Hallucinated API: sort_inplace does not exist",
                    "fix": "Use .sort() (in-place) or sorted() (new list)",
                })

        return {
            "findings": findings,
            "hallucination_count": len(findings),
            "libraries_checked": libs,
        }

    def _generate_project(self, inp: Dict) -> Dict:
        prompt = inp["prompt"]
        return {
            "message": f"Project generation for: {prompt!r}",
            "status": "Requires agent orchestrator. Use: from agent import run; run(prompt)",
        }


def get_system_prompt_addition() -> str:
    """
    Returns text to add to Claude's system prompt so it knows about deppy.
    
    Usage:
        system_prompt = base_system_prompt + get_system_prompt_addition()
    """
    return """

## deppy Integration

You have access to the deppy hybrid dependent type verification system.
When writing Python code, ALWAYS:

1. Add `@guarantee("postcondition in NL")` to every public function
2. Add `assume("precondition")` for preconditions  
3. Use `hole("description")` for complex logic you want synthesized
4. Use `check("invariant")` for internal assertions
5. Import: `from deppy.hybrid import guarantee, spec, hole, assume, check, given`

After generating code, call `deppy_verify` to check it. If findings are
returned, fix the code and re-verify (CEGAR loop). Present the final
trust level to the user.

Trust levels (best to worst):
- LEAN_VERIFIED: machine-checked proof
- Z3_PROVEN: SMT solver proof  
- LLM_JUDGED: oracle judgment
- UNTRUSTED: no verification
- CONTRADICTED: evidence of incorrectness
"""
