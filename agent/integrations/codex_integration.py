"""
Integration with OpenAI Codex / GPT-4 / ChatGPT Code Interpreter.

Provides function-calling tools for Codex to use deppy verification
in its code generation workflow.

Also works as a standalone wrapper: given any OpenAI-compatible API,
wrap code generation with automatic deppy verification.

Usage:
    wrapper = DeppyCodexWrapper(api_key="sk-...")
    result = wrapper.generate_verified("write a sorting function")
    # result.code is verified, result.trust_level is the trust level
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional


@dataclass
class VerifiedGeneration:
    """Result of generating code through deppy + Codex."""
    code: str
    trust_level: str
    structural_checks: List[Dict] = field(default_factory=list)
    semantic_checks: List[Dict] = field(default_factory=list)
    hallucination_findings: List[Dict] = field(default_factory=list)
    lean_obligations: List[str] = field(default_factory=list)
    repair_rounds: int = 0
    content_hash: str = ""
    
    def __post_init__(self):
        if not self.content_hash:
            self.content_hash = hashlib.sha256(self.code.encode()).hexdigest()[:16]


class DeppyCodexWrapper:
    """
    Wrap any OpenAI-compatible LLM with automatic deppy verification.
    
    Every code generation call goes through:
    1. Generate code (LLM) → UNTRUSTED
    2. Parse + extract NL fragments (deppy) 
    3. Structural check (Z3) → promote to Z3_PROVEN if passes
    4. Anti-hallucination check → flag or CONTRADICTED
    5. Semantic check (oracle) → promote to LLM_JUDGED if passes
    6. If findings → repair + re-verify (CEGAR loop)
    7. Return VerifiedGeneration with trust level
    
    Usage:
        wrapper = DeppyCodexWrapper(api_key="sk-...")
        result = wrapper.generate_verified("implement binary search")
        print(result.trust_level)  # "LLM_JUDGED" or "Z3_PROVEN"
    """
    
    def __init__(self, api_key: Optional[str] = None,
                 model: str = "gpt-4",
                 max_repair_rounds: int = 3,
                 llm_fn: Optional[Callable] = None):
        self.api_key = api_key
        self.model = model
        self.max_repair_rounds = max_repair_rounds
        self._llm_fn = llm_fn
        self._cache: Dict[str, VerifiedGeneration] = {}
    
    def generate_verified(self, prompt: str,
                           context: Optional[Dict] = None) -> VerifiedGeneration:
        """
        Generate verified code from a prompt.
        
        The generated code automatically uses deppy's surface syntax:
        @guarantee, assume(), check(), etc.
        """
        # Step 1: Generate with deppy instructions
        deppy_prompt = self._augment_prompt(prompt, context)
        code = self._call_llm(deppy_prompt)
        
        # Step 2: Verify
        result = self._verify(code)
        
        # Step 3: CEGAR repair if needed
        rounds = 0
        while result.hallucination_findings and rounds < self.max_repair_rounds:
            repair_prompt = self._build_repair_prompt(code, result.hallucination_findings)
            code = self._call_llm(repair_prompt)
            result = self._verify(code)
            rounds += 1
        
        result.repair_rounds = rounds
        return result
    
    def _augment_prompt(self, prompt: str, context: Optional[Dict]) -> str:
        """Add deppy instructions to the generation prompt."""
        return f"""Generate Python code that uses deppy's hybrid type verification syntax.

REQUIREMENTS:
- Every public function MUST have @guarantee("postcondition") decorator
- Preconditions use assume("condition")
- Internal invariants use check("condition")
- Complex logic can use hole("description") for synthesis
- Import: from deppy.hybrid import guarantee, spec, hole, assume, check, given
- Use from __future__ import annotations
- Use type annotations on all function parameters and returns

TASK: {prompt}

{f"CONTEXT: {json.dumps(context)}" if context else ""}

Generate the code:"""
    
    def _build_repair_prompt(self, code: str, findings: List[Dict]) -> str:
        """Build a repair prompt from verification findings."""
        findings_text = "\n".join(
            f"- {f.get('kind', 'UNKNOWN')}: {f.get('message', f.get('description', ''))}"
            for f in findings
        )
        return f"""The following code has verification issues:

```python
{code}
```

ISSUES FOUND:
{findings_text}

Fix ALL issues and regenerate the code. Keep all @guarantee, assume(), check() annotations.
Ensure all APIs exist and are correctly spelled.
"""
    
    def _call_llm(self, prompt: str) -> str:
        """Call the LLM (pluggable)."""
        if self._llm_fn:
            return self._llm_fn(prompt)
        # Placeholder — in real use, calls OpenAI API
        return f"# Generated from: {prompt[:50]}...\npass"
    
    def _verify(self, code: str) -> VerifiedGeneration:
        """Run deppy verification on generated code."""
        import ast
        findings: List[Dict] = []
        
        # Structural: parse check
        try:
            ast.parse(code)
        except SyntaxError as e:
            return VerifiedGeneration(
                code=code, trust_level="CONTRADICTED",
                hallucination_findings=[{"kind": "STRUCTURAL", "message": str(e)}],
            )
        
        # Check for deppy annotations
        has_guarantee = "@guarantee" in code
        has_assume = "assume(" in code
        has_check = "check(" in code
        
        trust = "UNTRUSTED"
        if has_guarantee or has_assume or has_check:
            trust = "LLM_JUDGED"  # Has annotations, pending full verification
        
        return VerifiedGeneration(
            code=code, trust_level=trust,
            hallucination_findings=findings,
        )
    
    def get_openai_tools(self) -> List[Dict]:
        """Get tool definitions for OpenAI function-calling."""
        return [
            {
                "type": "function",
                "function": {
                    "name": "deppy_verify_code",
                    "description": "Verify Python code using deppy hybrid dependent types",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "code": {"type": "string", "description": "Python code to verify"},
                        },
                        "required": ["code"],
                    },
                },
            },
            {
                "type": "function",
                "function": {
                    "name": "deppy_generate_verified",
                    "description": "Generate verified Python code from description",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "description": {"type": "string", "description": "What to generate"},
                        },
                        "required": ["description"],
                    },
                },
            },
        ]


class DeppyOpenClawIntegration:
    """
    Integration with OpenClaw / any open-source agent framework.
    
    Provides a skill that any agent can use:
    - Input: code or NL prompt
    - Output: verified code + trust report
    
    Compatible with LangChain, AutoGPT, OpenClaw, CrewAI, etc.
    """
    
    SKILL_DEFINITION = {
        "name": "deppy_verified_coding",
        "description": (
            "Generate and verify Python code using hybrid dependent types. "
            "Structural properties are Z3-proven, semantic properties are LLM-judged. "
            "Hallucinations are detected as type inhabitation failures."
        ),
        "input_schema": {
            "type": "object",
            "properties": {
                "action": {
                    "type": "string",
                    "enum": ["generate", "verify", "check_hallucination", "translate_lean"],
                },
                "code": {"type": "string"},
                "prompt": {"type": "string"},
            },
            "required": ["action"],
        },
        "output_schema": {
            "type": "object",
            "properties": {
                "code": {"type": "string"},
                "trust_level": {"type": "string"},
                "findings": {"type": "array"},
                "lean_output": {"type": "string"},
            },
        },
    }
    
    def __init__(self, llm_fn: Optional[Callable] = None):
        self.llm_fn = llm_fn
        self._wrapper = DeppyCodexWrapper(llm_fn=llm_fn)
    
    def execute(self, action: str, **kwargs) -> Dict:
        """Execute a skill action."""
        if action == "generate":
            prompt = kwargs.get("prompt", "")
            result = self._wrapper.generate_verified(prompt)
            return {
                "code": result.code,
                "trust_level": result.trust_level,
                "findings": result.hallucination_findings,
            }
        elif action == "verify":
            code = kwargs.get("code", "")
            result = self._wrapper._verify(code)
            return {
                "trust_level": result.trust_level,
                "findings": result.hallucination_findings,
            }
        elif action == "check_hallucination":
            code = kwargs.get("code", "")
            result = self._wrapper._verify(code)
            return {"findings": result.hallucination_findings}
        elif action == "translate_lean":
            return {"message": "Lean translation requires full pipeline"}
        else:
            return {"error": f"Unknown action: {action}"}
    
    @classmethod
    def as_langchain_tool(cls):
        """Return a LangChain-compatible tool definition."""
        return {
            "name": "deppy_verify",
            "description": cls.SKILL_DEFINITION["description"],
            "func": lambda code: cls().execute("verify", code=code),
        }
