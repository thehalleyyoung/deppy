"""
CLI entry point for deppy.

Usage:
    deppy <prompt>                    — generate verified project from NL prompt
    deppy --interactive <prompt>      — interactive mode (ask clarifying questions)
    deppy --resume <manifest.json>    — resume from saved state
    deppy --verify <file.py>          — verify existing file
    deppy --check <directory>         — check existing project
    deppy --report <manifest.json>    — generate HTML report

Options:
    --model <model>       LLM model (default: gpt-4)
    --output <dir>        Output directory (default: ./output)
    --lean                Enable Lean proof generation
    --strict              Require all obligations discharged
    --verbose             Show detailed progress
    --cache-dir <dir>     Cache directory (default: .deppy_cache)
    --max-iterations <n>  Max generation/repair iterations
"""
from __future__ import annotations

import argparse
import ast
import json
import os
import re
import shutil
import sys
import time
import logging
import subprocess
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple, IO

logger = logging.getLogger(__name__)

# ┌──────────────────────────────────────────────────────────────────────────┐
# │ LLM Interfaces                                                           │
# └──────────────────────────────────────────────────────────────────────────┘


class LLMInterface(ABC):
    """
    Abstract LLM interface that works with multiple providers.

    Subclass this to add new LLM backends.
    """

    def __init__(self, model: str, api_key: str) -> None:
        self.model = model
        self.api_key = api_key
        self._call_count = 0
        self._total_tokens = 0

    @abstractmethod
    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        """Generate a text completion."""
        ...

    @abstractmethod
    def complete_json(
        self,
        prompt: str,
        schema: Dict[str, Any],
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ) -> Dict[str, Any]:
        """Generate a JSON completion conforming to *schema*."""
        ...

    @property
    def call_count(self) -> int:
        return self._call_count

    @property
    def total_tokens(self) -> int:
        return self._total_tokens


class OpenAIInterface(LLMInterface):
    """OpenAI API backend (GPT-4, GPT-3.5, etc.)."""

    def __init__(self, model: str = "gpt-4", api_key: str = "") -> None:
        super().__init__(model, api_key)
        self._api_base = "https://api.openai.com/v1"

    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        """
        Call the OpenAI chat completions API.

        Requires the ``openai`` package at runtime.
        """
        self._call_count += 1
        try:
            import openai  # type: ignore[import-untyped]
            client = openai.OpenAI(api_key=self.api_key)
            response = client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=max_tokens,
                temperature=temperature,
            )
            usage = response.usage
            if usage:
                self._total_tokens += usage.total_tokens
            return response.choices[0].message.content or ""
        except ImportError:
            raise RuntimeError(
                "OpenAI package not installed. "
                "Run: pip install openai"
            )
        except Exception as exc:
            logger.error("OpenAI API error: %s", exc)
            raise

    def complete_json(
        self,
        prompt: str,
        schema: Dict[str, Any],
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ) -> Dict[str, Any]:
        """Call OpenAI with JSON mode and parse the result."""
        self._call_count += 1
        try:
            import openai  # type: ignore[import-untyped]
            client = openai.OpenAI(api_key=self.api_key)

            system_msg = (
                "You are a helpful assistant that responds in JSON. "
                f"Follow this schema: {json.dumps(schema)}"
            )
            response = client.chat.completions.create(
                model=self.model,
                messages=[
                    {"role": "system", "content": system_msg},
                    {"role": "user", "content": prompt},
                ],
                max_tokens=max_tokens,
                temperature=temperature,
                response_format={"type": "json_object"},
            )
            usage = response.usage
            if usage:
                self._total_tokens += usage.total_tokens
            text = response.choices[0].message.content or "{}"
            return json.loads(text)
        except ImportError:
            raise RuntimeError(
                "OpenAI package not installed. "
                "Run: pip install openai"
            )
        except json.JSONDecodeError as exc:
            logger.error("Failed to parse JSON from OpenAI: %s", exc)
            return {}


class AnthropicInterface(LLMInterface):
    """Anthropic API backend (Claude 3, Claude 2, etc.)."""

    def __init__(self, model: str = "claude-3-opus-20240229",
                 api_key: str = "") -> None:
        super().__init__(model, api_key)

    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        """Call the Anthropic messages API."""
        self._call_count += 1
        try:
            import anthropic  # type: ignore[import-untyped]
            client = anthropic.Anthropic(api_key=self.api_key)
            response = client.messages.create(
                model=self.model,
                max_tokens=max_tokens,
                temperature=temperature,
                messages=[{"role": "user", "content": prompt}],
            )
            usage = response.usage
            if usage:
                self._total_tokens += (
                    usage.input_tokens + usage.output_tokens
                )
            return response.content[0].text if response.content else ""
        except ImportError:
            raise RuntimeError(
                "Anthropic package not installed. "
                "Run: pip install anthropic"
            )
        except Exception as exc:
            logger.error("Anthropic API error: %s", exc)
            raise

    def complete_json(
        self,
        prompt: str,
        schema: Dict[str, Any],
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ) -> Dict[str, Any]:
        """Call Anthropic with JSON output instructions."""
        json_prompt = (
            f"{prompt}\n\n"
            f"Respond with valid JSON matching this schema:\n"
            f"{json.dumps(schema, indent=2)}\n\n"
            f"Output only the JSON object, nothing else."
        )
        text = self.complete(json_prompt, max_tokens, temperature)
        # Strip any markdown fences
        text = text.strip()
        if text.startswith("```"):
            lines = text.splitlines()
            # Remove first and last lines (fences)
            lines = [l for l in lines if not l.strip().startswith("```")]
            text = "\n".join(lines)
        try:
            return json.loads(text)
        except json.JSONDecodeError as exc:
            logger.error("Failed to parse JSON from Anthropic: %s", exc)
            return {}


class CopilotCLIInterface(LLMInterface):
    """GitHub Copilot CLI backend for non-interactive prompt completion."""

    def __init__(
        self,
        model: Optional[str] = None,
        executable: str = "copilot",
        timeout_seconds: int = 180,
    ) -> None:
        super().__init__(model or "copilot", api_key="")
        self._executable = executable
        self._timeout_seconds = timeout_seconds

    def _build_command(self, prompt: str) -> List[str]:
        command = [
            self._executable,
            "-p",
            prompt,
            "--output-format",
            "json",
            "--allow-all-tools",
            "--no-ask-user",
            "--stream",
            "off",
            "--no-custom-instructions",
            "--disable-builtin-mcps",
            "--available-tools=",
        ]
        if self.model and self.model not in {"gpt-4", "mock", "copilot"}:
            command.extend(["--model", self.model])
        return command

    def _run_prompt(self, prompt: str) -> str:
        command = self._build_command(prompt)
        try:
            completed = subprocess.run(
                command,
                check=True,
                capture_output=True,
                text=True,
                timeout=self._timeout_seconds,
            )
        except FileNotFoundError as exc:
            raise RuntimeError(
                "Copilot CLI executable not found. Install it with "
                "`brew install copilot-cli` or `npm install -g @github/copilot`."
            ) from exc
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(
                f"Copilot CLI prompt timed out after {self._timeout_seconds}s"
            ) from exc
        except subprocess.CalledProcessError as exc:
            stderr = (exc.stderr or "").strip()
            stdout = (exc.stdout or "").strip()
            details = stderr or stdout or str(exc)
            raise RuntimeError(
                f"Copilot CLI prompt failed with exit code {exc.returncode}: {details}"
            ) from exc
        raw_output = completed.stdout.strip()
        if not raw_output:
            return ""

        messages: List[str] = []
        for line in raw_output.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            if event.get("type") != "assistant.message":
                continue
            data = event.get("data", {})
            content = data.get("content")
            if isinstance(content, str):
                messages.append(content)
        if messages:
            return messages[-1].strip()
        return raw_output

    @staticmethod
    def _strip_markdown_fences(text: str) -> str:
        cleaned = text.strip()
        if cleaned.startswith("```"):
            lines = [
                line for line in cleaned.splitlines()
                if not line.strip().startswith("```")
            ]
            return "\n".join(lines).strip()
        return cleaned

    @staticmethod
    def _extract_json_payload(text: str) -> str:
        cleaned = CopilotCLIInterface._strip_markdown_fences(text)
        if not cleaned:
            return cleaned
        start = cleaned.find("{")
        end = cleaned.rfind("}")
        if start != -1 and end != -1 and end > start:
            return cleaned[start : end + 1]
        return cleaned

    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        del max_tokens, temperature
        self._call_count += 1
        response = self._run_prompt(prompt)
        self._total_tokens += len(prompt.split()) + len(response.split())
        return response

    def complete_json(
        self,
        prompt: str,
        schema: Dict[str, Any],
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ) -> Dict[str, Any]:
        del max_tokens, temperature
        json_prompt = (
            f"{prompt}\n\n"
            "Respond with valid JSON only. Do not use markdown fences.\n"
            f"Match this schema exactly:\n{json.dumps(schema, indent=2)}"
        )
        text = self._extract_json_payload(self.complete(json_prompt))
        try:
            return json.loads(text)
        except json.JSONDecodeError as exc:
            logger.error("Failed to parse JSON from Copilot CLI: %s", exc)
            return {}


class MockInterface(LLMInterface):
    """Mock LLM interface for testing — returns pre-programmed responses."""

    def __init__(
        self,
        model: str = "mock",
        api_key: str = "",
        responses: Optional[List[str]] = None,
        json_responses: Optional[List[Dict[str, Any]]] = None,
    ) -> None:
        super().__init__(model, api_key)
        self._responses = list(responses or [])
        self._json_responses = list(json_responses or [])
        self._response_index = 0
        self._json_response_index = 0

    def complete(
        self,
        prompt: str,
        max_tokens: int = 4096,
        temperature: float = 0.2,
    ) -> str:
        self._call_count += 1
        self._total_tokens += len(prompt.split()) + 100
        if self._responses:
            idx = self._response_index % len(self._responses)
            self._response_index += 1
            return self._responses[idx]
        return f"# Mock response for: {prompt[:80]}\npass\n"

    def complete_json(
        self,
        prompt: str,
        schema: Dict[str, Any],
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ) -> Dict[str, Any]:
        self._call_count += 1
        self._total_tokens += len(prompt.split()) + 50
        if self._json_responses:
            idx = self._json_response_index % len(self._json_responses)
            self._json_response_index += 1
            return self._json_responses[idx]
        return {"status": "mock", "prompt_preview": prompt[:80]}

    def add_response(self, response: str) -> None:
        """Enqueue a text response."""
        self._responses.append(response)

    def add_json_response(self, response: Dict[str, Any]) -> None:
        """Enqueue a JSON response."""
        self._json_responses.append(response)


def detect_llm_interface(
    model: Optional[str] = None,
) -> LLMInterface:
    """
    Auto-detect LLM interface from environment variables.

    Priority:
    1. OPENAI_API_KEY  → OpenAIInterface
    2. ANTHROPIC_API_KEY → AnthropicInterface
    3. Local Copilot CLI → CopilotCLIInterface
    4. Fallback → MockInterface (with warning)
    """
    openai_key = os.environ.get("OPENAI_API_KEY", "")
    anthropic_key = os.environ.get("ANTHROPIC_API_KEY", "")

    if openai_key:
        return OpenAIInterface(
            model=model or "gpt-4",
            api_key=openai_key,
        )

    if anthropic_key:
        return AnthropicInterface(
            model=model or "claude-3-opus-20240229",
            api_key=anthropic_key,
        )

    copilot_path = shutil.which("copilot")
    if copilot_path:
        logger.info(
            "No OpenAI or Anthropic API key found. Falling back to Copilot CLI."
        )
        return CopilotCLIInterface(
            model=model,
            executable=copilot_path,
        )

    logger.warning(
        "No LLM API key found in environment. "
        "Set OPENAI_API_KEY or ANTHROPIC_API_KEY, or install Copilot CLI. "
        "Falling back to MockInterface."
    )
    return MockInterface(model=model or "mock")


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ ProgressDisplay                                                          │
# └──────────────────────────────────────────────────────────────────────────┘


@dataclass
class ModuleProgress:
    """Progress state for a single module."""
    name: str
    index: int
    total: int
    status: str = "pending"
    pattern: str = ""
    structural: str = ""
    semantic: str = ""
    hallucination: str = ""
    lean: str = ""
    trust: str = ""
    cegar_round: int = 0
    error: str = ""


class ProgressDisplay:
    """
    Real-time progress display in the terminal.

    Renders a continuously-updated view of the deppy pipeline progress,
    including per-module verification status.
    """

    def __init__(
        self,
        output: IO[str] = sys.stderr,
        verbose: bool = False,
        use_color: bool = True,
    ) -> None:
        self._output = output
        self._verbose = verbose
        self._use_color = use_color and hasattr(output, "isatty") and output.isatty()
        self._start_time = time.monotonic()
        self._module_progress: Dict[str, ModuleProgress] = {}

    def intent_start(self, prompt: str) -> None:
        """Show intent resolution start."""
        self._emit(
            f"\U0001f9e0 Intent Oracle: Resolving \"{self._truncate(prompt, 60)}\"..."
        )

    def intent_resolved(
        self,
        domain: str,
        modules: List[str],
        constraints: List[str],
    ) -> None:
        """Show resolved intent details."""
        self._emit(f"   Domain: {domain}")
        self._emit(f"   Modules: {len(modules)} identified")
        if self._verbose:
            for m in modules:
                self._emit(f"     - {m}")
        self._emit(f"   Constraints: {len(constraints)} extracted")
        self._emit("")

    def module_start(
        self,
        name: str,
        index: int,
        total: int,
        pattern: str = "",
    ) -> None:
        """Show module generation start."""
        progress = ModuleProgress(
            name=name, index=index, total=total,
            status="generating", pattern=pattern,
        )
        self._module_progress[name] = progress

        msg = f"\U0001f4e6 Module {index}/{total}: {name}"
        self._emit(msg)

        gen_msg = "   \U0001f528 Generating..."
        if pattern:
            gen_msg += f" (pattern: {pattern})"
        else:
            gen_msg += " (LLM synthesis)"
        self._emit(gen_msg)

    def structural_done(
        self,
        name: str,
        proven: int,
        total: int,
        failed_claims: Optional[List[str]] = None,
    ) -> None:
        """Show structural verification result."""
        progress = self._module_progress.get(name)
        if progress:
            progress.structural = f"{proven}/{total}"

        if proven == total:
            self._emit(f"   \u2705 Structural: {proven}/{total} Z3_PROVEN")
        else:
            self._emit(
                f"   \u26a0\ufe0f  Structural: {proven}/{total} "
                f"({total - proven} FAILED)"
            )
            if self._verbose and failed_claims:
                for claim in failed_claims[:3]:
                    self._emit(f"      - {claim}")

    def semantic_done(
        self,
        name: str,
        passed: int,
        total: int,
        min_confidence: float = 0.0,
    ) -> None:
        """Show semantic verification result."""
        progress = self._module_progress.get(name)
        if progress:
            progress.semantic = f"{passed}/{total}"

        if passed == total:
            self._emit(
                f"   \u2705 Semantic: {passed}/{total} LLM_JUDGED "
                f"(conf \u2265 {min_confidence:.2f})"
            )
        else:
            self._emit(
                f"   \u26a0\ufe0f  Semantic: {passed}/{total} "
                f"({total - passed} below threshold)"
            )

    def hallucination_done(
        self,
        name: str,
        findings: int,
        high_severity: int = 0,
    ) -> None:
        """Show anti-hallucination check result."""
        progress = self._module_progress.get(name)
        if progress:
            progress.hallucination = str(findings)

        if findings == 0:
            self._emit(f"   \u2705 Anti-hallucination: 0 findings")
        else:
            severity_note = ""
            if high_severity > 0:
                severity_note = f", {high_severity} HIGH"
            self._emit(
                f"   \u26a0\ufe0f  Anti-hallucination: {findings} findings"
                f"{severity_note}"
            )

    def lean_done(
        self,
        name: str,
        obligations: int,
        discharged: int,
        residual: int,
    ) -> None:
        """Show Lean proof status."""
        progress = self._module_progress.get(name)
        if progress:
            progress.lean = f"{discharged}/{obligations}"

        self._emit(
            f"   \U0001f4d0 Lean: {obligations} obligations, "
            f"{discharged} discharged, {residual} sorry"
        )

    def cegar_start(self, name: str, round_no: int) -> None:
        """Show CEGAR repair round start."""
        progress = self._module_progress.get(name)
        if progress:
            progress.cegar_round = round_no
            progress.status = "repairing"

        self._emit(f"   \U0001f527 CEGAR repair round {round_no}...")

    def verification_start(self, name: str) -> None:
        """Show verification start for a generated module."""
        progress = self._module_progress.get(name)
        if progress:
            progress.status = "verifying"
        self._emit("   \U0001f50d Verifying generated module...")

    def cegar_done(self, name: str, round_no: int, success: bool) -> None:
        """Show CEGAR repair round result."""
        if success:
            self._emit(f"   \u2705 Repaired in round {round_no}")
        else:
            self._emit(f"   \u274c Repair round {round_no} did not converge")

    def module_done(self, name: str, trust: str) -> None:
        """Show module completion with trust level."""
        progress = self._module_progress.get(name)
        if progress:
            progress.trust = trust
            progress.status = "done"

        emoji = {
            "LEAN_VERIFIED": "\U0001f7e2",
            "Z3_PROVEN": "\U0001f7e1",
            "LLM_JUDGED": "\U0001f7e0",
            "UNCHECKED": "\U0001f534",
        }.get(trust, "\u2753")

        self._emit(f"   \U0001f512 Trust: {trust} {emoji}")
        self._emit("")

    def cross_module_done(
        self,
        verified: int,
        failed: int,
        h1: str,
    ) -> None:
        """Show cross-module verification result."""
        self._emit(f"\U0001f310 Cross-module: {verified} contracts verified")
        if failed > 0:
            self._emit(f"   \u26a0\ufe0f {failed} contracts unmatched")
        self._emit(f"   {h1}")
        self._emit("")

    def project_done(
        self,
        output_dir: str,
        overall_trust: str,
        stats: Dict[str, Any],
    ) -> None:
        """Show final project summary."""
        self._emit(f"\U0001f3c1 Project assembled: {output_dir}/")

        # Trust badge
        badge = {
            "LEAN_VERIFIED": "\U0001f7e2 LEAN_VERIFIED",
            "Z3_PROVEN": "\U0001f7e1 Z3_PROVEN",
            "LLM_JUDGED": "\U0001f7e0 LLM_JUDGED",
            "UNCHECKED": "\U0001f534 UNCHECKED",
        }.get(overall_trust, overall_trust)
        self._emit(f"   Overall trust: {badge}")

        # Stats
        sp = stats.get("structural_proven", 0)
        st = stats.get("structural_total", 0)
        self._emit(f"   Structural: {sp}/{st} Z3_PROVEN")

        sep = stats.get("semantic_passed", 0)
        set_ = stats.get("semantic_total", 0)
        self._emit(f"   Semantic: {sep}/{set_} LLM_JUDGED")

        if stats.get("lean_total", 0) > 0:
            ld = stats.get("lean_discharged", 0)
            lr = stats.get("lean_residual", 0)
            self._emit(
                f"   Lean: {ld + lr} obligations, {ld} discharged, {lr} sorry"
            )

        hf = stats.get("hallucinations_found", 0)
        hx = stats.get("hallucinations_fixed", 0)
        self._emit(f"   Hallucinations: {hf} found, {hx} fixed (CEGAR)")

        oc = stats.get("oracle_calls", 0)
        och = stats.get("oracle_cache_hits", 0)
        if oc > 0:
            savings = (och / oc * 100) if oc > 0 else 0
            self._emit(
                f"   Oracle calls: {oc} ({och} cached, "
                f"saving {savings:.0f}% tokens)"
            )

        elapsed = time.monotonic() - self._start_time
        self._emit(f"   Duration: {elapsed:.1f}s")
        self._emit("")

    def error(self, message: str) -> None:
        """Show an error message."""
        self._emit(f"\u274c Error: {message}")

    def warning(self, message: str) -> None:
        """Show a warning message."""
        self._emit(f"\u26a0\ufe0f  Warning: {message}")

    def info(self, message: str) -> None:
        """Show an info message (verbose only)."""
        if self._verbose:
            self._emit(f"   \u2139\ufe0f  {message}")

    # ── Private ───────────────────────────────────────────────────────────

    def _emit(self, line: str) -> None:
        """Write a line to the output stream."""
        try:
            self._output.write(line + "\n")
            self._output.flush()
        except (IOError, BrokenPipeError):
            pass

    @staticmethod
    def _truncate(text: str, max_len: int) -> str:
        if len(text) <= max_len:
            return text
        return text[: max_len - 3] + "..."


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ AgentCLI                                                                 │
# └──────────────────────────────────────────────────────────────────────────┘


@dataclass
class CLIConfig:
    """Parsed CLI configuration."""
    prompt: str = ""
    mode: str = "generate"  # generate, interactive, resume, verify, check, report
    model: str = "gpt-4"
    output_dir: str = "./output"
    lean: bool = False
    strict: bool = False
    verbose: bool = False
    cache_dir: str = ".deppy_cache"
    max_iterations: int = 5
    target_file: str = ""
    target_dir: str = ""
    manifest_path: str = ""
    ideation: bool = False
    orchestration: bool = False
    full: bool = False


class AgentCLI:
    """
    Main CLI controller.

    Parses arguments, sets up the LLM interface, creates the agent,
    runs the pipeline, and displays results.
    """

    def __init__(self, args: Optional[List[str]] = None) -> None:
        self._raw_args = args if args is not None else sys.argv[1:]
        self._config: Optional[CLIConfig] = None
        self._llm: Optional[LLMInterface] = None
        self._progress: Optional[ProgressDisplay] = None

    def parse_args(self) -> CLIConfig:
        """Parse command-line arguments into a CLIConfig."""
        parser = argparse.ArgumentParser(
            prog="deppy",
            description="Generate verified Python projects from natural language.",
            formatter_class=argparse.RawDescriptionHelpFormatter,
            epilog=textwrap.dedent("""\
                Examples:
                  deppy "write me a financial trading app"
                  deppy "build a verified trading system" --ideation --orchestration
                  deppy --full --ideation --orchestration "build a large verified system"
                  deppy --interactive "build a REST API"
                  deppy --verify my_module.py
                  deppy --check ./my_project
                  deppy --report deppy_manifest.json
                  deppy --lean --strict "write a math library"
            """),
        )

        # Positional
        parser.add_argument(
            "prompt",
            nargs="?",
            default="",
            help="Natural language prompt describing the project to generate.",
        )

        # Mode flags
        mode_group = parser.add_mutually_exclusive_group()
        mode_group.add_argument(
            "--interactive",
            action="store_true",
            help="Interactive mode: ask clarifying questions before generating.",
        )
        mode_group.add_argument(
            "--resume",
            metavar="MANIFEST",
            help="Resume generation from a saved manifest.",
        )
        mode_group.add_argument(
            "--verify",
            metavar="FILE",
            help="Verify an existing Python file.",
        )
        mode_group.add_argument(
            "--check",
            metavar="DIR",
            help="Check an existing project directory.",
        )
        mode_group.add_argument(
            "--report",
            metavar="MANIFEST",
            help="Generate an HTML trust report from a manifest.",
        )

        # Options
        parser.add_argument(
            "--model", default="gpt-4",
            help="LLM model to use (default: gpt-4).",
        )
        parser.add_argument(
            "--output", default="./output",
            help="Output directory (default: ./output).",
        )
        parser.add_argument(
            "--lean", action="store_true",
            help="Enable Lean 4 proof generation.",
        )
        parser.add_argument(
            "--strict", action="store_true",
            help="Require all Lean obligations discharged.",
        )
        parser.add_argument(
            "--verbose", action="store_true",
            help="Show detailed progress output.",
        )
        parser.add_argument(
            "--cache-dir", default=".deppy_cache",
            help="Cache directory (default: .deppy_cache).",
        )
        parser.add_argument(
            "--max-iterations", type=int, default=5,
            help="Max CEGAR iterations (default: 5).",
        )
        parser.add_argument(
            "--ideation",
            action="store_true",
            help=(
                "Run ideation-as-typing/algebraic-geometry before generation "
                "to require a novel, type-checked design idea."
            ),
        )
        parser.add_argument(
            "--orchestration",
            action="store_true",
            help=(
                "Build a TT/AG orchestration cover with module overlaps, "
                "gluing obligations, and typed generation order."
            ),
        )
        parser.add_argument(
            "--full",
            action="store_true",
            help=(
                "Aim for a large-scale ~50 KLoC implementation by applying "
                "Pillar 10 type expansion before module generation."
            ),
        )

        parsed = parser.parse_args(self._raw_args)

        config = CLIConfig(
            model=parsed.model,
            output_dir=parsed.output,
            lean=parsed.lean,
            strict=parsed.strict,
            verbose=parsed.verbose,
            cache_dir=parsed.cache_dir,
            max_iterations=parsed.max_iterations,
            ideation=parsed.ideation,
            orchestration=parsed.orchestration,
            full=parsed.full,
        )

        # Determine mode
        if parsed.verify:
            config.mode = "verify"
            config.target_file = parsed.verify
        elif parsed.check:
            config.mode = "check"
            config.target_dir = parsed.check
        elif parsed.report:
            config.mode = "report"
            config.manifest_path = parsed.report
        elif parsed.resume:
            config.mode = "resume"
            config.manifest_path = parsed.resume
        elif parsed.interactive:
            config.mode = "interactive"
            config.prompt = parsed.prompt or ""
        else:
            config.mode = "generate"
            config.prompt = parsed.prompt or ""

        self._config = config
        return config

    def setup(self) -> None:
        """Set up LLM interface and progress display."""
        if self._config is None:
            self.parse_args()
        assert self._config is not None

        # Set up logging
        level = logging.DEBUG if self._config.verbose else logging.INFO
        logging.basicConfig(
            level=level,
            format="%(levelname)s: %(message)s",
        )

        # LLM interface
        self._llm = detect_llm_interface(self._config.model)

        # Progress display
        self._progress = ProgressDisplay(
            verbose=self._config.verbose,
        )

        # Ensure output directory exists
        os.makedirs(self._config.output_dir, exist_ok=True)

        # Ensure cache directory exists
        os.makedirs(self._config.cache_dir, exist_ok=True)

    def run(self) -> int:
        """
        Run the CLI.

        Returns the exit code (0 = success, 1 = failure).
        """
        if self._config is None:
            self.parse_args()
        if self._llm is None:
            self.setup()

        assert self._config is not None
        assert self._progress is not None

        mode = self._config.mode

        try:
            if mode == "generate":
                return self._run_generate()
            elif mode == "interactive":
                return self._run_interactive()
            elif mode == "resume":
                return self._run_resume()
            elif mode == "verify":
                return self._run_verify()
            elif mode == "check":
                return self._run_check()
            elif mode == "report":
                return self._run_report()
            else:
                self._progress.error(f"Unknown mode: {mode}")
                return 1
        except KeyboardInterrupt:
            self._progress.error("Interrupted by user")
            return 130
        except Exception as exc:
            self._progress.error(f"Unhandled error: {exc}")
            if self._config.verbose:
                import traceback
                traceback.print_exc()
            return 1

    # ── Mode implementations ──────────────────────────────────────────────

    def _run_generate(self) -> int:
        """Generate a verified project from a prompt."""
        assert self._config is not None
        assert self._progress is not None

        prompt = self._config.prompt
        if not prompt:
            self._progress.error(
                "No prompt provided. Usage: deppy \"your prompt here\""
            )
            return 1

        self._progress.intent_start(prompt)

        # Import here to avoid circular imports at module level
        from .verification_loop import (
            VerificationConfig,
            VerificationLoop,
            CEGARVerificationLoop,
            CrossModuleVerifier,
        )
        from .project_assembler import (
            ProjectAssembler,
            VerifiedModule,
            TrustReportGenerator,
        )

        # Build verification config
        cegar_budget = self._cegar_round_budget()
        vconfig = VerificationConfig(
            emit_lean=self._config.lean,
            strict_mode=self._config.strict,
            max_cegar_rounds=cegar_budget,
        )

        # Resolve intent (in a real system, this calls the LLM)
        intent = self._resolve_intent(prompt)
        intent = self._enrich_intent(prompt, intent)
        modules_planned = self._ordered_modules(intent)
        domain = intent.get("domain", "general")
        constraints = intent.get("constraints", [])

        self._progress.intent_resolved(domain, modules_planned, constraints)

        # Generate and verify each module
        vloop = VerificationLoop(config=vconfig)
        cegar = CEGARVerificationLoop(verification_loop=vloop, config=vconfig)
        verified_modules: Dict[str, VerifiedModule] = {}
        all_results: Dict[str, Any] = {}
        generated_artifacts: Dict[str, Dict[str, Any]] = {}

        for i, mod_name in enumerate(modules_planned, 1):
            self._progress.module_start(
                mod_name, i, len(modules_planned),
                pattern=self._module_generation_pattern(intent, mod_name),
            )

            # Generate module source
            artifact = self._generate_module(intent, mod_name)
            self._progress.verification_start(mod_name)

            # CEGAR verification loop
            def _repair(art: Dict[str, Any], feedback: str) -> Dict[str, Any]:
                assert self._llm is not None
                repair_prompt = (
                    f"Fix the following code:\n\n{art.get('source', '')}\n\n"
                    f"Issues:\n{feedback}\n\n"
                    f"Produce the corrected code."
                )
                try:
                    new_source = self._sanitize_python_source(
                        self._llm.complete(repair_prompt)
                    )
                except Exception as exc:
                    logger.warning(
                        "Repair generation failed for %s: %s — using scaffold fallback",
                        art.get("module_name", "unknown"),
                        exc,
                    )
                    module_plan = self._module_plan(intent, art.get("module_name", "main"))
                    new_source = self._render_module_scaffold(
                        art.get("module_name", "main"),
                        module_plan,
                        intent,
                    )
                return {**art, "source": new_source}

            final_artifact, result = cegar.run(
                artifact, _repair, max_rounds=cegar_budget,
            )

            # Report progress
            struct_proven = sum(
                1 for r in result.structural_results
                if r.get("status") == "proven"
            )
            self._progress.structural_done(
                mod_name, struct_proven, len(result.structural_results),
            )

            sem_passed = sum(
                1 for r in result.semantic_results
                if r.get("status") == "passed"
            )
            min_conf = min(
                (r.get("confidence", 0) for r in result.semantic_results),
                default=0.0,
            )
            self._progress.semantic_done(
                mod_name, sem_passed, len(result.semantic_results), min_conf,
            )

            high_sev = sum(
                1 for f in result.hallucination_findings
                if f.get("severity") == "high"
            )
            self._progress.hallucination_done(
                mod_name, len(result.hallucination_findings), high_sev,
            )

            if self._config.lean:
                self._progress.lean_done(
                    mod_name,
                    len(result.lean_obligations),
                    result.discharged,
                    result.residual,
                )

            self._progress.module_done(mod_name, result.trust_level)

            # Store
            verified_modules[mod_name] = VerifiedModule(
                name=mod_name,
                source=final_artifact.get("source", ""),
                trust_level=result.trust_level,
                verification_result=result.to_dict(),
                cegar_rounds=result.cegar_rounds,
            )
            generated_artifacts[mod_name] = dict(final_artifact)
            all_results[mod_name] = result.to_dict()

        # Cross-module verification
        cross_verifier = CrossModuleVerifier(config=vconfig)
        module_sources = {
            n: m.source for n, m in verified_modules.items()
        }
        cross_result = cross_verifier.verify(module_sources)
        self._progress.cross_module_done(
            cross_result.contracts_verified,
            cross_result.contracts_failed,
            cross_result.h1_cross,
        )

        # Assemble project
        assembler = ProjectAssembler()
        project = assembler.assemble(
            intent, verified_modules, all_results,
        )

        # Write to disk
        written = project.write(self._config.output_dir)
        output_path = os.path.join(self._config.output_dir, project.name)
        self._write_generation_prompts(output_path, generated_artifacts)

        # Save manifest
        manifest_path = os.path.join(
            self._config.output_dir, project.name, "deppy_manifest.json",
        )

        # Final progress display
        overall_trust = project.trust_summary().split(":")[1].strip().split()[0] if ":" in project.trust_summary() else "UNCHECKED"
        stats = {
            "structural_proven": sum(
                sum(1 for r in res.get("structural_results", [])
                    if r.get("status") == "proven")
                for res in all_results.values()
            ),
            "structural_total": sum(
                len(res.get("structural_results", []))
                for res in all_results.values()
            ),
            "semantic_passed": sum(
                sum(1 for r in res.get("semantic_results", [])
                    if r.get("status") == "passed")
                for res in all_results.values()
            ),
            "semantic_total": sum(
                len(res.get("semantic_results", []))
                for res in all_results.values()
            ),
            "hallucinations_found": sum(
                len(res.get("hallucination_findings", []))
                for res in all_results.values()
            ),
            "hallucinations_fixed": sum(
                len(res.get("hallucination_findings", []))
                for res in all_results.values()
                if res.get("cegar_rounds", 0) > 0 and res.get("passed")
            ),
            "oracle_calls": vloop.stats.get("oracle_calls", 0),
            "oracle_cache_hits": vloop.stats.get("oracle_cache_hits", 0),
        }
        if self._config.lean:
            stats["lean_total"] = sum(
                len(res.get("lean_obligations", []))
                for res in all_results.values()
            )
            stats["lean_discharged"] = sum(
                res.get("discharged", 0)
                for res in all_results.values()
            )
            stats["lean_residual"] = sum(
                res.get("residual", 0)
                for res in all_results.values()
            )

        self._progress.project_done(output_path, overall_trust, stats)

        return 0

    def _run_interactive(self) -> int:
        """Run in interactive mode — placeholder."""
        assert self._progress is not None
        self._progress.info("Interactive mode is not yet implemented.")
        self._progress.info("Falling back to single-shot generation.")
        return self._run_generate()

    def _run_resume(self) -> int:
        """Resume from a saved manifest — placeholder."""
        assert self._config is not None
        assert self._progress is not None
        manifest_path = self._config.manifest_path
        if not os.path.isfile(manifest_path):
            self._progress.error(f"Manifest not found: {manifest_path}")
            return 1

        self._progress.info(f"Loading manifest: {manifest_path}")
        with open(manifest_path, "r") as f:
            manifest = json.load(f)

        self._progress.info(
            f"Loaded manifest for project: {manifest.get('project_name', '?')}"
        )
        self._progress.warning("Resume is not yet fully implemented.")
        return 0

    def _run_verify(self) -> int:
        """Verify a single file."""
        assert self._config is not None
        assert self._progress is not None

        target = self._config.target_file
        if not os.path.isfile(target):
            self._progress.error(f"File not found: {target}")
            return 1

        from .verification_loop import VerificationConfig, VerificationLoop

        with open(target, "r") as f:
            source = f.read()

        module_name = os.path.splitext(os.path.basename(target))[0]
        vconfig = VerificationConfig(
            emit_lean=self._config.lean,
            strict_mode=self._config.strict,
        )
        vloop = VerificationLoop(config=vconfig)
        result = vloop.verify(source, module_name)

        # Display results
        self._progress.module_start(module_name, 1, 1)
        sp = sum(1 for r in result.structural_results if r.get("status") == "proven")
        self._progress.structural_done(module_name, sp, len(result.structural_results))

        sep = sum(1 for r in result.semantic_results if r.get("status") == "passed")
        mc = min((r.get("confidence", 0) for r in result.semantic_results), default=0.0)
        self._progress.semantic_done(module_name, sep, len(result.semantic_results), mc)

        hs = sum(1 for f in result.hallucination_findings if f.get("severity") == "high")
        self._progress.hallucination_done(
            module_name, len(result.hallucination_findings), hs,
        )

        if self._config.lean:
            self._progress.lean_done(
                module_name, len(result.lean_obligations),
                result.discharged, result.residual,
            )

        self._progress.module_done(module_name, result.trust_level)

        # Print summary
        print(result.summary())

        return 0 if result.passed else 1

    def _run_check(self) -> int:
        """Check an existing project directory."""
        assert self._config is not None
        assert self._progress is not None

        target_dir = self._config.target_dir
        if not os.path.isdir(target_dir):
            self._progress.error(f"Directory not found: {target_dir}")
            return 1

        from .verification_loop import (
            VerificationConfig, VerificationLoop, CrossModuleVerifier,
        )

        vconfig = VerificationConfig(
            emit_lean=self._config.lean,
            strict_mode=self._config.strict,
        )
        vloop = VerificationLoop(config=vconfig)

        # Find all .py files
        py_files: List[str] = []
        for root, _dirs, files in os.walk(target_dir):
            for fname in files:
                if fname.endswith(".py") and not fname.startswith("test_"):
                    py_files.append(os.path.join(root, fname))

        if not py_files:
            self._progress.error(f"No Python files found in {target_dir}")
            return 1

        modules: Dict[str, str] = {}
        all_passed = True

        for i, fpath in enumerate(py_files, 1):
            with open(fpath, "r") as f:
                source = f.read()

            mod_name = os.path.splitext(os.path.basename(fpath))[0]
            self._progress.module_start(mod_name, i, len(py_files))

            result = vloop.verify(source, mod_name)
            modules[mod_name] = source

            sp = sum(1 for r in result.structural_results if r.get("status") == "proven")
            self._progress.structural_done(mod_name, sp, len(result.structural_results))

            hs = sum(1 for f in result.hallucination_findings if f.get("severity") == "high")
            self._progress.hallucination_done(
                mod_name, len(result.hallucination_findings), hs,
            )

            self._progress.module_done(mod_name, result.trust_level)

            if not result.passed:
                all_passed = False

        # Cross-module check
        if len(modules) > 1:
            cross = CrossModuleVerifier(config=vconfig)
            cross_result = cross.verify(modules)
            self._progress.cross_module_done(
                cross_result.contracts_verified,
                cross_result.contracts_failed,
                cross_result.h1_cross,
            )

        return 0 if all_passed else 1

    def _run_report(self) -> int:
        """Generate trust report from a manifest."""
        assert self._config is not None
        assert self._progress is not None

        manifest_path = self._config.manifest_path
        if not os.path.isfile(manifest_path):
            self._progress.error(f"Manifest not found: {manifest_path}")
            return 1

        from .project_assembler import TrustReportGenerator

        with open(manifest_path, "r") as f:
            manifest = json.load(f)

        # Extract results from manifest
        module_results: Dict[str, Any] = {}
        for mod_name, mod_info in manifest.get("modules", {}).items():
            module_results[mod_name] = mod_info.get("verification", {})

        gen = TrustReportGenerator()
        report = gen.generate_trust_report(module_results)

        # Write markdown report
        report_path = os.path.join(
            os.path.dirname(manifest_path),
            "deppy_trust_report.md",
        )
        with open(report_path, "w") as f:
            f.write(report.to_markdown())

        self._progress.info(f"Trust report written to {report_path}")
        print(report.to_markdown())

        return 0

    # ── Helpers ────────────────────────────────────────────────────────────

    def _resolve_intent(self, prompt: str) -> Dict[str, Any]:
        """
        Resolve a natural-language prompt into a structured intent.

        In the full system this calls the intent oracle (LLM); here we
        provide a deterministic fallback for when no LLM is available.
        """
        assert self._llm is not None

        schema = {
            "type": "object",
            "properties": {
                "project_name": {"type": "string"},
                "description": {"type": "string"},
                "domain": {"type": "string"},
                "modules": {
                    "type": "array",
                    "items": {"type": "string"},
                },
                "constraints": {
                    "type": "array",
                    "items": {"type": "string"},
                },
                "dependencies": {
                    "type": "array",
                    "items": {"type": "string"},
                },
            },
        }

        resolve_prompt = (
            f"You are a software architect. Given this user request, "
            f"decompose it into a project plan.\n\n"
            f"Request: {prompt}\n\n"
            f"Respond with a JSON object containing: project_name, "
            f"description, domain, modules (list of module names), "
            f"constraints (list of requirements), and dependencies "
            f"(list of pip packages needed)."
        )

        try:
            intent = self._llm.complete_json(resolve_prompt, schema)
            return self._normalize_intent(prompt, intent)
        except Exception as exc:
            logger.warning("Intent resolution failed: %s — using fallback", exc)
            return self._normalize_intent(prompt, {})

    @staticmethod
    def _slugify_module_name(name: str) -> str:
        cleaned = "".join(
            ch.lower() if ch.isalnum() else "_"
            for ch in str(name).strip()
        )
        while "__" in cleaned:
            cleaned = cleaned.replace("__", "_")
        return cleaned.strip("_") or "main"

    def _normalize_intent(self, prompt: str, intent: Any) -> Dict[str, Any]:
        payload = intent if isinstance(intent, dict) else {}
        lowered = prompt.lower()

        project_name = payload.get("project_name")
        if not isinstance(project_name, str) or not project_name.strip():
            words = [
                self._slugify_module_name(word)
                for word in prompt.split()
                if self._slugify_module_name(word)
            ]
            project_name = "_".join(words[:4]) or "project"

        description = payload.get("description")
        if not isinstance(description, str) or not description.strip():
            description = prompt

        domain = payload.get("domain")
        if not isinstance(domain, str) or not domain.strip():
            if any(token in lowered for token in ("trading", "market", "portfolio", "broker")):
                domain = "trading"
            elif any(token in lowered for token in ("api", "web", "http", "rest")):
                domain = "web"
            elif any(token in lowered for token in ("data", "pipeline", "etl")):
                domain = "data"
            else:
                domain = "general"

        raw_modules = payload.get("modules")
        modules: List[str] = []
        if isinstance(raw_modules, list):
            modules = [
                self._slugify_module_name(module)
                for module in raw_modules
                if isinstance(module, str) and module.strip()
            ]
        if not modules:
            if "trad" in lowered or "trad" in domain.lower():
                modules = [
                    "market_data",
                    "signal_geometry",
                    "strategy_kernel",
                    "risk_engine",
                    "execution",
                    "portfolio",
                    "compliance",
                    "main",
                ]
            else:
                modules = ["main"]

        raw_constraints = payload.get("constraints")
        constraints: List[str] = []
        if isinstance(raw_constraints, list):
            constraints = [
                str(item).strip()
                for item in raw_constraints
                if str(item).strip()
            ]
        if not constraints:
            if "novel" in lowered or "discover" in lowered:
                constraints.append("System must discover or realize a novel idea.")
            if any(token in lowered for token in ("verified", "prove", "proof")):
                constraints.append("Risk-critical behavior must be formally specified and verified.")
            if "risk" in lowered:
                constraints.append("Risk controls must be enforced before execution.")

        raw_dependencies = payload.get("dependencies")
        dependencies: List[str] = []
        if isinstance(raw_dependencies, list):
            dependencies = [
                str(item).strip()
                for item in raw_dependencies
                if str(item).strip()
            ]

        return {
            "raw_prompt": prompt,
            "project_name": self._slugify_module_name(project_name),
            "description": description,
            "domain": domain,
            "modules": self._ordered_unique_modules(modules),
            "constraints": constraints,
            "dependencies": dependencies,
        }

    def _enrich_intent(
        self,
        prompt: str,
        intent: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Apply optional ideation and orchestration passes to an intent."""
        enriched = dict(intent)
        if self._config is not None and self._config.ideation:
            enriched = self._apply_ideation(prompt, enriched)
        if self._config is not None and self._config.orchestration:
            enriched = self._apply_orchestration(prompt, enriched)
        if self._config is not None and self._config.full:
            enriched = self._apply_full_mode(prompt, enriched)
        return enriched

    def _apply_full_mode(
        self,
        prompt: str,
        intent: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Expand the resolved intent into a large-scale domain-agnostic plan."""
        target_loc = 50_000
        description = str(intent.get("description") or prompt)
        ordered_modules = self._ordered_modules(intent)
        role_map = intent.get("module_roles", {})
        roles = role_map if isinstance(role_map, dict) else {}
        orchestration = intent.get("orchestration", {})
        overlaps = orchestration.get("overlaps", []) if isinstance(orchestration, dict) else []
        ideation = intent.get("ideation", {})
        ideation_lenses = self._ideation_lenses(intent)
        ideation_benefit = {}
        if isinstance(ideation, dict):
            ideation_benefit.update(dict(ideation.get("benefit_evaluation", {})))
            scalar_typing = ideation.get("scalar_valued_typing", {})
            if isinstance(scalar_typing, dict) and scalar_typing:
                ideation_benefit["scalar_valued_typing"] = dict(scalar_typing)

        components: Dict[str, str] = {}
        for module_name in ordered_modules:
            role = str(roles.get(module_name) or self._module_pattern(intent, module_name) or module_name)
            obligations = [
                str(overlap.get("obligation", ""))
                for overlap in overlaps
                if module_name in (overlap.get("left"), overlap.get("right"))
            ]
            lines = [
                description,
                f"Component: {module_name}",
                f"Role: {role}",
            ]
            if obligations:
                lines.append("Overlap obligations:")
                lines.extend(f"- {item}" for item in obligations[:4])
            constraints = [str(item) for item in intent.get("constraints", [])[:6]]
            if constraints:
                lines.append("Constraints:")
                lines.extend(f"- {item}" for item in constraints)
            if ideation_lenses:
                lines.append("Ideation lenses:")
                for lens in ideation_lenses[:4]:
                    lines.append(
                        f"- {lens.get('kind', 'lens')}: {lens.get('label', '')}"
                    )
            components[module_name] = "\n".join(lines)

        try:
            from deppy.hybrid.type_expansion import LargeScaleGenerator
        except Exception as exc:
            logger.warning(
                "Full mode expansion unavailable: %s — keeping the existing cover",
                exc,
            )
            fallback = dict(intent)
            fallback["target_loc"] = target_loc
            fallback["full_mode"] = True
            return fallback

        report = LargeScaleGenerator(default_target_loc=target_loc).generate(
            {
                "spec": description,
                "target_loc": target_loc,
                "components": [
                    {
                        "name": name,
                        "spec": text,
                        "ideation_lenses": ideation_lenses,
                        "ideation_benefit": ideation_benefit,
                    }
                    for name, text in components.items()
                ],
            }
        )
        global_plan = report.get("global_plan", {})
        expanded_nodes = global_plan.get("modules", [])
        elaboration_tree = (
            global_plan.get("elaboration_tree", {})
            if isinstance(global_plan, dict)
            else {}
        )
        if not expanded_nodes:
            fallback = dict(intent)
            fallback["target_loc"] = target_loc
            fallback["full_mode"] = True
            return fallback

        expanded_modules = self._leaf_modules_from_tree(elaboration_tree)
        if not expanded_modules:
            expanded_modules = self._ordered_unique_modules(
                [str(node.get("name", "main")) for node in expanded_nodes]
            )
        expanded_roles = dict(roles)
        for node in expanded_nodes:
            expanded_roles[str(node.get("name", "main"))] = str(
                node.get("summary") or node.get("name", "expanded module")
            )

        interface_overlaps = [
            {
                "left": str(interface.get("provider", "")),
                "right": str(interface.get("consumer", "")),
                "obligation": str(
                    interface.get("obligation") or interface.get("name") or "interface compatibility"
                ),
            }
            for interface in global_plan.get("interfaces", [])
            if interface.get("provider") and interface.get("consumer")
        ]
        gluing_obligations = self._ordered_unique_modules(
            list(orchestration.get("gluing_obligations", [])) if isinstance(orchestration, dict) else []
            + [str(item["obligation"]) for item in interface_overlaps]
        )

        enriched = dict(intent)
        enriched["modules"] = expanded_modules
        enriched["module_roles"] = expanded_roles
        enriched["constraints"] = self._ordered_unique_modules(
            [str(item) for item in intent.get("constraints", [])]
            + [
                "Full mode target LOC: approximately 50000 lines across expanded modules.",
                "Use Σ/Π/refinement/identity expansion to refine the prompt into an H¹-aware large-scale plan.",
            ]
        )
        enriched["target_loc"] = target_loc
        enriched["full_mode"] = True
        enriched["full_expansion"] = report
        enriched["orchestration"] = {
            "mode": "tt_ag_full",
            "module_order": expanded_modules,
            "overlaps": interface_overlaps,
            "gluing_obligations": gluing_obligations,
            "expanded_candidates": ordered_modules,
            "component_count": report.get("component_count", len(ordered_modules)),
            "module_budget": report.get("module_count", len(expanded_modules)),
            "target_loc": target_loc,
            "type_elaboration_tree": elaboration_tree,
            "algebraic_geometry_view": (
                "Full-mode orchestration is a rooted Grothendieck cover: component charts "
                "refine into leaf modules, and execution proceeds by gluing local sections."
            ),
        }
        enriched["type_lenses"] = ideation_lenses
        enriched["type_benefit"] = ideation_benefit

        if self._config is not None and self._config.verbose:
            self._progress.info(
                "Full mode expansion: "
                f"{len(expanded_modules)} modules targeting ~{report.get('total_estimated_loc', target_loc)} LOC"
            )
            if elaboration_tree:
                self._progress.info(
                    f"Type elaboration tree: {self._summarize_tree(elaboration_tree)}"
                )

        return enriched

    def _apply_ideation(
        self,
        prompt: str,
        intent: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Attach TT/AG ideation metadata and require a novel design idea."""
        assert self._progress is not None

        try:
            from deppy.hybrid.ideation.analogy_types import (
                IdeationOracle,
                SelfImprovementLoop,
            )
        except ImportError as exc:
            self._progress.warning(
                f"Ideation requested but unavailable ({exc}); falling back."
            )
            return intent

        math_area_selection = self._math_area_selection(intent, prompt)
        baseline_domains = self._baseline_ideation_domains(intent, prompt)
        guided_selection = self._llm_guided_ideation_focus(
            intent,
            prompt,
            math_area_selection,
        )
        domains = (
            guided_selection["registry_domains"]
            if guided_selection is not None
            else self._ideation_domains(intent, prompt)
        )
        problem = intent.get("description") or prompt
        oracle = IdeationOracle()
        baseline_ideation = oracle.ideate(baseline_domains, problem)
        ideation = (
            baseline_ideation
            if domains == baseline_domains
            else oracle.ideate(domains, problem)
        )
        proposals = SelfImprovementLoop().propose_extension(problem)
        novel_idea = self._select_novel_idea(problem, ideation, proposals)
        benefit_evaluation = self._evaluate_ideation_benefit(
            baseline_ideation,
            ideation,
        )
        selected_math_area_details = self._selected_math_area_details(
            guided_selection["math_areas"]
            if guided_selection is not None
            else math_area_selection["selected_math_areas"]
        )
        scalar_typing = self._scalar_valued_typing(
            guided_selection=guided_selection,
            ideation=ideation,
            proposals=proposals,
            selected_area_details=selected_math_area_details,
            benefit_evaluation=benefit_evaluation,
            domains=domains,
        )
        novelty_packet = self._build_novelty_packet(
            problem,
            domains,
            novel_idea,
            ideation,
            proposals,
            scalar_typing,
        )

        constraints = list(intent.get("constraints", []))
        constraints.append(
            f"Novel idea requirement: {novel_idea}"
        )
        constraints.append(
            "Use ideation-as-typing: justify the design via topology-preserving "
            "analogies, cocycle checks, and H¹-aware gluing."
        )

        enriched = dict(intent)
        enriched["constraints"] = constraints
        enriched["ideation"] = {
            "domains": domains,
            "novel_idea": novel_idea,
            "unified_insights": ideation.unified_insights,
            "h1_dimension": ideation.h1_dimension,
            "deep_analogies": [
                analogy.summary()
                for analogy in ideation.deep_analogies[:3]
            ],
            "extension_proposals": [
                {
                    "name": proposal.name,
                    "description": proposal.description,
                    "confidence": proposal.confidence,
                    "rationale": proposal.rationale,
                }
                for proposal in proposals[:3]
            ],
            "novel_idea_structured": novelty_packet,
            "math_area_count_considered": math_area_selection["math_area_count"],
            "math_term_count_considered": math_area_selection["math_term_count"],
            "math_area_mode": math_area_selection["mode"],
            "selected_math_areas": math_area_selection["selected_math_areas"],
            "selected_math_area_details": selected_math_area_details,
            "math_ontology_summary": math_area_selection.get("ontology_summary", {}),
            "selection_strategy": {
                "mode": (
                    guided_selection["mode"]
                    if guided_selection is not None
                    else "heuristic_fallback"
                ),
                "baseline_domains": baseline_domains,
                "guided_domains": domains,
                "guided_math_areas": (
                    guided_selection["math_areas"]
                    if guided_selection is not None
                    else math_area_selection["selected_math_areas"]
                ),
                "rationale": (
                    guided_selection["reasoning"]
                    if guided_selection is not None
                    else []
                ),
            },
            "benefit_evaluation": benefit_evaluation,
            "scalar_valued_typing": scalar_typing,
        }

        if self._config is not None and self._config.verbose:
            self._progress.info(
                "Math ontology: "
                f"{math_area_selection['math_area_count']} areas / "
                f"{math_area_selection['math_term_count']} terms"
            )
            if math_area_selection["selected_math_areas"]:
                self._progress.info(
                    "Selected math areas: "
                    + ", ".join(math_area_selection["selected_math_areas"][:8])
                )
            self._progress.info(
                f"Ideation selection mode: {enriched['ideation']['selection_strategy']['mode']}"
            )
            self._progress.info(f"Ideation domains: {', '.join(domains)}")
            self._progress.info(
                "Benefit vs baseline: "
                f"score Δ={benefit_evaluation['score_delta']}, "
                f"deep Δ={benefit_evaluation['deep_analogies_delta']}, "
                f"novel Δ={benefit_evaluation['novel_connections_delta']}, "
                f"H¹ improvement={benefit_evaluation['h1_improvement']}"
            )
            self._progress.info(
                "Scalar-valued typing: "
                f"overall={scalar_typing['overall']:.3f}, "
                f"llm={scalar_typing['llm_belief']:.3f}, "
                f"math={scalar_typing['math_model']:.3f}"
            )
            self._progress.info("Novel idea packet:")
            for key in (
                "headline",
                "thesis",
                "ag_view",
                "typed_view",
                "scalar_valued_typing",
                "research_program",
                "proof_target",
            ):
                self._progress.info(f"   {key}: {novelty_packet[key]}")

        return enriched

    def _apply_orchestration(
        self,
        prompt: str,
        intent: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Construct a TT/AG orchestration cover for project generation."""
        trading = "trad" in prompt.lower() or "trad" in intent.get("domain", "").lower()

        if trading:
            ordered_modules = [
                "market_data",
                "signal_geometry",
                "strategy_kernel",
                "risk_engine",
                "execution",
                "portfolio",
                "compliance",
                "main",
            ]
            module_roles = {
                "market_data": "input site: normalize feeds and local market observations",
                "signal_geometry": "ideation site: turn local signals into a gluable global section",
                "strategy_kernel": "pi/sigma core: encode the trading thesis as typed strategy rules",
                "risk_engine": "refinement site: enforce leverage, drawdown, and exposure invariants",
                "execution": "code layer site: place orders only from coherent, risk-approved sections",
                "portfolio": "state site: reconcile fills, positions, and PnL as dependent records",
                "compliance": "proof boundary: witness policy and audit obligations on overlaps",
                "main": "global section: glue the local sites into one runnable verified system",
            }
            overlaps = [
                {
                    "left": "market_data",
                    "right": "signal_geometry",
                    "obligation": "restrictions preserve timestamp, symbol, and normalization invariants",
                },
                {
                    "left": "signal_geometry",
                    "right": "strategy_kernel",
                    "obligation": "alpha signals must glue into one coherent strategy section",
                },
                {
                    "left": "strategy_kernel",
                    "right": "risk_engine",
                    "obligation": "position intents and risk bounds must agree on all overlaps",
                },
                {
                    "left": "risk_engine",
                    "right": "execution",
                    "obligation": "only risk-approved intents descend to executable orders",
                },
                {
                    "left": "execution",
                    "right": "portfolio",
                    "obligation": "fills, positions, and cash updates satisfy identity constraints",
                },
                {
                    "left": "portfolio",
                    "right": "compliance",
                    "obligation": "audit trail and policy evidence form a trace-backed cocycle",
                },
            ]
        else:
            ordered_modules = self._ordered_unique_modules(intent.get("modules", ["main"]))
            module_roles = {
                name: f"local site for {name.replace('_', ' ')}"
                for name in ordered_modules
            }
            overlaps = []
            for left, right in zip(ordered_modules, ordered_modules[1:]):
                overlaps.append(
                    {
                        "left": left,
                        "right": right,
                        "obligation": (
                            f"{left} and {right} must agree on their shared API overlap"
                        ),
                    }
                )
        module_tree = (
            self._build_trading_module_tree(module_roles)
            if trading
            else self._build_generic_module_tree(ordered_modules, module_roles)
        )
        geometry_view = (
            "Treat trading subsystems as charts in a market sheaf: local alpha sections "
            "descend through risk and execution only when cocycle obligations vanish."
            if trading
            else "Treat modules as charts in a Grothendieck cover whose overlaps must glue "
            "into a single executable global section."
        )

        existing_modules = self._ordered_unique_modules(intent.get("modules", []))

        gluing_obligations = [
            overlap["obligation"] for overlap in overlaps
        ]
        gluing_obligations.append(
            "Cocycle condition: composing adjacent restriction maps must equal the direct map on triple overlaps."
        )
        gluing_obligations.append(
            "Global section condition: the assembled project must witness H¹ = 0 across module overlaps."
        )

        constraints = list(intent.get("constraints", []))
        constraints.append(
            "Use orchestration-as-typing: modules are local sections in a cover, and integration must discharge gluing obligations."
        )

        enriched = dict(intent)
        enriched["constraints"] = constraints
        enriched["modules"] = ordered_modules
        enriched["module_roles"] = module_roles
        enriched["orchestration"] = {
            "mode": "tt_ag",
            "module_order": ordered_modules,
            "module_roles": module_roles,
            "overlaps": overlaps,
            "gluing_obligations": gluing_obligations,
            "expanded_candidates": existing_modules,
            "type_elaboration_tree": module_tree,
            "algebraic_geometry_view": geometry_view,
        }

        if self._config is not None and self._config.verbose:
            self._progress.info(
                f"Typed orchestration cover: {' → '.join(ordered_modules)}"
            )
            self._progress.info(
                f"Typed orchestration tree: {self._summarize_tree(module_tree)}"
            )

        return enriched

    @staticmethod
    def _ordered_unique_modules(modules: List[str]) -> List[str]:
        """Return modules with order preserved and duplicates removed."""
        seen: set[str] = set()
        ordered: List[str] = []
        for module in modules:
            if module not in seen:
                seen.add(module)
                ordered.append(module)
        return ordered or ["main"]

    def _ordered_modules(self, intent: Dict[str, Any]) -> List[str]:
        orchestration = intent.get("orchestration", {})
        module_order = orchestration.get("module_order")
        if isinstance(module_order, list) and module_order:
            return list(module_order)
        if isinstance(orchestration, dict):
            leaf_modules = self._leaf_modules_from_tree(
                orchestration.get("type_elaboration_tree", {})
            )
            if leaf_modules:
                return leaf_modules
        return self._ordered_unique_modules(intent.get("modules", ["main"]))

    @staticmethod
    def _leaf_modules_from_tree(tree: Any) -> List[str]:
        if not isinstance(tree, dict):
            return []
        children = tree.get("children", [])
        if not isinstance(children, list) or not children:
            name = str(tree.get("name", "")).strip()
            return [name] if name else []
        ordered: List[str] = []
        for child in children:
            ordered.extend(AgentCLI._leaf_modules_from_tree(child))
        seen: set[str] = set()
        return [name for name in ordered if not (name in seen or seen.add(name))]

    @staticmethod
    def _summarize_tree(tree: Any) -> str:
        if not isinstance(tree, dict):
            return "unavailable"
        root = str(tree.get("name", "cover"))
        children = tree.get("children", [])
        if not isinstance(children, list) or not children:
            return root
        branches: List[str] = []
        for child in children[:4]:
            if not isinstance(child, dict):
                continue
            branch_name = str(child.get("name", "branch"))
            leaves = AgentCLI._leaf_modules_from_tree(child)
            leaf_preview = ", ".join(leaves[:3])
            if len(leaves) > 3:
                leaf_preview += ", ..."
            branches.append(f"{branch_name}[{leaf_preview}]")
        return f"{root} -> " + " | ".join(branches)

    @staticmethod
    def _module_tree_path(tree: Any, module_name: str) -> List[str]:
        if not isinstance(tree, dict):
            return []
        if str(tree.get("name", "")) == module_name:
            return [module_name]
        for child in tree.get("children", []):
            path = AgentCLI._module_tree_path(child, module_name)
            if path:
                current = str(tree.get("name", "")).strip()
                return ([current] if current else []) + path
        return []

    @staticmethod
    def _prompt_list_preview(
        items: Any,
        limit: int = 6,
        max_chars: int = 480,
    ) -> str:
        if not isinstance(items, list):
            return ProgressDisplay._truncate(str(items), max_chars)
        normalized = [str(item) for item in items if str(item).strip()]
        if not normalized:
            return "[]"
        preview = normalized[:limit]
        suffix = ""
        if len(normalized) > limit:
            suffix = f", ... ({len(normalized) - limit} more)"
        text = "[" + ", ".join(preview) + suffix + "]"
        return ProgressDisplay._truncate(text, max_chars)

    @staticmethod
    def _module_order_context(
        module_order: Any,
        module_name: str,
        radius: int = 2,
    ) -> str:
        if not isinstance(module_order, list):
            return "unavailable"
        normalized = [str(item) for item in module_order if str(item).strip()]
        if not normalized:
            return "[]"
        if module_name not in normalized:
            return AgentCLI._prompt_list_preview(
                normalized,
                limit=6,
                max_chars=320,
            )
        index = normalized.index(module_name)
        start = max(0, index - radius)
        end = min(len(normalized), index + radius + 1)
        window = normalized[start:end]
        window_text = " -> ".join(window)
        if start > 0:
            window_text = "... -> " + window_text
        if end < len(normalized):
            window_text += " -> ..."
        return (
            f"{len(normalized)} total modules; "
            f"local window around {module_name}: {window_text}"
        )

    @staticmethod
    def _prompt_bullet_preview(items: List[str], limit: int = 6) -> str:
        normalized = [str(item) for item in items if str(item).strip()]
        if not normalized:
            return ""
        lines = [f"  * {item}" for item in normalized[:limit]]
        if len(normalized) > limit:
            lines.append(f"  * ... ({len(normalized) - limit} more)")
        return "\n".join(lines) + "\n"

    @staticmethod
    def _build_generic_module_tree(
        ordered_modules: List[str],
        module_roles: Dict[str, str],
    ) -> Dict[str, Any]:
        clusters: List[Dict[str, Any]] = []
        for index in range(0, len(ordered_modules), 3):
            cluster_modules = ordered_modules[index:index + 3]
            clusters.append(
                {
                    "name": f"chart_cluster_{index // 3 + 1}",
                    "kind": "chart_cluster",
                    "summary": "Local chart family for typed orchestration.",
                    "children": [
                        {
                            "name": module_name,
                            "kind": "local_section",
                            "summary": module_roles.get(module_name, module_name),
                            "children": [],
                        }
                        for module_name in cluster_modules
                    ],
                }
            )
        return {
            "name": "project_cover",
            "kind": "grothendieck_cover",
            "summary": "Rooted cover for project orchestration.",
            "children": clusters,
        }

    @staticmethod
    def _build_trading_module_tree(module_roles: Dict[str, str]) -> Dict[str, Any]:
        def _leaf(name: str) -> Dict[str, Any]:
            return {
                "name": name,
                "kind": "local_section",
                "summary": module_roles.get(name, name),
                "children": [],
            }

        return {
            "name": "trading_system_cover",
            "kind": "grothendieck_cover",
            "summary": "Algebraic-geometric cover for trading discovery, risk, and execution.",
            "children": [
                {
                    "name": "research_chart",
                    "kind": "signal_sheaf",
                    "summary": "Discover local alpha sections from market charts.",
                    "children": [
                        _leaf("market_data"),
                        _leaf("signal_geometry"),
                        _leaf("strategy_kernel"),
                    ],
                },
                {
                    "name": "risk_execution_chart",
                    "kind": "refinement_descent",
                    "summary": "Refine candidate sections into executable, risk-safe intents.",
                    "children": [
                        _leaf("risk_engine"),
                        _leaf("execution"),
                        _leaf("portfolio"),
                    ],
                },
                {
                    "name": "assurance_chart",
                    "kind": "audit_boundary",
                    "summary": "Glue evidence and final system behavior into an auditable global section.",
                    "children": [
                        _leaf("compliance"),
                        _leaf("main"),
                    ],
                },
            ],
        }

    @staticmethod
    def _module_pattern(intent: Dict[str, Any], module_name: str) -> str:
        roles = intent.get("module_roles", {})
        if isinstance(roles, dict):
            return str(roles.get(module_name, ""))
        return ""

    def _module_generation_pattern(
        self,
        intent: Dict[str, Any],
        module_name: str,
    ) -> str:
        def _truncate(text: str, limit: int = 120) -> str:
            normalized = " ".join(text.split())
            if len(normalized) <= limit:
                return normalized
            return normalized[: max(0, limit - 3)].rstrip() + "..."

        module_plan = self._module_plan(intent, module_name)
        description = str(intent.get("description", "")).strip().lower()

        candidates: List[str] = []
        for spec in module_plan.get("class_specs", []):
            if not isinstance(spec, dict):
                continue
            local_models = spec.get("local_models", [])
            if isinstance(local_models, list) and local_models:
                candidates.append("model " + ", ".join(str(item) for item in local_models[:2]))
            transport_maps = spec.get("transport_maps", [])
            if isinstance(transport_maps, list) and transport_maps:
                candidates.append("transport via " + ", ".join(str(item) for item in transport_maps[:2]))

        for spec in module_plan.get("function_specs", []):
            if not isinstance(spec, dict):
                continue
            purpose = str(spec.get("purpose", "")).strip()
            if purpose and "operate the" not in purpose.lower():
                candidates.append(purpose)
            invariants = spec.get("invariants", [])
            if isinstance(invariants, list) and invariants:
                candidates.append("preserve " + ", ".join(str(item) for item in invariants[:2]))

        for item in module_plan.get("responsibilities", []):
            text = str(item).strip()
            lowered = text.lower()
            if (
                text
                and lowered != description
                and "full mode target loc" not in lowered
                and "sigma/pi/refinement" not in lowered
            ):
                candidates.append(text)

        summary = str(module_plan.get("summary", "")).strip()
        if summary and summary.lower() != description:
            candidates.append(summary)

        seen: set[str] = set()
        for candidate in candidates:
            normalized = " ".join(candidate.split())
            if not normalized:
                continue
            lowered = normalized.lower()
            if lowered in seen:
                continue
            seen.add(lowered)
            return _truncate(normalized, 120)

        return _truncate(module_name.replace("_", " "), 120)

    def _cegar_round_budget(self) -> int:
        if self._config is None:
            return 1
        if isinstance(self._llm, CopilotCLIInterface):
            return 1
        return max(1, int(self._config.max_iterations))

    @staticmethod
    def _write_generation_prompts(
        output_path: str,
        artifacts: Dict[str, Dict[str, Any]],
    ) -> None:
        prompt_dir = os.path.join(output_path, "prompts")
        os.makedirs(prompt_dir, exist_ok=True)
        for module_name, artifact in artifacts.items():
            prompt = str(artifact.get("generation_prompt", "")).strip()
            if not prompt:
                continue
            prompt_path = os.path.join(
                prompt_dir,
                f"{module_name}.generation_prompt.md",
            )
            body = (
                f"# Generation prompt for `{module_name}`\n\n"
                "```text\n"
                f"{prompt}\n"
                "```\n"
            )
            with open(prompt_path, "w", encoding="utf-8") as handle:
                handle.write(body)

    @staticmethod
    def _build_novelty_packet(
        problem: str,
        domains: List[str],
        novel_idea: str,
        ideation: Any,
        proposals: List[Any],
        scalar_typing: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, str]:
        lowered = problem.lower()
        proposal_name = ""
        if proposals:
            proposal_name = str(getattr(proposals[0], "name", "") or "").strip()
        headline = proposal_name or novel_idea.split(".")[0].strip() or "Typed novel idea"
        scalar_summary = (
            "Scalar-valued typing assigns a score to each type elaboration by combining "
            "the LLM's domain belief with the mathematical model's evidence for how well "
            "the idea fits the problem."
        )
        if isinstance(scalar_typing, dict):
            overall = scalar_typing.get("overall")
            llm_belief = scalar_typing.get("llm_belief")
            math_model = scalar_typing.get("math_model")
            if all(isinstance(item, (int, float)) for item in (overall, llm_belief, math_model)):
                scalar_summary = (
                    "Scalar-valued typing scores the current type elaboration by domain fit: "
                    f"overall={float(overall):.3f}, llm={float(llm_belief):.3f}, "
                    f"math={float(math_model):.3f}."
                )
        if "trad" in lowered or "market" in lowered or "portfolio" in lowered:
            ag_view = (
                "View historical and live regimes as charts in a market cover; only admit "
                "signals whose local sections glue across overlaps into a coherent thesis."
            )
            typed_view = (
                "Encode research hypotheses as dependent strategy sections and permit only "
                "risk-certified inhabitants to descend into order intents."
            )
            research_program = (
                "Search for candidate alphas on local market charts, reject cocycle-breaking "
                "signals, and keep the surviving section as the discovered idea."
            )
            proof_target = (
                "Prove the sizing, limits, and execution core preserves leverage, drawdown, "
                "and exposure invariants under composition."
            )
        else:
            ag_view = (
                "Treat the design as a Grothendieck cover whose local charts refine the problem "
                "until the resulting sections glue into one coherent implementation."
            )
            typed_view = (
                "Represent each local chart as a typed module with refinement obligations that "
                "must hold before integration."
            )
            research_program = (
                "Generate local design candidates, keep the ones that glue on overlaps, and "
                "promote the coherent family into the final architecture."
            )
            proof_target = (
                "Prove the risk- or correctness-critical core respects the refinement invariants "
                "exposed by the cover."
            )
        return {
            "headline": headline,
            "thesis": novel_idea,
            "domains": ", ".join(domains),
            "ag_view": ag_view,
            "typed_view": typed_view,
            "scalar_valued_typing": scalar_summary,
            "research_program": research_program,
            "proof_target": proof_target,
            "h1_hint": str(getattr(ideation, "h1_dimension", "unknown")),
        }

    @staticmethod
    def _fallback_class_specs(
        module_name: str,
        ideation_lenses: List[Dict[str, Any]],
    ) -> List[Dict[str, Any]]:
        prefix = AgentCLI._camel_case(module_name)
        local_models: List[str] = []
        transport_maps: List[str] = []
        invariants: List[str] = []
        certification_targets: List[str] = []
        for lens in ideation_lenses[:3]:
            local_models.extend(str(item) for item in lens.get("local_models", [])[:3])
            transport_maps.extend(str(item) for item in lens.get("transport_maps", [])[:3])
            invariants.extend(str(item) for item in lens.get("invariants", [])[:3])
            certification_targets.extend(
                str(item) for item in lens.get("certification_targets", [])[:2]
            )
        if not invariants:
            invariants = [
                str(lens.get("label", ""))
                for lens in ideation_lenses[:3]
                if str(lens.get("label", "")).strip()
            ]
        return [
            {
                "name": f"{prefix}Section",
                "role": "Typed local-section state object for the module.",
                "fields": [
                    "local_models: Dict[str, Any]",
                    "invariant_witnesses: Dict[str, Any]",
                ]
                + (["metadata: Dict[str, Any]"] if local_models else []),
                "invariants": invariants,
                "local_models": local_models[:4],
                "certification_targets": certification_targets[:3],
            },
            {
                "name": f"{prefix}Transport",
                "role": "Typed transport/gluing object for the module.",
                "fields": [
                    "dependencies: List[str]",
                    "transport_rules: Dict[str, Any]",
                ],
                "invariants": invariants,
                "transport_maps": transport_maps[:4],
                "certification_targets": certification_targets[:3],
            },
        ]

    @staticmethod
    def _fallback_function_specs(
        module_name: str,
        ideation_lenses: List[Dict[str, Any]],
    ) -> List[Dict[str, Any]]:
        invariants: List[str] = []
        theorems: List[str] = []
        equations: List[str] = []
        certification_targets: List[str] = []
        for lens in ideation_lenses[:3]:
            invariants.extend(str(item) for item in lens.get("invariants", [])[:3])
            theorems.extend(
                str(item.get("name", ""))
                for item in lens.get("theorem_schemas", [])[:2]
                if isinstance(item, dict) and str(item.get("name", "")).strip()
            )
            equations.extend(
                str(item.get("latex", ""))
                for item in lens.get("canonical_equations", [])[:2]
                if isinstance(item, dict) and str(item.get("latex", "")).strip()
            )
            certification_targets.extend(
                str(item) for item in lens.get("certification_targets", [])[:2]
            )
        if not invariants:
            invariants = [
                str(lens.get("label", ""))
                for lens in ideation_lenses[:3]
                if str(lens.get("label", "")).strip()
            ]
        return [
            {
                "name": f"build_{module_name}",
                "signature": "(payload: Dict[str, Any]) -> Dict[str, Any]",
                "purpose": f"Build the typed {module_name} module result.",
                "invariants": invariants,
                "theorem_schema": theorems[:1],
                "canonical_equation": equations[:1],
                "certification_target": certification_targets[:1],
            },
            {
                "name": f"validate_{module_name}",
                "signature": "(payload: Dict[str, Any]) -> bool",
                "purpose": f"Validate invariants for {module_name}.",
                "invariants": invariants,
                "theorem_schema": theorems[1:2] or theorems[:1],
                "canonical_equation": equations[1:2] or equations[:1],
                "certification_target": certification_targets[1:2] or certification_targets[:1],
            },
        ]

    @staticmethod
    def _typed_surface_preview(
        specs: List[Dict[str, Any]],
        *,
        kind: str,
        limit: int,
    ) -> str:
        lines: List[str] = []
        for spec in specs[:limit]:
            name = str(spec.get("name", kind))
            role = str(spec.get("role") or spec.get("purpose") or "")
            signature = str(spec.get("signature", ""))
            extras: List[str] = []
            if signature:
                extras.append(signature)
            invariants = spec.get("invariants", [])
            if isinstance(invariants, list) and invariants:
                extras.append(
                    "invariants=" + ", ".join(str(item) for item in invariants[:3])
                )
            theorems = spec.get("theorem_schema", [])
            if isinstance(theorems, list) and theorems:
                extras.append("theorem=" + ", ".join(str(item) for item in theorems[:1]))
            equations = spec.get("canonical_equation", [])
            if isinstance(equations, list) and equations:
                extras.append("equation=" + ", ".join(str(item) for item in equations[:1]))
            certs = spec.get("certification_target", [])
            if isinstance(certs, list) and certs:
                extras.append("certify=" + ", ".join(str(item) for item in certs[:1]))
            local_models = spec.get("local_models", [])
            if isinstance(local_models, list) and local_models:
                extras.append("locals=" + ", ".join(str(item) for item in local_models[:2]))
            transport_maps = spec.get("transport_maps", [])
            if isinstance(transport_maps, list) and transport_maps:
                extras.append("transport=" + ", ".join(str(item) for item in transport_maps[:2]))
            class_certs = spec.get("certification_targets", [])
            if isinstance(class_certs, list) and class_certs:
                extras.append("targets=" + ", ".join(str(item) for item in class_certs[:1]))
            detail = " | ".join(part for part in extras if part)
            if detail and role:
                lines.append(f"- {name}: {role} [{detail}]")
            elif detail:
                lines.append(f"- {name}: {detail}")
            else:
                lines.append(f"- {name}: {role}")
        return "\n".join(lines) + ("\n" if lines else "")

    def _math_area_selection(self, intent: Dict[str, Any], prompt: str) -> Dict[str, Any]:
        lowered = " ".join(
            str(part).lower()
            for part in (
                intent.get("domain", ""),
                intent.get("description", ""),
                prompt,
            )
        )
        explicit_all_math = any(
            cue in lowered
            for cue in (
                "all domains of math",
                "all of the domains of math",
                "all domains",
                "all of math",
            )
        )
        try:
            from deppy.hybrid.ideation.math_ontology_loader import (
                all_math_terms,
                ontology_summary,
                select_math_areas,
            )
        except Exception:
            return {
                "math_area_count": 0,
                "math_term_count": 0,
                "selected_math_areas": [],
                "selected_area_objects": [],
                "mode": "unavailable",
                "explicit_all_math": explicit_all_math,
            }

        selected_area_objects = list(
            select_math_areas(lowered, limit=12, include_all=False)
        )
        summary = ontology_summary()
        return {
            "math_area_count": int(summary["area_count"]),
            "math_term_count": len(all_math_terms()),
            "selected_math_areas": [str(area.get("name", "")) for area in selected_area_objects],
            "selected_area_objects": selected_area_objects,
            "mode": "all_500" if explicit_all_math else "targeted_500",
            "explicit_all_math": explicit_all_math,
            "ontology_summary": {
                "root": summary["root"],
                "category_count": summary["category_count"],
                "area_count": summary["area_count"],
                "term_count": summary["term_count"],
                "path": summary["path"],
            },
        }

    @staticmethod
    def _baseline_ideation_domains(intent: Dict[str, Any], prompt: str) -> List[str]:
        lowered = f"{intent.get('domain', '')} {intent.get('description', '')} {prompt}".lower()
        domains = ["type_theory", "algebraic_geometry", "formal_verification"]
        if any(token in lowered for token in ("trad", "market", "portfolio", "signal")):
            domains.append("machine_learning")
        return domains

    def _llm_guided_ideation_focus(
        self,
        intent: Dict[str, Any],
        prompt: str,
        math_area_selection: Dict[str, Any],
    ) -> Optional[Dict[str, Any]]:
        if self._llm is None:
            return None
        candidate_areas = math_area_selection.get("selected_math_areas", [])
        ontology_summary = math_area_selection.get("ontology_summary", {})
        try:
            from deppy.hybrid.ideation.domain_site import REGISTRY
            available_domains = REGISTRY.all_domains()
        except Exception:
            available_domains = self._ideation_domains(intent, prompt)

        schema = {
            "type": "object",
            "properties": {
                "registry_domains": {
                    "type": "array",
                    "items": {"type": "string"},
                },
                "math_areas": {
                    "type": "array",
                    "items": {"type": "string"},
                },
                "reasoning": {
                    "type": "array",
                    "items": {"type": "string"},
                },
                "idea_strength": {"type": "number"},
                "math_area_strengths": {
                    "type": "array",
                    "items": {
                        "type": "object",
                        "properties": {
                            "area": {"type": "string"},
                            "score": {"type": "number"},
                            "rationale": {"type": "string"},
                        },
                    },
                },
            },
        }
        selection_prompt = (
            "Select mathematically relevant lenses for deppy ideation.\n\n"
            f"Problem: {intent.get('description') or prompt}\n"
            f"Available registry domains: {available_domains}\n"
            f"Ontology summary: {ontology_summary}\n"
            f"Candidate math areas: {candidate_areas[:16]}\n\n"
            "Choose 3-6 registry domains and 4-10 math areas that are likely to "
            "yield structural, testable analogies inside the deppy ideation "
            "framework. Do not default to algebraic_geometry or type_theory "
            "unless they are genuinely relevant; include non-AG/DTT areas when "
            "they better explain the problem. Treat the result as scalar-valued typing: "
            "assign an idea_strength scalar between 0.0 and 1.0 for how strong the "
            "overall type elaboration is for this domain, and optionally per-area scores. "
            "Return JSON only."
        )
        try:
            payload = self._llm.complete_json(selection_prompt, schema)
        except Exception:
            return None
        if not isinstance(payload, dict):
            return None
        raw_domains = payload.get("registry_domains", [])
        registry_domains = [
            str(domain)
            for domain in raw_domains
            if str(domain) in available_domains
        ]
        if not registry_domains:
            return None
        math_areas = [
            str(area)
            for area in payload.get("math_areas", [])
            if str(area).strip()
        ]
        reasoning = [
            str(reason)
            for reason in payload.get("reasoning", [])
            if str(reason).strip()
        ]
        idea_strength = payload.get("idea_strength")
        if not isinstance(idea_strength, (int, float)):
            idea_strength = None
        raw_strengths = payload.get("math_area_strengths", [])
        area_strengths = []
        if isinstance(raw_strengths, list):
            for item in raw_strengths[:10]:
                if not isinstance(item, dict):
                    continue
                area = str(item.get("area", "")).strip()
                score = item.get("score")
                if not area or not isinstance(score, (int, float)):
                    continue
                area_strengths.append(
                    {
                        "area": area,
                        "score": max(0.0, min(1.0, float(score))),
                        "rationale": str(item.get("rationale", "")).strip(),
                    }
                )
        return {
            "mode": "llm_guided",
            "registry_domains": self._ordered_unique_modules(registry_domains),
            "math_areas": math_areas[:10] or candidate_areas[:10],
            "reasoning": reasoning[:6],
            "idea_strength": (
                max(0.0, min(1.0, float(idea_strength)))
                if idea_strength is not None
                else None
            ),
            "math_area_strengths": area_strengths,
        }

    @staticmethod
    def _evaluate_ideation_benefit(
        baseline: Any,
        guided: Any,
    ) -> Dict[str, Any]:
        def _score(result: Any) -> int:
            return (
                int(getattr(result, "analogies_validated", 0))
                + 2 * len(getattr(result, "deep_analogies", []))
                + len(getattr(result, "novel_connections", []))
                - int(getattr(result, "h1_dimension", 0))
            )

        baseline_score = _score(baseline)
        guided_score = _score(guided)
        score_delta = guided_score - baseline_score
        h1_improvement = int(getattr(baseline, "h1_dimension", 0)) - int(
            getattr(guided, "h1_dimension", 0)
        )
        better = score_delta > 0 or h1_improvement > 0
        return {
            "baseline_score": baseline_score,
            "guided_score": guided_score,
            "score_delta": score_delta,
            "validated_delta": int(getattr(guided, "analogies_validated", 0))
            - int(getattr(baseline, "analogies_validated", 0)),
            "deep_analogies_delta": len(getattr(guided, "deep_analogies", []))
            - len(getattr(baseline, "deep_analogies", [])),
            "novel_connections_delta": len(getattr(guided, "novel_connections", []))
            - len(getattr(baseline, "novel_connections", [])),
            "h1_improvement": h1_improvement,
            "guided_advantage": better,
            "framework_certificate": (
                "LLM-guided selection improved deppy ideation metrics over the "
                "typical baseline."
                if better
                else "LLM-guided selection did not beat the typical baseline on "
                "the current deppy metrics."
            ),
        }

    @staticmethod
    def _trim_math_area_detail(area: Dict[str, Any]) -> Dict[str, Any]:
        theorems = []
        for theorem in area.get("key_theorems", [])[:3]:
            if not isinstance(theorem, dict):
                continue
            theorems.append(
                {
                    "name": str(theorem.get("name", "")),
                    "statement": str(theorem.get("statement", "")),
                    "idea_seed": str(theorem.get("idea_seed", "")),
                }
            )
        equations = []
        for equation in area.get("canonical_equations", [])[:3]:
            if not isinstance(equation, dict):
                continue
            equations.append(
                {
                    "name": str(equation.get("name", "")),
                    "latex": str(equation.get("latex", "")),
                    "meaning": str(equation.get("meaning", "")),
                }
            )
        return {
            "name": str(area.get("name", "")),
            "category": str(area.get("category", "")),
            "family": str(area.get("family", "")),
            "summary": str(area.get("summary", "")),
            "core_idea": str(area.get("core_idea", "")),
            "ag_view": str(area.get("ag_view", "")),
            "dtt_view": str(area.get("dtt_view", "")),
            "bridge_domains": [str(item) for item in area.get("bridge_domains", [])[:6]],
            "key_objects": [str(item) for item in area.get("key_objects", [])[:6]],
            "key_morphisms": [str(item) for item in area.get("key_morphisms", [])[:6]],
            "key_invariants": [str(item) for item in area.get("key_invariants", [])[:6]],
            "key_theorems": theorems,
            "canonical_equations": equations,
            "certification_targets": [str(item) for item in area.get("certification_targets", [])[:5]],
            "idea_seeds": [
                str(seed.get("prompt", ""))
                for seed in area.get("idea_seeds", [])[:3]
                if isinstance(seed, dict) and str(seed.get("prompt", "")).strip()
            ],
        }

    @staticmethod
    def _clamp01(value: float) -> float:
        return max(0.0, min(1.0, float(value)))

    @classmethod
    def _scalar_valued_typing(
        cls,
        *,
        guided_selection: Optional[Dict[str, Any]],
        ideation: Any,
        proposals: List[Any],
        selected_area_details: List[Dict[str, Any]],
        benefit_evaluation: Dict[str, Any],
        domains: List[str],
    ) -> Dict[str, Any]:
        proposal_conf = 0.0
        if proposals:
            proposal_conf = max(
                float(getattr(proposal, "confidence", 0.0) or 0.0)
                for proposal in proposals[:3]
            )
        area_strength_map = {}
        llm_area_strengths = []
        if isinstance(guided_selection, dict):
            llm_area_strengths = list(guided_selection.get("math_area_strengths", []))
            for item in llm_area_strengths:
                if isinstance(item, dict):
                    area_strength_map[str(item.get("area", "")).strip().lower()] = item

        llm_belief = (
            float(guided_selection.get("idea_strength"))
            if isinstance(guided_selection, dict)
            and isinstance(guided_selection.get("idea_strength"), (int, float))
            else 0.55 + 0.25 * proposal_conf + 0.03 * min(len(domains), 5)
        )
        llm_belief = cls._clamp01(llm_belief)

        math_model = cls._clamp01(
            0.42
            + 0.06 * int(getattr(ideation, "analogies_validated", 0))
            + 0.07 * len(getattr(ideation, "deep_analogies", []))
            + 0.04 * len(getattr(ideation, "novel_connections", []))
            - 0.05 * int(getattr(ideation, "h1_dimension", 0))
            + 0.04 * (1.0 if benefit_evaluation.get("guided_advantage") else 0.0)
        )

        area_scores = []
        for index, area in enumerate(selected_area_details[:10]):
            if not isinstance(area, dict):
                continue
            area_name = str(area.get("name", "")).strip()
            key = area_name.lower()
            llm_item = area_strength_map.get(key, {})
            llm_score = (
                float(llm_item.get("score"))
                if isinstance(llm_item, dict) and isinstance(llm_item.get("score"), (int, float))
                else cls._clamp01(llm_belief - 0.04 * index)
            )
            math_score = cls._clamp01(
                0.38
                + 0.05 * min(len(area.get("bridge_domains", [])), 4)
                + 0.03 * min(len(area.get("key_invariants", [])), 4)
                + 0.03 * min(len(area.get("key_theorems", [])), 3)
                + 0.02 * min(len(area.get("certification_targets", [])), 3)
                - 0.02 * index
            )
            area_scores.append(
                {
                    "area": area_name,
                    "llm_belief": round(cls._clamp01(llm_score), 3),
                    "math_model": round(math_score, 3),
                    "overall": round(cls._clamp01(0.55 * llm_score + 0.45 * math_score), 3),
                    "rationale": (
                        str(llm_item.get("rationale", "")).strip()
                        if isinstance(llm_item, dict)
                        else ""
                    ),
                }
            )

        overall = cls._clamp01(
            0.55 * llm_belief
            + 0.45 * math_model
            + 0.05 * max((item["overall"] for item in area_scores), default=0.0)
        )
        return {
            "label": "scalar-valued typing",
            "definition": (
                "Assign a scalar score to the current type elaboration by combining the "
                "LLM's belief that the idea fits the domain with the mathematical model's "
                "evidence that the elaboration is structurally rich and certifiable."
            ),
            "scoring_rule": (
                "overall = clamp(0.55 * llm_belief + 0.45 * math_model + "
                "0.05 * max_area_strength)"
            ),
            "overall": round(overall, 3),
            "llm_belief": round(llm_belief, 3),
            "math_model": round(math_model, 3),
            "domain_fit": round(cls._clamp01((llm_belief + math_model) / 2.0), 3),
            "elaboration_strength": round(overall, 3),
            "area_strengths": area_scores,
        }

    @classmethod
    def _selected_math_area_details(
        cls,
        area_names: List[str],
    ) -> List[Dict[str, Any]]:
        try:
            from deppy.hybrid.ideation.math_ontology_loader import resolve_math_areas
        except Exception:
            return []
        return [cls._trim_math_area_detail(area) for area in resolve_math_areas(area_names)]

    @staticmethod
    def _ideation_lenses(intent: Dict[str, Any]) -> List[Dict[str, Any]]:
        ideation = intent.get("ideation", {})
        if not isinstance(ideation, dict):
            return []
        selection = ideation.get("selection_strategy", {})
        scalar_typing = ideation.get("scalar_valued_typing", {})
        area_strengths = (
            {
                str(item.get("area", "")).strip().lower(): item
                for item in scalar_typing.get("area_strengths", [])
                if isinstance(item, dict)
            }
            if isinstance(scalar_typing, dict)
            else {}
        )
        guided_domains = (
            list(selection.get("guided_domains", []))
            if isinstance(selection, dict)
            else []
        )
        guided_math_areas = (
            list(selection.get("guided_math_areas", []))
            if isinstance(selection, dict)
            else list(ideation.get("selected_math_areas", []))
        )
        deep_analogies = [str(item) for item in ideation.get("deep_analogies", [])]
        benefit = ideation.get("benefit_evaluation", {})
        lenses: List[Dict[str, Any]] = []
        if isinstance(scalar_typing, dict) and scalar_typing:
            lenses.append(
                {
                    "kind": "scalar_valued_typing",
                    "label": str(scalar_typing.get("label", "scalar-valued typing")),
                    "typed_role": str(
                        scalar_typing.get(
                            "definition",
                            "Scalar-valued typing scores how well the current elaboration fits the domain.",
                        )
                    ),
                    "score_formula": str(scalar_typing.get("scoring_rule", "")),
                    "scalar_weight": float(scalar_typing.get("overall", 0.5)),
                }
            )
        for domain in guided_domains[:6]:
            lenses.append(
                {
                    "kind": "registry_domain",
                    "label": str(domain),
                    "typed_role": f"Cross-domain ideation site from {domain}.",
                    "scalar_weight": (
                        float(scalar_typing.get("overall", 0.5))
                        if isinstance(scalar_typing, dict)
                        else 0.5
                    ),
                }
            )
        area_details = ideation.get("selected_math_area_details", [])
        if not isinstance(area_details, list) or not area_details:
            area_details = AgentCLI._selected_math_area_details(guided_math_areas[:8])
        for area in area_details[:8]:
            if not isinstance(area, dict):
                continue
            lenses.append(
                {
                    "kind": "math_area",
                    "label": str(area.get("name", "")),
                    "source_area": str(area.get("name", "")),
                    "category": str(area.get("category", "")),
                    "family": str(area.get("family", "")),
                    "summary": str(area.get("summary", "")),
                    "typed_role": str(area.get("dtt_view") or area.get("core_idea") or ""),
                    "local_models": [str(item) for item in area.get("key_objects", [])[:6]],
                    "transport_maps": [str(item) for item in area.get("key_morphisms", [])[:6]],
                    "invariants": [str(item) for item in area.get("key_invariants", [])[:6]],
                    "theorem_schemas": [
                        dict(item) for item in area.get("key_theorems", [])[:3] if isinstance(item, dict)
                    ],
                    "canonical_equations": [
                        dict(item)
                        for item in area.get("canonical_equations", [])[:3]
                        if isinstance(item, dict)
                    ],
                    "certification_targets": [
                        str(item) for item in area.get("certification_targets", [])[:5]
                    ],
                    "bridge_domains": [str(item) for item in area.get("bridge_domains", [])[:6]],
                    "idea_seeds": [str(item) for item in area.get("idea_seeds", [])[:3]],
                    "scalar_weight": float(
                        area_strengths.get(
                            str(area.get("name", "")).strip().lower(),
                            {},
                        ).get("overall", scalar_typing.get("overall", 0.5) if isinstance(scalar_typing, dict) else 0.5)
                    ),
                }
            )
        for analogy in deep_analogies[:3]:
            lenses.append(
                {
                    "kind": "deep_analogy",
                    "label": analogy,
                    "typed_role": "Validated analogy carried into elaboration as a structural guide.",
                    "scalar_weight": (
                        float(scalar_typing.get("overall", 0.5))
                        if isinstance(scalar_typing, dict)
                        else 0.5
                    ),
                }
            )
        if isinstance(benefit, dict) and benefit:
            lenses.append(
                {
                    "kind": "benefit_certificate",
                    "label": str(benefit.get("framework_certificate", "")),
                    "typed_role": "Framework-native evidence that the guided ideation improves over baseline.",
                    "scalar_weight": (
                        float(scalar_typing.get("overall", 0.5))
                        if isinstance(scalar_typing, dict)
                        else 0.5
                    ),
                }
            )
        return lenses

    def _ideation_domains(self, intent: Dict[str, Any], prompt: str) -> List[str]:
        lowered = " ".join(
            str(part).lower()
            for part in (
                intent.get("domain", ""),
                intent.get("description", ""),
                prompt,
            )
        )
        try:
            from deppy.hybrid.ideation.domain_site import REGISTRY
            available = REGISTRY.all_domains()
        except Exception:
            available = [
                "algebraic_geometry",
                "category_theory",
                "formal_verification",
                "machine_learning",
                "software_engineering",
                "type_theory",
            ]

        scores = {domain: 0 for domain in available}
        preferred_order = [
            "algebraic_geometry",
            "category_theory",
            "type_theory",
            "formal_verification",
            "machine_learning",
            "software_engineering",
            "linguistics",
        ]
        keyword_map = {
            "algebraic_geometry": (
                "geometry",
                "sheaf",
                "cohomology",
                "descent",
                "glue",
                "gluing",
                "cover",
                "topology",
                "regime",
            ),
            "category_theory": (
                "category",
                "functor",
                "natural transformation",
                "morphism",
                "compositional",
                "composition",
                "diagram",
            ),
            "type_theory": (
                "type",
                "typed",
                "dependent",
                "lambda",
                "elaboration",
                "proof term",
                "calculus",
            ),
            "formal_verification": (
                "verify",
                "verified",
                "proof",
                "prove",
                "soundness",
                "safety",
                "invariant",
                "refinement",
                "certificate",
            ),
            "machine_learning": (
                "learn",
                "learning",
                "model",
                "predict",
                "signal",
                "alpha",
                "market",
                "data",
                "pattern",
            ),
            "software_engineering": (
                "system",
                "architecture",
                "service",
                "module",
                "pipeline",
                "orchestration",
                "integration",
                "api",
            ),
            "linguistics": (
                "language",
                "semantics",
                "syntax",
                "grammar",
                "intent",
            ),
        }
        math_domains = {
            "algebraic_geometry",
            "category_theory",
            "type_theory",
            "formal_verification",
        }

        math_area_selection = self._math_area_selection(intent, prompt)
        explicit_all_math = bool(math_area_selection["explicit_all_math"])
        math_heavy_prompt = any(
            cue in lowered
            for cue in ("math", "mathemat", "theorem", "cohomology", "category", "geometry")
        )

        for domain, cues in keyword_map.items():
            if domain not in scores:
                continue
            for cue in cues:
                if cue in lowered:
                    scores[domain] += 2 if " " in cue else 1
        for area in math_area_selection["selected_area_objects"]:
            for domain in area.get("bridge_domains", []):
                if domain in scores:
                    scores[domain] += 2

        if "trad" in lowered or any(token in lowered for token in ("market", "portfolio", "risk")):
            for domain, bonus in (
                ("machine_learning", 4),
                ("formal_verification", 3),
                ("algebraic_geometry", 3),
                ("category_theory", 2),
                ("software_engineering", 2),
                ("type_theory", 1),
            ):
                if domain in scores:
                    scores[domain] += bonus

        if math_heavy_prompt or explicit_all_math:
            for domain in math_domains:
                if domain in scores:
                    scores[domain] += 3

        if explicit_all_math:
            ordered = sorted(
                available,
                key=lambda domain: (
                    0 if domain in math_domains else 1,
                    -scores[domain],
                    preferred_order.index(domain)
                    if domain in preferred_order
                    else len(preferred_order),
                    domain,
                ),
            )
            return ordered

        selected = [
            domain
            for domain in sorted(
                available,
                key=lambda domain: (
                    -scores[domain],
                    preferred_order.index(domain)
                    if domain in preferred_order
                    else len(preferred_order),
                    domain,
                ),
            )
            if scores[domain] > 0
        ]
        minimum_cover = [
            domain
            for domain in preferred_order
            if domain in available and (domain in math_domains or domain == "machine_learning")
        ]
        for domain in minimum_cover:
            if domain not in selected:
                selected.append(domain)
            if len(selected) >= 5:
                break
        return selected[:6]

    @staticmethod
    def _select_novel_idea(
        problem: str,
        ideation: Any,
        proposals: List[Any],
    ) -> str:
        """Pick a concrete novel idea from ideation output."""
        if proposals:
            proposal = proposals[0]
            if getattr(proposal, "description", ""):
                return str(proposal.description)
            if getattr(proposal, "name", ""):
                return f"Use the extension proposal {proposal.name!s}."

        if getattr(ideation, "unified_insights", None):
            for insight in ideation.unified_insights:
                if insight:
                    return str(insight)

        lowered = problem.lower()
        if "trad" in lowered:
            return (
                "Treat market regimes as a Grothendieck cover and trade only "
                "when local signals glue into a globally coherent strategy section."
            )
        return (
            "Introduce a topology-aware decomposition whose local proofs glue "
            "into one globally coherent implementation."
        )

    def _generate_module(
        self,
        intent: Dict[str, Any],
        module_name: str,
    ) -> Dict[str, Any]:
        """Generate source code for a module using the LLM."""
        assert self._llm is not None

        module_plan = self._module_plan(intent, module_name)
        llm_is_copilot = isinstance(self._llm, CopilotCLIInterface)
        module_pattern = self._module_generation_pattern(intent, module_name)
        full_mode = bool(intent.get("full_mode"))
        responsibility_preview = self._prompt_list_preview(
            module_plan["responsibilities"],
            limit=3 if llm_is_copilot else 6,
            max_chars=320 if llm_is_copilot else 720,
        )
        dependency_preview = self._prompt_list_preview(
            module_plan["depends_on"],
            limit=4 if llm_is_copilot else 6,
            max_chars=160 if llm_is_copilot else 240,
        )
        export_preview = self._prompt_list_preview(
            module_plan["exports"],
            limit=4 if llm_is_copilot else 6,
            max_chars=180 if llm_is_copilot else 240,
        )
        import_preview = self._prompt_list_preview(
            module_plan.get("imports", []),
            limit=4 if llm_is_copilot else 8,
            max_chars=180 if llm_is_copilot else 320,
        )
        class_preview = self._typed_surface_preview(
            module_plan.get("class_specs", []),
            kind="class",
            limit=2 if llm_is_copilot else 4,
        )
        function_preview = self._typed_surface_preview(
            module_plan.get("function_specs", []),
            kind="function",
            limit=3 if llm_is_copilot else 6,
        )
        constraint_preview = self._prompt_list_preview(
            intent.get("constraints", []),
            limit=3 if llm_is_copilot else 6,
            max_chars=260 if llm_is_copilot else 720,
        )
        gen_prompt = (
            f"You are implementing one module of a larger typed software system.\n\n"
            f"Write a complete Python module named '{module_name}'.\n"
            f"Project: {intent.get('description', '')}\n"
            f"Domain: {intent.get('domain', 'general')}\n"
            f"Module pattern: {module_pattern}\n"
            f"Module summary: {module_plan['summary']}\n"
            f"Responsibilities: {responsibility_preview}\n"
            f"Dependencies: {dependency_preview}\n"
            f"Exports: {export_preview}\n"
            f"Imports: {import_preview}\n"
            f"Desired classes:\n{class_preview}"
            f"Desired functions:\n{function_preview}"
            f"Estimated LOC budget for this module: {module_plan.get('estimated_loc', 120)}\n"
            f"Constraints: {constraint_preview}\n\n"
            "Implementation requirements:\n"
            "- Produce only valid Python source code. No markdown fences.\n"
            "- Include a module docstring that explains the typed intent and module role.\n"
            "- Include multiple concrete dataclasses/classes/functions with real logic.\n"
            "- Realize the desired typed classes and functions, not just generic scaffolding.\n"
            "- Use type annotations on all public functions and methods.\n"
            '- Include deppy verification annotations as comments: # @require(\"...\"), # @ensure(\"...\"), # @invariant(\"...\").\n'
            "- Avoid placeholders, TODOs, and bare pass statements.\n"
            "- Aim for a complete, substantial implementation rather than a stub.\n"
        )
        if full_mode:
            gen_prompt += (
                "- This is --full mode for a large-scale system.\n"
                + (
                    "- Focus only on this module; do not attempt the whole system architecture in one file.\n"
                    if llm_is_copilot
                    else ""
                )
                + f"- Make this module feel like a substantial slice sized toward ~{module_plan.get('estimated_loc', 120)} LOC.\n"
                + (
                    ""
                    if llm_is_copilot
                    else "- Include collaborating helper types, adaptation utilities, audit surfaces, and verification seams.\n"
                )
            )

        ideation = intent.get("ideation")
        if isinstance(ideation, dict):
            novel_idea = ideation.get("novel_idea")
            if novel_idea:
                gen_prompt += (
                    "\n\nIdeation-as-typing requirements:\n"
                    + (
                        f"- Typed focus for this module: {module_pattern}\n"
                        if llm_is_copilot
                        else f"- Novel idea to realize: {novel_idea}\n"
                    )
                )
            deep_analogies = ideation.get("deep_analogies", [])
            if deep_analogies and not llm_is_copilot:
                gen_prompt += (
                    "- Deep analogies to respect:\n"
                    + "\n".join(f"  * {item}" for item in deep_analogies[:3])
                    + "\n"
                )
            novelty_packet = ideation.get("novel_idea_structured", {})
            if isinstance(novelty_packet, dict) and novelty_packet and not llm_is_copilot:
                gen_prompt += (
                    "- Structured novelty packet:\n"
                    + "\n".join(
                        f"  * {key}: {value}"
                        for key, value in novelty_packet.items()
                        if key in {"headline", "ag_view", "typed_view", "proof_target"}
                    )
                    + "\n"
                )

        orchestration = intent.get("orchestration")
        if isinstance(orchestration, dict):
            overlaps = orchestration.get("overlaps", [])
            relevant = [
                overlap["obligation"]
                for overlap in overlaps
                if module_name in (overlap.get("left"), overlap.get("right"))
            ]
            gluing = orchestration.get("gluing_obligations", [])
            gen_prompt += (
                "\nTyped orchestration requirements:\n"
                + (
                    "- Module-local obligations only.\n"
                    if llm_is_copilot
                    else "- Module order context: "
                    + f"{self._module_order_context(orchestration.get('module_order', []), module_name)}\n"
                )
            )
            geometry_view = orchestration.get("algebraic_geometry_view")
            if geometry_view and not llm_is_copilot:
                gen_prompt += f"- Algebraic-geometry view: {geometry_view}\n"
            tree = orchestration.get("type_elaboration_tree", {})
            path = self._module_tree_path(tree, module_name)
            if path and not llm_is_copilot:
                gen_prompt += f"- Type elaboration path: {' -> '.join(path)}\n"
            if relevant:
                gen_prompt += (
                    "- Overlap obligations for this module:\n"
                    + self._prompt_bullet_preview(relevant, limit=2 if llm_is_copilot else 6)
                )
            if gluing and not llm_is_copilot:
                gen_prompt += (
                    "- Global gluing obligations:\n"
                    + self._prompt_bullet_preview(gluing, limit=4)
                )
        test_obligations = module_plan.get("test_obligations", [])
        if test_obligations:
            gen_prompt += (
                "- Test obligations to cover:\n"
                + self._prompt_bullet_preview(test_obligations, limit=6)
            )

        try:
            source = self._sanitize_python_source(self._llm.complete(gen_prompt))
        except Exception as exc:
            logger.warning(
                "Module generation failed for %s: %s — using scaffold fallback",
                module_name,
                exc,
            )
            source = self._render_module_scaffold(module_name, module_plan, intent)
        issues = self._module_quality_issues(source)
        attempts = 0
        max_refinements = 3 if full_mode else 2
        if llm_is_copilot:
            max_refinements = 0
        while issues and attempts < max_refinements:
            refine_prompt = (
                f"The previous draft for module '{module_name}' is too shallow or invalid.\n"
                f"Issues to fix:\n- " + "\n- ".join(issues) + "\n\n"
                f"Project: {intent.get('description', '')}\n"
                f"Domain: {intent.get('domain', 'general')}\n"
                f"Module summary: {module_plan['summary']}\n"
                f"Responsibilities: {responsibility_preview}\n"
                f"Dependencies: {dependency_preview}\n"
                f"Exports: {export_preview}\n\n"
                f"Previous draft:\n\n{source}\n\n"
                "Rewrite it into a longer, concrete, production-style Python module.\n"
                f"Aim for roughly {module_plan.get('estimated_loc', 120)} lines of substantive implementation.\n"
                "Produce only valid Python source code."
            )
            try:
                source = self._sanitize_python_source(self._llm.complete(refine_prompt))
            except Exception as exc:
                logger.warning(
                    "Refinement failed for %s: %s — using scaffold fallback",
                    module_name,
                    exc,
                )
                source = self._render_module_scaffold(module_name, module_plan, intent)
                break
            issues = self._module_quality_issues(source)
            attempts += 1
        if issues:
            source = self._render_module_scaffold(module_name, module_plan, intent)
        return {
            "source": source,
            "module_name": module_name,
            "intent": intent,
            "generation_prompt": gen_prompt,
        }

    @staticmethod
    def _sanitize_python_source(source: str) -> str:
        cleaned = source.strip()
        if not cleaned:
            return "\n"
        if cleaned.startswith("```"):
            lines = [
                line
                for line in cleaned.splitlines()
                if not line.strip().startswith("```")
            ]
            cleaned = "\n".join(lines).strip()

        lines = cleaned.splitlines()
        code_markers = (
            "from ",
            "import ",
            "class ",
            "def ",
            "async def ",
            "@",
            "\"\"\"",
            "'''",
            "#",
        )
        for index, line in enumerate(lines):
            stripped = line.strip()
            if stripped.startswith(code_markers) or re.match(r"[A-Za-z_][A-Za-z0-9_]*\s*=", stripped):
                cleaned = "\n".join(lines[index:]).strip()
                break
        else:
            lowered = cleaned.lower()
            prose_markers = (
                "i changed ",
                "validated with ",
                "fixed `",
                "that addresses ",
                "full suite ",
                "tests/test_",
                " passed",
            )
            if any(marker in lowered for marker in prose_markers):
                return "\n"
        return cleaned + "\n"

    def _module_plan(self, intent: Dict[str, Any], module_name: str) -> Dict[str, Any]:
        full_expansion = intent.get("full_expansion", {})
        ideation_lenses = self._ideation_lenses(intent)
        ideation_benefit = dict(intent.get("type_benefit", {})) if isinstance(
            intent.get("type_benefit", {}), dict
        ) else {}
        if isinstance(full_expansion, dict):
            global_plan = full_expansion.get("global_plan", {})
            candidate_modules: List[Dict[str, Any]] = []
            if isinstance(global_plan, dict):
                candidate_modules.extend(
                    node for node in global_plan.get("modules", []) if isinstance(node, dict)
                )
            candidate_modules.extend(
                node for node in full_expansion.get("modules", []) if isinstance(node, dict)
            )
            for node in candidate_modules:
                if str(node.get("name", "")) != module_name:
                    continue
                responsibilities = [str(item) for item in node.get("responsibilities", []) if item]
                responsibilities.extend(str(item) for item in intent.get("constraints", [])[:3])
                return {
                    "summary": str(node.get("summary") or module_name),
                    "responsibilities": self._ordered_unique_modules(responsibilities),
                    "depends_on": [str(item) for item in node.get("depends_on", [])],
                    "exports": [str(item) for item in node.get("exports", [])] or [
                        f"build_{module_name}",
                        f"validate_{module_name}",
                        f"{module_name}_summary",
                    ],
                    "imports": [str(item) for item in node.get("imports", [])],
                    "estimated_loc": int(node.get("estimated_loc", 240)),
                    "test_obligations": [str(item) for item in node.get("test_obligations", [])],
                    "class_specs": [dict(item) for item in node.get("class_specs", [])],
                    "function_specs": [dict(item) for item in node.get("function_specs", [])],
                    "ideation_lenses": [dict(item) for item in node.get("ideation_lenses", [])] or ideation_lenses,
                    "ideation_benefit": dict(node.get("ideation_benefit", {})) or ideation_benefit,
                }

        orchestration = intent.get("orchestration", {})
        overlaps = orchestration.get("overlaps", []) if isinstance(orchestration, dict) else []
        relevant = [
            overlap.get("obligation", "")
            for overlap in overlaps
            if module_name in (overlap.get("left"), overlap.get("right"))
        ]
        ordered = self._ordered_modules(intent)
        depends_on: List[str] = []
        for left, right in zip(ordered, ordered[1:]):
            if right == module_name:
                depends_on.append(left)
        responsibilities = [self._module_pattern(intent, module_name) or f"implement {module_name}"]
        responsibilities.extend(str(item) for item in relevant if item)
        responsibilities.extend(str(item) for item in intent.get("constraints", [])[:3])
        exports = [
            f"build_{module_name}",
            f"validate_{module_name}",
            f"{module_name}_summary",
        ]
        return {
            "summary": self._module_pattern(intent, module_name) or f"typed module for {module_name}",
            "responsibilities": responsibilities,
            "depends_on": depends_on,
            "exports": exports,
            "imports": [],
            "estimated_loc": 120,
            "test_obligations": [],
            "class_specs": self._fallback_class_specs(module_name, ideation_lenses),
            "function_specs": self._fallback_function_specs(module_name, ideation_lenses),
            "ideation_lenses": ideation_lenses,
            "ideation_benefit": ideation_benefit,
        }

    @staticmethod
    def _module_quality_issues(source: str) -> List[str]:
        issues: List[str] = []
        if not source.strip():
            return ["The module is empty."]
        lowered = source.lower()
        if any(
            marker in lowered
            for marker in (
                "i changed ",
                "validated with ",
                "fixed `",
                "the affected frozen dataclasses",
                "full suite ",
            )
        ):
            issues.append("Remove assistant commentary and return only Python source code.")
        if source.lstrip().startswith("# Mock response"):
            issues.append("Replace mock placeholder text with real Python code.")
        if source.count("\n") < 40:
            issues.append("Expand the implementation to include substantial logic.")
        try:
            tree = ast.parse(source)
        except SyntaxError as exc:
            return [f"Return syntactically valid Python ({exc.msg})."]

        function_count = sum(
            isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            for node in ast.walk(tree)
        )
        class_count = sum(isinstance(node, ast.ClassDef) for node in ast.walk(tree))
        pass_count = sum(isinstance(node, ast.Pass) for node in ast.walk(tree))
        if function_count + class_count < 4:
            issues.append("Include multiple classes and functions, not just one stub.")
        if ast.get_docstring(tree) is None:
            issues.append("Add a module docstring.")
        if pass_count > 1:
            issues.append("Replace placeholder pass statements with concrete logic.")
        return issues

    @staticmethod
    def _camel_case(name: str) -> str:
        parts = [part for part in name.replace("-", "_").split("_") if part]
        return "".join(part[:1].upper() + part[1:] for part in parts) or "Module"

    @staticmethod
    def _surface_doc_lines(spec: Dict[str, Any]) -> List[str]:
        lines: List[str] = []
        role = str(spec.get("role") or spec.get("purpose") or "").strip()
        if role:
            lines.append(role)
        signature = str(spec.get("signature", "")).strip()
        if signature:
            lines.append(f"Desired signature: {signature}")
        for key, label in (
            ("invariants", "Invariants"),
            ("local_models", "Local models"),
            ("transport_maps", "Transport maps"),
            ("theorem_schema", "Theorem schema"),
            ("canonical_equation", "Canonical equation"),
            ("certification_target", "Certification target"),
            ("certification_targets", "Certification targets"),
        ):
            value = spec.get(key, [])
            if isinstance(value, list) and value:
                lines.append(f"{label}: {', '.join(str(item) for item in value[:3])}")
        return lines

    def _render_spec_class_block(self, spec: Dict[str, Any]) -> str:
        name = str(spec.get("name", "TypedSurface"))
        fields = [str(item) for item in spec.get("fields", []) if str(item).strip()]
        if not fields:
            fields = ["payload: Dict[str, Any]", "metadata: Dict[str, Any]"]
        doc_lines = self._surface_doc_lines(spec) or ["Typed surface class."]
        field_lines = "\n".join(f"    {field}" for field in fields)
        invariant_literal = repr([str(item) for item in spec.get("invariants", [])[:4]])
        return (
            "@dataclass(frozen=True)\n"
            f"class {name}:\n"
            f'    """{" ".join(doc_lines)}"""\n\n'
            f"{field_lines}\n"
            f"    invariants: List[str] = field(default_factory=lambda: {invariant_literal})\n\n\n"
        )

    @staticmethod
    def _function_return_type(signature: str) -> str:
        lowered = signature.lower()
        if "-> bool" in lowered:
            return "bool"
        if "-> dict" in lowered:
            return "Dict[str, Any]"
        return "Dict[str, Any]"

    def _render_spec_function_block(
        self,
        spec: Dict[str, Any],
        *,
        class_prefix: str,
        module_name: str,
    ) -> str:
        name = str(spec.get("name", f"build_{module_name}"))
        return_type = self._function_return_type(str(spec.get("signature", "")))
        doc_lines = self._surface_doc_lines(spec) or ["Typed surface function."]
        if return_type == "bool":
            body = (
                f"    try:\n"
                f"        {class_prefix}Service().validate_request({class_prefix}Request(payload=payload))\n"
                f"    except (TypeError, ValueError):\n"
                f"        return False\n"
                f"    return True\n"
            )
        elif name.startswith("build_"):
            body = (
                f"    result = {class_prefix}Service().execute({class_prefix}Request(payload=payload))\n"
                f"    return result.artifacts\n"
            )
        else:
            body = (
                f"    return {{\n"
                f'        "module": "{module_name}",\n'
                f'        "function": "{name}",\n'
                f'        "payload_keys": sorted(str(key) for key in payload.keys()),\n'
                f'        "purpose": {repr(str(spec.get("purpose", "")))},\n'
                f"    }}\n"
            )
        return (
            f"def {name}(payload: Dict[str, Any]) -> {return_type}:\n"
            f'    """{" ".join(doc_lines)}"""\n'
            f"{body}\n"
        )

    def _render_module_scaffold(
        self,
        module_name: str,
        module_plan: Dict[str, Any],
        intent: Dict[str, Any],
    ) -> str:
        class_prefix = self._camel_case(module_name)
        role = self._module_pattern(intent, module_name) or module_plan["summary"]
        responsibilities = module_plan.get("responsibilities", [])
        depends_on = module_plan.get("depends_on", [])
        exports = module_plan.get("exports", [])
        constraint_comments = "\n".join(
            f"# - {item}" for item in intent.get("constraints", [])[:5]
        ) or "# - No additional constraints were captured."
        responsibility_doc = "\n".join(
            f"    - {item}" for item in responsibilities[:6]
        ) or "    - Implement the module role coherently."
        export_names = ", ".join(exports[:3]) or "build, validate, summarize"
        class_specs = [dict(item) for item in module_plan.get("class_specs", []) if isinstance(item, dict)]
        function_specs = [dict(item) for item in module_plan.get("function_specs", []) if isinstance(item, dict)]
        spec_class_blocks = "".join(self._render_spec_class_block(spec) for spec in class_specs[:4])
        rendered_functions: List[str] = []
        seen_function_names: set[str] = set()
        for spec in function_specs[:6]:
            name = str(spec.get("name", "")).strip()
            if not name or name in seen_function_names:
                continue
            seen_function_names.add(name)
            rendered_functions.append(
                self._render_spec_function_block(
                    spec,
                    class_prefix=class_prefix,
                    module_name=module_name,
                )
            )
        spec_function_blocks = "\n".join(rendered_functions)

        return (
            f'"""\n'
            f"{module_name}\n\n"
            f"Autonomous typed scaffold generated from iterative ideation/orchestration.\n\n"
            f"Module role: {role}\n"
            f"Dependencies: {depends_on}\n"
            f"Exports: {export_names}\n"
            f"Responsibilities:\n{responsibility_doc}\n"
            f'"""\n\n'
            f"from __future__ import annotations\n\n"
            f"from dataclasses import dataclass, field\n"
            f"from typing import Any, Dict, Iterable, List\n\n\n"
            f"{spec_class_blocks}"
            f"@dataclass(frozen=True)\n"
            f"class {class_prefix}Request:\n"
            f'    """Typed request entering the {module_name} module."""\n\n'
            f"    payload: Dict[str, Any]\n"
            f"    metadata: Dict[str, Any] = field(default_factory=dict)\n\n\n"
            f"@dataclass(frozen=True)\n"
            f"class {class_prefix}Result:\n"
            f'    """Typed result emitted by the {module_name} module."""\n\n'
            f"    ok: bool\n"
            f"    artifacts: Dict[str, Any]\n"
            f"    warnings: List[str] = field(default_factory=list)\n\n\n"
            f"class {class_prefix}Service:\n"
            f'    """Concrete service implementation for the {module_name} stage."""\n\n'
            f"    def __init__(self) -> None:\n"
            f"        self.responsibilities = {responsibilities[:6]!r}\n"
            f"        self.dependencies = {depends_on!r}\n\n"
            f"    # @require(\"non-empty\")\n"
            f"    def validate_request(self, request: {class_prefix}Request) -> None:\n"
            f"        payload = request.payload\n"
            f"        if not isinstance(payload, dict):\n"
            f'            raise TypeError(\"request payload must be a dictionary\")\n'
            f"        if not payload:\n"
            f'            raise ValueError(\"request payload cannot be empty\")\n\n'
            f"    # @ensure(\"returns list\")\n"
            f"    def plan_steps(self, request: {class_prefix}Request) -> list[str]:\n"
            f"        keys = sorted(str(key) for key in request.payload.keys())\n"
            f"        steps = [f\"inspect:{{key}}\" for key in keys]\n"
            f"        for responsibility in self.responsibilities:\n"
            f"            steps.append(f\"responsibility:{{responsibility}}\")\n"
            f"        return steps\n\n"
            f"    # @invariant(\"bounded\")\n"
            f"    def execute(self, request: {class_prefix}Request) -> {class_prefix}Result:\n"
            f"        self.validate_request(request)\n"
            f"        steps = self.plan_steps(request)\n"
            f"        normalized = {{str(key): value for key, value in request.payload.items()}}\n"
            f"        preview_steps = steps[: min(len(steps), 5)]\n"
            f"        artifacts = {{\n"
            f'            "module": "{module_name}",\n'
            f'            "role": "{role}",\n'
            f'            "steps": steps,\n'
            f'            "preview_steps": preview_steps,\n'
            f'            "normalized_payload": normalized,\n'
            f'            "dependency_chain": list(self.dependencies),\n'
            f'            "responsibility_count": len(self.responsibilities),\n'
            f"        }}\n"
            f"        warnings: List[str] = []\n"
            f"        if len(normalized) < 2:\n"
            f'            warnings.append(\"payload is small; downstream composition may be underspecified\")\n'
            f"        return {class_prefix}Result(ok=True, artifacts=artifacts, warnings=warnings)\n\n"
            f"    # @ensure(\"returns dict\")\n"
            f"    def summarize(self, result: {class_prefix}Result) -> dict[str, Any]:\n"
            f"        return {{\n"
            f'            "module": "{module_name}",\n'
            f'            "ok": result.ok,\n'
            f'            "artifact_keys": sorted(result.artifacts.keys()),\n'
            f'            "warning_count": len(result.warnings),\n'
            f"        }}\n\n\n"
            f"{spec_function_blocks}\n\n"
            f"def {module_name}_summary(payload: Dict[str, Any]) -> Dict[str, Any]:\n"
            f'    """Compute a compact audit summary for this module."""\n'
            f"    result = {class_prefix}Service().execute({class_prefix}Request(payload=payload))\n"
            f"    return {class_prefix}Service().summarize(result)\n\n\n"
            f"# Constraints carried from iterative typed ideation:\n"
            f"{constraint_comments}\n"
        )


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ Helpers                                                                  │
# └──────────────────────────────────────────────────────────────────────────┘

# textwrap import used in argparse epilog
import textwrap as textwrap  # noqa: E402, F811


# ┌──────────────────────────────────────────────────────────────────────────┐
# │ main() entry point                                                       │
# └──────────────────────────────────────────────────────────────────────────┘

def main(args: Optional[List[str]] = None) -> int:
    """
    CLI entry point for deppy.

    Parse args and run the agent:

    Usage:
        deppy <prompt>                    — generate verified project
        deppy --interactive <prompt>      — interactive mode
        deppy --resume <manifest.json>    — resume from saved state
        deppy --verify <file.py>          — verify existing file
        deppy --check <directory>         — check existing project
        deppy --report <manifest.json>    — generate trust report

    Options:
        --model <model>       LLM model (default: gpt-4)
        --output <dir>        Output directory (default: ./output)
        --lean                Enable Lean proof generation
        --strict              Require all obligations discharged
        --verbose             Show detailed progress
        --cache-dir <dir>     Cache directory (default: .deppy_cache)
        --max-iterations <n>  Max generation/repair iterations

    Returns the exit code (0 = success).
    """
    cli = AgentCLI(args=args)
    cli.parse_args()
    cli.setup()
    return cli.run()


if __name__ == "__main__":
    sys.exit(main())
