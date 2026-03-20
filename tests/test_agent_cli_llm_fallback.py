from __future__ import annotations

import json
import subprocess

from agent.cli import (
    CopilotCLIInterface,
    OpenAIInterface,
    detect_llm_interface,
)


def test_detect_llm_interface_prefers_openai_over_copilot(
    monkeypatch,
) -> None:
    monkeypatch.setenv("OPENAI_API_KEY", "test-key")
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.setattr("agent.cli.shutil.which", lambda _name: "/usr/bin/copilot")

    llm = detect_llm_interface()

    assert isinstance(llm, OpenAIInterface)


def test_detect_llm_interface_uses_copilot_when_no_api_keys(
    monkeypatch,
) -> None:
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.setattr("agent.cli.shutil.which", lambda _name: "/usr/bin/copilot")

    llm = detect_llm_interface("gpt-5.2")

    assert isinstance(llm, CopilotCLIInterface)
    assert llm.model == "gpt-5.2"


def test_copilot_cli_interface_builds_noninteractive_prompt_command() -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")

    command = llm._build_command("Reply with OK")

    assert command == [
        "/usr/bin/copilot",
        "-p",
        "Reply with OK",
        "--output-format",
        "json",
        "--allow-all-tools",
        "--no-ask-user",
        "--stream",
        "off",
        "--no-custom-instructions",
        "--disable-builtin-mcps",
        "--available-tools=",
        "--model",
        "gpt-5.2",
    ]


def test_copilot_cli_interface_omits_legacy_default_model_flag() -> None:
    llm = CopilotCLIInterface(model="gpt-4", executable="/usr/bin/copilot")

    command = llm._build_command("Reply with OK")

    assert "--model" not in command


def test_copilot_cli_interface_complete_json_parses_fenced_output(
    monkeypatch,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")
    payload = {"status": "ok", "items": [1, 2, 3]}
    monkeypatch.setattr(
        llm,
        "complete",
        lambda prompt, max_tokens=4096, temperature=0.0: (
            "```json\n" + json.dumps(payload) + "\n```"
        ),
    )

    result = llm.complete_json("Return JSON", {"type": "object"})

    assert result == payload


def test_copilot_cli_interface_complete_json_extracts_wrapped_object(
    monkeypatch,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")
    payload = {"status": "ok", "items": [1, 2, 3]}
    monkeypatch.setattr(
        llm,
        "complete",
        lambda prompt, max_tokens=4096, temperature=0.0: (
            "Here is the JSON you asked for:\n" + json.dumps(payload)
        ),
    )

    result = llm.complete_json("Return JSON", {"type": "object"})

    assert result == payload


def test_copilot_cli_interface_extracts_final_message_from_jsonl(
    monkeypatch,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")

    class _Completed:
        def __init__(self) -> None:
            self.stdout = (
                '{"type":"assistant.turn_start","data":{"turnId":"0"}}\n'
                '{"type":"assistant.message","data":{"content":"draft"}}\n'
                '{"type":"assistant.message","data":{"content":"final answer"}}\n'
                '{"type":"result","exitCode":0}\n'
            )

    monkeypatch.setattr(
        "agent.cli.subprocess.run",
        lambda *args, **kwargs: _Completed(),
    )

    result = llm.complete("ignored")

    assert result == "final answer"


def test_copilot_cli_interface_uses_text_only_prompt_mode(
    monkeypatch,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")
    captured_kwargs = {}

    class _Completed:
        def __init__(self) -> None:
            self.stdout = '{"type":"assistant.message","data":{"content":"final answer"}}\n'

    def _fake_run(*args, **kwargs):
        captured_kwargs.update(kwargs)
        captured_kwargs["command"] = args[0]
        return _Completed()

    monkeypatch.setattr("agent.cli.subprocess.run", _fake_run)

    result = llm.complete("ignored")

    assert result == "final answer"
    assert captured_kwargs["timeout"] == 180
    assert "--disable-builtin-mcps" in captured_kwargs["command"]
    assert "--available-tools=" in captured_kwargs["command"]


def test_copilot_cli_interface_raises_on_timeout(monkeypatch) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot", timeout_seconds=7)

    def _fake_run(*args, **kwargs):
        raise subprocess.TimeoutExpired(cmd=args[0], timeout=kwargs["timeout"])

    monkeypatch.setattr("agent.cli.subprocess.run", _fake_run)

    try:
        llm.complete("ignored")
    except RuntimeError as exc:
        assert "timed out after 7s" in str(exc)
    else:
        raise AssertionError("expected RuntimeError on Copilot timeout")
