from __future__ import annotations

import json

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
        "--stream",
        "off",
        "--no-custom-instructions",
        "--disable-builtin-mcps",
        "--model",
        "gpt-5.2",
    ]


def test_copilot_cli_interface_omits_legacy_default_model_flag() -> None:
    llm = CopilotCLIInterface(model="gpt-4", executable="/usr/bin/copilot")

    command = llm._build_command("Reply with OK")

    assert "--model" not in command


def test_copilot_cli_interface_builds_tool_enabled_file_command(tmp_path) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")

    command = llm._build_command(
        "Write the module file.",
        output_format="text",
        tool_mode=True,
        add_dirs=[str(tmp_path)],
    )

    assert command == [
        "/usr/bin/copilot",
        "-p",
        "Write the module file.",
        "--output-format",
        "text",
        "--stream",
        "off",
        "--no-custom-instructions",
        "--disable-builtin-mcps",
        "--allow-all-tools",
        "--no-ask-user",
        "--available-tools=report_intent,glob,view,apply_patch,bash",
        "--add-dir",
        str(tmp_path),
        "--model",
        "gpt-5.2",
    ]


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

    class _Process:
        def __init__(self) -> None:
            self.stdout = iter(
                (
                '{"type":"assistant.turn_start","data":{"turnId":"0"}}\n'
                '{"type":"assistant.message","data":{"content":"draft"}}\n'
                '{"type":"assistant.message","data":{"content":"final answer"}}\n'
                '{"type":"result","exitCode":0}\n'
                ).splitlines(keepends=True)
            )

        def wait(self) -> int:
            return 0

    monkeypatch.setattr(
        "agent.cli.subprocess.Popen",
        lambda *args, **kwargs: _Process(),
    )

    result = llm.complete("ignored")

    assert result == "final answer"


def test_copilot_cli_interface_prefers_final_answer_over_tool_loop_messages(
    monkeypatch,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")

    class _Process:
        def __init__(self) -> None:
            self.stdout = iter(
                (
                    '{"type":"assistant.message","data":{"content":"","toolRequests":[{"name":"glob"}],"phase":"commentary"}}\n'
                    '{"type":"assistant.message","data":{"content":"I made a plan.","toolRequests":[{"name":"view"}],"phase":"commentary"}}\n'
                    '{"type":"assistant.message","data":{"content":"final module source","toolRequests":[],"phase":"final_answer"}}\n'
                ).splitlines(keepends=True)
            )

        def wait(self) -> int:
            return 0

    monkeypatch.setattr(
        "agent.cli.subprocess.Popen",
        lambda *args, **kwargs: _Process(),
    )

    result = llm.complete("ignored")

    assert result == "final module source"


def test_copilot_cli_interface_uses_text_only_prompt_mode(
    monkeypatch,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")
    captured_kwargs = {}

    class _Process:
        def __init__(self) -> None:
            self.stdout = iter(
                ['{"type":"assistant.message","data":{"content":"final answer"}}\n']
            )

        def wait(self) -> int:
            return 0

    def _fake_popen(*args, **kwargs):
        captured_kwargs.update(kwargs)
        captured_kwargs["command"] = args[0]
        return _Process()

    monkeypatch.setattr("agent.cli.subprocess.Popen", _fake_popen)

    result = llm.complete("ignored")

    assert result == "final answer"
    assert captured_kwargs["stdout"] is not None
    assert captured_kwargs["stderr"] is not None
    assert "--disable-builtin-mcps" in captured_kwargs["command"]
    assert "--allow-all-tools" not in captured_kwargs["command"]
    assert "--no-ask-user" not in captured_kwargs["command"]


def test_copilot_cli_interface_writes_module_file_via_tool_mode(
    monkeypatch,
    tmp_path,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")
    captured_kwargs = {}
    captured_command = []
    target_path = tmp_path / "main.py"

    class _Process:
        def __init__(self) -> None:
            self.stdout = iter(["copilot wrote main.py\n"])

        def wait(self) -> int:
            return 0

    def _fake_popen(*args, **kwargs):
        captured_kwargs.update(kwargs)
        captured_command.extend(args[0])
        target_path.write_text("print('ok')\n", encoding="utf-8")
        return _Process()

    monkeypatch.setattr("agent.cli.subprocess.Popen", _fake_popen)

    result = llm.write_module_file("Write a module.", str(target_path))

    assert result == "print('ok')\n"
    assert captured_kwargs["cwd"] == str(tmp_path)
    assert "--allow-all-tools" in captured_command
    assert "--autopilot" not in captured_command
    assert "--available-tools=report_intent,glob,view,apply_patch,bash" in captured_command


def test_copilot_cli_interface_writes_multiple_module_files_via_tool_mode(
    monkeypatch,
    tmp_path,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")
    captured_kwargs = {}
    captured_command = []
    target_a = tmp_path / "alpha.py"
    target_b = tmp_path / "beta.py"

    class _Process:
        def __init__(self) -> None:
            self.stdout = iter(["copilot wrote alpha.py and beta.py\n"])

        def wait(self) -> int:
            return 0

    def _fake_popen(*args, **kwargs):
        captured_kwargs.update(kwargs)
        captured_command.extend(args[0])
        target_a.write_text("print('a')\n", encoding="utf-8")
        target_b.write_text("print('b')\n", encoding="utf-8")
        return _Process()

    monkeypatch.setattr("agent.cli.subprocess.Popen", _fake_popen)

    result = llm.write_module_files("Write modules.", [str(target_a), str(target_b)])

    assert result[str(target_a)] == "print('a')\n"
    assert result[str(target_b)] == "print('b')\n"
    assert captured_kwargs["cwd"] == str(tmp_path)
    assert "--available-tools=report_intent,glob,view,apply_patch,bash" in captured_command


def test_copilot_cli_interface_normalizes_relative_write_paths(
    monkeypatch,
    tmp_path,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")
    captured_kwargs = {}
    captured_command = []

    class _Process:
        def __init__(self) -> None:
            self.stdout = iter(["copilot wrote nested/main.py\n"])

        def wait(self) -> int:
            return 0

    def _fake_popen(*args, **kwargs):
        captured_kwargs.update(kwargs)
        captured_command.extend(args[0])
        target = tmp_path / "nested" / "main.py"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("print('ok')\n", encoding="utf-8")
        return _Process()

    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr("agent.cli.subprocess.Popen", _fake_popen)

    result = llm.write_module_file("Write a module.", "nested/main.py")

    assert result == "print('ok')\n"
    assert captured_kwargs["cwd"] == str(tmp_path / "nested")
    assert "--add-dir" in captured_command
    add_dir_index = captured_command.index("--add-dir")
    assert captured_command[add_dir_index + 1] == str(tmp_path / "nested")


def test_copilot_cli_interface_removes_empty_stub_before_tool_write(
    monkeypatch,
    tmp_path,
) -> None:
    llm = CopilotCLIInterface(model="gpt-5.2", executable="/usr/bin/copilot")
    target_path = tmp_path / "main.py"
    target_path.write_text("", encoding="utf-8")

    class _Process:
        def __init__(self) -> None:
            self.stdout = iter(["copilot wrote main.py\n"])

        def wait(self) -> int:
            return 0

    def _fake_popen(*args, **kwargs):
        assert not target_path.exists()
        target_path.write_text("print('ok')\n", encoding="utf-8")
        return _Process()

    monkeypatch.setattr("agent.cli.subprocess.Popen", _fake_popen)

    result = llm.write_module_file("Write a module.", str(target_path))

    assert result == "print('ok')\n"
