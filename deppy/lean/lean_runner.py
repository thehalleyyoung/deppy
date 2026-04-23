"""Lean compilation harness for emitted runtime-safety modules (Gap 16)."""
from __future__ import annotations

import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from deppy.core.kernel import ConditionalEffectWitness, SafetyObligation
from deppy.lean.safety_lean import DEPPY_LEAN_PRELUDE, emit_safety_module


@dataclass
class LeanCheckResult:
    ok: bool
    command: list[str]
    stdout: str = ""
    stderr: str = ""
    source_path: str = ""
    module_source: str = ""


def render_compilable_safety_module(
    namespace: str,
    witnesses: list[ConditionalEffectWitness],
    obligations: Optional[list[SafetyObligation]] = None,
) -> str:
    """Render a complete self-contained Lean file."""
    body = emit_safety_module(namespace, witnesses, obligations or [])
    return f"{DEPPY_LEAN_PRELUDE}\n\nopen DeppySafety\n\n{body}\n"


def check_lean_module_source(
    source: str,
    *,
    lean_cmd: Optional[str] = None,
    timeout_s: int = 20,
) -> LeanCheckResult:
    """Compile a Lean source string with the local `lean` binary."""
    lean_bin = lean_cmd or shutil.which("lean")
    if not lean_bin:
        return LeanCheckResult(
            ok=False,
            command=[],
            stderr="lean binary not found",
            module_source=source,
        )
    with tempfile.TemporaryDirectory(prefix="deppy-lean-") as td:
        path = Path(td) / "Safety.lean"
        path.write_text(source, encoding="utf-8")
        cmd = [lean_bin, str(path)]
        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout_s,
                check=False,
            )
        except subprocess.TimeoutExpired as e:
            return LeanCheckResult(
                ok=False,
                command=cmd,
                stdout=e.stdout or "",
                stderr=(e.stderr or "") + "\nlean timed out",
                source_path=str(path),
                module_source=source,
            )
        return LeanCheckResult(
            ok=(proc.returncode == 0),
            command=cmd,
            stdout=proc.stdout,
            stderr=proc.stderr,
            source_path=str(path),
            module_source=source,
        )


__all__ = [
    "LeanCheckResult",
    "render_compilable_safety_module",
    "check_lean_module_source",
]
