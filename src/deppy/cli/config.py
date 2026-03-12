"""CLI configuration and defaults for DepPy.

Manages configuration loading from command-line arguments, TOML config
files (.deppy.toml), and environment variables.  Supports layered
configuration with ``merge(base, override)``.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from pathlib import Path
from typing import (
    Any,
    Dict,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

from deppy.core._protocols import TrustLevel
from deppy.pipeline.pipeline_config import (
    IncrementalConfig,
    IncrementalStrategy,
    OutputFormat,
    PipelineConfig,
    TheoryPack,
    TimeoutConfig,
    Verbosity,
)


# ===================================================================
#  Config file discovery
# ===================================================================


_CONFIG_FILENAMES = (
    ".deppy.toml",
    "deppy.toml",
    "pyproject.toml",
)


def find_config_file(start_dir: Optional[str] = None) -> Optional[Path]:
    """Walk up from *start_dir* looking for a deppy config file.

    Returns the first config file found, or ``None``.
    """
    current = Path(start_dir) if start_dir else Path.cwd()
    for _ in range(50):  # bounded to avoid infinite loops
        for name in _CONFIG_FILENAMES:
            candidate = current / name
            if candidate.is_file():
                return candidate
        parent = current.parent
        if parent == current:
            break
        current = parent
    return None


def _parse_toml(path: Path) -> Dict[str, Any]:
    """Parse a TOML file into a dictionary.

    Uses tomllib (Python 3.11+) with fallback to basic parsing.
    """
    try:
        import tomllib  # type: ignore[import-not-found]
        with open(path, "rb") as f:
            data = tomllib.load(f)
    except ImportError:
        try:
            import tomli as tomllib  # type: ignore[import-not-found,no-redef]
            with open(path, "rb") as f:
                data = tomllib.load(f)
        except ImportError:
            # Fallback: basic line parser for simple key=value TOML
            data = _basic_toml_parse(path)
    # For pyproject.toml, look under [tool.deppy]
    if path.name == "pyproject.toml":
        return data.get("tool", {}).get("deppy", {})
    return data


def _basic_toml_parse(path: Path) -> Dict[str, Any]:
    """Minimal TOML-like parser for environments without tomllib."""
    result: Dict[str, Any] = {}
    current_section: Optional[str] = None
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return result

    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            current_section = line[1:-1].strip()
            result.setdefault(current_section, {})
            continue
        if "=" in line:
            key, _, value = line.partition("=")
            key = key.strip()
            value = value.strip().strip('"').strip("'")
            # Type coercion
            parsed_value: Any = value
            if value.lower() in ("true", "false"):
                parsed_value = value.lower() == "true"
            elif value.isdigit():
                parsed_value = int(value)
            else:
                try:
                    parsed_value = float(value)
                except ValueError:
                    pass

            if current_section:
                parts = current_section.split(".")
                target = result
                for part in parts:
                    target = target.setdefault(part, {})
                target[key] = parsed_value
            else:
                result[key] = parsed_value

    return result


# ===================================================================
#  CLIConfig
# ===================================================================


@dataclass(frozen=True)
class CLIConfig:
    """CLI-layer configuration combining arguments, config file, and env vars.

    This is the user-facing configuration that gets translated into a
    PipelineConfig for the analysis pipeline.
    """

    _source_paths: Tuple[str, ...] = ()
    _output_format: str = "terminal"
    _verbosity: int = 1
    _strict: bool = False
    _color: bool = True
    _max_iterations: int = 20
    _timeout: float = 120.0
    _theory_packs: Tuple[str, ...] = ()
    _trust_threshold: str = "residual"
    _incremental: bool = False
    _watch: bool = False
    _config_file: Optional[str] = None
    _subcommand: str = "check"
    _explain_site: Optional[str] = None
    _prove_target: Optional[str] = None
    _generate_output: Optional[str] = None
    _extra: Dict[str, Any] = field(default_factory=dict)

    @property
    def source_paths(self) -> Tuple[str, ...]:
        return self._source_paths

    @property
    def output_format(self) -> str:
        return self._output_format

    @property
    def verbosity(self) -> int:
        return self._verbosity

    @property
    def strict(self) -> bool:
        return self._strict

    @property
    def color(self) -> bool:
        return self._color

    @property
    def max_iterations(self) -> int:
        return self._max_iterations

    @property
    def timeout(self) -> float:
        return self._timeout

    @property
    def theory_packs(self) -> Tuple[str, ...]:
        return self._theory_packs

    @property
    def trust_threshold(self) -> str:
        return self._trust_threshold

    @property
    def incremental(self) -> bool:
        return self._incremental

    @property
    def watch(self) -> bool:
        return self._watch

    @property
    def config_file(self) -> Optional[str]:
        return self._config_file

    @property
    def subcommand(self) -> str:
        return self._subcommand

    @property
    def explain_site(self) -> Optional[str]:
        return self._explain_site

    @property
    def prove_target(self) -> Optional[str]:
        return self._prove_target

    @property
    def generate_output(self) -> Optional[str]:
        return self._generate_output

    # -- Factories --------------------------------------------------------

    @classmethod
    def from_args(cls, args: Any) -> CLIConfig:
        """Build a CLIConfig from parsed argparse Namespace."""
        source_paths = getattr(args, "files", ()) or getattr(args, "source", ())
        if isinstance(source_paths, str):
            source_paths = (source_paths,)

        theory_packs_raw = getattr(args, "theory_packs", None) or ()
        if isinstance(theory_packs_raw, str):
            theory_packs_raw = (theory_packs_raw,)

        return cls(
            _source_paths=tuple(source_paths),
            _output_format=getattr(args, "format", "terminal"),
            _verbosity=getattr(args, "verbose", 1),
            _strict=getattr(args, "strict", False),
            _color=not getattr(args, "no_color", False),
            _max_iterations=getattr(args, "max_iterations", 20),
            _timeout=getattr(args, "timeout", 120.0),
            _theory_packs=tuple(theory_packs_raw),
            _trust_threshold=getattr(args, "trust_threshold", "residual"),
            _incremental=getattr(args, "incremental", False),
            _watch=getattr(args, "watch", False),
            _config_file=getattr(args, "config", None),
            _subcommand=getattr(args, "subcommand", "check"),
            _explain_site=getattr(args, "site", None),
            _prove_target=getattr(args, "target", None),
            _generate_output=getattr(args, "output", None),
        )

    @classmethod
    def from_file(cls, path: str) -> CLIConfig:
        """Load CLIConfig from a TOML config file."""
        config_path = Path(path)
        if not config_path.is_file():
            return cls()

        data = _parse_toml(config_path)
        theory_packs_raw = data.get("theory_packs", ())
        if isinstance(theory_packs_raw, str):
            theory_packs_raw = (theory_packs_raw,)

        return cls(
            _source_paths=tuple(data.get("source_paths", ())),
            _output_format=data.get("output_format", "terminal"),
            _verbosity=data.get("verbosity", 1),
            _strict=data.get("strict", False),
            _color=data.get("color", True),
            _max_iterations=data.get("max_iterations", 20),
            _timeout=data.get("timeout", 120.0),
            _theory_packs=tuple(theory_packs_raw),
            _trust_threshold=data.get("trust_threshold", "residual"),
            _incremental=data.get("incremental", False),
            _config_file=path,
            _extra=data.get("extra", {}),
        )

    @staticmethod
    def merge(base: CLIConfig, override: CLIConfig) -> CLIConfig:
        """Merge two configs with *override* taking precedence for non-default values."""
        return CLIConfig(
            _source_paths=override.source_paths or base.source_paths,
            _output_format=override.output_format if override.output_format != "terminal" else base.output_format,
            _verbosity=max(override.verbosity, base.verbosity),
            _strict=override.strict or base.strict,
            _color=override.color and base.color,
            _max_iterations=override.max_iterations if override.max_iterations != 20 else base.max_iterations,
            _timeout=override.timeout if override.timeout != 120.0 else base.timeout,
            _theory_packs=override.theory_packs or base.theory_packs,
            _trust_threshold=override.trust_threshold if override.trust_threshold != "residual" else base.trust_threshold,
            _incremental=override.incremental or base.incremental,
            _watch=override.watch,
            _config_file=override.config_file or base.config_file,
            _subcommand=override.subcommand,
            _explain_site=override.explain_site,
            _prove_target=override.prove_target,
            _generate_output=override.generate_output,
            _extra={**base._extra, **override._extra},
        )

    # -- Conversion to PipelineConfig -------------------------------------

    def to_pipeline_config(self) -> PipelineConfig:
        """Convert CLIConfig to a PipelineConfig for the analysis pipeline."""
        # Map output format
        format_map = {
            "terminal": OutputFormat.TERMINAL,
            "plain": OutputFormat.PLAIN,
            "json": OutputFormat.JSON,
            "sarif": OutputFormat.SARIF,
        }
        output_format = format_map.get(self._output_format, OutputFormat.TERMINAL)

        # Map verbosity
        verbosity_map = {
            0: Verbosity.QUIET,
            1: Verbosity.NORMAL,
            2: Verbosity.VERBOSE,
            3: Verbosity.DEBUG,
        }
        verbosity = verbosity_map.get(
            min(self._verbosity, 3), Verbosity.NORMAL
        )

        # Map theory packs
        packs: List[TheoryPack] = []
        if self._theory_packs:
            for name in self._theory_packs:
                try:
                    packs.append(TheoryPack(name))
                except ValueError:
                    pass
        if not packs:
            packs = [
                TheoryPack.BUILTIN_ARITHMETIC,
                TheoryPack.BUILTIN_STRING,
                TheoryPack.BUILTIN_COLLECTION,
                TheoryPack.BUILTIN_NONE,
            ]

        # Map trust threshold
        trust_map = {
            "residual": TrustLevel.RESIDUAL,
            "assumed": TrustLevel.ASSUMED,
            "trace_backed": TrustLevel.TRACE_BACKED,
            "bounded_auto": TrustLevel.BOUNDED_AUTO,
            "trusted_auto": TrustLevel.TRUSTED_AUTO,
            "proof_backed": TrustLevel.PROOF_BACKED,
        }
        trust = trust_map.get(self._trust_threshold, TrustLevel.RESIDUAL)

        # Build incremental config
        incremental = IncrementalConfig(
            _strategy=(
                IncrementalStrategy.FUNCTION_LEVEL
                if self._incremental
                else IncrementalStrategy.NONE
            ),
        )

        # Build timeout config
        timeout = TimeoutConfig(_total=self._timeout)

        return PipelineConfig(
            _theory_packs=tuple(packs),
            _max_iterations=self._max_iterations,
            _trust_threshold=trust,
            _output_format=output_format,
            _verbosity=verbosity,
            _timeout=timeout,
            _incremental=incremental,
            _target_files=self._source_paths,
            _strict_mode=self._strict,
            _color_output=self._color,
        )

    def __repr__(self) -> str:
        return (
            f"CLIConfig(cmd={self._subcommand}, "
            f"files={len(self._source_paths)}, "
            f"strict={self._strict})"
        )
