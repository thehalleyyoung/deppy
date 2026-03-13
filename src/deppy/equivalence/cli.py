"""CLI command for sheaf equivalence checking.

Adds the ``deppy equiv`` subcommand that accepts two source files and
runs the full equivalence checking pipeline.  Integrates with the
existing Command ABC from ``deppy.cli.commands``.

Usage::

    deppy equiv file1.py file2.py
    deppy equiv file1.py file2.py --function my_func
    deppy equiv file1.py file2.py --verbose --sarif out.sarif
    deppy equiv file1.py file2.py --json
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import Any, Dict, List, Optional

from deppy.equivalence._protocols import (
    EquivalenceStrength,
    EquivalenceVerdict,
    ProgramId,
)
from deppy.equivalence.pipeline import (
    EquivalencePipeline,
    EquivalencePipelineConfig,
    EquivalencePipelineHooks,
    EquivalencePipelineResult,
)
from deppy.equivalence.render import (
    EquivalenceJsonRenderer,
    EquivalenceSarifRenderer,
    EquivalenceSummaryRenderer,
    EquivalenceTerminalRenderer,
)


# ═══════════════════════════════════════════════════════════════════════════════
# CLI configuration
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class EquivCliConfig:
    """Configuration parsed from CLI arguments."""
    source_f: str
    source_g: str
    function_name: Optional[str] = None
    verbose: bool = False
    json_output: bool = False
    sarif_output: Optional[str] = None
    strength: str = "denotational"
    no_solver: bool = False
    solver_timeout_ms: int = 10000
    max_sites: int = 500
    no_color: bool = False
    quiet: bool = False

    def to_pipeline_config(self) -> EquivalencePipelineConfig:
        """Convert to pipeline configuration."""
        try:
            strength = EquivalenceStrength(self.strength)
        except ValueError:
            strength = EquivalenceStrength.DENOTATIONAL

        return EquivalencePipelineConfig(
            strength=strength,
            function_name=self.function_name,
            check_gluing=True,
            compute_cohomology=True,
            use_solver=not self.no_solver,
            solver_timeout_ms=self.solver_timeout_ms,
            max_sites=self.max_sites,
            verbose=self.verbose,
            sarif_output=self.sarif_output,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# Argument parser
# ═══════════════════════════════════════════════════════════════════════════════


def parse_equiv_args(argv: List[str]) -> EquivCliConfig:
    """Parse equivalence CLI arguments.

    Accepts a list of arguments (typically ``sys.argv[1:]`` after the
    ``equiv`` subcommand has been consumed).
    """
    config = EquivCliConfig(source_f="", source_g="")
    positional: List[str] = []
    i = 0

    while i < len(argv):
        arg = argv[i]

        if arg == "--function" and i + 1 < len(argv):
            config.function_name = argv[i + 1]
            i += 2
        elif arg == "--verbose" or arg == "-v":
            config.verbose = True
            i += 1
        elif arg == "--json":
            config.json_output = True
            i += 1
        elif arg == "--sarif" and i + 1 < len(argv):
            config.sarif_output = argv[i + 1]
            i += 2
        elif arg == "--strength" and i + 1 < len(argv):
            config.strength = argv[i + 1]
            i += 2
        elif arg == "--no-solver":
            config.no_solver = True
            i += 1
        elif arg == "--solver-timeout" and i + 1 < len(argv):
            config.solver_timeout_ms = int(argv[i + 1])
            i += 2
        elif arg == "--max-sites" and i + 1 < len(argv):
            config.max_sites = int(argv[i + 1])
            i += 2
        elif arg == "--no-color":
            config.no_color = True
            i += 1
        elif arg == "--quiet" or arg == "-q":
            config.quiet = True
            i += 1
        elif arg == "--help" or arg == "-h":
            _print_usage()
            sys.exit(0)
        elif not arg.startswith("-"):
            positional.append(arg)
            i += 1
        else:
            print(f"Unknown option: {arg}", file=sys.stderr)
            _print_usage()
            sys.exit(1)

    if len(positional) < 2:
        print("Error: two source files required", file=sys.stderr)
        _print_usage()
        sys.exit(1)

    config.source_f = positional[0]
    config.source_g = positional[1]

    return config


def _print_usage() -> None:
    """Print usage information."""
    print(
        "Usage: deppy equiv <file1.py> <file2.py> [options]\n"
        "\n"
        "Check two programs for equivalence using sheaf-theoretic analysis.\n"
        "\n"
        "Options:\n"
        "  --function NAME     Restrict to a specific function\n"
        "  --verbose, -v       Show detailed site-by-site analysis\n"
        "  --json              Output as JSON\n"
        "  --sarif PATH        Export results as SARIF\n"
        "  --strength KIND     Equivalence strength: denotational, observational,\n"
        "                      contextual, bisimulation (default: denotational)\n"
        "  --no-solver         Skip Z3 solver (structural check only)\n"
        "  --solver-timeout N  Solver timeout in milliseconds (default: 10000)\n"
        "  --max-sites N       Maximum sites to check (default: 500)\n"
        "  --no-color          Disable colored output\n"
        "  --quiet, -q         Minimal output (exit code only)\n"
        "  --help, -h          Show this help\n",
        file=sys.stderr,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# Command class (integrates with deppy CLI)
# ═══════════════════════════════════════════════════════════════════════════════


class EquivCommand:
    """Equivalence checking command.

    Integrates with the deppy CLI command infrastructure.

    Usage from within deppy::

        deppy equiv file1.py file2.py [options]

    Exit codes:
        0 — programs are equivalent
        1 — programs are inequivalent
        2 — equivalence is unknown / partial refinement
        3 — error during analysis
    """

    name = "equiv"
    help = "Check two programs for sheaf-theoretic equivalence"

    def run(self, cli_config: Any = None) -> int:
        """Run the equivalence command.

        Parameters:
            cli_config: Either an EquivCliConfig or a raw CLI config
                        from the deppy CLI framework.

        Returns:
            Exit code (0 = equivalent, 1 = inequivalent, 2 = unknown, 3 = error)
        """
        if isinstance(cli_config, EquivCliConfig):
            config = cli_config
        else:
            # Fall back to parsing sys.argv
            config = parse_equiv_args(sys.argv[2:] if len(sys.argv) > 2 else [])

        return self.run_with_config(config)

    def run_with_config(self, config: EquivCliConfig) -> int:
        """Run equivalence check with a fully parsed config."""
        try:
            pipeline_config = config.to_pipeline_config()

            # Set up hooks for verbose mode
            hooks = EquivalencePipelineHooks()
            if config.verbose and not config.quiet and not config.json_output:
                hooks.on_stage_start = lambda stage: print(f"  ⏳ {stage}...", file=sys.stderr)
                hooks.on_stage_end = lambda stage, t: print(
                    f"  ✓ {stage} ({t:.3f}s)", file=sys.stderr
                )

            pipeline = EquivalencePipeline(
                config=pipeline_config,
                hooks=hooks,
            )

            result = pipeline.run(
                source_f=config.source_f,
                source_g=config.source_g,
                program_f=ProgramId(name="f", source_file=config.source_f),
                program_g=ProgramId(name="g", source_file=config.source_g),
            )

            return self._output_result(result, config)

        except FileNotFoundError as e:
            print(f"Error: {e}", file=sys.stderr)
            return 3
        except Exception as e:
            print(f"Error during equivalence analysis: {e}", file=sys.stderr)
            if config.verbose:
                import traceback
                traceback.print_exc(file=sys.stderr)
            return 3

    def _output_result(
        self,
        result: EquivalencePipelineResult,
        config: EquivCliConfig,
    ) -> int:
        """Format and output the result, returning the exit code."""
        if config.quiet:
            # Just exit code
            pass
        elif config.json_output:
            renderer = EquivalenceJsonRenderer()
            print(renderer.render(result.judgment))
        else:
            renderer = EquivalenceTerminalRenderer(
                use_color=not config.no_color,
                verbose=config.verbose,
            )
            print(renderer.render(result.judgment))

            # Print timing if verbose
            if config.verbose:
                print(f"\nPipeline timing:")
                for stage, elapsed in result.stages.items():
                    if not stage.startswith("_"):
                        print(f"  {stage}: {elapsed:.3f}s")
                print(f"  total: {result.total_elapsed:.3f}s")

        # SARIF was handled by pipeline
        if result.sarif_path:
            print(f"SARIF exported to: {result.sarif_path}", file=sys.stderr)

        return self._verdict_to_exit_code(result.verdict)

    def _verdict_to_exit_code(self, verdict: EquivalenceVerdict) -> int:
        return {
            EquivalenceVerdict.EQUIVALENT: 0,
            EquivalenceVerdict.INEQUIVALENT: 1,
            EquivalenceVerdict.REFINED: 2,
            EquivalenceVerdict.UNKNOWN: 2,
        }.get(verdict, 3)


# ═══════════════════════════════════════════════════════════════════════════════
# Entrypoint for direct invocation
# ═══════════════════════════════════════════════════════════════════════════════


def main(argv: Optional[List[str]] = None) -> int:
    """Main entrypoint for the equivalence CLI.

    Can be called directly or via ``deppy equiv``.
    """
    args = argv if argv is not None else sys.argv[1:]
    config = parse_equiv_args(args)
    cmd = EquivCommand()
    return cmd.run_with_config(config)


if __name__ == "__main__":
    sys.exit(main())
