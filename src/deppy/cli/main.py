"""Entry point and argument parsing for the DepPy CLI.

Usage::

    deppy check myfile.py
    deppy explain myfile.py --site "func_name"
    deppy prove myfile.py --target "func_name.postcondition"
    deppy generate myfile.py --output contracts.py
    deppy watch src/

Supports all standard configuration via command-line flags, .deppy.toml
config files, and environment variables.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import (
    Any,
    Dict,
    List,
    Optional,
    Sequence,
)

from deppy.cli.config import CLIConfig, find_config_file
from deppy.cli.commands import (
    CheckCommand,
    ExplainCommand,
    GenerateCommand,
    ProveCommand,
    WatchCommand,
    available_commands,
    get_command,
)


# ===================================================================
#  Argument parser construction
# ===================================================================


def _build_parser() -> argparse.ArgumentParser:
    """Build the argument parser with all subcommands."""
    parser = argparse.ArgumentParser(
        prog="deppy",
        description=(
            "DepPy: Sheaf-descent semantic typing for Python. "
            "Analyzes Python source code using sheaf-theoretic methods "
            "to infer refined types and verify contracts."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  deppy check myfile.py\n"
            "  deppy check src/ --strict --format json\n"
            "  deppy explain myfile.py --site my_function\n"
            "  deppy prove myfile.py --target my_function\n"
            "  deppy generate myfile.py --output contracts.py\n"
            "  deppy watch src/ --incremental\n"
        ),
    )

    # Global options
    parser.add_argument(
        "--version",
        action="version",
        version="deppy 2.0.0",
    )
    parser.add_argument(
        "--config",
        type=str,
        default=None,
        help="Path to configuration file (.deppy.toml)",
    )
    parser.add_argument(
        "--verbose", "-v",
        action="count",
        default=1,
        help="Increase verbosity (use -vv for debug)",
    )
    parser.add_argument(
        "--quiet", "-q",
        action="store_true",
        help="Suppress non-error output",
    )
    parser.add_argument(
        "--no-color",
        action="store_true",
        help="Disable colored output",
    )
    parser.add_argument(
        "--format",
        choices=["terminal", "plain", "json", "sarif"],
        default="terminal",
        help="Output format (default: terminal)",
    )

    # Subcommands
    subparsers = parser.add_subparsers(
        dest="subcommand",
        help="Available commands",
    )

    # --- check ---
    check_parser = subparsers.add_parser(
        "check",
        help="Run sheaf-descent analysis and report diagnostics",
        description="Analyze Python source files for type errors using sheaf-descent semantics.",
    )
    _add_common_analysis_args(check_parser)
    check_parser.add_argument(
        "--strict",
        action="store_true",
        help="Enable strict mode (fail on warnings)",
    )
    check_parser.add_argument(
        "--emit-contracts",
        action="store_true",
        default=True,
        help="Emit inferred contract annotations",
    )

    # --- explain ---
    explain_parser = subparsers.add_parser(
        "explain",
        help="Explain the analysis for a specific site or scope",
        description="Show detailed analysis information including cover structure, sections, and morphisms.",
    )
    _add_common_analysis_args(explain_parser)
    explain_parser.add_argument(
        "--site",
        type=str,
        default=None,
        help="Name of the site or scope to explain",
    )

    # --- prove ---
    prove_parser = subparsers.add_parser(
        "prove",
        help="Attempt to prove a specific property",
        description="Use sheaf-descent analysis to verify a specific property or contract.",
    )
    _add_common_analysis_args(prove_parser)
    prove_parser.add_argument(
        "--target",
        type=str,
        required=True,
        help="The property or function to prove",
    )

    # --- generate ---
    generate_parser = subparsers.add_parser(
        "generate",
        help="Generate contract annotations from analysis",
        description="Run analysis and output inferred @requires/@ensures decorators.",
    )
    _add_common_analysis_args(generate_parser)
    generate_parser.add_argument(
        "--output", "-o",
        type=str,
        default=None,
        help="Output file for generated contracts (default: stdout)",
    )

    # --- watch ---
    watch_parser = subparsers.add_parser(
        "watch",
        help="Watch files for changes and re-analyze",
        description="Monitor source files and re-run analysis when changes are detected.",
    )
    _add_common_analysis_args(watch_parser)

    return parser


def _add_common_analysis_args(parser: argparse.ArgumentParser) -> None:
    """Add analysis-related arguments common to multiple subcommands."""
    parser.add_argument(
        "files",
        nargs="*",
        default=[],
        help="Source files or directories to analyze",
    )
    parser.add_argument(
        "--max-iterations",
        type=int,
        default=20,
        help="Maximum number of synthesis iterations (default: 20)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=120.0,
        help="Total analysis timeout in seconds (default: 120)",
    )
    parser.add_argument(
        "--theory-packs",
        nargs="+",
        default=None,
        help=(
            "Theory packs to enable "
            "(e.g., builtin_arithmetic builtin_string builtin_collection)"
        ),
    )
    parser.add_argument(
        "--trust-threshold",
        choices=[
            "residual", "assumed", "trace_backed",
            "bounded_auto", "trusted_auto", "proof_backed",
        ],
        default="residual",
        help="Minimum trust level for reporting (default: residual)",
    )
    parser.add_argument(
        "--incremental",
        action="store_true",
        help="Enable incremental analysis mode",
    )


# ===================================================================
#  CLI entry point
# ===================================================================


def main(argv: Optional[Sequence[str]] = None) -> int:
    """Main CLI entry point.

    Parameters
    ----------
    argv : sequence of str, optional
        Command-line arguments.  Defaults to ``sys.argv[1:]``.

    Returns
    -------
    int
        Exit code (0 = success, 1 = errors found, 2 = usage error).
    """
    parser = _build_parser()
    args = parser.parse_args(argv)

    # Handle quiet mode
    if getattr(args, "quiet", False):
        args.verbose = 0

    # Default subcommand is "check"
    if args.subcommand is None:
        # If no subcommand but files given as positional args, default to check
        if hasattr(args, "files") and args.files:
            args.subcommand = "check"
        else:
            parser.print_help()
            return 0

    # Build CLI config from args
    cli_config = CLIConfig.from_args(args)

    # Load config file if present
    config_file_path = cli_config.config_file
    if config_file_path is None:
        # Auto-discover
        found = find_config_file()
        if found:
            config_file_path = str(found)

    if config_file_path:
        file_config = CLIConfig.from_file(config_file_path)
        cli_config = CLIConfig.merge(file_config, cli_config)

    # Dispatch to command
    command = get_command(cli_config.subcommand)
    if command is None:
        print(
            f"Unknown command: {cli_config.subcommand}. "
            f"Available: {', '.join(available_commands())}",
            file=sys.stderr,
        )
        return 2

    try:
        return command.run(cli_config)
    except KeyboardInterrupt:
        print("\nInterrupted.", file=sys.stderr)
        return 130
    except Exception as exc:
        print(f"Error: {exc}", file=sys.stderr)
        if cli_config.verbosity >= 3:
            import traceback
            traceback.print_exc()
        return 2


def cli_entry_point() -> None:
    """Console script entry point (for setup.py/pyproject.toml)."""
    sys.exit(main())


if __name__ == "__main__":
    cli_entry_point()
