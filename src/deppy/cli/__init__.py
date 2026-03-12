"""deppy.cli -- Command-line interface for sheaf-descent semantic typing.

Subcommands: check, explain, prove, generate, watch.

Usage::

    deppy check myfile.py
    deppy explain myfile.py --site my_function
"""

from deppy.cli.main import main, cli_entry_point
from deppy.cli.config import CLIConfig, find_config_file
from deppy.cli.commands import (
    CheckCommand,
    Command,
    ExplainCommand,
    GenerateCommand,
    ProveCommand,
    WatchCommand,
    available_commands,
    get_command,
)
from deppy.cli.formatters import (
    Formatter,
    JsonFormatter,
    PlainFormatter,
    TerminalFormatter,
    create_formatter,
)

__all__ = [
    # main
    "main",
    "cli_entry_point",
    # config
    "CLIConfig",
    "find_config_file",
    # commands
    "CheckCommand",
    "Command",
    "ExplainCommand",
    "GenerateCommand",
    "ProveCommand",
    "WatchCommand",
    "available_commands",
    "get_command",
    # formatters
    "Formatter",
    "JsonFormatter",
    "PlainFormatter",
    "TerminalFormatter",
    "create_formatter",
]
