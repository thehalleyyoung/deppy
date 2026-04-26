"""Entry point for ``python -m deppy``."""
from __future__ import annotations

import sys

from deppy.cli import main

if __name__ == "__main__":
    sys.exit(main())
