"""Single deppy CLI runner for any ``.deppy`` sidecar specification.

Usage::

    python -m deppy.pipeline.run_verify <path-to.deppy>
    python -m deppy.pipeline.run_verify <path-to.deppy> --out OUT.lean
    python -m deppy.pipeline.run_verify <path-to.deppy> --module sympy

This is the user-facing entry point.  The actual pipeline lives in
:mod:`deppy.lean.sidecar_runner` (library-agnostic) and accepts any
``.deppy`` file.

When invoked with a single positional argument, the runner:

  1. Loads the ``.deppy`` via :meth:`SidecarModule.from_file`.
  2. Inspects the declared ``module:`` library to record version /
     source path for the certificate provenance.
  3. Renders the certificate (audit + mechanization + body
     translation + foundation Z3 + counterexample search +
     cubical analysis + cohomology cocycles + bicomplex + verify
     blocks + PSDL compilation + …).
  4. Writes the Lean text to the output path (default:
     ``<deppy-stem>.lean`` next to the input).
  5. Round-trips through :func:`deppy.lean.lean_runner.check_lean_module_source`.
  6. Prints the structured report and the certify_or_die verdict.

Exit code: ``0`` on success, ``1`` on failure to load / render.
"""
from __future__ import annotations

import sys

from deppy.lean.sidecar_runner import main as _main


if __name__ == "__main__":
    sys.exit(_main(sys.argv[1:]))
