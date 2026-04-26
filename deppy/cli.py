"""
deppy.cli — command-line interface for the verification harness.

Subcommands
-----------
    deppy check    <path>            — run the safety pipeline on a Python file or module
    deppy export   <path> --lean ... — compile to Lean 4, optionally invoke Lean
    deppy upgrade  <path> --level L  — re-run verification at a stricter trust level

The entry point is :func:`main`.  ``python -m deppy`` dispatches here.

Exit codes
----------
    0   verification succeeded
    1   verification produced a definitive failure (counterexample, rejected proof)
    2   verification was inconclusive (unknown / structural leaf / missing verifier)
    3   input error (file not found, unparseable Python)
"""
from __future__ import annotations

import argparse
import importlib
import importlib.util
import json
import os
import shutil
import sys
import types
from pathlib import Path
from typing import Callable, Optional


# ─────────────────────────────────────────────────────────────────────
# Target loading
# ─────────────────────────────────────────────────────────────────────

def _load_target(spec: str) -> tuple[str, str, Optional[types.ModuleType]]:
    """Resolve ``spec`` (a file path OR a dotted module path) to
    (display_name, source_text, imported_module_or_None).

    File paths: the file is read and returned as source.  Dotted specs:
    imported through ``importlib`` and the source is pulled via
    ``inspect.getsource(module)``.
    """
    # File path (has a suffix or contains a path separator).
    path = Path(spec)
    if path.exists() and path.is_file():
        source = path.read_text(encoding="utf-8")
        return str(path), source, None

    # Dotted module.
    try:
        mod = importlib.import_module(spec)
    except Exception as exc:
        raise FileNotFoundError(
            f"Could not resolve '{spec}' as a file or importable module: {exc}"
        )
    if not getattr(mod, "__file__", None):
        raise FileNotFoundError(
            f"Module '{spec}' has no __file__ attribute (C-extension?)"
        )
    source = Path(mod.__file__).read_text(encoding="utf-8")
    return mod.__name__, source, mod


# ─────────────────────────────────────────────────────────────────────
# `deppy check`
# ─────────────────────────────────────────────────────────────────────

def _cmd_check(args: argparse.Namespace) -> int:
    from deppy.pipeline.safety_pipeline import verify_module_safety

    try:
        display, source, _mod = _load_target(args.target)
    except FileNotFoundError as e:
        print(f"deppy check: {e}", file=sys.stderr)
        return 3

    sidecar_specs = None
    if getattr(args, "sidecar", None):
        from deppy.proofs.sidecar import SidecarModule
        sidecar_path = Path(args.sidecar)
        if not sidecar_path.is_file():
            print(
                f"deppy check: sidecar {sidecar_path} not found",
                file=sys.stderr,
            )
            return 3
        try:
            sm = SidecarModule.from_file(str(sidecar_path))
        except Exception as e:
            print(
                f"deppy check: failed to parse sidecar {sidecar_path}: {e}",
                file=sys.stderr,
            )
            return 3
        sidecar_specs = dict(sm.specs)

    verdict = verify_module_safety(
        source,
        module_path=display,
        use_drafts=args.use_drafts,
        emit_lean=args.emit_lean,
        verbose_progress=args.verbose,
        sidecar_specs=sidecar_specs,
    )

    if args.json:
        # Render the verdict as JSON — one object per function.
        payload = {
            "module_path": verdict.module_path,
            "module_safe": verdict.module_safe,
            "is_safe": verdict.is_safe,
            "aggregate_trust": verdict.aggregate_trust.name,
            "functions": {
                name: {
                    "name": fv.name,
                    "is_safe": fv.is_safe,
                    "trust": fv.trust.name,
                    "coverage_ratio": fv.coverage_ratio,
                    "unaddressed": list(fv.unaddressed),
                    "counterexamples": len(fv.counterexamples),
                }
                for name, fv in verdict.functions.items()
            },
            "notes": verdict.notes,
        }
        json.dump(payload, sys.stdout, indent=2)
        sys.stdout.write("\n")
    else:
        # Human-readable summary.
        print(verdict.summary())

    if verdict.is_safe:
        return 0
    # Decide 1 (definitive fail) vs 2 (inconclusive):
    # any function with a counterexample → 1, otherwise → 2.
    has_cex = any(fv.counterexamples for fv in verdict.functions.values())
    return 1 if has_cex else 2


# ─────────────────────────────────────────────────────────────────────
# `deppy export`
# ─────────────────────────────────────────────────────────────────────

def _cmd_export(args: argparse.Namespace) -> int:
    from deppy.lean.compiler import compile_to_lean

    try:
        display, _source, mod = _load_target(args.target)
    except FileNotFoundError as e:
        print(f"deppy export: {e}", file=sys.stderr)
        return 3

    if mod is None:
        # For file paths, import them first — compile_to_lean can also
        # take a raw path, but loading gives us access to decorated fns.
        spec = importlib.util.spec_from_file_location(
            Path(display).stem, display,
        )
        if spec is None or spec.loader is None:
            print(f"deppy export: failed to load {display}", file=sys.stderr)
            return 3
        mod = importlib.util.module_from_spec(spec)
        try:
            spec.loader.exec_module(mod)
        except Exception as exc:
            print(f"deppy export: failed to import {display}: {exc}",
                  file=sys.stderr)
            return 3

    output_path: Optional[Path] = Path(args.output) if args.output else None
    cert = compile_to_lean(mod, output_path=output_path)

    # Optionally invoke Lean.
    if args.run_lean:
        cert = cert.verify_with_lean(timeout_s=args.lean_timeout)

    if args.json:
        payload = {
            "module_name": cert.module_name,
            "trust_level": cert.trust_level,
            "is_kernel_verified": cert.is_kernel_verified,
            "is_syntax_complete": cert.is_syntax_complete,
            "sorry_count": cert.sorry_count,
            "proved_count": cert.proved_count,
            "obligations": list(cert.obligations),
            "output_path": str(output_path) if output_path else None,
            "lean_stdout": cert.lean_check_stdout,
            "lean_stderr": cert.lean_check_stderr,
        }
        json.dump(payload, sys.stdout, indent=2)
        sys.stdout.write("\n")
    else:
        print(cert.summary())
        if output_path:
            print(f"\nWrote {output_path}")

    # Exit codes (stricter; distinguishes hard reject from
    # axiom-dependent / inconclusive):
    #   0 — Lean accepted, or no-sorry no-axiom syntactically complete
    #   1 — Lean ran and rejected the file (definitive failure)
    #   2 — file declares raw axioms, OR Lean didn't run, OR Lean missing
    if cert.is_kernel_verified:
        return 0
    if cert.trust_level == "LEAN_REJECTED":
        return 1
    if cert.trust_level == "LEAN_SYNTAX_COMPLETE":
        return 0
    if cert.trust_level == "ASSUMPTION_DEPENDENT":
        return 2
    if cert.trust_level == "LEAN_UNAVAILABLE":
        return 2
    return 2


# ─────────────────────────────────────────────────────────────────────
# `deppy upgrade`
# ─────────────────────────────────────────────────────────────────────

# Map level names the CLI accepts → kernel TrustLevel / Lean label.
# Users invoke ``deppy upgrade --level LEAN_KERNEL_VERIFIED foo.py``.
_UPGRADE_LEVELS = {
    "KERNEL",
    "Z3_VERIFIED",
    "STRUCTURAL_CHAIN",
    "LEAN_KERNEL_VERIFIED",
    "LEAN_SYNTAX_COMPLETE",
}


def _cmd_upgrade(args: argparse.Namespace) -> int:
    from deppy.pipeline.safety_pipeline import verify_module_safety
    from deppy.core.kernel import TrustLevel

    if args.level not in _UPGRADE_LEVELS:
        print(
            f"deppy upgrade: unknown target level '{args.level}'.  "
            f"Pick one of: {sorted(_UPGRADE_LEVELS)}",
            file=sys.stderr,
        )
        return 3

    try:
        display, source, mod = _load_target(args.target)
    except FileNotFoundError as e:
        print(f"deppy upgrade: {e}", file=sys.stderr)
        return 3

    # First: run the pipeline in its normal mode.
    verdict = verify_module_safety(
        source,
        module_path=display,
        use_drafts=True,
        emit_lean=args.level == "LEAN_KERNEL_VERIFIED",
        verbose_progress=args.verbose,
    )

    # If the user asked for a Lean-kernel upgrade, re-run through the
    # Lean compiler and actually invoke Lean.
    lean_ok = True
    if args.level in {"LEAN_KERNEL_VERIFIED", "LEAN_SYNTAX_COMPLETE"}:
        from deppy.lean.compiler import compile_to_lean

        if mod is None:
            spec = importlib.util.spec_from_file_location(
                Path(display).stem, display,
            )
            if spec is None or spec.loader is None:
                print(f"deppy upgrade: failed to load {display}",
                      file=sys.stderr)
                return 3
            mod = importlib.util.module_from_spec(spec)
            try:
                spec.loader.exec_module(mod)
            except Exception as exc:
                print(f"deppy upgrade: failed to import: {exc}",
                      file=sys.stderr)
                return 3

        cert = compile_to_lean(mod)
        if args.level == "LEAN_KERNEL_VERIFIED":
            cert = cert.verify_with_lean(timeout_s=args.lean_timeout)
            lean_ok = cert.is_kernel_verified
        else:
            lean_ok = cert.is_syntax_complete

    # Decide whether the target level was reached.
    target_reached = False
    target = args.level
    if target == "LEAN_KERNEL_VERIFIED":
        target_reached = lean_ok
    elif target == "LEAN_SYNTAX_COMPLETE":
        target_reached = lean_ok
    elif target == "KERNEL":
        target_reached = verdict.aggregate_trust >= TrustLevel.KERNEL
    elif target == "Z3_VERIFIED":
        target_reached = verdict.aggregate_trust >= TrustLevel.Z3_VERIFIED
    elif target == "STRUCTURAL_CHAIN":
        target_reached = verdict.aggregate_trust >= TrustLevel.STRUCTURAL_CHAIN

    if args.json:
        payload = {
            "target_level": target,
            "reached": target_reached,
            "module_path": verdict.module_path,
            "aggregate_trust": verdict.aggregate_trust.name,
        }
        json.dump(payload, sys.stdout, indent=2)
        sys.stdout.write("\n")
    else:
        mark = "✓" if target_reached else "✗"
        print(f"{mark} upgrade to {target}: "
              f"aggregate_trust = {verdict.aggregate_trust.name}")
        if not target_reached:
            print("  ↳ not reached.  Consider:")
            print("      (1) adding @guarantee / @requires specs,")
            print("      (2) installing z3-solver for SMT discharge,")
            print("      (3) installing the `lean` binary for "
                  "LEAN_KERNEL_VERIFIED.")

    return 0 if target_reached else 2


# ─────────────────────────────────────────────────────────────────────
# Argument parsing
# ─────────────────────────────────────────────────────────────────────

def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="deppy",
        description=(
            "Deppy: Python with dependent types.  Verify code via Z3, "
            "the deppy kernel, or export to Lean 4."
        ),
    )
    sub = p.add_subparsers(dest="command", required=True, metavar="{check,export,upgrade}")

    # check
    p_check = sub.add_parser(
        "check",
        help="Run the safety pipeline on a Python file or module",
    )
    p_check.add_argument("target", help="Path to .py file or dotted module name")
    p_check.add_argument("--no-drafts", dest="use_drafts", action="store_false",
                         default=True,
                         help="Disable auto-inferred draft specs")
    p_check.add_argument("--emit-lean", action="store_true",
                         help="Also emit Lean proofs for verified functions")
    p_check.add_argument("--sidecar", metavar="PATH",
                         help="Path to a .deppy or .json sidecar spec file")
    p_check.add_argument("--json", action="store_true", help="Emit JSON verdict")
    p_check.add_argument("--verbose", action="store_true",
                         help="Verbose progress output")
    p_check.set_defaults(func=_cmd_check)

    # export
    p_export = sub.add_parser(
        "export",
        help="Compile to Lean 4; optionally invoke the lean binary",
    )
    p_export.add_argument("target", help="Path to .py file or module name")
    p_export.add_argument("--output", "-o",
                          help="Write the rendered .lean file here")
    p_export.add_argument("--run-lean", action="store_true",
                          help="After rendering, run `lean` against the file "
                               "(sets LEAN_KERNEL_VERIFIED on success)")
    p_export.add_argument("--lean-timeout", type=int, default=60,
                          help="Timeout (seconds) for the lean invocation")
    p_export.add_argument("--json", action="store_true",
                          help="Emit JSON certificate summary")
    p_export.set_defaults(func=_cmd_export)

    # upgrade
    p_up = sub.add_parser(
        "upgrade",
        help="Re-run verification aiming at a target trust level",
    )
    p_up.add_argument("target", help="Path to .py file or module name")
    p_up.add_argument("--level", "--to", dest="level", required=True,
                      choices=sorted(_UPGRADE_LEVELS),
                      help="Target trust level (--to is an alias)")
    p_up.add_argument("--lean-timeout", type=int, default=60,
                      help="Timeout (seconds) for lean invocation")
    p_up.add_argument("--json", action="store_true")
    p_up.add_argument("--verbose", action="store_true")
    p_up.set_defaults(func=_cmd_upgrade)

    # trust — convenience grouping; ``deppy trust upgrade <path> --to L``
    # behaves identically to ``deppy upgrade <path> --level L``.
    p_trust = sub.add_parser(
        "trust",
        help="Trust-level subcommands (alias group: `trust upgrade …`)",
    )
    trust_sub = p_trust.add_subparsers(
        dest="trust_command", required=True, metavar="{upgrade}",
    )
    p_trust_up = trust_sub.add_parser(
        "upgrade",
        help="Alias for `deppy upgrade --level …`",
    )
    p_trust_up.add_argument("target", help="Path to .py file or module name")
    p_trust_up.add_argument("--to", "--level", dest="level", required=True,
                            choices=sorted(_UPGRADE_LEVELS),
                            help="Target trust level")
    p_trust_up.add_argument("--lean-timeout", type=int, default=60)
    p_trust_up.add_argument("--json", action="store_true")
    p_trust_up.add_argument("--verbose", action="store_true")
    p_trust_up.set_defaults(func=_cmd_upgrade)

    return p


def main(argv: Optional[list[str]] = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
