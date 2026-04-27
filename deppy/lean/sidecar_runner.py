"""Generic deppy CLI: take any ``.deppy`` sidecar (and any target
library it references) and emit a Lean certificate.

This is the library-agnostic runner.  No part of it knows about
sympy, numpy, torch, or any other specific library — the .deppy
file's ``module:`` declaration and target paths drive everything.

Usage as a module::

    python -m deppy.lean.sidecar_runner <path-to.deppy> [--out OUT.lean]

Usage from Python::

    from deppy.lean.sidecar_runner import run_sidecar
    section = run_sidecar(
        "path/to/spec.deppy",
        out_path="path/to/Certificate.lean",
    )
    print(section.full_text[:400])

The runner:

  1. Loads the .deppy via :meth:`SidecarModule.from_file`.
  2. Inspects the declared ``module:`` library to record version /
     source path for the certificate's provenance comment.
  3. Renders the certificate via
     :func:`deppy.lean.sidecar_certificate.render_sidecar_section`
     (which engages: source audit, mechanization, body translation,
     code-proofs via deppy's kernel, fibration descent, cubical
     analysis, and ``verify`` blocks).
  4. Writes the Lean text to ``out_path`` and prints a structured
     report identical to the per-library run scripts.
"""
from __future__ import annotations

import argparse
import importlib
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


@dataclass
class RunReport:
    """Aggregate report from :func:`run_sidecar`."""
    section: object                       # SidecarCertificateSection
    elapsed_ms: float = 0.0
    out_path: Optional[Path] = None
    library_summary: str = ""
    sidecar_path: Path = Path()
    # deppy.lean.lean_runner.check_lean_module_source result.
    lean_runner_ok: bool = False
    lean_runner_stderr: str = ""
    lean_runner_invoked: bool = False
    # certify_or_die verdict
    certified: bool = False
    certify_failures: list[str] = field(default_factory=list)
    # AUDIT 1.A.7 — JSON sidecar path (machine-readable report
    # with goal-state-on-failure + counters).  ``None`` if not
    # emitted; ``json_emission_error`` records the reason.
    json_sidecar_path: Optional[Path] = None
    json_emission_error: str = ""


def _certify_or_die(s) -> tuple[bool, list[str]]:
    """Top-level certification verdict.  Refuses to certify when:

      * lean_runner round-trip fails, OR
      * any soundness gate fired, OR
      * any counterexample was found for an admitted foundation, OR
      * any code-proof was rejected by the kernel, OR
      * AUDIT 1.5: any theorem cited a counterexample-rejected foundation, OR
      * AUDIT 1.11: any verify block had a hash drift, OR
      * AUDIT 1.12: any expecting_counterexample expectation was violated.
    """
    failures: list[str] = []
    if s.soundness_gate_fail > 0:
        failures.append(
            f"soundness gate fired in {s.soundness_gate_fail} proof(s)"
        )
    if s.counterexamples_found > 0:
        failures.append(
            f"{s.counterexamples_found} counterexample(s) found "
            "for admitted foundations"
        )
    if getattr(s, "rejected_theorem_count", 0) > 0:
        failures.append(
            f"{s.rejected_theorem_count} theorem(s) cited "
            "counterexample-rejected foundations"
        )
    if getattr(s, "hash_drift_count", 0) > 0:
        failures.append(
            f"{s.hash_drift_count} verify block(s) failed "
            "expects_sha256 hash check"
        )
    if getattr(s, "counterexample_expectation_violations", 0) > 0:
        failures.append(
            f"{s.counterexample_expectation_violations} verify block(s) "
            "expected counterexample but none found"
        )
    return (len(failures) == 0, failures)


def _inspect_library(module_name: str) -> str:
    """Return a one-line provenance string for the named library."""
    if not module_name:
        return ""
    try:
        mod = importlib.import_module(module_name)
    except (ImportError, ValueError):
        return f"{module_name} (not importable)"
    version = getattr(mod, "__version__", "?")
    source = getattr(mod, "__file__", "<unknown>")
    return f"{module_name} {version} — {Path(source).parent.name if source != '<unknown>' else '?'}"


def run_sidecar(
    deppy_path: str | Path,
    *,
    out_path: Optional[str | Path] = None,
    module_name: str = "",
) -> RunReport:
    """Run the full deppy sidecar pipeline on a ``.deppy`` file.

    Args:
        deppy_path: Path to the .deppy specification.
        out_path:   Where to write the Lean certificate.  When
                    omitted, defaults to ``<deppy_path>.lean``.
        module_name: Override the ``module:`` declaration in the
                    .deppy.  When empty, uses whatever the file
                    declares.

    Returns:
        :class:`RunReport` whose ``section`` field is the rendered
        :class:`SidecarCertificateSection`.
    """
    deppy_path = Path(deppy_path)
    if out_path is None:
        out_path = deppy_path.with_suffix(".lean")
    out_path = Path(out_path)

    from deppy.proofs.sidecar import SidecarModule
    from deppy.lean.sidecar_certificate import render_sidecar_section

    sm = SidecarModule.from_file(str(deppy_path))
    target_module = module_name or getattr(sm, "name", "") or ""
    library_summary = _inspect_library(target_module)

    t0 = time.perf_counter()
    section = render_sidecar_section(
        sm,
        module_name=f"Deppy_{deppy_path.stem}",
        library_source_summary=library_summary,
    )
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    out_path.write_text(section.full_text, encoding="utf-8")

    # Round-trip through deppy.lean.lean_runner — actually invoke
    # Lean and record the kernel verdict (not just the parser's).
    lean_ok = False
    lean_stderr = ""
    lean_invoked = False
    try:
        from deppy.lean.lean_runner import check_lean_module_source
        result = check_lean_module_source(section.full_text, timeout_s=60)
        lean_invoked = True
        lean_ok = result.ok
        lean_stderr = result.stderr or ""
    except Exception as e:  # pragma: no cover
        lean_stderr = f"lean_runner failed: {e}"

    rr = RunReport(
        section=section,
        elapsed_ms=elapsed_ms,
        out_path=out_path,
        library_summary=library_summary,
        sidecar_path=deppy_path,
        lean_runner_ok=lean_ok,
        lean_runner_stderr=lean_stderr,
        lean_runner_invoked=lean_invoked,
    )
    certified, failures = _certify_or_die(section)
    if lean_invoked and not lean_ok:
        certified = False
        failures.append("lean_runner round-trip rejected")
    rr.certified = certified
    rr.certify_failures = failures
    # AUDIT 1.A.7 / K.1 — emit a machine-readable JSON sidecar
    # alongside the .lean output.  When Lean rejects the certificate,
    # the JSON contains the goal-state-on-failure (parsed from
    # stderr) plus per-verify-block outcomes (success/fail, kernel
    # trust level, axioms used, counterexample explanation when
    # rejected).  Tools and LLMs can consume this directly.
    try:
        import json
        json_path = out_path.with_suffix(".json")
        json_payload = {
            "sidecar": str(deppy_path),
            "lean_path": str(out_path),
            "library_summary": library_summary,
            "elapsed_ms": elapsed_ms,
            "certified": certified,
            "failures": list(failures),
            "lean_runner": {
                "invoked": lean_invoked,
                "ok": lean_ok,
                "stderr": lean_stderr,
                # Goal state on failure: heuristically extract any
                # ``unsolved goals`` block from stderr so the user
                # / LLM sees what's still open.
                "goal_state_on_failure": _extract_goal_states(
                    lean_stderr,
                ) if not lean_ok else [],
            },
            "section_counters": {
                "foundation_count": section.foundation_count,
                "axiom_count": section.axiom_count,
                "verify_total": section.verify_total,
                "verify_kernel_verified": section.verify_kernel_verified,
                "mechanized_axioms": section.mechanized_axioms,
                "body_links_exact": section.body_links_exact,
                "body_links_sorry": section.body_links_sorry,
                "counterexamples_found": section.counterexamples_found,
                "counterexamples_attempted": (
                    section.counterexamples_attempted
                ),
                "rejected_theorem_count": section.rejected_theorem_count,
                "soundness_gate_pass": section.soundness_gate_pass,
                "soundness_gate_fail": section.soundness_gate_fail,
                "foundations_z3_verified": section.foundations_z3_verified,
                "foundations_z3_attempted": section.foundations_z3_attempted,
                "kan_obligations_total": section.kan_obligations_total,
                "kan_obligations_verified": (
                    section.kan_obligations_verified
                ),
                "cubical_methods_analysed": section.cubical_methods_analysed,
                "cubical_total_cells": section.cubical_total_cells,
                "cohomology_c0_count": section.cohomology_c0_count,
                "cohomology_c1_count": section.cohomology_c1_count,
                "cohomology_c2_count": section.cohomology_c2_count,
            },
            "classification_counts": dict(section.classification_counts),
            "unmatched_proofs": list(section.unmatched_proofs),
        }
        json_path.write_text(
            json.dumps(json_payload, indent=2, default=str),
            encoding="utf-8",
        )
        rr.json_sidecar_path = json_path
    except Exception as e:  # pragma: no cover
        # Don't fail the whole run if JSON emission has a problem;
        # just record it.
        rr.json_emission_error = f"{e}"
    return rr


def _extract_goal_states(stderr: str) -> list[dict]:
    """Heuristically extract ``unsolved goals`` blocks from Lean
    stderr — each block is a structured payload tools/LLMs can use
    to drive the next iteration.

    Lean's ``unsolved goals`` message format::

        <file>:<line>:<col>: error: unsolved goals
        ⊢ <goal_text>

    We split on that header and capture the goal text per block.
    """
    if not stderr:
        return []
    out: list[dict] = []
    lines = stderr.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if "unsolved goals" in line:
            # Parse the location prefix.
            location = ""
            try:
                head, _ = line.split("error", 1)
                location = head.strip().rstrip(":")
            except ValueError:
                pass
            # Following lines until the next ``error`` / ``warning``
            # are the goal text.
            j = i + 1
            goal_lines: list[str] = []
            while j < len(lines):
                ln = lines[j]
                if (
                    ":" in ln
                    and (" error:" in ln or " warning:" in ln)
                ):
                    break
                goal_lines.append(ln)
                j += 1
            out.append({
                "location": location,
                "goal_text": "\n".join(goal_lines).strip(),
            })
            i = j
            continue
        i += 1
    return out


def print_report(rr: RunReport) -> None:
    """Print a structured human-readable report to stdout."""
    s = rr.section
    print()
    print("═" * 72)
    print("  Deppy sidecar verification report")
    print(f"  Sidecar:  {rr.sidecar_path.name}")
    print(f"  Library:  {rr.library_summary}")
    print(f"  Output:   {rr.out_path.name if rr.out_path else '<none>'}")
    print("─" * 72)
    print(f"  Foundations declared (trust surface):    {s.foundation_count}")
    print(f"  Sidecar axioms (library claims):         {s.axiom_count}")
    print(f"    grounded (formal + methods exist):     {s.grounded_axioms}")
    print(f"      mechanized (concrete Lean Props):    {s.mechanized_axioms}")
    print(f"    NL documentation:                      {s.nl_axioms}")
    print(f"    target-missing:                        {s.target_missing_axioms}")
    print(f"    method-missing:                        {s.method_missing_axioms}")
    print(f"  Body links (deppy.body_translation on source):")
    print(f"    methods linked total:                  {s.body_links_total}")
    print(f"    translation EXACT:                     {s.body_links_exact}")
    print(f"    translation produced sorry:            {s.body_links_sorry}")
    print(f"    resolution/parse errors:               {s.body_links_error}")
    print(f"  Code-proofs (kernel-verified ProofTerms):")
    print(f"    matched & emitted as theorems:         {s.code_proofs_matched}")
    print(f"    soundness gate (no Structural leaf):   "
          f"{s.soundness_gate_pass} pass / {s.soundness_gate_fail} fail")
    print(f"  Cubical analysis (deppy.pipeline.cubical_ast):")
    print(f"    methods analysed:                      {s.cubical_methods_analysed}")
    print(f"    total cells:                           {s.cubical_total_cells}")
    print(f"    Kan candidates:                        {s.cubical_kan_candidates}")
    print(f"    Kan-fill obligations / kernel-verified:"
          f" {s.kan_obligations_total}/{s.kan_obligations_verified}")
    print(f"  Cohomology (deppy.lean.cohomology emitter):")
    print(f"    C⁰ cocycles (per-function):            {s.cohomology_c0_count}")
    print(f"    C¹ cocycles (per call site):           {s.cohomology_c1_count}")
    print(f"    C² coherences (per chain):             {s.cohomology_c2_count}")
    print(f"  Bicomplex (deppy.lean.cubical_simplicial_bicomplex):")
    print(f"    built:                                 {s.bicomplex_built}")
    print(f"    edges / faces / Euler χ:               "
          f"{s.bicomplex_edges} / {s.bicomplex_faces} / {s.bicomplex_euler}")
    print(f"  Fibration descent (FibrationVerifier.verify_per_fiber):")
    print(f"    outcomes / successes:                  "
          f"{s.fibration_outcomes} / {s.fibration_successes}")
    print(f"  Foundation Z3 discharge:")
    print(f"    foundations / Z3-attempted / verified: "
          f"{s.foundations_total} / {s.foundations_z3_attempted} / "
          f"{s.foundations_z3_verified}")
    print(f"  Counterexample search (deppy.pipeline.counterexample):")
    print(f"    foundations attempted / counterexamples: "
          f"{s.counterexamples_attempted} / {s.counterexamples_found}")
    print(f"  Subsystem invocations (B1–B16 audit batch):")
    print(f"    invoked / successful:                  "
          f"{s.subsystems_invoked} / {s.subsystems_successful}")
    print(f"  ProofTerm subclasses (C1–C7 audit batch):")
    print(f"    constructed / kernel-accepted:         "
          f"{s.proofterm_subclasses_probed} / "
          f"{s.proofterm_subclasses_kernel_accepted}")
    print(f"  ``verify`` blocks (.deppy → kernel.verify):")
    print(f"    total verify blocks:                   {s.verify_total}")
    print(f"    accepted by ProofKernel.verify:        {s.verify_kernel_verified}")
    print(f"  Specs (informational):                   {s.spec_count}")
    print(f"  Proofs total:                            {s.proof_count}")
    print(f"    derived (real proof bodies):           {s.derived_count}")
    print(f"    cited  (renaming of trusted axioms):   {s.cited_count}")
    print(f"    sorry  (unrecognised by-clause):       {s.sorry_count}")
    if s.classification_counts:
        print("  Per-classification:")
        for k, v in sorted(s.classification_counts.items()):
            print(f"    {k:24s} : {v}")
    if s.unmatched_proofs:
        print(f"  Unmatched proofs: {len(s.unmatched_proofs)}")
    print(f"  Elapsed:                                 {rr.elapsed_ms:.1f} ms")
    print("─" * 72)
    if rr.lean_runner_invoked:
        verdict = "OK" if rr.lean_runner_ok else "REJECTED"
        print(
            f"  deppy.lean.lean_runner round-trip:       {verdict}"
        )
        if not rr.lean_runner_ok and rr.lean_runner_stderr:
            preview = rr.lean_runner_stderr.strip().splitlines()[:3]
            for line in preview:
                print(f"    {line[:80]}")
    else:
        print(
            f"  deppy.lean.lean_runner round-trip:       not invoked"
        )
    print("─" * 72)
    if rr.certified:
        print(f"  ✓ CERTIFIED — top-level certify_or_die: PASS")
    else:
        print(f"  ✗ NOT CERTIFIED — failures:")
        for f in rr.certify_failures:
            print(f"    • {f}")
    print("═" * 72)
    if rr.out_path:
        print(f"  Certificate at: {rr.out_path}")
    if rr.json_sidecar_path is not None:
        print(f"  JSON sidecar:   {rr.json_sidecar_path}")
    if rr.json_emission_error:
        print(f"  JSON sidecar error: {rr.json_emission_error}")
    print()


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        prog="deppy.lean.sidecar_runner",
        description=(
            "Run the deppy sidecar verification pipeline on a .deppy "
            "file (or a Python module with @foundation/@axiom/@verify "
            "decorators) and emit a Lean certificate."
        ),
    )
    p.add_argument(
        "deppy",
        nargs="?",
        default=None,
        help="path to .deppy specification (or omit when using --from-module)",
    )
    p.add_argument(
        "--out", default=None,
        help="output Lean path (default: <deppy>.lean / <module>.lean)",
    )
    p.add_argument(
        "--module", default="",
        help="override the .deppy ``module:`` declaration",
    )
    p.add_argument(
        "--from-module", default=None, dest="from_module",
        help=(
            "import a Python module and extract its decorator-based "
            "sidecar (alternative to a .deppy file).  Example: "
            "``--from-module examples.decorated_geometry``"
        ),
    )
    args = p.parse_args(argv)

    if not args.deppy and not args.from_module:
        p.error("either deppy path or --from-module is required")

    try:
        if args.from_module:
            rr = run_sidecar_from_module(
                args.from_module,
                out_path=args.out,
                module_name=args.module,
            )
        else:
            rr = run_sidecar(
                args.deppy,
                out_path=args.out,
                module_name=args.module,
            )
    except Exception as e:
        print(
            f"deppy.sidecar_runner: failed: {e}",
            file=sys.stderr,
        )
        return 1
    print_report(rr)
    return 0


def run_sidecar_from_module(
    module_path: str,
    *,
    out_path: Optional[str | Path] = None,
    module_name: str = "",
) -> RunReport:
    """Import a Python module by dotted path, extract the
    decorator-based sidecar, and run the same pipeline that
    ``.deppy`` uses.

    The module is imported via :func:`importlib.import_module` so
    its decorators run as a side effect.  All
    ``__deppy_foundation__`` / ``__deppy_axiom__`` /
    ``__deppy_verify__`` / ``__deppy_spec__`` / ``__deppy_lemma__``
    attributes are scanned.

    Output paths default to ``<module_basename>.lean`` /
    ``<module_basename>.json`` in the current working directory.
    """
    import importlib
    from deppy.proofs.sidecar_decorators import extract_sidecar_module
    mod = importlib.import_module(module_path)
    sm = extract_sidecar_module(mod)
    if not out_path:
        basename = module_path.split(".")[-1]
        out_path = Path.cwd() / f"{basename}.lean"
    return _run_with_module(
        sm,
        out_path=Path(out_path),
        sidecar_path=Path(getattr(mod, "__file__", module_path)),
        module_name=module_name,
    )


def _run_with_module(
    sm,
    *,
    out_path: Path,
    sidecar_path: Path,
    module_name: str = "",
) -> RunReport:
    """Run the certificate emitter + Lean round-trip on an
    in-memory ``SidecarModule`` (no file path).  Shared internals
    of ``run_sidecar`` and ``run_sidecar_from_module``.
    """
    import time
    import json
    library_summary = _detect_library_summary(sm, module_name)
    t0 = time.perf_counter()
    from deppy.lean.sidecar_certificate import render_sidecar_section
    section = render_sidecar_section(
        sm,
        module_name=module_name or sm.name or "DecoratedSidecar",
        library_source_summary=library_summary,
    )
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    out_path.write_text(section.full_text, encoding="utf-8")
    lean_ok = False
    lean_stderr = ""
    lean_invoked = False
    try:
        from deppy.lean.lean_runner import check_lean_module_source
        result = check_lean_module_source(section.full_text, timeout_s=60)
        lean_invoked = True
        lean_ok = result.ok
        lean_stderr = result.stderr or ""
    except Exception as e:  # pragma: no cover
        lean_stderr = f"lean_runner failed: {e}"
    rr = RunReport(
        section=section,
        elapsed_ms=elapsed_ms,
        out_path=out_path,
        library_summary=library_summary,
        sidecar_path=sidecar_path,
        lean_runner_ok=lean_ok,
        lean_runner_stderr=lean_stderr,
        lean_runner_invoked=lean_invoked,
    )
    certified, failures = _certify_or_die(section)
    if lean_invoked and not lean_ok:
        certified = False
        failures.append("lean_runner round-trip rejected")
    rr.certified = certified
    rr.certify_failures = failures
    # JSON sidecar — same as run_sidecar.
    try:
        json_path = out_path.with_suffix(".json")
        json_payload = {
            "sidecar": str(sidecar_path),
            "lean_path": str(out_path),
            "library_summary": library_summary,
            "elapsed_ms": elapsed_ms,
            "certified": certified,
            "failures": list(failures),
            "lean_runner": {
                "invoked": lean_invoked,
                "ok": lean_ok,
                "stderr": lean_stderr,
                "goal_state_on_failure": _extract_goal_states(
                    lean_stderr,
                ) if not lean_ok else [],
            },
            "section_counters": {
                "foundation_count": section.foundation_count,
                "axiom_count": section.axiom_count,
                "verify_total": section.verify_total,
                "verify_kernel_verified": section.verify_kernel_verified,
                "mechanized_axioms": section.mechanized_axioms,
                "body_links_exact": section.body_links_exact,
                "body_links_sorry": section.body_links_sorry,
                "counterexamples_found": section.counterexamples_found,
                "counterexamples_attempted": (
                    section.counterexamples_attempted
                ),
                "rejected_theorem_count": section.rejected_theorem_count,
                "soundness_gate_pass": section.soundness_gate_pass,
                "soundness_gate_fail": section.soundness_gate_fail,
                "foundations_z3_verified": section.foundations_z3_verified,
                "foundations_z3_attempted": section.foundations_z3_attempted,
            },
            "classification_counts": dict(section.classification_counts),
            "unmatched_proofs": list(section.unmatched_proofs),
        }
        json_path.write_text(
            json.dumps(json_payload, indent=2, default=str),
            encoding="utf-8",
        )
        rr.json_sidecar_path = json_path
    except Exception as e:  # pragma: no cover
        rr.json_emission_error = f"{e}"
    return rr


def _detect_library_summary(sm, module_name: str) -> str:
    """Best-effort summary of the library/module the sidecar targets."""
    name = module_name or sm.name or "<sidecar>"
    return name


if __name__ == "__main__":
    sys.exit(main())


__all__ = ["run_sidecar", "print_report", "main", "RunReport"]
