"""Run deppy on geometry_properties.py + sympy_geometry.deppy and
produce a Lean certificate.

This is the entry point a user would invoke:

    PYTHONPATH=. python3 verify_sympy_geometry/run_verify.py

It exercises the full deppy stack — pipeline analysis, cubical AST,
@implies tactic selection, cohomology emission, certificate write —
and prints a structured summary plus the path of the produced
``.lean`` file.
"""
from __future__ import annotations

import sys
import time
from pathlib import Path


def main() -> int:
    here = Path(__file__).resolve().parent
    py_path = here / "geometry_properties.py"
    deppy_path = here / "sympy_geometry.deppy"
    out_path = here / "GeometryCertificate.lean"

    # Read the Python source.
    source = py_path.read_text()

    # Load the sidecar specs AND axioms.
    sidecar_specs = None
    sidecar_module = None
    try:
        from deppy.proofs.sidecar import SidecarModule
        sm = SidecarModule.from_file(str(deppy_path))
        sidecar_specs = dict(sm.specs)
        sidecar_module = sm
    except Exception as e:
        print(
            f"deppy: WARNING — failed to load sidecar "
            f"{deppy_path.name}: {e}",
            file=sys.stderr,
        )

    # Produce the Lean certificate.
    from deppy.lean.certificate import write_certificate
    t0 = time.perf_counter()
    report = write_certificate(
        source, out_path,
        sidecar_specs=sidecar_specs,
        sidecar_module=sidecar_module,
        use_drafts=True,
        module_name="DeppySympyGeometry",
        run_lean=False,
    )
    elapsed = (time.perf_counter() - t0) * 1000

    cert = report.certificate
    print()
    print("═" * 70)
    print("  Deppy — Sympy Geometry Verification Report")
    print(f"  Sidecar:    {deppy_path.name}")
    print(f"  Source:     {py_path.name}")
    print(f"  Output:     {out_path.name}")
    print("─" * 70)
    print(f"  Functions:                {cert.function_count}")
    print(f"  Theorems (total):         {cert.theorem_count}")
    print(f"    safety + @implies:      "
          f"{cert.theorem_count - cert.cubical_kan_theorems_count - cert.cubical_higher_path_theorems_count}")
    print(f"    cubical Kan theorems:   {cert.cubical_kan_theorems_count}")
    print(f"    cubical higher paths:   {cert.cubical_higher_path_theorems_count}")
    print(f"  Aux declarations:         {cert.aux_decl_count}")
    print(f"  Sorries:                  {cert.sorry_count}  "
          f"(of which {cert.cubical_sorries} from cubical)")
    print()
    print("  Cohomology (round-2):")
    print(f"    |C^0| (per-fn safety):  {cert.cocycle_count_c0}")
    print(f"    |C^1| (call edges):     {cert.cocycle_count_c1}")
    print(f"    |C^2| (composition):    {cert.cocycle_count_c2}")
    print(f"    |H^0| (verified-safe):  {cert.cohomology_h0_size}")
    print(f"    |H^1| (open):           {cert.cohomology_h1_size}")
    print(f"    |H^2| (coherence):      {cert.cohomology_h2_size}")
    print()
    print("  @implies accounting:")
    print(f"    Total:                  {cert.implies_count}")
    print(f"    Auto-proved:            {cert.implies_auto_proved}")
    print(f"    User-supplied:          {cert.implies_user_supplied}")
    print(f"    Unproved (sorry):       {cert.implies_unproved}")
    print()
    print(f"  Elapsed: {elapsed:.0f} ms")
    print("═" * 70)
    print(f"\n  Certificate written to:  {out_path}")
    if cert.sorry_count == 0:
        print(f"  ✓ All theorems closed without sorry.")
    else:
        print(
            f"  ⚠ {cert.sorry_count} sorry/sorries — "
            f"obligations honestly admitted.\n"
            f"    Inspect the certificate to see which."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
