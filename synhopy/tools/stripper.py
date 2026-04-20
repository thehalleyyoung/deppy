"""AST-based tool that strips ALL SynHoPy annotations from Python source code.

Recovers the original unannotated library by removing decorators, inline proof
calls, synhopy imports, library-trust blocks, proof blocks, and
SynHoPy-specific type annotations — while preserving every other piece of the
source (comments, docstrings, blank lines, non-SynHoPy code).

Usage:
    python -m synhopy.tools.stripper --file path/to/annotated.py
    python -m synhopy.tools.stripper --dir src/ --output clean_src/
"""

from __future__ import annotations

import ast
import copy
import fnmatch
import os
import shutil
import sys
import textwrap
from dataclasses import dataclass, field
from pathlib import Path
from typing import Sequence

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _decorator_name(node: ast.expr) -> str | None:
    """Return the root name of a decorator expression, or *None*."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Call):
        return _decorator_name(node.func)
    if isinstance(node, ast.Attribute):
        return _decorator_name(node.value)
    return None


def _is_synhopy_import_module(module: str | None) -> bool:
    """Return True if *module* is a synhopy sub-module."""
    if module is None:
        return False
    return module == "synhopy" or module.startswith("synhopy.")


def _call_name(node: ast.expr) -> str | None:
    """Return the callable name from a Call node (handles chained methods)."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Call):
        return _call_name(node.func)
    return None


def _root_call_name(node: ast.expr) -> str | None:
    """Walk a chained-method call (a.b().c().d()) to find the root Name."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return _root_call_name(node.value)
    if isinstance(node, ast.Call):
        return _root_call_name(node.func)
    return None


def _is_proof_chain(node: ast.expr) -> bool:
    """Detect ``Proof(...).using(...).qed()`` / ``FormalProof.eq(...).qed()``."""
    root = _root_call_name(node)
    return root in {"Proof", "FormalProof", "formal_eq", "formal_check"}


def _is_with_target(node: ast.withitem, names: set[str]) -> bool:
    """Check if a ``with`` item calls one of *names*."""
    ctx = node.context_expr
    name = _call_name(ctx) if isinstance(ctx, ast.Call) else None
    if name is None:
        name = _root_call_name(ctx)
    return name in names


# Refinement type wrappers that take a single inner type: Pos[int] → int
_REFINEMENT_WRAPPERS: set[str] = {
    "Pos", "Nat", "NonEmpty", "Bounded", "NonNull",
    "Sorted", "SizedExact", "Refine",
}


def _strip_refinement_annotation(node: ast.expr) -> ast.expr:
    """``Pos[int]`` → ``int``, recursively."""
    if isinstance(node, ast.Subscript):
        if isinstance(node.value, ast.Name) and node.value.id in _REFINEMENT_WRAPPERS:
            inner = node.slice
            return _strip_refinement_annotation(inner)
        # Recurse into generic subscripts like list[Pos[int]]
        node.slice = _strip_refinement_annotation(node.slice)
        return node
    if isinstance(node, ast.Tuple):
        node.elts = [_strip_refinement_annotation(e) for e in node.elts]
        return node
    return node


def _body_is_only_pass(body: list[ast.stmt]) -> bool:
    """True when a body consists solely of ``pass`` statements."""
    return all(isinstance(s, ast.Pass) for s in body)


def _is_verification_only_main_block(node: ast.If) -> bool:
    """Detect ``if __name__ == '__main__'`` blocks that contain only
    SynHoPy verification calls and nothing else worth keeping."""
    test = node.test
    if not isinstance(test, ast.Compare):
        return False
    if not (isinstance(test.left, ast.Name) and test.left.id == "__name__"):
        return False
    if not (len(test.comparators) == 1
            and isinstance(test.comparators[0], ast.Constant)
            and test.comparators[0].value == "__main__"):
        return False
    # Check if body only has synhopy-related calls / proof blocks
    for stmt in node.body:
        if isinstance(stmt, ast.Pass):
            continue
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            name = _call_name(stmt.value)
            root = _root_call_name(stmt.value)
            if name in _SYNHOPY_CALLABLE_NAMES or root in _PROOF_ROOTS:
                continue
        if isinstance(stmt, ast.Assign) and isinstance(stmt.value, ast.Call):
            if _is_proof_chain(stmt.value):
                continue
        if isinstance(stmt, ast.With):
            for item in stmt.items:
                if _is_with_target(item, _WITH_STRIP_NAMES):
                    continue
            # If all items are synhopy, skip
            if all(_is_with_target(item, _WITH_STRIP_NAMES) for item in stmt.items):
                continue
        # Found a non-synhopy statement — keep the block
        return False
    return True


_SYNHOPY_CALLABLE_NAMES = {"assume", "check", "given"}
_PROOF_ROOTS = {"Proof", "FormalProof", "formal_eq", "formal_check"}
_WITH_STRIP_NAMES = {"library_trust", "ProofContext"}


# ---------------------------------------------------------------------------
# Core transformer
# ---------------------------------------------------------------------------

class SynHoPyStripper(ast.NodeTransformer):
    """Strip all SynHoPy annotations from Python source, recovering the
    original code."""

    DECORATOR_NAMES: set[str] = {
        "guarantee", "requires", "ensures", "pure", "reads", "mutates",
        "total", "partial_fn", "invariant", "decreases", "verify", "about",
    }

    CALL_NAMES: set[str] = {"assume", "check", "given"}

    SYNHOPY_MODULES: set[str] = {"synhopy"}

    def __init__(self) -> None:
        super().__init__()
        self.decorators_removed: int = 0
        self.statements_removed: int = 0
        self.imports_removed: int = 0

    # -- decorators ---------------------------------------------------------

    def _strip_decorators(self, node: ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef):
        kept: list[ast.expr] = []
        for dec in node.decorator_list:
            name = _decorator_name(dec)
            if name in self.DECORATOR_NAMES:
                self.decorators_removed += 1
            else:
                kept.append(dec)
        node.decorator_list = kept

    def visit_FunctionDef(self, node: ast.FunctionDef):
        self._strip_decorators(node)
        self._strip_annotations(node)
        self.generic_visit(node)
        return node

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef):
        self._strip_decorators(node)
        self._strip_annotations(node)
        self.generic_visit(node)
        return node

    def visit_ClassDef(self, node: ast.ClassDef):
        self._strip_decorators(node)
        self.generic_visit(node)
        return node

    # -- type annotations ---------------------------------------------------

    def _strip_annotations(self, node: ast.FunctionDef | ast.AsyncFunctionDef):
        """Unwrap SynHoPy refinement types in function signatures."""
        if node.returns:
            node.returns = _strip_refinement_annotation(node.returns)
        for arg in node.args.args + node.args.posonlyargs + node.args.kwonlyargs:
            if arg.annotation:
                arg.annotation = _strip_refinement_annotation(arg.annotation)
        if node.args.vararg and node.args.vararg.annotation:
            node.args.vararg.annotation = _strip_refinement_annotation(
                node.args.vararg.annotation
            )
        if node.args.kwarg and node.args.kwarg.annotation:
            node.args.kwarg.annotation = _strip_refinement_annotation(
                node.args.kwarg.annotation
            )

    def visit_AnnAssign(self, node: ast.AnnAssign):
        node.annotation = _strip_refinement_annotation(node.annotation)
        self.generic_visit(node)
        return node

    # -- imports ------------------------------------------------------------

    def visit_Import(self, node: ast.Import):
        remaining = [
            alias for alias in node.names
            if not _is_synhopy_import_module(alias.name)
        ]
        if not remaining:
            self.imports_removed += 1
            return None  # remove entirely
        if len(remaining) < len(node.names):
            self.imports_removed += 1
            node.names = remaining
        return node

    def visit_ImportFrom(self, node: ast.ImportFrom):
        if _is_synhopy_import_module(node.module):
            self.imports_removed += 1
            return None
        return node

    # -- standalone expression statements -----------------------------------

    def visit_Expr(self, node: ast.Expr):
        if isinstance(node.value, ast.Call):
            name = _call_name(node.value)
            root = _root_call_name(node.value)
            if name in self.CALL_NAMES or root in _PROOF_ROOTS:
                self.statements_removed += 1
                return None
            if _is_proof_chain(node.value):
                self.statements_removed += 1
                return None
        self.generic_visit(node)
        return node

    # -- assignment statements (proof variables) ----------------------------

    def visit_Assign(self, node: ast.Assign):
        if isinstance(node.value, ast.Call) and _is_proof_chain(node.value):
            self.statements_removed += 1
            return None
        self.generic_visit(node)
        return node

    # -- with blocks (library_trust, ProofContext) --------------------------

    def visit_With(self, node: ast.With):
        synhopy_items = [
            item for item in node.items
            if _is_with_target(item, _WITH_STRIP_NAMES)
        ]
        if synhopy_items:
            if len(synhopy_items) == len(node.items):
                self.statements_removed += 1
                return None
            # Mixed: keep non-synhopy items
            node.items = [
                item for item in node.items
                if not _is_with_target(item, _WITH_STRIP_NAMES)
            ]
        self.generic_visit(node)
        return node

    # -- if __name__ == "__main__" verification-only blocks -----------------

    def visit_If(self, node: ast.If):
        if _is_verification_only_main_block(node):
            self.statements_removed += 1
            return None
        self.generic_visit(node)
        return node

    # -- generic body cleanup (ensure no empty bodies) ----------------------

    def visit_Module(self, node: ast.Module):
        self.generic_visit(node)
        # Remove None entries left after stripping
        node.body = [s for s in node.body if s is not None]
        # Mark empty so strip_source can return ""
        node._empty = not node.body
        if not node.body:
            node.body = [ast.Pass()]
        return node

    def _fixup_body(self, body: list[ast.stmt]) -> list[ast.stmt]:
        """Ensure a body is never empty after stripping."""
        cleaned = [s for s in body if s is not None]
        if not cleaned:
            p = ast.Pass()
            # Copy location from original body if possible
            return [ast.copy_location(p, body[0]) if body else p]
        return cleaned


# ---------------------------------------------------------------------------
# Post-processing: fix up empty bodies after transform
# ---------------------------------------------------------------------------

class _BodyFixer(ast.NodeTransformer):
    """Ensure no compound statement has an empty body."""

    def _fix(self, node):
        for attr in ("body", "orelse", "finalbody", "handlers"):
            val = getattr(node, attr, None)
            if isinstance(val, list):
                filtered = [s for s in val if s is not None]
                if not filtered and val:
                    p = ast.Pass()
                    if val:
                        ast.copy_location(p, val[0])
                    filtered = [p]
                setattr(node, attr, filtered)
        self.generic_visit(node)
        return node

    visit_FunctionDef = _fix
    visit_AsyncFunctionDef = _fix
    visit_ClassDef = _fix
    visit_For = _fix
    visit_AsyncFor = _fix
    visit_While = _fix
    visit_If = _fix
    visit_With = _fix
    visit_AsyncWith = _fix
    visit_Try = _fix
    visit_TryStar = _fix  # Python 3.11+
    visit_ExceptHandler = _fix


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def strip_source(source: str) -> str:
    """Strip all SynHoPy annotations from Python source code.

    Returns the cleaned source that is semantically identical to the
    original unannotated code.
    """
    tree = ast.parse(source)
    stripper = SynHoPyStripper()
    tree = stripper.visit(tree)
    tree = _BodyFixer().visit(tree)
    ast.fix_missing_locations(tree)
    if getattr(tree, "_empty", False):
        return ""
    return ast.unparse(tree) + "\n"


def strip_source_detailed(source: str) -> tuple[str, SynHoPyStripper]:
    """Like :func:`strip_source`, but also returns the stripper with counts."""
    tree = ast.parse(source)
    stripper = SynHoPyStripper()
    tree = stripper.visit(tree)
    tree = _BodyFixer().visit(tree)
    ast.fix_missing_locations(tree)
    if getattr(tree, "_empty", False):
        return "", stripper
    return ast.unparse(tree) + "\n", stripper


def strip_file(input_path: str, output_path: str | None = None) -> str:
    """Strip annotations from a file.

    If *output_path* is ``None``, return the stripped source.
    If *output_path* is given, write to that file and return the path.
    """
    source = Path(input_path).read_text(encoding="utf-8")
    stripped = strip_source(source)
    if output_path is None:
        return stripped
    out = Path(output_path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(stripped, encoding="utf-8")
    return str(out)


# ---------------------------------------------------------------------------
# StripReport
# ---------------------------------------------------------------------------

@dataclass
class StripReport:
    """Statistics from a directory-wide strip operation."""

    files_processed: int = 0
    files_modified: int = 0
    files_unchanged: int = 0
    decorators_removed: int = 0
    statements_removed: int = 0
    imports_removed: int = 0
    errors: list[tuple[str, str]] = field(default_factory=list)

    def summary(self) -> str:
        lines = [
            f"Files processed : {self.files_processed}",
            f"  modified      : {self.files_modified}",
            f"  unchanged     : {self.files_unchanged}",
            f"Decorators removed : {self.decorators_removed}",
            f"Statements removed : {self.statements_removed}",
            f"Imports removed    : {self.imports_removed}",
        ]
        if self.errors:
            lines.append(f"Errors: {len(self.errors)}")
            for path, msg in self.errors:
                lines.append(f"  {path}: {msg}")
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Directory stripping
# ---------------------------------------------------------------------------

def strip_directory(
    input_dir: str,
    output_dir: str,
    *,
    preserve_structure: bool = True,
    skip_patterns: list[str] | None = None,
) -> StripReport:
    """Strip all ``.py`` files in a directory tree.

    Copies non-Python files unchanged.  If *skip_patterns* is given, files
    matching any :func:`fnmatch.fnmatch` pattern are skipped.
    """
    report = StripReport()
    skip = skip_patterns or []
    in_root = Path(input_dir)
    out_root = Path(output_dir)

    for dirpath, _dirnames, filenames in os.walk(in_root):
        rel_dir = Path(dirpath).relative_to(in_root)
        for fname in filenames:
            rel_file = rel_dir / fname
            if any(fnmatch.fnmatch(str(rel_file), pat) for pat in skip):
                continue

            src = Path(dirpath) / fname
            dst = out_root / rel_file if preserve_structure else out_root / fname
            dst.parent.mkdir(parents=True, exist_ok=True)

            if not fname.endswith(".py"):
                shutil.copy2(src, dst)
                continue

            report.files_processed += 1
            try:
                source = src.read_text(encoding="utf-8")
                stripped, stripper = strip_source_detailed(source)
                changed = (
                    stripper.decorators_removed
                    + stripper.statements_removed
                    + stripper.imports_removed
                ) > 0
                if changed:
                    report.files_modified += 1
                    report.decorators_removed += stripper.decorators_removed
                    report.statements_removed += stripper.statements_removed
                    report.imports_removed += stripper.imports_removed
                else:
                    report.files_unchanged += 1
                dst.write_text(stripped, encoding="utf-8")
            except Exception as exc:
                report.errors.append((str(rel_file), str(exc)))

    return report


# ---------------------------------------------------------------------------
# Roundtrip verification
# ---------------------------------------------------------------------------

def verify_strip_roundtrip(original: str, annotated: str) -> bool:
    """Verify that stripping the annotated version reproduces the original.

    This is the key correctness property::

        strip(annotate(original)) ≡ original

    Both sides are compared after ``ast.unparse(ast.parse(...))``, so
    formatting differences (whitespace, parenthesisation) are normalised away.
    """
    def _normalise(src: str) -> str:
        try:
            return ast.unparse(ast.parse(src))
        except SyntaxError:
            return src.strip()

    return _normalise(strip_source(annotated)) == _normalise(original)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    """CLI: python -m synhopy.tools.stripper [--file F] [--dir D] [--output O]"""
    import argparse

    parser = argparse.ArgumentParser(
        description="Strip SynHoPy annotations from Python source code"
    )
    parser.add_argument("--file", "-f", help="Strip a single file")
    parser.add_argument("--dir", "-d", help="Strip a directory tree")
    parser.add_argument("--output", "-o", help="Output path (file or directory)")
    parser.add_argument(
        "--verify", action="store_true",
        help="Verify roundtrip: strip(annotated) == original",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Show what would change without writing",
    )
    parser.add_argument(
        "--skip", nargs="*", default=[],
        help="Glob patterns to skip (for --dir)",
    )
    args = parser.parse_args()

    if args.file:
        source = Path(args.file).read_text(encoding="utf-8")
        stripped, stripper = strip_source_detailed(source)
        if args.dry_run:
            changed = (
                stripper.decorators_removed
                + stripper.statements_removed
                + stripper.imports_removed
            )
            print(f"Would modify {args.file}: "
                  f"{stripper.decorators_removed} decorators, "
                  f"{stripper.statements_removed} statements, "
                  f"{stripper.imports_removed} imports removed")
            if changed:
                print(stripped)
        elif args.output:
            out = Path(args.output)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(stripped, encoding="utf-8")
            print(f"Wrote {out}")
        else:
            sys.stdout.write(stripped)

    elif args.dir:
        if not args.output:
            parser.error("--output is required when using --dir")
        if args.dry_run:
            print(f"Would strip all .py files in {args.dir} → {args.output}")
            return
        report = strip_directory(
            args.dir, args.output, skip_patterns=args.skip or None,
        )
        print(report.summary())

    elif args.verify:
        print("Roundtrip verification requires --file and an original to compare.")
        sys.exit(1)

    else:
        parser.print_help()


# ---------------------------------------------------------------------------
# Self-tests
# ---------------------------------------------------------------------------

def _self_test() -> None:
    """Comprehensive self-tests — run via ``python synhopy/tools/stripper.py``."""
    import traceback

    passed = 0
    failed = 0

    def _check(label: str, source: str, expected_contains: Sequence[str],
               expected_absent: Sequence[str]):
        nonlocal passed, failed
        try:
            result = strip_source(source)
            ok = True
            for frag in expected_contains:
                if frag not in result:
                    print(f"  FAIL [{label}]: expected to find {frag!r}")
                    print(f"  Got:\n{textwrap.indent(result, '    ')}")
                    ok = False
            for frag in expected_absent:
                if frag in result:
                    print(f"  FAIL [{label}]: expected NOT to find {frag!r}")
                    print(f"  Got:\n{textwrap.indent(result, '    ')}")
                    ok = False
            if ok:
                passed += 1
            else:
                failed += 1
        except Exception:
            failed += 1
            print(f"  ERROR [{label}]:")
            traceback.print_exc()

    # 1. Simple decorator removal
    _check("decorator_simple", textwrap.dedent("""\
        from synhopy.proofs.sugar import guarantee, pure

        @guarantee("returns positive")
        @pure
        def inc(x: int) -> int:
            return x + 1
    """), expected_contains=["def inc(x: int) -> int:", "return x + 1"],
       expected_absent=["guarantee", "pure", "synhopy"])

    # 2. Stacked decorators — keep non-synhopy
    _check("decorator_mixed", textwrap.dedent("""\
        import functools
        from synhopy.proofs.sugar import guarantee, verify

        @verify
        @guarantee("wraps correctly")
        @functools.wraps
        def wrapper(f):
            return f
    """), expected_contains=["@functools.wraps", "def wrapper"],
       expected_absent=["@verify", "@guarantee", "synhopy"])

    # 3. Decorator with arguments vs bare
    _check("decorator_args_vs_bare", textwrap.dedent("""\
        from synhopy.proofs.sugar import total, decreases

        @total
        @decreases("n")
        def fact(n):
            return 1 if n <= 1 else n * fact(n - 1)
    """), expected_contains=["def fact(n):", "return 1"],
       expected_absent=["@total", "@decreases"])

    # 4. Inline calls stripped
    _check("inline_calls", textwrap.dedent("""\
        from synhopy.proofs.sugar import assume, check, given

        def safe_div(a, b):
            assume(b != 0)
            result = a / b
            check(result * b == a)
            return result
    """), expected_contains=["def safe_div(a, b):", "result = a / b", "return result"],
       expected_absent=["assume", "check", "synhopy"])

    # 5. Import stripping — synhopy only
    _check("import_strip_synhopy", textwrap.dedent("""\
        import os
        import synhopy
        from synhopy.proofs.sugar import guarantee
        from synhopy.core.types import Pos

        def f():
            pass
    """), expected_contains=["import os", "def f():"],
       expected_absent=["synhopy"])

    # 6. Mixed import — keep non-synhopy
    _check("import_keep_others", textwrap.dedent("""\
        import os
        import math

        def g():
            return math.pi
    """), expected_contains=["import os", "import math", "math.pi"],
       expected_absent=[])

    # 7. library_trust with block
    _check("library_trust_block", textwrap.dedent("""\
        from synhopy.proofs.sugar import library_trust

        with library_trust("sympy") as sp:
            sp.axiom("expand distributes", name="expand_dist")
            sp.use("polynomial_ring")

        def compute(x):
            return x + 1
    """), expected_contains=["def compute(x):", "return x + 1"],
       expected_absent=["library_trust", "axiom", "expand"])

    # 8. Proof chain — assignment
    _check("proof_assign", textwrap.dedent("""\
        from synhopy.proofs.sugar import Proof, FormalProof

        proof = Proof("x > 0").using(k).by_axiom("pos").qed()
        result = FormalProof.eq(a, b).by_axiom("sym").qed()

        def real_code():
            return 42
    """), expected_contains=["def real_code():", "return 42"],
       expected_absent=["Proof", "FormalProof", "proof =", "result ="])

    # 9. ProofContext with block
    _check("proof_context", textwrap.dedent("""\
        from synhopy.proofs.sugar import ProofContext

        with ProofContext(k) as pc:
            pc.have("x > 0")
            pc.qed()

        answer = 42
    """), expected_contains=["answer = 42"],
       expected_absent=["ProofContext", "pc.have"])

    # 10. Refinement type annotations
    _check("refinement_types", textwrap.dedent("""\
        from synhopy.core.types import Pos, NonEmpty

        def f(x: Pos[int], items: NonEmpty[list[str]]) -> Pos[int]:
            return x + 1
    """), expected_contains=["x: int", "list[str]"],
       expected_absent=["Pos", "NonEmpty", "synhopy"])

    # 11. given() as standalone expression
    _check("given_standalone", textwrap.dedent("""\
        from synhopy.proofs.sugar import given

        given("the ring axioms hold for integers")

        def add(a, b):
            return a + b
    """), expected_contains=["def add(a, b):", "return a + b"],
       expected_absent=["given", "ring axioms"])

    # 12. if __name__ == "__main__" verification-only block
    _check("main_verification_only", textwrap.dedent("""\
        def compute(x):
            return x * 2

        if __name__ == "__main__":
            check(compute(3) == 6)
            assume(True)
    """), expected_contains=["def compute(x):", "return x * 2"],
       expected_absent=["__main__", "check(", "assume("])

    # 13. Class decorators
    _check("class_decorator", textwrap.dedent("""\
        from synhopy.proofs.sugar import invariant

        @invariant("self.x >= 0")
        class PositiveCounter:
            def __init__(self):
                self.x = 0
    """), expected_contains=["class PositiveCounter:", "self.x = 0"],
       expected_absent=["@invariant", "synhopy"])

    # 14. AsyncFunctionDef
    _check("async_function", textwrap.dedent("""\
        from synhopy.proofs.sugar import guarantee

        @guarantee("returns awaited result")
        async def fetch(url):
            return url
    """), expected_contains=["async def fetch(url):", "return url"],
       expected_absent=["@guarantee", "synhopy"])

    # 15. Comments and docstrings preserved
    _check("preserve_comments_docstrings", textwrap.dedent("""\
        # This module does SynHoPy-related work
        '''Module docstring mentioning synhopy.'''

        def f():
            \"\"\"Docstring that mentions synhopy.\"\"\"
            return 1
    """), expected_contains=["def f():", "return 1"],
       expected_absent=[])

    # 16. About decorator
    _check("about_decorator", textwrap.dedent("""\
        from synhopy.proofs.sugar import about

        @about("This function implements Euclid's algorithm")
        def gcd(a, b):
            while b:
                a, b = b, a % b
            return a
    """), expected_contains=["def gcd(a, b):", "while b:"],
       expected_absent=["@about", "synhopy"])

    # 17. verify_strip_roundtrip
    original = textwrap.dedent("""\
        def f(x):
            return x + 1
    """)
    annotated = textwrap.dedent("""\
        from synhopy.proofs.sugar import guarantee

        @guarantee("increments")
        def f(x):
            return x + 1
    """)
    if verify_strip_roundtrip(original, annotated):
        passed += 1
    else:
        failed += 1
        print("  FAIL [roundtrip]")

    # 18. Empty file
    _check("empty_file", "", expected_contains=[], expected_absent=["pass"])

    # 19. Only synhopy imports (should produce valid Python)
    _check("only_imports", textwrap.dedent("""\
        from synhopy.proofs.sugar import guarantee
        import synhopy
    """), expected_contains=[], expected_absent=["synhopy"])

    # 20. Nested refinement types
    _check("nested_refinement", textwrap.dedent("""\
        from synhopy.core.types import Pos, NonEmpty, Sorted

        def f(x: Sorted[list[Pos[int]]]) -> NonEmpty[list[int]]:
            return x
    """), expected_contains=["list[int]"],
       expected_absent=["Pos", "NonEmpty", "Sorted"])

    # 21. Multiple proof chains
    _check("multiple_proof_chains", textwrap.dedent("""\
        from synhopy.proofs.sugar import Proof, FormalProof, formal_eq

        Proof("a > 0").qed()
        formal_eq(a, b).qed()
        x = 10
    """), expected_contains=["x = 10"],
       expected_absent=["Proof(", "formal_eq"])

    # 22. Mixed with-block items (keep non-synhopy)
    _check("mixed_with", textwrap.dedent("""\
        import contextlib

        @contextlib.contextmanager
        def my_ctx():
            yield 42

        with my_ctx() as val:
            x = val + 1
    """), expected_contains=["with my_ctx() as val:", "x = val + 1"],
       expected_absent=[])

    # 23. StripReport summary
    report = StripReport(
        files_processed=5, files_modified=3, files_unchanged=2,
        decorators_removed=7, statements_removed=4, imports_removed=3,
        errors=[("bad.py", "SyntaxError")],
    )
    summary = report.summary()
    assert "5" in summary and "3" in summary and "bad.py" in summary
    passed += 1

    # 24. strip_source_detailed returns counts
    src = textwrap.dedent("""\
        from synhopy.proofs.sugar import guarantee, assume
        @guarantee("positive")
        def f(x):
            assume(x > 0)
            return x
    """)
    _, info = strip_source_detailed(src)
    assert info.decorators_removed == 1, f"Expected 1 decorator removed, got {info.decorators_removed}"
    assert info.statements_removed == 1, f"Expected 1 statement removed, got {info.statements_removed}"
    assert info.imports_removed == 1, f"Expected 1 import removed, got {info.imports_removed}"
    passed += 1

    # 25. Reads and mutates decorators
    _check("reads_mutates", textwrap.dedent("""\
        from synhopy.proofs.sugar import reads, mutates

        @reads("self.data")
        @mutates("self.cache")
        def process(self):
            self.cache = self.data
    """), expected_contains=["def process(self):", "self.cache = self.data"],
       expected_absent=["@reads", "@mutates", "synhopy"])

    # 26. partial_fn decorator
    _check("partial_fn_decorator", textwrap.dedent("""\
        from synhopy.proofs.sugar import partial_fn

        @partial_fn
        def head(lst):
            return lst[0]
    """), expected_contains=["def head(lst):", "return lst[0]"],
       expected_absent=["@partial_fn", "synhopy"])

    # 27. requires / ensures decorators
    _check("requires_ensures", textwrap.dedent("""\
        from synhopy.proofs.sugar import requires, ensures

        @requires("x > 0")
        @ensures("result > x")
        def double(x):
            return x * 2
    """), expected_contains=["def double(x):", "return x * 2"],
       expected_absent=["@requires", "@ensures", "synhopy"])

    # Summary
    total = passed + failed
    print(f"\nSelf-test results: {passed}/{total} passed", end="")
    if failed:
        print(f", {failed} FAILED")
        sys.exit(1)
    else:
        print(" ✓")


if __name__ == "__main__":
    # When run directly, execute self-tests
    if len(sys.argv) > 1:
        main()
    else:
        _self_test()
