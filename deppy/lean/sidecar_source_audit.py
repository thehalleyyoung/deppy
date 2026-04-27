"""Generic, library-agnostic source-level audit of sidecar axioms.

The deppy ``.deppy`` DSL lets the user declare axioms as Python-syntax
strings (e.g. ``"Point.distance(p, q) >= 0"``).  This module audits
each axiom by inspecting the *actual* installed library and asking:

  1. Does the target (e.g. ``sympy.geometry.point.Point``) resolve?
  2. Does the axiom's statement reference methods/attributes that
     actually exist on the target?
  3. Is the axiom statement *syntactically formal* (a Python AST that
     parses as a comparison or boolean expression), or is it natural
     language with no formal structure?

The classification result lets the certificate distinguish:

  * **GROUNDED** — axiom is formal AND every method/attribute it
    references actually exists on the resolved target.  These axioms
    are candidates for source-level verification: their truth is a
    claim about real Python code that deppy has the source for.

  * **METHOD_MISSING** — axiom references methods that don't exist
    on the target.  These are *not* claims about library behaviour
    but mathematical claims (Euler line, power of point, etc.) about
    concepts the library never implements.  They can be admitted as
    documentation but should never be presented as "verified from
    sympy source" — there is no sympy source for them.

  * **NL_DOCUMENTATION** — axiom statement is natural language (won't
    parse as a Python AST expression, or contains free-form prose).
    Cannot be tied to source.  Honest documentation, not a verified
    claim.

  * **TARGET_MISSING** — the target itself doesn't import.

The audit is library-agnostic: it works on any ``.deppy`` sidecar
about any Python library.  It does not contain hard-coded sympy
knowledge.

Output usage in the certificate
-------------------------------

The certificate renderer can use the audit to:

  * label each axiom with its classification,
  * decline to call NL or method-missing axioms "verified from source",
  * surface a top-level honesty banner: "of N axioms, M are grounded
    in actual source, K are mathematical claims, J are NL-only".
"""
from __future__ import annotations

import ast
import importlib
import re
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Optional


class AxiomGrounding(Enum):
    GROUNDED = "GROUNDED"
    METHOD_MISSING = "METHOD_MISSING"
    NL_DOCUMENTATION = "NL_DOCUMENTATION"
    TARGET_MISSING = "TARGET_MISSING"


@dataclass
class AxiomAuditResult:
    name: str
    target_path: str
    statement: str
    grounding: AxiomGrounding
    referenced_attrs: list[str] = field(default_factory=list)
    missing_attrs: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


@dataclass
class SourceAuditReport:
    results: list[AxiomAuditResult] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.results)

    def count(self, g: AxiomGrounding) -> int:
        return sum(1 for r in self.results if r.grounding == g)

    @property
    def grounded(self) -> int:
        return self.count(AxiomGrounding.GROUNDED)

    @property
    def method_missing(self) -> int:
        return self.count(AxiomGrounding.METHOD_MISSING)

    @property
    def nl_only(self) -> int:
        return self.count(AxiomGrounding.NL_DOCUMENTATION)

    @property
    def target_missing(self) -> int:
        return self.count(AxiomGrounding.TARGET_MISSING)


# ─────────────────────────────────────────────────────────────────────
#  Target resolution (library-agnostic)
# ─────────────────────────────────────────────────────────────────────

def _resolve_target(dotted: str) -> Optional[Any]:
    """Resolve a dotted Python path like ``sympy.geometry.point.Point``.

    Returns the resolved object, or ``None`` if resolution fails at
    any step.  Splits on dots, walks ``importlib.import_module`` for
    the longest module prefix, then ``getattr`` for the remainder.
    """
    if not dotted:
        return None
    parts = dotted.split(".")
    # Try progressively shorter module paths.
    for i in range(len(parts), 0, -1):
        module_path = ".".join(parts[:i])
        try:
            mod = importlib.import_module(module_path)
        except (ImportError, ValueError):
            continue
        obj: Any = mod
        ok = True
        for attr in parts[i:]:
            if not hasattr(obj, attr):
                ok = False
                break
            obj = getattr(obj, attr)
        if ok:
            return obj
    return None


# ─────────────────────────────────────────────────────────────────────
#  Axiom statement parsing
# ─────────────────────────────────────────────────────────────────────

def _is_likely_nl(statement: str) -> bool:
    """Heuristic: does the statement read like prose?

    Triggers when the statement contains any of: a colon-prefixed
    quantifier ('for any', 'for every'), an em-dash, or other
    free-form prose markers.  Markers that could equally be used
    as identifiers (``perpendicular``, ``parallel``, ``iff``) are
    *only* flagged when they appear in clear-prose contexts —
    surrounded by spaces, not followed by an open paren.

    Note: this is intentionally conservative.  Strict-formal axioms
    like ``"Point.distance(p, q) >= 0"`` still pass the AST parse
    even if they read fluently.
    """
    s = statement.strip()
    low = s.lower()

    # Quantifier-style prose — these are unambiguous.
    for m in (
        "for any ", "for every ", "for all ",
        " any ", " every ",
        "intersect at", "lies on", "lies between",
        "passes through",
    ):
        if m in low:
            return True

    # Markers that could be identifiers OR prose.  Flag only when
    # they appear as bare words (followed by a space and a non-paren
    # character) — i.e. real prose, not ``perpendicular(a, b)``.
    for m in ("perpendicular", "parallel", "iff", "where", "longest", "shortest"):
        # find each occurrence and check the next character
        idx = 0
        while True:
            j = low.find(m, idx)
            if j < 0:
                break
            after = j + len(m)
            ch = low[after] if after < len(low) else " "
            # Function-call style ``m(`` — not prose.
            if ch == "(":
                idx = after
                continue
            # Identifier continuation ``m_x`` / ``mxxx`` — not prose.
            if ch == "_" or ch.isalnum():
                idx = after
                continue
            # Bare word followed by space or end — likely prose.
            return True
    return False


def _try_parse_python_expr(statement: str) -> Optional[ast.AST]:
    """Try to parse the statement as a Python expression."""
    s = statement.strip()
    # Try the raw form first.
    try:
        return ast.parse(s, mode="eval")
    except SyntaxError:
        pass
    # Some axioms include "==" for equality at expression level —
    # already valid Python — but strip a few common .deppy idioms:
    s2 = s.replace("Σ", "sum").replace("·", "*").replace("²", "**2")
    s2 = re.sub(r"\bθ\b", "theta", s2)
    s2 = s2.replace("²", "**2")
    try:
        return ast.parse(s2, mode="eval")
    except SyntaxError:
        return None


def _extract_attr_chains(node: ast.AST) -> list[tuple[str, ...]]:
    """Find every attribute access chain in the AST.

    Returns a list of tuples like ``("Point", "distance")`` for
    each ``Foo.bar`` reference.  Only chains rooted at a Name node
    are returned (so ``a.b.c`` becomes ``("a", "b", "c")``,
    ``f().g`` is skipped).
    """
    chains: list[tuple[str, ...]] = []
    for sub in ast.walk(node):
        if isinstance(sub, ast.Attribute):
            parts: list[str] = []
            cur: Optional[ast.AST] = sub
            while isinstance(cur, ast.Attribute):
                parts.append(cur.attr)
                cur = cur.value
            if isinstance(cur, ast.Name):
                parts.append(cur.id)
                parts.reverse()
                chains.append(tuple(parts))
    return chains


# ─────────────────────────────────────────────────────────────────────
#  Per-axiom audit
# ─────────────────────────────────────────────────────────────────────

def audit_axiom(
    name: str,
    target_path: str,
    statement: str,
) -> AxiomAuditResult:
    """Audit one axiom against the live module.

    Steps:
      1. Resolve target_path; if missing, classify TARGET_MISSING.
      2. Parse statement as Python AST; if not parseable, NL_DOCUMENTATION.
      3. If the statement contains NL prose markers (``for any``,
         ``iff``, ``intersect at``, etc.), classify NL_DOCUMENTATION
         even if it parses (e.g. ``is_collinear(A, B, C) iff ...``).
      4. Extract every attribute chain (``Class.method``).  For each
         chain whose head matches the target's leaf class name
         (or equals the target), check whether the trailing attrs
         exist on the target.  Any missing trailing attr → METHOD_MISSING.
      5. Otherwise GROUNDED.
    """
    target = _resolve_target(target_path)
    if target is None:
        return AxiomAuditResult(
            name=name,
            target_path=target_path,
            statement=statement,
            grounding=AxiomGrounding.TARGET_MISSING,
            notes=["target failed to resolve via importlib"],
        )

    # NL prose detection.
    if _is_likely_nl(statement):
        return AxiomAuditResult(
            name=name,
            target_path=target_path,
            statement=statement,
            grounding=AxiomGrounding.NL_DOCUMENTATION,
            notes=["statement contains natural-language markers"],
        )

    parsed = _try_parse_python_expr(statement)
    if parsed is None:
        return AxiomAuditResult(
            name=name,
            target_path=target_path,
            statement=statement,
            grounding=AxiomGrounding.NL_DOCUMENTATION,
            notes=["statement does not parse as Python expression"],
        )

    chains = _extract_attr_chains(parsed)
    # The leaf class name of the target — e.g. "Point" for
    # ``sympy.geometry.point.Point``.
    target_class_name = target_path.rsplit(".", 1)[-1]

    referenced: list[str] = []
    missing: list[str] = []
    for chain in chains:
        # Look for chains whose head matches the leaf class name.
        if chain[0] == target_class_name and len(chain) >= 2:
            attr_path = ".".join(chain[1:])
            referenced.append(attr_path)
            # Walk the attrs from the target.
            obj: Any = target
            ok = True
            for a in chain[1:]:
                if not hasattr(obj, a):
                    ok = False
                    break
                obj = getattr(obj, a)
            if not ok:
                missing.append(attr_path)

    if missing:
        return AxiomAuditResult(
            name=name,
            target_path=target_path,
            statement=statement,
            grounding=AxiomGrounding.METHOD_MISSING,
            referenced_attrs=referenced,
            missing_attrs=missing,
            notes=[
                f"{target_class_name} has no attribute(s): "
                f"{', '.join(missing)}"
            ],
        )

    return AxiomAuditResult(
        name=name,
        target_path=target_path,
        statement=statement,
        grounding=AxiomGrounding.GROUNDED,
        referenced_attrs=referenced,
    )


def audit_all(sidecar_module) -> SourceAuditReport:
    """Audit every axiom in a sidecar module."""
    if sidecar_module is None:
        return SourceAuditReport()
    axioms = getattr(sidecar_module, "axioms", {}) or {}
    out: list[AxiomAuditResult] = []
    for ax_name in sorted(axioms.keys()):
        ax = axioms[ax_name]
        target_path = getattr(ax, "target", "") or ""
        statement = getattr(ax, "statement", "") or ""
        out.append(audit_axiom(ax_name, target_path, statement))
    return SourceAuditReport(results=out)


__all__ = [
    "AxiomGrounding",
    "AxiomAuditResult",
    "SourceAuditReport",
    "audit_axiom",
    "audit_all",
]
