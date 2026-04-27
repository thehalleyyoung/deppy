"""Decorator-based sidecar — write proof annotations inline with Python.

When you are *writing* a Python module rather than *proving properties
of one already written*, this is the natural way to attach proof
metadata.  Each decorator stamps the function with a ``__deppy_*__``
attribute and registers the construct with a module-local registry.
Extracting via :func:`extract_sidecar_module` produces the same
:class:`~deppy.proofs.sidecar.SidecarModule` shape that
:meth:`SidecarModule.from_file` produces for a ``.deppy`` file — so
the *same pipeline* runs on either form.

Example
-------

::

    # my_module.py
    from deppy.proofs.sidecar_decorators import (
        foundation, axiom, verify, spec, lemma,
        psdl_proof, by_lean, code_type, lean_import,
    )

    @foundation
    def Real_add_comm():
        \"\"\"a + b == b + a\"\"\"

    @foundation(citation="ring axiom", deps=["Real_add_comm"])
    def Real_add_assoc():
        return "(a + b) + c == a + (b + c)"

    @code_type("Point", "Int → Int")
    @axiom(
        target="my_module.Point",
        statement="Point.distance(p, q) >= 0",
    )
    def dist_nonneg():
        pass

    @spec(
        guarantees=["distance is non-negative"],
        axioms=["dist_nonneg"],
    )
    class Point:
        @verify(
            via="foundation Real_sqrt_nonneg",
            binders={"p": "Point", "q": "Point"},
            property="Point.distance(p, q) >= 0",
        )
        @psdl_proof(\"\"\"
        if isinstance(other, Point):
            inline(Point.distance, sqrt(sum_zip_sub_sq(self, other)))
            apply(Real_sqrt_nonneg)
            assert sum_zip_sub_sq(self, other) >= 0, "z3"
        else:
            raise NotImplementedError
        \"\"\")
        def distance(self, other):
            ...

Extraction::

    import my_module
    from deppy.proofs.sidecar_decorators import extract_sidecar_module
    sm = extract_sidecar_module(my_module)
    # sm is now a SidecarModule — feed to the pipeline as usual.

Or via CLI::

    python -m deppy.pipeline.run_verify --from-module my_module

The decorator form is the **dual** of the .deppy form: the proof
metadata travels *with* the code, so refactors keep them aligned.
"""
from __future__ import annotations

import inspect
from dataclasses import dataclass, field
from typing import Any, Callable, Optional


# ───────────────────────────────────────────────────────────────────
#  Module-local registry — discovered via ``extract_sidecar_module``
# ───────────────────────────────────────────────────────────────────

@dataclass
class _SidecarRegistry:
    foundations: dict[str, Any] = field(default_factory=dict)
    axioms: dict[str, Any] = field(default_factory=dict)
    specs: dict[str, Any] = field(default_factory=dict)
    verifies: list[Any] = field(default_factory=list)
    lemmas: list[Any] = field(default_factory=list)
    predicates: dict[str, str] = field(default_factory=dict)
    constants: dict[str, str] = field(default_factory=dict)
    code_types: dict[str, str] = field(default_factory=dict)
    lean_imports: list[str] = field(default_factory=list)
    lean_preamble_lines: list[str] = field(default_factory=list)
    foundation_deps: dict[str, list[str]] = field(
        default_factory=dict,
    )


# Global registry — populated as decorators run at import time.
# ``extract_sidecar_module`` snapshots it per-module via the
# ``__deppy_*__`` attributes on each member.
_registry = _SidecarRegistry()


def _get_statement(fn: Callable, override: Optional[str]) -> str:
    """Pull a statement from ``override``, then docstring, then by
    calling the function (it should ``return`` the string)."""
    if override:
        return override
    doc = inspect.getdoc(fn) or ""
    if doc:
        return doc.strip()
    try:
        v = fn()
        if isinstance(v, str):
            return v
    except Exception:
        pass
    return ""


# ───────────────────────────────────────────────────────────────────
#  Foundation decorator
# ───────────────────────────────────────────────────────────────────

def foundation(
    arg=None,
    /,
    *,
    name: Optional[str] = None,
    statement: Optional[str] = None,
    citation: str = "",
    deps: tuple[str, ...] = (),
    lean_proof: str = "",
    lean_signature: str = "",
):
    """Mark a function as a deppy foundation.

    Forms:
      * ``@foundation`` (no parens) — name from function, statement
        from docstring or return value.
      * ``@foundation(...)`` — explicit metadata.

    The wrapped function's ``__deppy_foundation__`` attribute carries
    the metadata as a dict.  ``extract_sidecar_module`` reads this.
    """
    def make(fn: Callable) -> Callable:
        nm = name or fn.__name__
        st = _get_statement(fn, statement)
        meta = {
            "name": nm,
            "statement": st,
            "citation": citation,
            "deps": list(deps),
            "lean_proof": lean_proof,
            "lean_signature": lean_signature,
        }
        fn.__deppy_foundation__ = meta  # type: ignore[attr-defined]
        _registry.foundations[nm] = fn
        if deps:
            _registry.foundation_deps[nm] = list(deps)
        return fn
    if callable(arg):
        return make(arg)
    return make


# ───────────────────────────────────────────────────────────────────
#  Axiom decorator
# ───────────────────────────────────────────────────────────────────

def axiom(
    arg=None,
    /,
    *,
    name: Optional[str] = None,
    target: str = "",
    statement: Optional[str] = None,
    module: str = "",
    precondition: str = "",
    lean_proof: str = "",
    lean_signature: str = "",
):
    """Mark a function as a deppy sidecar axiom (a claim about the
    target library's behaviour)."""
    def make(fn: Callable) -> Callable:
        nm = name or fn.__name__
        st = _get_statement(fn, statement)
        meta = {
            "name": nm,
            "target": target,
            "statement": st,
            "module": module,
            "precondition": precondition,
            "lean_proof": lean_proof,
            "lean_signature": lean_signature,
        }
        fn.__deppy_axiom__ = meta  # type: ignore[attr-defined]
        _registry.axioms[nm] = fn
        return fn
    if callable(arg):
        return make(arg)
    return make


# ───────────────────────────────────────────────────────────────────
#  Verify decorator (the most common form for code being written)
# ───────────────────────────────────────────────────────────────────

def verify(
    *,
    name: Optional[str] = None,
    function: Optional[str] = None,
    property: str = "",
    via: str = "",
    binders: Optional[dict[str, str]] = None,
    fibration: str = "",
    cubical: bool = False,
    requires: str = "",
    ensures: str = "",
    effect: str = "",
    decreases: str = "",
    z3_binders: Optional[dict[str, str]] = None,
    cubical_dim: int = 0,
    cohomology_level: int = 0,
    expecting_counterexample: bool = False,
    expects_sha256: str = "",
    by_lean: str = "",
    lean_signature: str = "",
):
    """Mark a function as the *target* of a verify block.

    The function ``function`` argument can be omitted — the
    decorator infers it from the function's qualified name
    (``module.Class.method``) at extraction time.
    """
    def make(fn: Callable) -> Callable:
        # Infer function path from the qualified name when omitted.
        fn_path = function
        if not fn_path:
            mod = getattr(fn, "__module__", "") or ""
            qual = getattr(fn, "__qualname__", "") or fn.__name__
            fn_path = f"{mod}.{qual}" if mod else qual
        # Default verify-block name is the function's qualified name
        # with dots replaced — keeps it Python-identifier-safe.
        nm = name or fn.__name__ + "_verify"
        meta = {
            "name": nm,
            "function": fn_path,
            "property": property,
            "foundation": (
                via.removeprefix("foundation ").strip()
                if via.startswith("foundation ") else via
            ),
            "via": via,
            "binders": dict(binders or {}),
            "fibration": fibration,
            "cubical": cubical,
            "requires": requires,
            "ensures": ensures,
            "effect": effect,
            "decreases": decreases,
            "z3_binders": dict(z3_binders or {}),
            "cubical_dim": cubical_dim,
            "cohomology_level": cohomology_level,
            "expecting_counterexample": expecting_counterexample,
            "expects_sha256": expects_sha256,
            "by_lean": by_lean,
            "lean_signature": lean_signature,
        }
        # Compose with @psdl_proof when present.
        existing = getattr(fn, "__deppy_verify__", None)
        if existing is not None:
            meta["psdl_proof"] = existing.get("psdl_proof", "")
        else:
            meta["psdl_proof"] = ""
        fn.__deppy_verify__ = meta  # type: ignore[attr-defined]
        _registry.verifies.append(fn)
        return fn
    return make


# ───────────────────────────────────────────────────────────────────
#  PSDL proof decorator — composes with @verify
# ───────────────────────────────────────────────────────────────────

def psdl_proof(text: str):
    """Attach a PSDL proof body (Python-syntax tactic block) to a
    function.  Combined with ``@verify``, the PSDL gets compiled to
    a deppy ProofTerm and Lean tactic at extraction time."""
    def make(fn: Callable) -> Callable:
        existing = getattr(fn, "__deppy_verify__", None) or {}
        existing["psdl_proof"] = text
        fn.__deppy_verify__ = existing  # type: ignore[attr-defined]
        return fn
    return make


# ───────────────────────────────────────────────────────────────────
#  Spec decorator (on classes)
# ───────────────────────────────────────────────────────────────────

def _validate_formal(s: str, *, kind: str = "guarantee") -> str:
    """Validate that ``s`` is a *formal* claim, not a natural-language
    string.  Accepted forms:

      * ``"lean: <Lean expression>"`` — verbatim Lean syntax.
      * ``"smt: <SMTLib expression>"`` — verbatim SMTLib (or
        ``"smtlib: ..."``).
      * Anything else — must parse as a Python ``ast.parse(..., mode='eval')``
        expression.

    Returns the input unchanged on success.  Raises ``ValueError``
    on natural-language strings — guarantees / invariants / axioms
    must be in one of the three formal forms so the verify pipeline
    can mechanise them.  Comment-only documentation belongs in the
    class's docstring, not in the spec.
    """
    import ast as _ast
    text = (s or "").strip()
    if not text:
        raise ValueError(
            f"deppy: empty {kind!r} string — must be a Python "
            f"expression, ``lean: ...``, or ``smt: ...``"
        )
    if text.startswith(("lean:", "smt:", "smtlib:")):
        return text  # trust the user — the certificate emitter
                      # will splice the body verbatim.
    try:
        _ast.parse(text, mode="eval")
        return text
    except SyntaxError as e:
        raise ValueError(
            f"deppy: {kind} {s!r} is not a Python expression and "
            f"doesn't start with ``lean:`` / ``smt:``.  Natural-"
            f"language strings cannot be verified — put commentary "
            f"in the class docstring; put formal claims here.  "
            f"(parser said: {e.msg})"
        ) from None


def spec(
    *,
    target: Optional[str] = None,
    guarantees: Optional[list[str]] = None,
    axioms: Optional[list[str]] = None,
    invariants: Optional[list[str]] = None,
):
    """Mark a class with a deppy spec block listing guarantees and
    cited axioms / invariants.

    Every entry in ``guarantees`` and ``invariants`` must be one of:

      * a Python expression (parseable via ``ast.parse(_, mode='eval')``),
      * ``"lean: <code>"`` to splice raw Lean,
      * ``"smt: <expr>"`` (or ``"smtlib: ..."``) for raw SMTLib.

    Natural-language strings are rejected at decoration time —
    deppy can't verify what it can't parse.  Use the class
    docstring for human-readable commentary; reserve the spec
    fields for formal claims.

    ``axioms`` is a *list of axiom names* (strings naming
    previously-declared ``@axiom`` functions), not Python
    expressions, so it isn't validated by ``_validate_formal``.
    """
    # Validate each guarantee / invariant up-front so the
    # NL-vs-formal mistake fails at decoration time.
    g_validated = [
        _validate_formal(g, kind="guarantee")
        for g in (guarantees or [])
    ]
    i_validated = [
        _validate_formal(i, kind="invariant")
        for i in (invariants or [])
    ]
    def make(cls: type) -> type:
        nm = target or cls.__module__ + "." + cls.__qualname__
        meta = {
            "target": nm,
            "guarantees": g_validated,
            "axioms": list(axioms or []),
            "invariants": i_validated,
        }
        cls.__deppy_spec__ = meta  # type: ignore[attr-defined]
        _registry.specs[nm] = cls
        return cls
    return make


# ───────────────────────────────────────────────────────────────────
#  Lemma decorator
# ───────────────────────────────────────────────────────────────────

def lemma(
    *,
    name: Optional[str] = None,
    statement: str = "",
    by: str = "",
    lean_proof: str = "",
    lean_signature: str = "",
    lean_imports: tuple[str, ...] = (),
):
    """Declare a local lemma the certificate can cite via
    ``proof X: by lemma <name>``."""
    def make(fn: Callable) -> Callable:
        nm = name or fn.__name__
        st = statement or _get_statement(fn, None)
        meta = {
            "name": nm,
            "statement": st,
            "by": by,
            "lean_proof": lean_proof,
            "lean_signature": lean_signature,
            "lean_imports": list(lean_imports),
        }
        fn.__deppy_lemma__ = meta  # type: ignore[attr-defined]
        _registry.lemmas.append(fn)
        return fn
    return make


# ───────────────────────────────────────────────────────────────────
#  Predicate, constant, code_type, lean_import, lean_preamble
# ───────────────────────────────────────────────────────────────────

def predicate(name: str, body: str):
    """Register a custom predicate ``name(args) := body`` for use in
    foundation / axiom statements.  Substituted at compile time."""
    _registry.predicates[name] = body


def constant(name: str, body: str):
    """Register a symbolic constant ``name := body`` (e.g.
    ``constant("tau", "2*pi")``)."""
    _registry.constants[name] = body


def code_type(name: str, signature: str):
    """Register a Lean type signature for a function name, used
    when the inferred signature isn't right.

    Usage::

        @code_type("sqrt", "Int → Int")
        @code_type("Point.distance", "Point → Point → Int")
    """
    _registry.code_types[name] = signature
    # Allow stacking by returning the inner argument unchanged.
    def passthrough(arg):
        return arg
    return passthrough


def lean_import(line: str) -> None:
    """Add a top-level Lean import line to the certificate."""
    if line not in _registry.lean_imports:
        _registry.lean_imports.append(line)


def lean_preamble(text: str) -> None:
    """Append text to the top-level Lean preamble injected into
    the certificate."""
    _registry.lean_preamble_lines.append(text)


def by_lean(text: str):
    """Decorator alias for ``@verify(by_lean=text)``.  Composes by
    setting the field on an existing __deppy_verify__ dict."""
    def make(fn: Callable) -> Callable:
        existing = getattr(fn, "__deppy_verify__", None) or {}
        existing["by_lean"] = text
        fn.__deppy_verify__ = existing  # type: ignore[attr-defined]
        return fn
    return make


# ───────────────────────────────────────────────────────────────────
#  Extraction — build a SidecarModule from a Python module's
#  decorated members
# ───────────────────────────────────────────────────────────────────

def extract_sidecar_module(module):
    """Walk ``module``'s members, collect every ``__deppy_*__``
    attribute, and assemble a :class:`SidecarModule` equivalent.

    Returns a real ``SidecarModule`` ready to feed to the verify
    pipeline.
    """
    from deppy.proofs.sidecar import (
        SidecarModule,
        FoundationDecl,
        AxiomDecl,
        ExternalSpec,
        VerifyDecl,
        LemmaDecl,
    )

    sm = SidecarModule(name=getattr(module, "__name__", "decorated"))
    # Walk every top-level member of the module — and one level
    # into classes (since methods carry __deppy_verify__).
    members: list[Any] = []
    seen_id: set[int] = set()

    def visit(obj):
        if id(obj) in seen_id:
            return
        seen_id.add(id(obj))
        members.append(obj)
        # If it's a class, descend into its dict.
        if inspect.isclass(obj):
            for name in dir(obj):
                try:
                    v = getattr(obj, name)
                except Exception:
                    continue
                if callable(v) and (
                    getattr(v, "__deppy_verify__", None)
                    or getattr(v, "__deppy_axiom__", None)
                    or getattr(v, "__deppy_lemma__", None)
                ):
                    visit(v)

    for name in dir(module):
        try:
            obj = getattr(module, name)
        except Exception:
            continue
        if callable(obj) or inspect.isclass(obj):
            visit(obj)

    for obj in members:
        # Foundations
        f_meta = getattr(obj, "__deppy_foundation__", None)
        if f_meta:
            f_decl = FoundationDecl(
                name=f_meta["name"],
                statement=f_meta["statement"],
                citation=f_meta["citation"],
                lean_proof=f_meta.get("lean_proof", ""),
                lean_signature=f_meta.get("lean_signature", ""),
            )
            sm._foundations[f_decl.name] = f_decl
            if f_meta.get("deps"):
                sm._foundation_deps[f_decl.name] = list(f_meta["deps"])
        # Axioms
        a_meta = getattr(obj, "__deppy_axiom__", None)
        if a_meta:
            a_decl = AxiomDecl(
                name=a_meta["name"],
                target=a_meta["target"],
                statement=a_meta["statement"],
                module=a_meta["module"],
                precondition=a_meta["precondition"],
                lean_proof=a_meta.get("lean_proof", ""),
                lean_signature=a_meta.get("lean_signature", ""),
            )
            sm._axioms[a_decl.name] = a_decl
        # Specs (ExternalSpec).
        s_meta = getattr(obj, "__deppy_spec__", None)
        if s_meta:
            s_decl = ExternalSpec(
                target=obj if inspect.isclass(obj) else None,
                target_name=s_meta["target"],
                module_name=(s_meta["target"].split(".")[0]
                             if "." in s_meta["target"] else ""),
                guarantees=list(s_meta["guarantees"]),
                axioms=list(s_meta["axioms"]),
            )
            sm._specs[s_decl.target_name] = s_decl
        # Verify blocks
        v_meta = getattr(obj, "__deppy_verify__", None)
        if v_meta:
            v_decl = VerifyDecl(
                name=v_meta["name"],
                function=v_meta["function"],
                property=v_meta["property"],
                foundation=v_meta["foundation"],
                fibration_type=v_meta["fibration"],
                use_cubical=v_meta["cubical"],
                binders=dict(v_meta["binders"]),
                requires=v_meta["requires"],
                ensures=v_meta["ensures"],
                effect=v_meta["effect"],
                decreases=v_meta["decreases"],
                z3_binders=dict(v_meta["z3_binders"]),
                cubical_dim=v_meta["cubical_dim"],
                cohomology_level=v_meta["cohomology_level"],
                expects_sha256=v_meta["expects_sha256"],
                by_lean=v_meta["by_lean"],
                psdl_proof=v_meta.get("psdl_proof", ""),
            )
            # ``lean_signature`` and ``expecting_counterexample`` are
            # set as separate fields when the VerifyDecl supports them.
            for opt in ("lean_signature", "expecting_counterexample"):
                if hasattr(v_decl, opt):
                    setattr(v_decl, opt, v_meta.get(opt, ""))
            sm._verifies.append(v_decl)
        # Lemmas
        l_meta = getattr(obj, "__deppy_lemma__", None)
        if l_meta:
            l_decl = LemmaDecl(
                name=l_meta["name"],
                statement=l_meta["statement"],
                proof=l_meta.get("by", ""),
                lean_proof=l_meta["lean_proof"],
                lean_signature=l_meta["lean_signature"],
                lean_imports=list(l_meta["lean_imports"]),
            )
            sm._lemmas.append(l_decl)

    # Pull in module-level registry entries (predicates / constants
    # / code_types / lean_imports / lean_preamble) as accumulated by
    # decorator side-effects at import time.
    for k, v in _registry.predicates.items():
        sm._predicates.setdefault(k, v)
    for k, v in _registry.constants.items():
        sm._symbolic_constants.setdefault(k, v)
    for k, v in _registry.code_types.items():
        sm._code_types.setdefault(k, v)
    for line in _registry.lean_imports:
        if line not in sm._lean_imports:
            sm._lean_imports.append(line)
    if _registry.lean_preamble_lines:
        existing = sm._lean_preamble or ""
        appended = "\n".join(_registry.lean_preamble_lines)
        sm._lean_preamble = (
            (existing + "\n") if existing else ""
        ) + appended
    return sm


def reset_registry() -> None:
    """Clear the module-local registry (useful for tests)."""
    global _registry
    _registry = _SidecarRegistry()


__all__ = [
    "foundation",
    "axiom",
    "verify",
    "spec",
    "lemma",
    "psdl_proof",
    "by_lean",
    "predicate",
    "constant",
    "code_type",
    "lean_import",
    "lean_preamble",
    "extract_sidecar_module",
    "reset_registry",
]
