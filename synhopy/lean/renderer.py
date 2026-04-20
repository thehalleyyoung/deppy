"""
Lean 4 AST pretty-printer / renderer.

Produces valid Lean 4 surface syntax from AST nodes defined in
``cctt.mathlib_bridge.lean_parser``.  The renderer is **duck-typed**: it
dispatches on ``type(node).__name__`` and reads attributes by name, so it works
with both the canonical dataclasses and any compatible stand-ins.

Public API
----------
    render_expr(expr)  → str
    render_decl(decl)  → str
    render_file(file)  → str
"""

from __future__ import annotations

from typing import Optional

# ── constants ────────────────────────────────────────────────────────────
INDENT = "  "  # 2-space indent per Lean 4 convention

_BINDER_OPEN = {
    "explicit": "(",
    "implicit": "{",
    "instance": "[",
    "strict_implicit": "⦃",
}
_BINDER_CLOSE = {
    "explicit": ")",
    "implicit": "}",
    "instance": "]",
    "strict_implicit": "⦄",
}


# ── helpers ──────────────────────────────────────────────────────────────

def _indent(text: str, level: int = 1) -> str:
    """Indent every line of *text* by *level* indentation steps."""
    prefix = INDENT * level
    return "\n".join(prefix + line for line in text.splitlines())


def _node_name(node: object) -> str:
    return type(node).__name__


def _needs_parens(expr: object) -> bool:
    """Return True if *expr* should be wrapped in parentheses when used as
    an argument inside a function application."""
    name = _node_name(expr)
    return name in (
        "LeanApp", "LeanLam", "LeanPi", "LeanMatch", "LeanLet",
        "LeanIf", "LeanDo",
    )


# ── expression renderer ─────────────────────────────────────────────────

def render_expr(expr: object) -> str:  # noqa: C901 — dispatch table
    """Render any ``LeanExpr`` node to a Lean 4 source string."""
    name = _node_name(expr)

    if name == "LeanVar":
        return expr.name  # type: ignore[attr-defined]

    if name == "LeanLit":
        v = expr.value  # type: ignore[attr-defined]
        if isinstance(v, bool):
            return "true" if v else "false"
        if isinstance(v, str):
            return f'"{v}"'
        return str(v)

    if name == "LeanSort":
        level: int = expr.level  # type: ignore[attr-defined]
        if level == 0:
            return "Prop"
        if level == 1:
            return "Type"
        return f"Type {level - 1}"

    if name == "LeanHole":
        return "_"

    if name == "LeanSorry":
        return "sorry"

    if name == "LeanApp":
        fn_str = render_expr(expr.fn)  # type: ignore[attr-defined]
        if _needs_parens(expr.fn):  # type: ignore[attr-defined]
            fn_str = f"({fn_str})"
        parts = [fn_str]
        for a in expr.args:  # type: ignore[attr-defined]
            a_str = render_expr(a)
            if _needs_parens(a):
                a_str = f"({a_str})"
            parts.append(a_str)
        return " ".join(parts)

    if name == "LeanLam":
        params_str = " ".join(_render_param(p) for p in expr.params)  # type: ignore[attr-defined]
        body_str = render_expr(expr.body)  # type: ignore[attr-defined]
        return f"fun {params_str} => {body_str}"

    if name == "LeanPi":
        params_str = " ".join(_render_param(p) for p in expr.params)  # type: ignore[attr-defined]
        cod_str = render_expr(expr.codomain)  # type: ignore[attr-defined]
        return f"∀ {params_str}, {cod_str}"

    if name == "LeanMatch":
        return _render_match(expr)

    if name == "LeanLet":
        n = expr.name  # type: ignore[attr-defined]
        val_str = render_expr(expr.value)  # type: ignore[attr-defined]
        body_str = render_expr(expr.body)  # type: ignore[attr-defined]
        type_ann = ""
        if getattr(expr, "type_", None) is not None:
            type_ann = f" : {render_expr(expr.type_)}"
        return f"let {n}{type_ann} := {val_str}\n{body_str}"

    if name == "LeanProj":
        base = render_expr(expr.expr)  # type: ignore[attr-defined]
        if _needs_parens(expr.expr):  # type: ignore[attr-defined]
            base = f"({base})"
        return f"{base}.{expr.field}"  # type: ignore[attr-defined]

    if name == "LeanIf":
        cond = render_expr(expr.cond)  # type: ignore[attr-defined]
        then_ = render_expr(expr.then_)  # type: ignore[attr-defined]
        else_ = render_expr(expr.else_)  # type: ignore[attr-defined]
        return f"if {cond} then {then_} else {else_}"

    if name == "LeanTactic":
        tac_name: str = expr.tactic_name  # type: ignore[attr-defined]
        args = expr.args  # type: ignore[attr-defined]
        if args:
            return tac_name + " " + " ".join(render_expr(a) for a in args)
        return tac_name

    if name == "LeanTacticBlock":
        tactics = expr.tactics  # type: ignore[attr-defined]
        if len(tactics) == 1:
            return f"by {render_expr(tactics[0])}"
        lines = "\n".join(render_expr(t) for t in tactics)
        return "by\n" + _indent(lines)

    if name == "LeanAnonymousCtor":
        inner = ", ".join(render_expr(a) for a in expr.args)  # type: ignore[attr-defined]
        return f"⟨{inner}⟩"

    if name == "LeanDo":
        stmts = "\n".join(render_expr(s) for s in expr.stmts)  # type: ignore[attr-defined]
        return "do\n" + _indent(stmts)

    # Fallback — unknown node
    return repr(expr)


# ── param renderer ───────────────────────────────────────────────────────

def _render_param(param: object) -> str:
    """Render a single ``LeanParam`` with appropriate binder brackets."""
    name: str = getattr(param, "name", "_")
    type_expr = getattr(param, "type_", None)
    binder: str = getattr(param, "binder", "explicit")
    default = getattr(param, "default", None)

    open_b = _BINDER_OPEN.get(binder, "(")
    close_b = _BINDER_CLOSE.get(binder, ")")

    inner = name
    if type_expr is not None:
        inner += f" : {render_expr(type_expr)}"
    if default is not None:
        inner += f" := {render_expr(default)}"

    return f"{open_b}{inner}{close_b}"


# ── match renderer ───────────────────────────────────────────────────────

def _render_match(expr: object) -> str:
    scrutinees = ", ".join(
        render_expr(s) for s in expr.scrutinees  # type: ignore[attr-defined]
    )
    lines = [f"match {scrutinees} with"]
    for arm in expr.arms:  # type: ignore[attr-defined]
        pats = ", ".join(render_expr(p) for p in arm.patterns)
        rhs = render_expr(arm.rhs)
        lines.append(f"| {pats} => {rhs}")
    return "\n".join(lines)


# ── declaration renderer ────────────────────────────────────────────────

def render_decl(decl: object) -> str:  # noqa: C901
    """Render a ``LeanDecl`` node to Lean 4 source."""
    kind: str = getattr(decl, "kind", "def")
    name: str = getattr(decl, "name", "unnamed")
    universe_params: list = getattr(decl, "universe_params", [])
    params: list = getattr(decl, "params", [])
    return_type = getattr(decl, "return_type", None)
    body = getattr(decl, "body", None)
    attributes: list = getattr(decl, "attributes", [])
    docstring: Optional[str] = getattr(decl, "docstring", None)
    namespace: str = getattr(decl, "namespace", "")

    parts: list[str] = []

    # docstring
    if docstring:
        parts.append(f"/-- {docstring} -/")

    # attributes
    if attributes:
        attr_str = ", ".join(attributes)
        parts.append(f"@[{attr_str}]")

    # header line
    header = kind
    if kind == "inductive":
        header = _render_inductive(decl)
        parts.append(header)
        return "\n".join(parts)

    header += f" {name}"
    if universe_params:
        header += ".{" + ", ".join(universe_params) + "}"

    # params
    if params:
        header += " " + " ".join(_render_param(p) for p in params)

    # return type
    if return_type is not None:
        header += f" : {render_expr(return_type)}"

    # body
    if body is not None:
        body_name = _node_name(body)
        if body_name == "LeanTacticBlock":
            body_str = render_expr(body)
            header += f" := {body_str}"
        elif body_name == "LeanSorry":
            header += " := sorry"
        else:
            body_str = render_expr(body)
            if "\n" in body_str:
                header += " :=\n" + _indent(body_str)
            else:
                header += f" := {body_str}"

    parts.append(header)
    return "\n".join(parts)


# ── inductive renderer ──────────────────────────────────────────────────

def _render_inductive(decl: object) -> str:
    name: str = getattr(decl, "name", "unnamed")
    params: list = getattr(decl, "params", [])
    return_type = getattr(decl, "return_type", None)
    body = getattr(decl, "body", None)

    header = f"inductive {name}"
    if params:
        header += " " + " ".join(_render_param(p) for p in params)
    if return_type is not None:
        header += f" : {render_expr(return_type)}"
    header += " where"

    # body should be a list of LeanInductiveCtor or similar
    ctors: list = []
    if body is not None:
        if isinstance(body, list):
            ctors = body
        elif hasattr(body, "args"):
            ctors = body.args
        elif hasattr(body, "stmts"):
            ctors = body.stmts

    for c in ctors:
        ctor_name = getattr(c, "name", str(c))
        ctor_type = getattr(c, "type_", None)
        if ctor_type is not None:
            header += f"\n  | {ctor_name} : {render_expr(ctor_type)}"
        else:
            header += f"\n  | {ctor_name}"

    return header


# ── file renderer ────────────────────────────────────────────────────────

def render_file(file: object) -> str:
    """Render a ``LeanFile`` node to a complete ``.lean`` source file."""
    imports: list = getattr(file, "imports", [])
    opens: list = getattr(file, "opens", [])
    ns: Optional[str] = getattr(file, "namespace", None)
    declarations: list = getattr(file, "declarations", [])
    variables: list = getattr(file, "variables", [])
    sections: list = getattr(file, "sections", [])

    blocks: list[str] = []

    # imports
    if imports:
        blocks.append("\n".join(f"import {imp}" for imp in imports))

    # opens
    if opens:
        blocks.append("\n".join(f"open {o}" for o in opens))

    # variables
    if variables:
        var_lines = []
        for v in variables:
            var_lines.append(f"variable {_render_param(v)}")
        blocks.append("\n".join(var_lines))

    # namespace wrapper
    decl_block = "\n\n".join(render_decl(d) for d in declarations)

    if ns:
        blocks.append(f"namespace {ns}\n")
        if decl_block:
            blocks.append(_indent(decl_block))
        blocks.append(f"\nend {ns}")
    else:
        if decl_block:
            blocks.append(decl_block)

    return "\n\n".join(blocks) + "\n"
