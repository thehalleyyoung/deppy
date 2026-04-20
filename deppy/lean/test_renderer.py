"""Tests for the Lean 4 AST renderer.

We build AST nodes directly (duck-typed dataclasses) so the tests are
self-contained and do not require the full cctt parser.
"""

from __future__ import annotations

import textwrap
from dataclasses import dataclass, field
from typing import Optional, Union

import pytest

# ── lightweight AST stubs (mirror the cctt.mathlib_bridge.lean_parser shapes) ─

@dataclass
class LeanExpr:
    pass

@dataclass
class LeanVar(LeanExpr):
    name: str

@dataclass
class LeanApp(LeanExpr):
    fn: LeanExpr
    args: list

@dataclass
class LeanLam(LeanExpr):
    params: list
    body: LeanExpr

@dataclass
class LeanPi(LeanExpr):
    params: list
    codomain: LeanExpr

@dataclass
class LeanMatch(LeanExpr):
    scrutinees: list
    arms: list

@dataclass
class LeanLet(LeanExpr):
    name: str
    type_: Optional[LeanExpr]
    value: LeanExpr
    body: LeanExpr

@dataclass
class LeanLit(LeanExpr):
    value: Union[int, float, str, bool]

@dataclass
class LeanSort(LeanExpr):
    level: int

@dataclass
class LeanProj(LeanExpr):
    expr: LeanExpr
    field: str

@dataclass
class LeanIf(LeanExpr):
    cond: LeanExpr
    then_: LeanExpr
    else_: LeanExpr

@dataclass
class LeanTactic(LeanExpr):
    tactic_name: str
    args: list

@dataclass
class LeanTacticBlock(LeanExpr):
    tactics: list

@dataclass
class LeanAnonymousCtor(LeanExpr):
    args: list

@dataclass
class LeanDo(LeanExpr):
    stmts: list

@dataclass
class LeanHole(LeanExpr):
    pass

@dataclass
class LeanSorry(LeanExpr):
    pass

@dataclass
class MatchArm:
    patterns: list
    rhs: LeanExpr

@dataclass
class LeanParam:
    name: str
    type_: Optional[LeanExpr]
    binder: str
    default: Optional[LeanExpr] = None

@dataclass
class LeanDecl:
    kind: str
    name: str
    universe_params: list
    params: list
    return_type: Optional[LeanExpr]
    body: Optional[LeanExpr]
    attributes: list
    docstring: Optional[str]
    namespace: str

@dataclass
class LeanInductiveCtor:
    name: str
    type_: Optional[LeanExpr]

@dataclass
class LeanFile:
    imports: list
    opens: list
    namespace: Optional[str]
    declarations: list
    variables: list
    sections: list

# ── import renderer under test ───────────────────────────────────────────

from deppy.lean.renderer import render_expr, render_decl, render_file

# ── helpers ──────────────────────────────────────────────────────────────

def _nat() -> LeanVar:
    return LeanVar("Nat")

def _param(name: str, ty: LeanExpr, binder: str = "explicit") -> LeanParam:
    return LeanParam(name=name, type_=ty, binder=binder)

# ── 1. simple theorem ───────────────────────────────────────────────────

def test_theorem_add_comm():
    """theorem add_comm (a b : Nat) : a + b = b + a := by omega"""
    decl = LeanDecl(
        kind="theorem",
        name="add_comm",
        universe_params=[],
        params=[
            _param("a", _nat()),
            _param("b", _nat()),
        ],
        return_type=LeanApp(
            fn=LeanVar("Eq"),
            args=[
                LeanApp(fn=LeanVar("HAdd.hAdd"), args=[LeanVar("a"), LeanVar("b")]),
                LeanApp(fn=LeanVar("HAdd.hAdd"), args=[LeanVar("b"), LeanVar("a")]),
            ],
        ),
        body=LeanTacticBlock(tactics=[LeanTactic("omega", [])]),
        attributes=[],
        docstring=None,
        namespace="",
    )
    out = render_decl(decl)
    assert out.startswith("theorem add_comm")
    assert "(a : Nat)" in out
    assert "(b : Nat)" in out
    assert "by omega" in out


# ── 2. function def ─────────────────────────────────────────────────────

def test_def_double():
    """def double (n : Nat) : Nat := n + n"""
    decl = LeanDecl(
        kind="def",
        name="double",
        universe_params=[],
        params=[_param("n", _nat())],
        return_type=_nat(),
        body=LeanApp(fn=LeanVar("HAdd.hAdd"), args=[LeanVar("n"), LeanVar("n")]),
        attributes=[],
        docstring=None,
        namespace="",
    )
    out = render_decl(decl)
    assert out.startswith("def double")
    assert "(n : Nat)" in out
    assert ": Nat" in out
    assert ":=" in out
    assert "HAdd.hAdd n n" in out


# ── 3. match expression ─────────────────────────────────────────────────

def test_match_expr():
    expr = LeanMatch(
        scrutinees=[LeanVar("n")],
        arms=[
            MatchArm(patterns=[LeanLit(0)], rhs=LeanLit(1)),
            MatchArm(
                patterns=[LeanApp(fn=LeanVar("Nat.succ"), args=[LeanVar("k")])],
                rhs=LeanApp(fn=LeanVar("HMul.hMul"), args=[
                    LeanVar("n"),
                    LeanApp(fn=LeanVar("factorial"), args=[LeanVar("k")]),
                ]),
            ),
        ],
    )
    out = render_expr(expr)
    assert "match n with" in out
    assert "| 0 => 1" in out
    assert "| Nat.succ k =>" in out


# ── 4. full file ────────────────────────────────────────────────────────

def test_render_file():
    thm = LeanDecl(
        kind="theorem",
        name="my_thm",
        universe_params=[],
        params=[_param("x", _nat())],
        return_type=LeanApp(fn=LeanVar("Eq"), args=[LeanVar("x"), LeanVar("x")]),
        body=LeanTacticBlock(tactics=[LeanTactic("rfl", [])]),
        attributes=["simp"],
        docstring="Reflexivity of Nat",
        namespace="",
    )
    fn = LeanDecl(
        kind="def",
        name="id'",
        universe_params=["u"],
        params=[
            _param("α", LeanSort(1), "implicit"),
            _param("a", LeanVar("α")),
        ],
        return_type=LeanVar("α"),
        body=LeanVar("a"),
        attributes=[],
        docstring=None,
        namespace="",
    )
    lf = LeanFile(
        imports=["Mathlib.Tactic", "Mathlib.Data.Nat.Basic"],
        opens=["Nat"],
        namespace="MyProject",
        declarations=[thm, fn],
        variables=[],
        sections=[],
    )
    out = render_file(lf)
    assert "import Mathlib.Tactic" in out
    assert "import Mathlib.Data.Nat.Basic" in out
    assert "open Nat" in out
    assert "namespace MyProject" in out
    assert "end MyProject" in out
    assert "/-- Reflexivity of Nat -/" in out
    assert "@[simp]" in out
    assert "{α : Type}" in out


# ── 5. tactics ──────────────────────────────────────────────────────────

def test_single_tactic():
    tb = LeanTacticBlock(tactics=[LeanTactic("ring", [])])
    assert render_expr(tb) == "by ring"


def test_multi_tactic_block():
    tb = LeanTacticBlock(tactics=[
        LeanTactic("intro", [LeanVar("h")]),
        LeanTactic("exact", [LeanVar("h")]),
    ])
    out = render_expr(tb)
    assert out.startswith("by\n")
    assert "intro h" in out
    assert "exact h" in out


# ── 6. let expression ───────────────────────────────────────────────────

def test_let_expr():
    expr = LeanLet(
        name="x",
        type_=_nat(),
        value=LeanLit(42),
        body=LeanApp(fn=LeanVar("HAdd.hAdd"), args=[LeanVar("x"), LeanLit(1)]),
    )
    out = render_expr(expr)
    assert "let x : Nat := 42" in out
    assert "HAdd.hAdd x 1" in out


# ── 7. if-then-else ─────────────────────────────────────────────────────

def test_if_then_else():
    expr = LeanIf(
        cond=LeanApp(fn=LeanVar("BEq.beq"), args=[LeanVar("n"), LeanLit(0)]),
        then_=LeanLit(1),
        else_=LeanVar("n"),
    )
    out = render_expr(expr)
    assert out.startswith("if ")
    assert " then 1 else n" in out


# ── 8. lambda expressions ───────────────────────────────────────────────

def test_lambda():
    expr = LeanLam(
        params=[_param("x", _nat())],
        body=LeanApp(fn=LeanVar("HAdd.hAdd"), args=[LeanVar("x"), LeanLit(1)]),
    )
    out = render_expr(expr)
    assert out.startswith("fun ")
    assert "(x : Nat)" in out
    assert "=>" in out


# ── 9. pi types (∀) ─────────────────────────────────────────────────────

def test_pi_type():
    expr = LeanPi(
        params=[_param("n", _nat())],
        codomain=LeanApp(fn=LeanVar("Eq"), args=[LeanVar("n"), LeanVar("n")]),
    )
    out = render_expr(expr)
    assert out.startswith("∀ ")
    assert "(n : Nat)" in out
    assert "Eq n n" in out


# ── 10. sorry ────────────────────────────────────────────────────────────

def test_sorry_expr():
    assert render_expr(LeanSorry()) == "sorry"


def test_sorry_in_decl():
    decl = LeanDecl(
        kind="theorem",
        name="todo",
        universe_params=[],
        params=[],
        return_type=LeanSort(0),  # Prop
        body=LeanSorry(),
        attributes=[],
        docstring=None,
        namespace="",
    )
    out = render_decl(decl)
    assert "sorry" in out


# ── additional coverage ─────────────────────────────────────────────────

def test_hole():
    assert render_expr(LeanHole()) == "_"


def test_anonymous_ctor():
    out = render_expr(LeanAnonymousCtor(args=[LeanLit(1), LeanLit(2)]))
    assert out == "⟨1, 2⟩"


def test_projection():
    out = render_expr(LeanProj(expr=LeanVar("p"), field="fst"))
    assert out == "p.fst"


def test_do_block():
    out = render_expr(LeanDo(stmts=[
        LeanApp(fn=LeanVar("IO.println"), args=[LeanLit("hello")]),
    ]))
    assert out.startswith("do\n")
    assert 'IO.println "hello"' in out


def test_lit_bool():
    assert render_expr(LeanLit(True)) == "true"
    assert render_expr(LeanLit(False)) == "false"


def test_lit_string():
    assert render_expr(LeanLit("hi")) == '"hi"'


def test_sort_prop():
    assert render_expr(LeanSort(0)) == "Prop"


def test_sort_type():
    assert render_expr(LeanSort(1)) == "Type"


def test_sort_type_2():
    assert render_expr(LeanSort(3)) == "Type 2"


def test_implicit_and_instance_binders():
    decl = LeanDecl(
        kind="def",
        name="foo",
        universe_params=[],
        params=[
            _param("α", LeanSort(1), "implicit"),
            _param("inst", LeanApp(fn=LeanVar("BEq"), args=[LeanVar("α")]), "instance"),
            _param("a", LeanVar("α")),
        ],
        return_type=LeanVar("Bool"),
        body=LeanApp(fn=LeanVar("BEq.beq"), args=[LeanVar("a"), LeanVar("a")]),
        attributes=[],
        docstring=None,
        namespace="",
    )
    out = render_decl(decl)
    assert "{α : Type}" in out
    assert "[inst : BEq α]" in out
    assert "(a : α)" in out


def test_let_without_type():
    expr = LeanLet(
        name="y",
        type_=None,
        value=LeanLit(10),
        body=LeanVar("y"),
    )
    out = render_expr(expr)
    assert "let y := 10" in out
    assert "y" in out.splitlines()[-1]


def test_variables_in_file():
    lf = LeanFile(
        imports=[],
        opens=[],
        namespace=None,
        declarations=[],
        variables=[_param("n", _nat())],
        sections=[],
    )
    out = render_file(lf)
    assert "variable (n : Nat)" in out


def test_file_no_namespace():
    decl = LeanDecl(
        kind="def",
        name="bar",
        universe_params=[],
        params=[],
        return_type=_nat(),
        body=LeanLit(0),
        attributes=[],
        docstring=None,
        namespace="",
    )
    lf = LeanFile(
        imports=[],
        opens=[],
        namespace=None,
        declarations=[decl],
        variables=[],
        sections=[],
    )
    out = render_file(lf)
    assert "namespace" not in out
    assert "def bar" in out


def test_inductive():
    ctors = [
        LeanInductiveCtor(name="zero", type_=None),
        LeanInductiveCtor(name="succ", type_=LeanApp(fn=LeanVar("→"), args=[LeanVar("MyNat"), LeanVar("MyNat")])),
    ]
    decl = LeanDecl(
        kind="inductive",
        name="MyNat",
        universe_params=[],
        params=[],
        return_type=LeanSort(1),
        body=ctors,
        attributes=[],
        docstring=None,
        namespace="",
    )
    out = render_decl(decl)
    assert "inductive MyNat" in out
    assert ": Type" in out
    assert "where" in out
    assert "| zero" in out
    assert "| succ" in out


def test_universe_params():
    decl = LeanDecl(
        kind="def",
        name="myId",
        universe_params=["u", "v"],
        params=[_param("a", LeanVar("α"))],
        return_type=LeanVar("α"),
        body=LeanVar("a"),
        attributes=[],
        docstring=None,
        namespace="",
    )
    out = render_decl(decl)
    assert "myId.{u, v}" in out
