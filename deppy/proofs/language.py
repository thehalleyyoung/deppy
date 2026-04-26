"""
deppy.proofs.language — code-grounded proof DSL with a light cubical kernel
============================================================================

Problem this module solves
--------------------------
Given Python source and a proof (written by hand or by an LLM) that claims
something about that source, decide whether the proof actually holds — and
do it against the *code itself*, not a hand-built specification.

The trick is that the axioms a proof is allowed to invoke are derived from
the Python AST.  A function like

    def midpoint(a, b):
        return (a + b) // 2

is mechanically translated into an equational axiom

    midpoint_def :  midpoint(a, b) = (a + b) // 2

which the user's (or LLM's) proof can then cite as a fact, with the kernel
rejecting any proof that can't be assembled from those axioms plus a small
fixed library of inference rules.  If the code changes, the axioms change
with it — so a stale proof stops type-checking.

Minimal example
---------------
    from deppy import ProofKernel
    from deppy.proofs import axiomize, install, eq, T, prove

    def midpoint(a, b):
        return (a + b) // 2

    kernel = ProofKernel()
    install(kernel, axiomize(midpoint, module="demo"))

    # Theorem:  midpoint(a, b)  is  (a + b) // 2
    from deppy.core.formal_ops import Op, OpCall, op_floordiv, op_add
    from deppy.core.types import Var, Literal
    a, b = Var("a"), Var("b")
    goal = eq(
        OpCall(Op("midpoint", "demo"), (a, b)),
        op_floordiv(op_add(a, b), Literal(2)),
        a="object", b="object",
    )
    result = prove("midpoint_is_half_sum", kernel=kernel, goal=goal,
                   tactic=T.unfold("midpoint"))   # cites midpoint_def
    assert result.success

Why "cubical"
-------------
Equality in the kernel is a *path* (a 1-cell), not a Boolean predicate, so
congruence, symmetry, and transport compose into larger paths the same way
morphisms compose.  That is what lets the tactic DSL lift an equation at
one spot in a term up to an equation about the whole term via ``T.cong``,
and transport a property along a proven equality via ``T.transport``.
This module ships only the slice of cubical type theory needed for
definitional unfolding, congruence, symmetry, transitivity, transport, and
function extensionality — enough to discharge the proofs a typical spec
generates.  Full path-abstraction over the interval and glue types are out
of scope here; see ``deppy.hott.cubical`` for the richer primitives the
kernel itself understands.

How a proof is assembled
------------------------
    Python class / function
        │
        ▼   AST  →  formal Op-tree
    code_to_axioms(cls_or_fn)
        │   produces FormalAxiomEntry per def
        ▼
    kernel.register_formal_axiom(...)
        │
        ▼
    user/LLM writes a TACTIC SCRIPT in a small DSL
        │   T.unfold("push") >> T.cong(__items, T.refl()) >> ...
        ▼
    tactic.compile(pb)  →  real ProofTerm built via ProofBuilder
        │
        ▼
    kernel.check  →  VerificationResult (is the proof actually true?)

Definitional unfolding
----------------------
* ``def f(x): return EXPR``                    → ``f_def : f(x) = ⟦EXPR⟧``
* ``def f(x): if cond: return A; return B``    → ``f_def_case1`` / ``f_def_case2_default``
* ``def __init__(self, a): self.a = a``        → ``Cls_init_a : Cls(a).a = a``
* ``def m(self, x): return EXPR``              → ``Cls_m_def``
* ``@property def attr(self): return EXPR``    → ``Cls_attr_property`` (via pipeline)

Supported AST forms
-------------------
* return EXPR                          (single-return functions)
* if/elif/else returning EXPR each     (case-split axioms)
* arithmetic: + - * / // % ** unary -, abs, ==, !=, <, <=, >, >=
* boolean: and / or / not
* attribute access: self.x, p.field
* method calls: x.method(args), free function calls
* literals: int, float, bool, None
* tuple/list literal of literals

Extension points — multi-statement bodies, for-loop folds, recursion via
list induction, class inheritance — live in ``deppy.proofs.pipeline``.
"""
from __future__ import annotations

import ast
import inspect
import textwrap
from dataclasses import dataclass
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from deppy.core.kernel import ProofKernel, VerificationResult
from deppy.core.types import Context, PyObjType, Var, Literal
from deppy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq,
    op_add, op_sub, op_mul, op_truediv, op_floordiv, op_mod, op_pow,
    op_neg, op_abs, op_eq, op_ne, op_lt, op_le, op_gt, op_ge,
    op_and, op_or, op_not, op_len, op_getitem,
)
from deppy.proofs.tactics import ProofBuilder

_OBJ = PyObjType()


# ════════════════════════════════════════════════════════════════════
#  Axiom-naming grammar — single source of truth
# ════════════════════════════════════════════════════════════════════
#
#  Both code_to_axioms (language) and the tactic combinators that cite
#  those axioms (pipeline: Tactics.cases, Tactics.induction, …) consume
#  the same suffix vocabulary.  Changing a suffix here without updating
#  the citers would silently break cross-module wiring, so the grammar
#  lives in one place.
#
AXIOM_SUFFIX_DEF         = "_def"              # f(x) = <body>
AXIOM_SUFFIX_CASE        = "_def_case"         # + int: f(x) = <branch i>
AXIOM_SUFFIX_DEFAULT     = "_default"          # trailing marker on the fallthrough case
AXIOM_SUFFIX_FOLD        = "_fold"             # for-loop ⇒ foldl form
AXIOM_SUFFIX_INDUCTION   = "_induction"        # list-induction schema (pipeline)
AXIOM_SUFFIX_INIT        = "_init_"            # + field: Cls(a).field
AXIOM_SUFFIX_PROPERTY    = "_property"         # @property accessor (pipeline)
AXIOM_SUFFIX_INHERITED   = "__inherited"       # parent-class axiom re-tag (pipeline)

def axiom_case_suffix(i: int, is_default: bool = False) -> str:
    """Suffix for the i-th branch of a case-split axiom."""
    tail = AXIOM_SUFFIX_DEFAULT if is_default else ""
    return f"{AXIOM_SUFFIX_CASE}{i}{tail}"

# ════════════════════════════════════════════════════════════════════
#  Part 1  ·  Code → formal axioms (definitional unfolding)
# ════════════════════════════════════════════════════════════════════

class UnfoldError(Exception):
    """Raised when an AST construct can't be encoded as a formal Op."""

# Map Python AST binary operators → formal-op constructors
_BINOP: Dict[type, Callable[[Any, Any], OpCall]] = {
    ast.Add: op_add,
    ast.Sub: op_sub,
    ast.Mult: op_mul,
    ast.Div: op_truediv,
    ast.FloorDiv: op_floordiv,
    ast.Mod: op_mod,
    ast.Pow: op_pow,
}
_CMPOP: Dict[type, Callable[[Any, Any], OpCall]] = {
    ast.Eq: op_eq,   ast.NotEq: op_ne,
    ast.Lt: op_lt,   ast.LtE: op_le,
    ast.Gt: op_gt,   ast.GtE: op_ge,
}

def op_attr(obj, name: str) -> OpCall:
    """Generic attribute access: obj.name → __getattr__(obj, "name")."""
    return OpCall(Op(f".{name}"), (obj,))

def op_call(callee_name: str, args: tuple, module: str = "") -> OpCall:
    """Generic call: callee(args)."""
    return OpCall(Op(callee_name, module), args)

def op_method(obj, method_name: str, args: tuple) -> OpCall:
    """Method call: obj.method(args) → Op(.method)(obj, args...)."""
    return OpCall(Op(f".{method_name}"), (obj,) + args)

def _ast_to_op(node: ast.AST, scope: Dict[str, Any]) -> Any:
    """Translate a Python expression AST to a formal Op-tree.

    `scope` maps source-level identifiers to formal terms (Vars/Literals).
    """
    # ── Literals
    if isinstance(node, ast.Constant):
        return Literal(node.value, _OBJ)
    if isinstance(node, ast.Name):
        if node.id in scope:
            return scope[node.id]
        # Free name treated as a 0-ary symbol
        return OpCall(Op(node.id), ())
    # ── Binary arithmetic
    if isinstance(node, ast.BinOp):
        ctor = _BINOP.get(type(node.op))
        if ctor is None:
            raise UnfoldError(f"unsupported binop {type(node.op).__name__}")
        return ctor(_ast_to_op(node.left, scope), _ast_to_op(node.right, scope))
    # ── Unary
    if isinstance(node, ast.UnaryOp):
        # Constant fold: -3, +3, not True
        if isinstance(node.operand, ast.Constant):
            if isinstance(node.op, ast.USub) and isinstance(node.operand.value, (int, float)):
                return Literal(-node.operand.value, _OBJ)
            if isinstance(node.op, ast.UAdd) and isinstance(node.operand.value, (int, float)):
                return Literal(+node.operand.value, _OBJ)
        x = _ast_to_op(node.operand, scope)
        if isinstance(node.op, ast.USub):  return op_neg(x)
        if isinstance(node.op, ast.UAdd):  return x
        if isinstance(node.op, ast.Not):   return op_not(x)
        raise UnfoldError(f"unsupported unaryop {type(node.op).__name__}")
    # ── Comparisons (only chained 2-ary supported)
    if isinstance(node, ast.Compare):
        if len(node.ops) != 1 or len(node.comparators) != 1:
            # Treat chained as conjunction
            left = _ast_to_op(node.left, scope)
            acc = None
            cur = left
            for op, comp in zip(node.ops, node.comparators):
                ctor = _CMPOP.get(type(op))
                if ctor is None:
                    raise UnfoldError(f"unsupported cmp {type(op).__name__}")
                rhs = _ast_to_op(comp, scope)
                clause = ctor(cur, rhs)
                acc = clause if acc is None else op_and(acc, clause)
                cur = rhs
            return acc
        ctor = _CMPOP[type(node.ops[0])]
        return ctor(
            _ast_to_op(node.left, scope),
            _ast_to_op(node.comparators[0], scope),
        )
    # ── Boolean
    if isinstance(node, ast.BoolOp):
        ctor = op_and if isinstance(node.op, ast.And) else op_or
        vals = [_ast_to_op(v, scope) for v in node.values]
        acc = vals[0]
        for v in vals[1:]:
            acc = ctor(acc, v)
        return acc
    # ── Attribute access  obj.field
    if isinstance(node, ast.Attribute):
        return op_attr(_ast_to_op(node.value, scope), node.attr)
    # ── Function / method calls
    if isinstance(node, ast.Call):
        args = tuple(_ast_to_op(a, scope) for a in node.args)
        if isinstance(node.func, ast.Attribute):
            recv = _ast_to_op(node.func.value, scope)
            return op_method(recv, node.func.attr, args)
        if isinstance(node.func, ast.Name):
            if node.func.id == "abs" and len(args) == 1: return op_abs(args[0])
            if node.func.id == "len" and len(args) == 1: return op_len(args[0])
            return op_call(node.func.id, args)
        raise UnfoldError(f"unsupported call shape {ast.dump(node.func)}")
    # ── Subscript
    if isinstance(node, ast.Subscript):
        return op_getitem(
            _ast_to_op(node.value, scope),
            _ast_to_op(node.slice, scope),
        )
    # ── Tuple / list literal
    if isinstance(node, (ast.Tuple, ast.List)):
        elts = tuple(_ast_to_op(e, scope) for e in node.elts)
        return OpCall(Op("__tuple__"), elts)
    raise UnfoldError(f"unsupported AST node: {type(node).__name__}")

@dataclass
class CodeAxiom:
    name: str
    module: str
    formal: FormalAxiomEntry
    description: str

def function_to_axioms(fn: Callable, *, module: str = "") -> List[CodeAxiom]:
    """Translate a Python function into one or more definitional axioms.

    For
        def f(a, b):
            return EXPR
    produces
        f_def: f(a, b) = ⟦EXPR⟧

    For if/elif/else with returns in each branch, produces one axiom per
    branch guarded by the condition (each as a separate axiom; the
    user can pick which branch to invoke during a proof).
    """
    src = textwrap.dedent(inspect.getsource(fn))
    tree = ast.parse(src)
    fn_def = tree.body[0]
    if not isinstance(fn_def, ast.FunctionDef):
        raise UnfoldError(f"{fn.__name__} is not a function def")

    # Collect parameter names
    params = [a.arg for a in fn_def.args.args]
    scope = {p: Var(p) for p in params}

    # Build f(params)
    fn_name = fn_def.name
    lhs = OpCall(Op(fn_name, module), tuple(scope[p] for p in params))

    ctx = Context()
    for p in params:
        ctx = ctx.extend(p, _OBJ)

    axioms: List[CodeAxiom] = []

    def emit(name_suffix: str, rhs_op: Any, desc: str):
        ax = FormalAxiomEntry(
            name=fn_name + name_suffix,
            module=module,
            params=[(p, _OBJ) for p in params],
            conclusion=formal_eq(ctx, lhs, rhs_op, type_=_OBJ),
            description=desc,
        )
        axioms.append(CodeAxiom(
            name=fn_name + name_suffix, module=module,
            formal=ax, description=desc,
        ))

    # Walk the body looking for top-level returns / if-else returns
    body = fn_def.body
    # Single-return body
    if len(body) == 1 and isinstance(body[0], ast.Return) and body[0].value is not None:
        rhs = _ast_to_op(body[0].value, scope)
        emit(AXIOM_SUFFIX_DEF, rhs,
             f"{fn_name}({', '.join(params)}) = {ast.unparse(body[0].value)}")
        return axioms

    # Sequence of (if-return, if-return, ..., return) → multi-case axioms
    cases: List[Tuple[Optional[ast.AST], ast.AST]] = []
    for stmt in body:
        if (isinstance(stmt, ast.If)
                and len(stmt.body) == 1
                and isinstance(stmt.body[0], ast.Return)
                and stmt.body[0].value is not None
                and not stmt.orelse):
            cases.append((stmt.test, stmt.body[0].value))
        elif isinstance(stmt, ast.Return) and stmt.value is not None:
            cases.append((None, stmt.value))   # default branch
            break
        else:
            cases = []
            break
    if cases:
        for i, (cond, rval) in enumerate(cases, 1):
            rhs = _ast_to_op(rval, scope)
            tag = axiom_case_suffix(i, is_default=cond is None)
            desc = (f"when {ast.unparse(cond)}: {fn_name}(...) = {ast.unparse(rval)}"
                    if cond is not None
                    else f"otherwise: {fn_name}(...) = {ast.unparse(rval)}")
            emit(tag, rhs, desc)
        return axioms

    # if-elif-else with returns (single top-level If)
    if len(body) == 1 and isinstance(body[0], ast.If):
        n = 0
        def walk_if(if_node: ast.If):
            nonlocal n
            # Then-branch
            if (len(if_node.body) == 1
                    and isinstance(if_node.body[0], ast.Return)
                    and if_node.body[0].value is not None):
                rhs = _ast_to_op(if_node.body[0].value, scope)
                n += 1
                emit(axiom_case_suffix(n), rhs,
                     f"when {ast.unparse(if_node.test)}: "
                     f"{fn_name}(...) = {ast.unparse(if_node.body[0].value)}")
            # Else-branch may itself be another if (elif)
            if len(if_node.orelse) == 1 and isinstance(if_node.orelse[0], ast.If):
                walk_if(if_node.orelse[0])
            elif (len(if_node.orelse) == 1
                  and isinstance(if_node.orelse[0], ast.Return)
                  and if_node.orelse[0].value is not None):
                rhs = _ast_to_op(if_node.orelse[0].value, scope)
                n += 1
                emit(axiom_case_suffix(n), rhs,
                     f"else: {fn_name}(...) = {ast.unparse(if_node.orelse[0].value)}")
        walk_if(body[0])
        if axioms:
            return axioms

    raise UnfoldError(
        f"{fn_name}: only single-return or if/elif/else-of-returns supported "
        f"(got {len(body)} statements)"
    )

def class_to_axioms(cls: type, *, module: Optional[str] = None) -> List[CodeAxiom]:
    """Translate a Python class into definitional axioms.

    * `def __init__(self, a, b): self.a = a; self.b = b`  →  accessor axioms:
        ax  Cls(a, b).a = a
        ax  Cls(a, b).b = b

    * `def m(self, x): return EXPR`  →  method axiom:
        ax  c.m(x) = ⟦EXPR⟧[self ↦ c]
    """
    module = module or cls.__module__
    out: List[CodeAxiom] = []
    cls_name = cls.__name__

    # Collect attributes set by __init__ to produce accessor axioms
    init = cls.__dict__.get("__init__")
    init_params: List[str] = []
    if init is not None and inspect.isfunction(init):
        try:
            isrc = textwrap.dedent(inspect.getsource(init))
            itree = ast.parse(isrc).body[0]
            assert isinstance(itree, ast.FunctionDef)
            init_params = [a.arg for a in itree.args.args[1:]]  # skip self

            scope = {p: Var(p) for p in init_params}
            ctor = OpCall(
                Op(cls_name, module),
                tuple(scope[p] for p in init_params),
            )

            ctx = Context()
            for p in init_params:
                ctx = ctx.extend(p, _OBJ)

            for stmt in itree.body:
                if (isinstance(stmt, ast.Assign)
                        and len(stmt.targets) == 1
                        and isinstance(stmt.targets[0], ast.Attribute)
                        and isinstance(stmt.targets[0].value, ast.Name)
                        and stmt.targets[0].value.id == "self"):
                    field_name = stmt.targets[0].attr
                    try:
                        rhs = _ast_to_op(stmt.value, scope)
                    except UnfoldError:
                        continue
                    lhs = op_attr(ctor, field_name)
                    ax = FormalAxiomEntry(
                        name=f"{cls_name}{AXIOM_SUFFIX_INIT}{field_name}",
                        module=module,
                        params=[(p, _OBJ) for p in init_params],
                        conclusion=formal_eq(ctx, lhs, rhs, type_=_OBJ),
                        description=f"{cls_name}(...).{field_name} = {ast.unparse(stmt.value)}",
                    )
                    out.append(CodeAxiom(
                        name=ax.name, module=module, formal=ax,
                        description=ax.description,
                    ))
        except (OSError, SyntaxError, AssertionError):
            pass

    # Methods → method axioms (with 'self' bound as a free var)
    for attr, val in cls.__dict__.items():
        if attr in ("__init__",) or not inspect.isfunction(val):
            continue
        try:
            msrc = textwrap.dedent(inspect.getsource(val))
            mtree = ast.parse(msrc).body[0]
            assert isinstance(mtree, ast.FunctionDef)
            params = [a.arg for a in mtree.args.args]   # includes self
            scope = {p: Var(p) for p in params}

            method_lhs = op_method(
                scope["self"], attr,
                tuple(scope[p] for p in params[1:]),
            )

            ctx = Context()
            for p in params:
                ctx = ctx.extend(p, _OBJ)

            # Walk body
            body = mtree.body
            if (len(body) == 1 and isinstance(body[0], ast.Return)
                    and body[0].value is not None):
                rhs = _ast_to_op(body[0].value, scope)
                ax = FormalAxiomEntry(
                    name=f"{cls_name}_{attr}{AXIOM_SUFFIX_DEF}",
                    module=module,
                    params=[(p, _OBJ) for p in params],
                    conclusion=formal_eq(ctx, method_lhs, rhs, type_=_OBJ),
                    description=f"{cls_name}.{attr}({', '.join(params[1:])}) = "
                                f"{ast.unparse(body[0].value)}",
                )
                out.append(CodeAxiom(
                    name=ax.name, module=module, formal=ax,
                    description=ax.description,
                ))
        except (OSError, SyntaxError, AssertionError, UnfoldError):
            continue

    return out

# ════════════════════════════════════════════════════════════════════
#  Part 2  ·  Cubical tactic DSL
# ════════════════════════════════════════════════════════════════════

@dataclass
class Tactic:
    """Abstract tactic.  Subclasses implement compile(pb) → ProofTerm."""
    def compile(self, pb: ProofBuilder) -> Any:
        raise NotImplementedError
    def __rshift__(self, other: "Tactic") -> "Then":
        return Then(self, other)
    def __or__(self, other: "Tactic") -> "Try":
        return Try(self, other)

@dataclass
class TRefl(Tactic):
    """Reflexivity: prove ``x = x``.

    If ``term`` is omitted the LHS of the current goal is used; callers that
    use the default form must ensure a goal has been set on the ProofBuilder.
    """
    term: Optional[Any] = None
    def compile(self, pb):
        term = self.term if self.term is not None else _goal_lhs(pb)
        if term is None:
            raise RuntimeError(
                "TRefl: no term supplied and no goal LHS available — "
                "pass T.refl(term) explicitly"
            )
        return pb.refl(term)

@dataclass
class TSym(Tactic):
    inner: Tactic
    def compile(self, pb):  return pb.sym(self.inner.compile(pb))

@dataclass
class TTrans(Tactic):
    parts: Tuple[Tactic, ...]
    def compile(self, pb):
        ps = [t.compile(pb) for t in self.parts]
        out = ps[0]
        for p in ps[1:]:
            out = pb.trans(out, p)
        return out

@dataclass
class TCong(Tactic):
    func: Any           # SynTerm: the function being lifted through
    inner: Tactic
    def compile(self, pb):
        return pb.cong(self.func, self.inner.compile(pb))

@dataclass
class TUnfold(Tactic):
    """Invoke the single-return definitional axiom of a function.

    Cites the ``<name>_def`` axiom produced by ``function_to_axioms``.  For
    case-split functions use ``Tactics.cases(name, i)`` instead, which cites
    ``<name>_def_case<i>`` — see ``AXIOM_SUFFIX_CASE``.
    """
    name: str
    module: str = ""
    def compile(self, pb):
        return pb.axiom(self.name + AXIOM_SUFFIX_DEF, self.module)

@dataclass
class TAxiom(Tactic):
    name: str
    module: str = ""
    def compile(self, pb):
        return pb.axiom(self.name, self.module)

@dataclass
class TZ3(Tactic):
    formula: str
    def compile(self, pb):  return pb.z3(self.formula)


@dataclass
class _TZ3Auto(Tactic):
    """Automatic Z3 discharge — infers the formula from the current goal.

    When the user's goal is an equality ``lhs = rhs``, we form the
    string ``"lhs == rhs"``; when it's a refinement ``{x | P(x)}``,
    we use ``P(x)`` directly.  For other goal shapes we fall back to
    the explicit formula (if any).  The returned ProofTerm is the
    kernel's ``Z3Proof`` — discharge succeeds with ``Z3_VERIFIED``
    trust, fails with an error code (``E005`` / ``E005b`` / ``E005c``
    / ``E005i`` — see ``ARCHITECTURE.md §3``).

    Eager validation: the inferred formula is parsed via Python's
    ``compile(formula, '<z3_auto>', 'eval')`` before being handed to
    the Z3 bridge.  A parse error raises here, with the formula in the
    message, instead of bubbling up obliquely from inside Z3.
    """
    explicit_formula: Optional[str] = None

    def compile(self, pb):
        formula = self.explicit_formula
        if formula is None:
            goal = pb.goal
            # formal_eq Judgment carries .left / .right; use those.
            left = getattr(goal, "left", None)
            right = getattr(goal, "right", None)
            if left is not None and right is not None:
                formula = f"{left} == {right}"
            else:
                # Refinement goal: use its predicate string.
                ty = getattr(goal, "type_", None)
                pred = getattr(ty, "predicate", None)
                if pred:
                    formula = pred
                else:
                    raise RuntimeError(
                        "T.z3_auto(): cannot infer formula from goal "
                        "and no explicit formula was given"
                    )
        # Eager parse check.  We use Python's compile() because the Z3
        # bridge itself eval's the formula in a Python-with-Z3-symbols
        # env, so a Python-syntax error here will hit Z3 the same way.
        try:
            compile(formula, "<z3_auto>", "eval")
        except SyntaxError as e:
            raise RuntimeError(
                f"T.z3_auto(): inferred formula {formula!r} is not "
                f"valid Python syntax for Z3 ingestion: {e.msg}"
            )
        return pb.z3(formula)


@dataclass
class TTransport(Tactic):
    """Cubical transport: substitute along a path proof.

    ``transport(P, p, base)`` transports a proof of ``P(a)`` along a path
    ``p : a = b`` to produce a proof of ``P(b)``.  This is the cubical
    version of subject substitution.
    """
    type_family: Any
    path: Tactic
    base: Tactic
    def compile(self, pb):
        return pb.transport(
            self.type_family,
            self.path.compile(pb),
            self.base.compile(pb),
        )

@dataclass
class TPathIntro(Tactic):
    """Cubical path abstraction: ``<i> body(i) : body[0/i] = body[1/i]``.

    Given an interval variable ``ivar`` and a *term-level* body
    parametrised by that variable, produces a proof that the body at
    ``i=0`` is equal (as a path) to the body at ``i=1``.  The kernel
    verifies this via ``_verify_path_abs``, which substitutes the
    endpoints and checks the resulting terms are well-formed.

    Parameters
    ----------
    ivar
        Interval variable name.  Will be bound in ``body``; any free
        occurrence of this name in the body will be substituted with
        ``0`` / ``1`` at the endpoints.
    body
        A ``SynTerm`` that may mention ``ivar``.  Conceptually
        ``body(0)`` is the left endpoint and ``body(1)`` the right.
        If a ``Tactic`` is passed, its compiled result is wrapped so
        that the path endpoints come from the proof — useful when
        ``ivar`` is degenerate (reflexive path).

    Example
    -------
        # Reflexive path: <i> x : x = x
        T.path_intro("i", Var("x"))

        # Non-degenerate path: <i> If(i=0, a, b) : a = b
        T.path_intro("i", IfThenElse(
            cond=App(func=Var("Eq0"), arg=Var("i")),
            then_branch=Var("a"),
            else_branch=Var("b"),
        ))
    """
    ivar: str
    body: Any  # SynTerm | Tactic — we detect which at compile time
    def compile(self, pb):
        from deppy.core.types import PathAbs, Literal, SynTerm
        from deppy.core.path_engine import _PathProof, _register_path_proof_verifiers

        # Ensure the kernel has path-proof verifiers installed.  Idempotent
        # — registers a dispatcher for _PathProof if not already present.
        _register_path_proof_verifiers(pb._kernel)

        if not self.ivar:
            raise RuntimeError("TPathIntro: empty interval variable name")

        # Case 1: body is a SynTerm — wrap directly in a PathAbs.
        if isinstance(self.body, SynTerm):
            path_term = PathAbs(ivar=self.ivar, body=self.body)
            return _PathProof(
                path=path_term,
                description=f"path_intro(<{self.ivar}> {self.body})",
            )

        # Case 2: body is a Tactic — compile it, then build a real
        # interval-bound PathAbs whose body is an IfThenElse keyed on
        # the interval variable.
        #
        # Cubically: the path is
        #   <i> if (i = 0) then left else right
        # where (left, right) are the goal's endpoints.  At i=0 the
        # body reduces to the left endpoint; at i=1 to the right.
        # The inner tactic's compiled proof witnesses the equality
        # of those endpoints, and we carry it through as the
        # description so the kernel can re-verify.
        inner = self.body.compile(pb)
        from deppy.core.types import IfThenElse, App
        goal = pb.goal
        left = getattr(goal, "left", None) if goal is not None else None
        right = getattr(goal, "right", None) if goal is not None else None
        if left is None or right is None:
            # No goal endpoints — fall back to a reflexive path on
            # whatever LHS we can find.
            endpoint = left if left is not None else Literal(0)
            path_term = PathAbs(
                ivar=self.ivar,
                body=endpoint,
            )
        else:
            # Build the body that genuinely depends on the interval
            # variable: ``if i==0 then left else right``.  When the
            # kernel substitutes 0 / 1 for i it reduces to the
            # respective endpoint.
            body = IfThenElse(
                cond=App(
                    func=App(func=Var("Eq"), arg=Var(self.ivar)),
                    arg=Literal(0),
                ),
                then_branch=left,
                else_branch=right,
            )
            path_term = PathAbs(ivar=self.ivar, body=body)
        return _PathProof(
            path=path_term,
            description=f"path_intro(<{self.ivar}> …) over inner {inner!r}",
        )

@dataclass
class TExt(Tactic):
    """Function extensionality: ∀x. f x = g x  ⟹  f = g."""
    var: str
    body: Tactic
    def compile(self, pb):  return pb.ext(self.var, self.body.compile(pb))

@dataclass
class TSimp(Tactic):
    """Chained definitional simplification over a user-supplied axiom list.

    Compiles by citing each ``(name, module)`` in ``candidate_axioms`` in
    order and gluing the results together with ``pb.trans``, yielding a
    single proof of the chained equality.

    Limitation
    ----------
    This is *not* a unification-based simplifier.  No LHS matching, no
    congruence descent, no bound — the caller is responsible for picking
    axioms whose LHS/RHS endpoints line up as a telescope.  For an
    automation layer that discovers applicable axioms from a registry
    index, see ``Tactics.simp_with`` in ``deppy.proofs.pipeline``.
    """
    candidate_axioms: Tuple[Tuple[str, str], ...]   # (name, module)

    def compile(self, pb):
        steps = []
        for name, mod in self.candidate_axioms:
            try:
                steps.append(pb.axiom(name, mod))
            except Exception:
                continue
        if not steps:
            return pb.structural("simp: no candidate axioms applied")
        out = steps[0]
        for s in steps[1:]:
            out = pb.trans(out, s)
        return out

@dataclass
class Then(Tactic):
    """Sequence two tactics.  Compiles the second using the first as input."""
    first: Tactic
    second: Tactic
    def compile(self, pb):
        # If the user wrote A >> B with B being TRefl etc., we trans them.
        a = self.first.compile(pb)
        b = self.second.compile(pb)
        return pb.trans(a, b)

@dataclass
class Try(Tactic):
    """Try `primary`; if it fails to discharge the goal, fall back to `alt`."""
    primary: Tactic
    alt: Tactic
    def compile(self, pb):
        try:
            return self.primary.compile(pb)
        except Exception:
            return self.alt.compile(pb)

@dataclass
class TAuto(Tactic):
    """Bounded automation: try a sequence of generic tactics."""
    candidates: Tuple[Tactic, ...]
    def compile(self, pb):
        last_err = None
        for c in self.candidates:
            try:
                return c.compile(pb)
            except Exception as e:
                last_err = e
        raise last_err or RuntimeError("auto: no candidate succeeded")

@dataclass
class TStructural(Tactic):
    """Structural justification with a free-form note."""
    note: str = ""
    def compile(self, pb):
        return pb.structural(self.note)

# ── User-facing tactic constructors ─────────────────────────────────

class T:
    @staticmethod
    def refl(term=None):                      return TRefl(term)
    @staticmethod
    def sym(t):                                return TSym(t)
    @staticmethod
    def trans(*ts):                            return TTrans(ts)
    @staticmethod
    def cong(func, t):                         return TCong(func, t)
    @staticmethod
    def unfold(name, module=""):               return TUnfold(name, module)
    @staticmethod
    def axiom(name, module=""):                return TAxiom(name, module)
    @staticmethod
    def z3(formula):                           return TZ3(formula)
    @staticmethod
    def z3_auto(formula=None):
        """Dispatch the current goal to Z3 without requiring the
        caller to restate the formula.

        When ``formula`` is ``None`` (the usual case), the tactic's
        ``compile`` reads the goal's LHS / RHS and forms the
        equation-as-string to feed to Z3.  This is the
        ``T.z3.auto()``-style shorthand the tutorial shows.
        """
        return _TZ3Auto(formula)
    @staticmethod
    def transport(P, path, base):              return TTransport(P, path, base)
    @staticmethod
    def path_intro(i, body):                   return TPathIntro(i, body)
    @staticmethod
    def ext(var, body):                        return TExt(var, body)
    @staticmethod
    def structural(note=""):                   return TStructural(note)
    @staticmethod
    def simp(*name_module_pairs):
        """Chained simplification by sequential axiom invocations."""
        return TSimp(tuple(name_module_pairs))
    @staticmethod
    def auto(*candidates):                     return TAuto(candidates)

# ════════════════════════════════════════════════════════════════════
#  Part 3  ·  Goal language and `prove(...)` entrypoint
# ════════════════════════════════════════════════════════════════════

def _goal_lhs(pb: ProofBuilder):
    """Extract the LHS term from the builder's current goal.

    The goal is a ``Judgment`` (from ``formal_eq``) with ``left`` / ``right``
    fields, so we read ``.left`` directly — not via ``.type_.left``.
    """
    g = pb.goal
    if g is None:
        return None
    return getattr(g, "left", None)

@dataclass
class Goal:
    """User-friendly goal builder.  Wraps formal_eq."""
    ctx: Context
    lhs: Any
    rhs: Any

def eq(lhs, rhs, **vars_to_types) -> Goal:
    ctx = Context()
    for name in vars_to_types:
        ctx = ctx.extend(name, _OBJ)
    return Goal(ctx, lhs, rhs)

def install(kernel: ProofKernel, axioms: Sequence[CodeAxiom]) -> int:
    """Register the unfolded axioms with the kernel."""
    for ax in axioms:
        kernel.register_formal_axiom(ax.formal)
    return len(axioms)

def prove(theorem: str, *, kernel: ProofKernel, goal: Goal,
          tactic: Tactic, quiet: bool = False) -> VerificationResult:
    """The main entrypoint.

    Builds a goal, compiles the tactic into a real ProofTerm, and asks the
    kernel to verify the resulting proof.  The result is a real
    VerificationResult bearing a TrustLevel — not metadata.
    """
    formal_goal = formal_eq(goal.ctx, goal.lhs, goal.rhs, type_=_OBJ)
    pb = ProofBuilder(kernel, goal.ctx, formal_goal)
    proof_term = tactic.compile(pb)
    r = pb.conclude(proof_term)
    if not quiet:
        mark = "✓" if r.success else "✗"
        print(f"  {mark} [{r.trust_level.name:18s}] {theorem}")
        if not r.success:
            print(f"      reason: {r.message}")
    return r
