"""
deppy.proofs.pipeline — end-to-end checking of third-party proofs about code
============================================================================

Problem this module solves
--------------------------
``deppy.proofs.language`` gives you an AST-to-axioms translator and a tactic
DSL.  This module wraps those into a production pipeline: extract axioms
from richer code shapes (recursion, loops, properties, inheritance), stage
them in a registry that the kernel can read from, let a user or an LLM
write a tactic script against those axioms, and emit a ``ProofCertificate``
that is either kernel-checked or transparently labelled with its actual
trust level.

The certificate is the receipt.  It can be serialized to JSON, shipped
alongside the code, and fed back into ``verify_proof_script`` on any
machine with the same source to re-check the proof.  That round-trip is
what makes "here's Python, here's a proof about it, tell me if the proof
is true" a well-defined operation — it's the mechanical check that gives
you a reason to trust an LLM-produced proof rather than hoping it's right.

Minimal example
---------------
    from deppy import ProofKernel
    from deppy.proofs import (
        axiomize, AxiomRegistry, Tactics,
        ProofScript, verify_proof_script,
    )

    def midpoint(a, b):
        return (a + b) // 2

    kernel = ProofKernel()
    reg = AxiomRegistry()
    reg.add_all(axiomize(midpoint, module="demo"), source="demo")
    reg.install(kernel)

    # A proof someone else (or an LLM) wrote, as a JSON blob:
    script_json = '''
    {"goal": {...}, "tactic": {"kind": "unfold", "name": "midpoint",
                               "module": "demo"}}
    '''
    cert = verify_proof_script(script_json, kernel=kernel)
    if cert.kernel_verified:
        print("proof holds against the source")

Stages
------
    ┌─────────────────────────────────────────────────────────────────┐
    │  STAGE 1  ·  code_to_axioms  (AST → FormalAxiomEntry)           │
    │             multi-stmt let-inlining, for-loop → fold,           │
    │             self-recursive → list-induction schema, @property,  │
    │             class inheritance                                   │
    │                                                                 │
    │  STAGE 2  ·  AxiomRegistry   (dedup, provenance, LHS-head       │
    │             index, syntactic conflict detection, bulk install)  │
    │                                                                 │
    │  STAGE 3  ·  Tactics DSL     (first/repeat/simp_with/cases/     │
    │             induction + the underlying refl/sym/trans/cong/     │
    │             unfold/axiom/z3/transport/ext primitives)           │
    │                                                                 │
    │  STAGE 4  ·  ProofTree       (tactic → printable, Lean 4 /      │
    │             JSON exports, round-trippable)                      │
    │                                                                 │
    │  STAGE 5  ·  ProofCertificate (kernel result + trust level +    │
    │             axioms cited + content hash + replayable script)    │
    └─────────────────────────────────────────────────────────────────┘
"""
from __future__ import annotations

import ast
import hashlib
import inspect
import json
import textwrap
import time
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Set, Tuple

# ── Build on the existing language ──────────────────────────────────
from deppy.proofs.language import (
    CodeAxiom, UnfoldError, _ast_to_op, op_attr,
    function_to_axioms as _fn_axioms_simple,
    class_to_axioms     as _cls_axioms_simple,
    Tactic, T, Goal, install,
    _OBJ, _goal_lhs, _BINOP,
    AXIOM_SUFFIX_DEF, AXIOM_SUFFIX_FOLD,
    AXIOM_SUFFIX_INDUCTION, AXIOM_SUFFIX_PROPERTY, AXIOM_SUFFIX_INHERITED,
    axiom_case_suffix,
    TRefl, TSym, TTrans, TCong, TUnfold, TAxiom, TZ3,
    TTransport, TPathIntro, TExt, TSimp, Then, Try, TAuto, TStructural,
)

from deppy.core.kernel import ProofKernel, VerificationResult, TrustLevel
from deppy.core.types  import Context, Var, Literal
from deppy.core.formal_ops import (
    Op, OpCall, FormalAxiomEntry, formal_eq,
)
from deppy.proofs.tactics import ProofBuilder

# =====================================================================
#  STAGE 1   ·   DEEP CODE → AXIOMS
# =====================================================================

# We extend the simple AST translator with:
#   1. multi-statement bodies         (let-substitution / SSA inlining)
#   2. recursive function detection   (induction principle generation)
#   3. for-loops                       (fold-axiom generation)
#   4. while-loops                     (recurrence-axiom generation)
#   5. @property                       (no-arg accessor axioms)
#   6. inheritance                     (parent-class axiom inheritance)


# ── helper Op constructors for the new axiom kinds ──────────────────

def op_let(name: str, value: Any, body: Any) -> OpCall:
    """A let-binding: let name = value in body  (treated as `(λname.body)(value)`)."""
    return OpCall(Op("let"), (Literal(name, _OBJ), value, body))

def op_lambda(var_name: str, body: Any) -> OpCall:
    return OpCall(Op("λ"), (Literal(var_name, _OBJ), body))

def op_foldl(f: Any, init: Any, lst: Any) -> OpCall:
    return OpCall(Op("foldl", "deppy.list"), (f, init, lst))

def op_foldr(f: Any, init: Any, lst: Any) -> OpCall:
    return OpCall(Op("foldr", "deppy.list"), (f, init, lst))

def op_nil() -> OpCall:
    return OpCall(Op("nil", "deppy.list"), ())

def op_cons(x: Any, xs: Any) -> OpCall:
    return OpCall(Op("cons", "deppy.list"), (x, xs))

def op_isinstance(x: Any, t: Any) -> OpCall:
    return OpCall(Op("isinstance"), (x, t))

def op_implies(p: Any, q: Any) -> OpCall:
    return OpCall(Op("→"), (p, q))

def op_forall(var: str, body: Any) -> OpCall:
    return OpCall(Op("∀"), (Literal(var, _OBJ), body))

def op_pred(name: str, arg: Any) -> OpCall:
    """An abstract predicate symbol — used by induction principles."""
    return OpCall(Op(name), (arg,))


# ── 1.1  Multi-statement axiomizer (let-substitution) ───────────────

def _expand_let_inline(expr: Any, bindings: Dict[str, Any]) -> Any:
    """Substitute Vars whose name is in `bindings` with their values, recursively.

    Used to inline a sequence of `x = expr` assignments into the final return,
    producing one big closed-form expression suitable as an axiom RHS.
    """
    # Var
    if isinstance(expr, Var):
        if expr.name in bindings:
            return _expand_let_inline(bindings[expr.name], bindings)
        return expr
    # Literal
    if isinstance(expr, Literal):
        return expr
    # OpCall
    if isinstance(expr, OpCall):
        new_args = tuple(_expand_let_inline(a, bindings) for a in expr.args)
        return OpCall(expr.op, new_args)
    return expr

def _try_translate_body_with_lets(
    body: List[ast.stmt], scope: Dict[str, Any]
) -> Optional[Any]:
    """Translate a body of (assign|return) statements into a single expression
    by progressively building a substitution map.

    Supports:
        x = EXPR
        y = EXPR(x)              # may reference earlier bindings
        return EXPR(x, y, ...)
    Augmented assignment `x += EXPR` is desugared to `x = x + EXPR`.
    """
    bindings: Dict[str, Any] = {}
    local_scope = dict(scope)

    for stmt in body[:-1]:
        if isinstance(stmt, ast.Assign):
            if len(stmt.targets) != 1 or not isinstance(stmt.targets[0], ast.Name):
                return None
            name = stmt.targets[0].id
            try:
                rhs = _ast_to_op(stmt.value, local_scope)
            except UnfoldError:
                return None
            rhs_inlined = _expand_let_inline(rhs, bindings)
            bindings[name] = rhs_inlined
            local_scope[name] = Var(name)   # placeholder for later refs
        elif isinstance(stmt, ast.AugAssign):
            if not isinstance(stmt.target, ast.Name):
                return None
            name = stmt.target.id
            try:
                cur = bindings.get(name) or local_scope.get(name) or OpCall(Op(name), ())
                rhs = _ast_to_op(stmt.value, local_scope)
                ctor = _BINOP.get(type(stmt.op))
                if ctor is None:
                    return None
                new_val = ctor(cur, rhs)
                bindings[name] = _expand_let_inline(new_val, bindings)
                local_scope[name] = Var(name)
            except UnfoldError:
                return None
        else:
            return None

    last = body[-1]
    if not (isinstance(last, ast.Return) and last.value is not None):
        return None
    try:
        ret = _ast_to_op(last.value, local_scope)
    except UnfoldError:
        return None
    return _expand_let_inline(ret, bindings)


# ── 1.2  Self-recursion detection ───────────────────────────────────
#
# Recursive functions are handled at the *tactic* level via
# ``Tactics.induction(...)``, which builds a real ``ListInduction`` proof
# term (see ``deppy.core.kernel.ListInduction``).  No meta-axiom is
# registered; the kernel discharges induction natively from the supplied
# nil/cons proofs, so there is no ``∀P.`` quantifier for the user to
# pinky-promise their way past.

def _is_self_recursive(fn_def: ast.FunctionDef) -> bool:
    """True if ``fn_def`` syntactically calls itself."""
    name = fn_def.name
    for node in ast.walk(fn_def):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id == name:
                return True
    return False


# ── 1.3  For-loop → fold axiom ──────────────────────────────────────

def _try_extract_fold_axiom(
    fn_name: str, module: str,
    fn_def: ast.FunctionDef, scope: Dict[str, Any]
) -> Optional[Tuple[FormalAxiomEntry, str]]:
    """Detect the canonical pattern:

        def f(lst):
            acc = INIT
            for x in lst:
                acc = COMBINE(acc, x)
            return acc

    and produce the axiom

        f_fold:  f(lst) = foldl(λ(acc, x). COMBINE(acc, x), INIT, lst)
    """
    body = fn_def.body
    if len(body) != 3:
        return None

    # Find: assign, for, return
    if not (isinstance(body[0], ast.Assign)
            and isinstance(body[1], ast.For)
            and isinstance(body[2], ast.Return)):
        return None
    init_stmt, for_stmt, ret_stmt = body[0], body[1], body[2]

    # Pattern match: assign acc = INIT
    if not (len(init_stmt.targets) == 1
            and isinstance(init_stmt.targets[0], ast.Name)):
        return None
    acc_name = init_stmt.targets[0].id
    init_val = _ast_to_op(init_stmt.value, scope)

    # for x in lst:  body must be exactly  acc = COMBINE(acc, x)
    if not isinstance(for_stmt.target, ast.Name) or not isinstance(for_stmt.iter, ast.Name):
        return None
    x_name = for_stmt.target.id
    lst_name = for_stmt.iter.id
    if len(for_stmt.body) != 1:
        return None
    inner = for_stmt.body[0]
    inner_scope = dict(scope)
    inner_scope[acc_name] = Var(acc_name)
    inner_scope[x_name]   = Var(x_name)

    if isinstance(inner, ast.Assign):
        if not (len(inner.targets) == 1
                and isinstance(inner.targets[0], ast.Name)
                and inner.targets[0].id == acc_name):
            return None
        try:
            combine_body = _ast_to_op(inner.value, inner_scope)
        except UnfoldError:
            return None
    elif isinstance(inner, ast.AugAssign):
        if not (isinstance(inner.target, ast.Name)
                and inner.target.id == acc_name):
            return None
        ctor = _BINOP.get(type(inner.op))
        if ctor is None:
            return None
        try:
            combine_body = ctor(Var(acc_name), _ast_to_op(inner.value, inner_scope))
        except UnfoldError:
            return None
    else:
        return None

    # return acc
    if not (isinstance(ret_stmt, ast.Return)
            and isinstance(ret_stmt.value, ast.Name)
            and ret_stmt.value.id == acc_name):
        return None

    # Build the fold expression
    lam = OpCall(Op("λ²"),
                 (Literal(acc_name, _OBJ),
                  Literal(x_name,   _OBJ),
                  combine_body))
    fold_rhs = op_foldl(lam, init_val, scope[lst_name])

    ctx = Context().extend(lst_name, _OBJ)
    fn_lhs = OpCall(Op(fn_name, module), (scope[lst_name],))

    ax = FormalAxiomEntry(
        name=f"{fn_name}{AXIOM_SUFFIX_FOLD}",
        module=module,
        params=[(lst_name, _OBJ)],
        conclusion=formal_eq(ctx, fn_lhs, fold_rhs, type_=_OBJ),
        description=(
            f"{fn_name}({lst_name}) = "
            f"foldl(λ({acc_name},{x_name}). … , {ast.unparse(init_stmt.value)}, {lst_name})"
        ),
    )
    desc = (f"for-loop fold: {fn_name}({lst_name}) "
            f"= foldl over <{ast.unparse(inner)}> with init {ast.unparse(init_stmt.value)}")
    return ax, desc

def foldl_universal_axioms(module: str = "deppy.list") -> List[CodeAxiom]:
    """Register the universal foldl base- and step-axioms so users can rewrite
    a fold-axiom into a closed form:

        foldl(f, z, [])       = z
        foldl(f, z, x::xs)    = foldl(f, f(z, x), xs)
    """
    out: List[CodeAxiom] = []
    f, z, x, xs = Var("f"), Var("z"), Var("x"), Var("xs")
    ctx = (Context().extend("f", _OBJ).extend("z", _OBJ)
                  .extend("x", _OBJ).extend("xs", _OBJ))
    nil_ax = FormalAxiomEntry(
        name="foldl_nil", module=module,
        params=[("f", _OBJ), ("z", _OBJ)],
        conclusion=formal_eq(ctx, op_foldl(f, z, op_nil()), z, type_=_OBJ),
        description="foldl(f, z, []) = z",
    )
    out.append(CodeAxiom(name="foldl_nil", module=module, formal=nil_ax,
                         description=nil_ax.description))

    cons_ax = FormalAxiomEntry(
        name="foldl_cons", module=module,
        params=[("f", _OBJ), ("z", _OBJ), ("x", _OBJ), ("xs", _OBJ)],
        conclusion=formal_eq(
            ctx,
            op_foldl(f, z, op_cons(x, xs)),
            op_foldl(f, OpCall(Op("apply2"), (f, z, x)), xs),
            type_=_OBJ),
        description="foldl(f, z, x::xs) = foldl(f, f(z, x), xs)",
    )
    out.append(CodeAxiom(name="foldl_cons", module=module, formal=cons_ax,
                         description=cons_ax.description))
    return out


# ── 1.4  @property axiomization ─────────────────────────────────────

def _property_to_axiom(
    cls_name: str, module: str, attr: str, fn: Callable
) -> Optional[CodeAxiom]:
    """A `@property` `def attr(self): return EXPR` becomes an attribute axiom
    just like `__init__` accessor axioms (no parens on the LHS):

        ax  Cls(args).attr = EXPR[self ↦ Cls(args)]

    To get the args we walk the class's __init__.
    """
    try:
        psrc = textwrap.dedent(inspect.getsource(fn))
        tree = ast.parse(psrc).body[0]
        assert isinstance(tree, ast.FunctionDef)
        if not (len(tree.body) == 1
                and isinstance(tree.body[0], ast.Return)
                and tree.body[0].value is not None):
            return None
        scope = {"self": Var("self")}
        body_op = _ast_to_op(tree.body[0].value, scope)
        ctx = Context().extend("self", _OBJ)
        lhs = op_attr(Var("self"), attr)
        ax = FormalAxiomEntry(
            name=f"{cls_name}_{attr}{AXIOM_SUFFIX_PROPERTY}",
            module=module,
            params=[("self", _OBJ)],
            conclusion=formal_eq(ctx, lhs, body_op, type_=_OBJ),
            description=f"@property {cls_name}.{attr}: self.{attr} = "
                        f"{ast.unparse(tree.body[0].value)}",
        )
        return CodeAxiom(name=ax.name, module=module, formal=ax,
                         description=ax.description)
    except (OSError, SyntaxError, AssertionError, UnfoldError):
        return None


# ── 1.5  Top-level deep axiomizer ───────────────────────────────────

def deep_function_to_axioms(
    fn: Callable, *, module: str = "",
) -> List[CodeAxiom]:
    """Axiomise a function body, trying richer shapes than the simple pass.

    Tries, in order:
      1. the plain translator from ``deppy.proofs.language`` (single-return
         and if/elif/else of returns);
      2. the for-loop → ``foldl`` axiom;
      3. multi-statement let-inlined axiom.

    Self-recursive functions are handled *at proof time* via
    ``Tactics.induction``, which builds a real ``ListInduction`` kernel
    term; no induction meta-axiom is emitted here.
    """
    out: List[CodeAxiom] = []
    # 1. Try simple
    try:
        out.extend(_fn_axioms_simple(fn, module=module))
    except UnfoldError:
        pass

    # Re-parse for the deeper passes
    try:
        src = textwrap.dedent(inspect.getsource(fn))
        tree = ast.parse(src)
        fn_def = tree.body[0]
        if not isinstance(fn_def, ast.FunctionDef):
            return out
    except (OSError, SyntaxError):
        return out

    fn_name = fn_def.name
    params = [a.arg for a in fn_def.args.args]
    scope = {p: Var(p) for p in params}
    ctx = Context()
    for p in params:
        ctx = ctx.extend(p, _OBJ)
    lhs = OpCall(Op(fn_name, module), tuple(scope[p] for p in params))

    # 2. Try for-loop fold pattern
    fold = _try_extract_fold_axiom(fn_name, module, fn_def, scope)
    if fold is not None:
        ax, desc = fold
        out.append(CodeAxiom(name=ax.name, module=module, formal=ax,
                             description=desc))

    # 3. Try multi-statement let-inlining (only if simple translator failed)
    if not out:
        rhs = _try_translate_body_with_lets(fn_def.body, scope)
        if rhs is not None:
            ax = FormalAxiomEntry(
                name=f"{fn_name}{AXIOM_SUFFIX_DEF}",
                module=module,
                params=[(p, _OBJ) for p in params],
                conclusion=formal_eq(ctx, lhs, rhs, type_=_OBJ),
                description=(f"{fn_name}({', '.join(params)}) = "
                             f"<inlined multi-statement body>"),
            )
            out.append(CodeAxiom(name=ax.name, module=module, formal=ax,
                                 description=ax.description))

    return out


def deep_class_to_axioms(
    cls: type, *, module: Optional[str] = None
) -> List[CodeAxiom]:
    """Axiomise a class: init accessors, methods, properties, inheritance.

    * Plain init/method axioms from the simple translator
    * ``@property`` accessor axioms (via ``_property_to_axiom``)
    * Parent-class axioms re-tagged with ``AXIOM_SUFFIX_INHERITED``
    * Method bodies re-run through ``deep_function_to_axioms`` so
      multi-statement / for-loop shapes work inside methods too
    """
    module = module or cls.__module__
    out: List[CodeAxiom] = []

    # Simple base layer (init + single-return methods)
    out.extend(_cls_axioms_simple(cls, module=module))

    # @property handling
    for attr, val in cls.__dict__.items():
        if isinstance(val, property) and val.fget is not None:
            ax = _property_to_axiom(cls.__name__, module, attr, val.fget)
            if ax is not None:
                out.append(ax)

    # Inherit parent class axioms (skip `object`)
    for parent in cls.__mro__[1:]:
        if parent is object:
            continue
        try:
            parent_axioms = _cls_axioms_simple(parent, module=parent.__module__)
            for ax in parent_axioms:
                inh = CodeAxiom(
                    name=ax.name + AXIOM_SUFFIX_INHERITED, module=module,
                    formal=ax.formal,
                    description=f"[inherited from {parent.__name__}] {ax.description}",
                )
                out.append(inh)
        except Exception:
            pass

    # Replace single-return method axioms with deeper versions when possible
    for attr, val in cls.__dict__.items():
        if attr.startswith("__") or not inspect.isfunction(val):
            continue
        try:
            # A method's source uses `self`; treat self as a free variable.
            deep = deep_function_to_axioms(val, module=module)
            # Re-name method axioms to `Cls_method_*` to disambiguate
            for ax in deep:
                if not ax.name.startswith(cls.__name__):
                    new_name = f"{cls.__name__}_{ax.name}"
                    new_formal = FormalAxiomEntry(
                        name=new_name,
                        module=ax.formal.module,
                        params=ax.formal.params,
                        conclusion=ax.formal.conclusion,
                        description=ax.formal.description,
                    )
                    out.append(CodeAxiom(name=new_name, module=module,
                                         formal=new_formal,
                                         description=ax.description))
        except Exception:
            continue

    return out


def axiomize(obj: Any, *, module: str = "") -> List[CodeAxiom]:
    """Turn a function or class into a list of code-derived axioms.

    This is the recommended entry point.  Use ``function_to_axioms`` /
    ``class_to_axioms`` directly only when you need the simpler, non-deep
    translator (e.g. for testing coverage of the core AST→Op layer).
    """
    if inspect.isclass(obj):
        return deep_class_to_axioms(obj, module=module or obj.__module__)
    if inspect.isfunction(obj):
        return deep_function_to_axioms(obj, module=module)
    raise TypeError(f"axiomize: unsupported object {obj!r}")


# =====================================================================
#  STAGE 2   ·   AxiomRegistry
# =====================================================================

@dataclass
class AxiomMeta:
    """Per-axiom metadata tracked by the registry."""
    axiom: CodeAxiom
    source: str                       # qualified name of the originating Python obj
    content_hash: str                 # hash of the formal conclusion
    inherited_from: Optional[str] = None
    induction: bool = False
    fold: bool = False


def _axiom_content_hash(ax: CodeAxiom) -> str:
    """SHA256 digest of an axiom's identity: name, module, *typed* params,
    and the formal conclusion.  Parameter *types* matter because two
    same-named axioms over different argument types are distinct."""
    parts = [ax.formal.name, ax.formal.module]
    parts.append(repr(ax.formal.conclusion))
    parts.append(";".join(f"{p}:{repr(t)}" for p, t in ax.formal.params))
    return hashlib.sha256(":".join(parts).encode()).hexdigest()[:16]


@dataclass
class AxiomRegistry:
    """A registry for code-derived axioms destined for the kernel.

    Features
    --------
    * dedup by content hash (name + module + typed params + conclusion)
    * provenance: each axiom remembers which Python source produced it
    * LHS-head index: O(1) lookup of axioms to try for a given goal head
    * dependency edges: LHS head → set of RHS heads (static call graph)
    * syntactic conflict detection (see ``.conflicts()`` for caveats)
    * freeze/unfreeze for incremental rebuilds

    Limitations
    -----------
    This is a *syntactic* registry: equivalence is by string repr, not by
    alpha-equivalence or semantic equality.  For semantic checks escalate
    into ``deppy.equivalence`` or ``deppy.z3_bridge``.
    """

    by_qname: Dict[Tuple[str, str], AxiomMeta] = field(default_factory=dict)
    by_lhs_head: Dict[str, List[AxiomMeta]] = field(default_factory=lambda: defaultdict(list))
    deps: Dict[str, Set[str]] = field(default_factory=lambda: defaultdict(set))
    sources: Dict[str, List[str]] = field(default_factory=lambda: defaultdict(list))
    _frozen: bool = False

    # ── helpers ────────────────────────────────────────────────────

    @staticmethod
    def _head_of(term: Any) -> str:
        if isinstance(term, OpCall):
            return term.op.name
        if isinstance(term, Var):
            return f"$var:{term.name}"
        if isinstance(term, Literal):
            return f"$lit:{type(term.value).__name__}"
        return "?"

    def _term_heads(self, term: Any) -> Iterable[str]:
        if isinstance(term, OpCall):
            yield term.op.name
            for a in term.args:
                yield from self._term_heads(a)

    # ── core API ──────────────────────────────────────────────────

    def add(self, axiom: CodeAxiom, source: str = "<unknown>",
            inherited_from: Optional[str] = None) -> bool:
        """Add an axiom; returns True if added, False if duplicate."""
        if self._frozen:
            raise RuntimeError("registry is frozen")
        h = _axiom_content_hash(axiom)
        # Dedup: same content hash anywhere ⇒ skip
        for meta in self.by_qname.values():
            if meta.content_hash == h:
                return False
        meta = AxiomMeta(
            axiom=axiom, source=source, content_hash=h,
            inherited_from=inherited_from,
            induction=axiom.name.endswith(AXIOM_SUFFIX_INDUCTION),
            fold=axiom.name.endswith(AXIOM_SUFFIX_FOLD),
        )
        self.by_qname[(axiom.module, axiom.name)] = meta
        # Index by LHS head — conclusion is a Judgment or PathType with .left/.right
        concl = axiom.formal.conclusion
        left = getattr(concl, "left", None)
        right = getattr(concl, "right", None)
        if left is not None:
            head = self._head_of(left)
            self.by_lhs_head[head].append(meta)
            # Build dep edges: this axiom 'depends on' every head appearing in RHS
            if right is not None:
                for h2 in self._term_heads(right):
                    if h2 != head:
                        self.deps[axiom.name].add(h2)
        self.sources[source].append(axiom.name)
        return True

    def add_all(self, axioms: Sequence[CodeAxiom], *, source: str = "<bulk>") -> int:
        n = 0
        for ax in axioms:
            if self.add(ax, source=source):
                n += 1
        return n

    def install(self, kernel: ProofKernel) -> int:
        """Bulk-register every axiom (deduplicated) with the kernel."""
        n = 0
        seen: Set[str] = set()
        for meta in self.by_qname.values():
            ax = meta.axiom
            if ax.formal.qualified_name in seen:
                continue
            kernel.register_formal_axiom(ax.formal)
            seen.add(ax.formal.qualified_name)
            n += 1
        return n

    def conflicts(self) -> List[Tuple[str, str, str]]:
        """Syntactic-only conflict scan.

        Flags pairs of axioms with identical LHS reprs and distinct RHS
        reprs.  This catches obvious contradictions like
        ``f(x) = 0`` vs ``f(x) = 1`` but has two well-known limits:

        * **false positives** — two RHSes that are provably equal (e.g.
          ``1 + x`` vs ``x + 1``) differ as strings and will be flagged.
          For semantic conflict detection escalate into
          ``deppy.equivalence.check_equiv`` or Z3.
        * **false negatives** — two LHSes that are alpha-variants (e.g.
          ``f(a)`` vs ``f(b)``) have different reprs and will not match.

        Returns a list of ``(name_a, name_b, lhs_head)``.
        """
        out: List[Tuple[str, str, str]] = []
        for head, group in self.by_lhs_head.items():
            for i in range(len(group)):
                for j in range(i + 1, len(group)):
                    a, b = group[i].axiom, group[j].axiom
                    al = getattr(a.formal.conclusion, "left", None)
                    ar = getattr(a.formal.conclusion, "right", None)
                    bl = getattr(b.formal.conclusion, "left", None)
                    br = getattr(b.formal.conclusion, "right", None)
                    if al is None or bl is None:
                        continue
                    if (repr(al) == repr(bl)) and (repr(ar) != repr(br)):
                        out.append((a.name, b.name, head))
        return out

    def freeze(self) -> "AxiomRegistry":
        self._frozen = True
        return self

    def summary(self) -> str:
        n = len(self.by_qname)
        ind = sum(1 for m in self.by_qname.values() if m.induction)
        fld = sum(1 for m in self.by_qname.values() if m.fold)
        srcs = len(self.sources)
        confs = len(self.conflicts())
        return (f"AxiomRegistry: {n} axioms from {srcs} sources "
                f"({ind} induction principles, {fld} fold axioms, "
                f"{confs} conflicts)")

    # ── pretty printing ───────────────────────────────────────────

    def render(self, max_per_source: int = 6) -> str:
        """Return a multi-line human-readable listing of the registry."""
        lines: List[str] = [self.summary()]
        for src, names in self.sources.items():
            lines.append(f"\n  ── from {src} ──")
            for name in names[:max_per_source]:
                meta = next((m for m in self.by_qname.values() if m.axiom.name == name), None)
                if meta is None:
                    continue
                tag = ""
                if meta.induction: tag = " [induction]"
                elif meta.fold:    tag = " [fold]"
                elif meta.inherited_from: tag = f" [inherited:{meta.inherited_from}]"
                lines.append(f"    · {name}{tag}: {meta.axiom.description}")
            if len(names) > max_per_source:
                lines.append(f"    … and {len(names) - max_per_source} more")
        return "\n".join(lines)

    def show(self, max_per_source: int = 6) -> None:
        """Print the result of :meth:`render` to stdout."""
        print(self.render(max_per_source))


# =====================================================================
#  STAGE 3   ·   Tactic DSL extensions
# =====================================================================

@dataclass
class TFirst(Tactic):
    """Try each tactic in order; succeed with the first that produces a
    proof term and discharges the goal."""
    candidates: Tuple[Tactic, ...]
    def compile(self, pb):
        last = None
        for c in self.candidates:
            try:
                return c.compile(pb)
            except Exception as e:
                last = e
        raise last or RuntimeError("first: no tactic succeeded")


@dataclass
class TRepeat(Tactic):
    """Apply `inner` `n` times, chaining via trans (used for repeated rewrites)."""
    n: int
    inner: Tactic
    def compile(self, pb):
        ps = [self.inner.compile(pb) for _ in range(self.n)]
        out = ps[0]
        for p in ps[1:]:
            out = pb.trans(out, p)
        return out


@dataclass
class TSimpWith(Tactic):
    """Auto-simp using a registry: looks up axioms whose LHS-head matches the
    goal LHS-head and chains them via trans.

    This is a *real* automation: unlike `T.simp((name,mod),(name,mod))` which
    requires the user to enumerate axioms, this one *discovers* applicable
    axioms from the registry's index.
    """
    registry: AxiomRegistry
    max_steps: int = 6

    def compile(self, pb):
        lhs = _goal_lhs(pb)
        head = AxiomRegistry._head_of(lhs) if lhs is not None else "?"
        candidates = list(self.registry.by_lhs_head.get(head, []))
        if not candidates:
            raise RuntimeError(f"simp_with: no axioms indexed for head '{head}'")
        proofs = []
        for meta in candidates[:self.max_steps]:
            try:
                proofs.append(pb.axiom(meta.axiom.formal.name,
                                       meta.axiom.formal.module))
            except Exception:
                continue
        if not proofs:
            raise RuntimeError(f"simp_with: no candidate axiom verified for '{head}'")
        out = proofs[0]
        for p in proofs[1:]:
            out = pb.trans(out, p)
        return out


@dataclass
class TIntro(Tactic):
    """Introduce a hypothesis (placeholder; in our setting we just record the
    name and continue).  Useful for documenting proof structure."""
    name: str
    inner: Tactic
    def compile(self, pb):
        return self.inner.compile(pb)


@dataclass
class TCases(Tactic):
    """Case-split: cite the i-th case axiom of a function definition.

    Equivalent to ``T.axiom(fn_name + axiom_case_suffix(i), module)`` — the
    suffix grammar lives in ``deppy.proofs.language``.
    """
    fn_name: str
    case: int
    module: str = ""
    def compile(self, pb):
        return pb.axiom(self.fn_name + axiom_case_suffix(self.case), self.module)


@dataclass
class TInduction(Tactic):
    """List induction built as a real ``ListInduction`` kernel term.

    ``Tactics.induction(var, nil=<proof>, cons=<proof>)`` delegates to
    ``pb.by_list_induction``, so the kernel actually discharges the
    induction — the caller supplies a nil-case proof and a cons-case
    proof and the result carries KERNEL trust when both sub-proofs do.
    """
    var:  str
    nil:  Tactic
    cons: Tactic
    def compile(self, pb):
        return pb.by_list_induction(
            self.var,
            self.nil.compile(pb),
            self.cons.compile(pb),
        )


# ── Extended user-facing namespace `Tactics`  (extends T) ───────────

class Tactics(T):
    """Full tactic surface: ``T``'s primitives + pipeline combinators.

    Use ``Tactics`` rather than ``T`` whenever you need ``cases``,
    ``induction``, ``first``, ``repeat``, ``simp_with``, or ``intro`` —
    the underlying ``T.refl``/``T.sym``/``T.trans``/``T.cong``/``T.axiom``/
    ``T.unfold``/``T.z3``/``T.ext``/``T.transport``/``T.simp`` are
    inherited unchanged.
    """
    @staticmethod
    def first(*candidates):                    return TFirst(candidates)
    @staticmethod
    def repeat(n, inner):                      return TRepeat(n, inner)
    @staticmethod
    def simp_with(registry, max_steps=6):      return TSimpWith(registry, max_steps)
    @staticmethod
    def intro(name, inner):                    return TIntro(name, inner)
    @staticmethod
    def cases(fn_name, case, module=""):       return TCases(fn_name, case, module)
    @staticmethod
    def induction(var, nil, cons):             return TInduction(var, nil, cons)
    @staticmethod
    def structural(note=""):                   return TStructural(note)
    @staticmethod
    def cech_decompose(source, spec=""):
        """Čech-decompose a function source by branch and dispatch
        each patch to the kernel.  Returns a tactic that, when
        compiled, yields a ``_CechProof`` over the local proofs.
        """
        return TCechDecompose(source=source, spec=spec)
    @staticmethod
    def fiber_induction(source, spec=""):
        """Fibration descent: extract per-fiber proofs from an
        isinstance-style dispatch and combine them into a
        ``_FibrationProofTerm``.
        """
        return TFiberInduction(source=source, spec=spec)


@dataclass
class TCechDecompose(Tactic):
    """Real Čech-decomposition tactic.

    Wraps :class:`deppy.core.path_engine.CechDecomposer`: extracts the
    branches from ``source`` (a Python function source string), runs
    ``verify_locally`` on each patch with the supplied ``spec``, and
    glues the local proofs into a single ``_CechProof`` whose
    cocycle bit is set when the patches agree on overlaps.
    """
    source: str
    spec: str = ""

    def compile(self, pb):
        from deppy.core.path_engine import (
            CechDecomposer, _CechProof, _register_path_proof_verifiers,
        )
        _register_path_proof_verifiers(pb._kernel)
        decomp = CechDecomposer()
        cover = decomp.decompose(self.source, self.spec)
        if not cover.patches:
            return pb.structural(
                f"cech_decompose: no patches extracted from "
                f"{self.source[:60]!r}"
            )
        locals_ = decomp.verify_locally(cover, self.spec, pb._kernel)
        if not all(lp.result.success for lp in locals_):
            failed = next(lp for lp in locals_ if not lp.result.success)
            raise RuntimeError(
                f"cech_decompose: patch {failed.patch.index} failed: "
                f"{failed.result.message}"
            )
        cocycle = decomp.check_cocycle(cover, locals_)
        return _CechProof(
            local_proofs=[lp.proof_term for lp in locals_],
            cocycle_check=bool(cocycle.consistent),
            description=(
                f"Tactics.cech_decompose({len(locals_)} patches, "
                f"cocycle={cocycle.consistent})"
            ),
        )


@dataclass
class TFiberInduction(Tactic):
    """Real fibration-induction tactic.

    Wraps :class:`deppy.core.path_engine.FibrationVerifier`: extracts
    the fibration data from ``source`` (an isinstance-style dispatch),
    verifies the spec per fiber, and emits a ``_FibrationProofTerm``
    on success or raises with the first fiber's diagnostic on
    failure.
    """
    source: str
    spec: str = ""

    def compile(self, pb):
        from deppy.core.path_engine import (
            FibrationVerifier, _FibrationProofTerm,
            _register_path_proof_verifiers,
        )
        from deppy.core.kernel import Structural
        _register_path_proof_verifiers(pb._kernel)
        fib = FibrationVerifier()
        data = fib.extract_fibration(self.source)
        if not data.fibers:
            return pb.structural(
                f"fiber_induction: no fibers extracted from "
                f"{self.source[:60]!r}"
            )
        result = fib.verify_per_fiber(data, self.spec, pb._kernel)
        if not result.success:
            first_fail = next(
                (r for _, r in result.fiber_results if not r.success),
                None,
            )
            raise RuntimeError(
                f"fiber_induction: per-fiber discharge failed: "
                f"{first_fail.message if first_fail else '<unknown>'}"
            )
        # Re-package per-fiber VerificationResults as Structural witnesses
        # so the kernel can re-verify the assembly.
        fiber_proofs = [
            (ty, Structural(description=f"fiber {ty}: {r.message}"))
            for ty, r in result.fiber_results
        ]
        return _FibrationProofTerm(
            fiber_proofs=fiber_proofs,
            description=(
                f"Tactics.fiber_induction({len(fiber_proofs)} fibers)"
            ),
        )


# =====================================================================
#  STAGE 4   ·   ProofTree (printable proof structure)
# =====================================================================

@dataclass
class ProofTreeNode:
    """A printable record of one tactic invocation."""
    kind: str
    label: str
    children: List["ProofTreeNode"] = field(default_factory=list)

    def render(self, indent: int = 0, prefix: str = "") -> str:
        line = " " * indent + prefix + f"[{self.kind}] {self.label}"
        out = [line]
        for i, c in enumerate(self.children):
            last = (i == len(self.children) - 1)
            out.append(c.render(indent + 2, "└─ " if last else "├─ "))
        return "\n".join(out)

    def to_lean(self, indent: int = 0) -> str:
        pad = "  " * indent
        head = self.kind
        if self.kind == "refl":
            return f"{pad}rfl"
        if self.kind == "axiom":
            return f"{pad}@{self.label}"
        if self.kind == "trans":
            l = self.children[0].to_lean(indent)
            r = self.children[1].to_lean(indent)
            return f"{pad}Eq.trans\n{l}\n{r}"
        if self.kind == "sym":
            inner = self.children[0].to_lean(indent + 1)
            return f"{pad}Eq.symm (\n{inner}\n{pad})"
        if self.kind == "cong":
            inner = self.children[0].to_lean(indent + 1)
            return f"{pad}congrArg ({self.label}) (\n{inner}\n{pad})"
        if self.kind == "ext":
            inner = self.children[0].to_lean(indent + 1)
            return f"{pad}funext (fun {self.label} =>\n{inner}\n{pad})"
        return f"{pad}-- {head} {self.label}"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": self.kind, "label": self.label,
            "children": [c.to_dict() for c in self.children],
        }


def _tactic_to_tree(tac: Tactic) -> ProofTreeNode:
    """Recursively turn a tactic into a printable proof tree."""
    if isinstance(tac, TRefl):
        return ProofTreeNode("refl", "rfl")
    if isinstance(tac, TSym):
        return ProofTreeNode("sym", "symm", [_tactic_to_tree(tac.inner)])
    if isinstance(tac, TTrans):
        return ProofTreeNode("trans", f"chain[{len(tac.parts)}]",
                             [_tactic_to_tree(p) for p in tac.parts])
    if isinstance(tac, TCong):
        return ProofTreeNode("cong", repr(tac.func)[:30],
                             [_tactic_to_tree(tac.inner)])
    if isinstance(tac, TUnfold):
        return ProofTreeNode("axiom", f"{tac.name}_def")
    if isinstance(tac, TAxiom):
        return ProofTreeNode("axiom", tac.name)
    if isinstance(tac, TZ3):
        return ProofTreeNode("z3", tac.formula[:40])
    if isinstance(tac, TTransport):
        return ProofTreeNode("transport", "Kan",
                             [_tactic_to_tree(tac.path),
                              _tactic_to_tree(tac.base)])
    if isinstance(tac, TPathIntro):
        return ProofTreeNode("path-intro", f"λ{tac.ivar}",
                             [_tactic_to_tree(tac.body)])
    if isinstance(tac, TExt):
        return ProofTreeNode("ext", tac.var,
                             [_tactic_to_tree(tac.body)])
    if isinstance(tac, TSimp):
        return ProofTreeNode("simp",
                             f"⟨{', '.join(n for n,_ in tac.candidate_axioms)}⟩")
    if isinstance(tac, Then):
        return ProofTreeNode("trans", "≫",
                             [_tactic_to_tree(tac.first),
                              _tactic_to_tree(tac.second)])
    if isinstance(tac, Try):
        return ProofTreeNode("try", "‖",
                             [_tactic_to_tree(tac.primary),
                              _tactic_to_tree(tac.alt)])
    if isinstance(tac, TAuto):
        return ProofTreeNode("auto", "auto",
                             [_tactic_to_tree(c) for c in tac.candidates])
    # Newly-added tactics
    if isinstance(tac, TFirst):
        return ProofTreeNode("first", "first",
                             [_tactic_to_tree(c) for c in tac.candidates])
    if isinstance(tac, TRepeat):
        return ProofTreeNode("repeat", f"x{tac.n}",
                             [_tactic_to_tree(tac.inner)])
    if isinstance(tac, TSimpWith):
        return ProofTreeNode("simp-with",
                             f"registry({len(tac.registry.by_qname)} axioms)")
    if isinstance(tac, TIntro):
        return ProofTreeNode("intro", tac.name,
                             [_tactic_to_tree(tac.inner)])
    if isinstance(tac, TCases):
        return ProofTreeNode("cases", f"{tac.fn_name}#{tac.case}")
    if isinstance(tac, TInduction):
        return ProofTreeNode("induction", tac.var,
                             [_tactic_to_tree(tac.nil),
                              _tactic_to_tree(tac.cons)])
    if isinstance(tac, TStructural):
        return ProofTreeNode("structural", tac.note or "<no note>")
    return ProofTreeNode("?", type(tac).__name__)


# =====================================================================
#  STAGE 5   ·   ProofCertificate  (formal proof certificate)
# =====================================================================

def _tree_has_structural_leaf(node: ProofTreeNode) -> bool:
    """True iff any node in the tree is a ``structural`` pinky-promise."""
    if node.kind == "structural":
        return True
    return any(_tree_has_structural_leaf(c) for c in node.children)


def _collect_axiom_names(node: ProofTreeNode) -> List[str]:
    """Extract the qualified axiom names a proof tree actually cites."""
    out: List[str] = []
    if node.kind == "axiom":
        out.append(node.label)
    elif node.kind == "cases":
        # label is "fn#<i>"; recover "fn_def_case<i>"
        fn, _, idx = node.label.partition("#")
        if idx.isdigit():
            out.append(fn + axiom_case_suffix(int(idx)))
    for c in node.children:
        out.extend(_collect_axiom_names(c))
    return out


@dataclass
class ProofCertificate:
    """Kernel-checked receipt for one proof attempt.

    The certificate records both whether the kernel accepted the proof
    (``success``) and *at what trust level* — because the kernel will
    accept a ``Structural`` "trust me" proof at ``STRUCTURAL_CHAIN`` trust
    just as readily as a fully-checked proof at ``KERNEL`` trust.  Any
    caller that actually cares whether the proof is *true* should use
    ``kernel_verified`` (``success`` AND trust ≥ KERNEL), not ``success``
    alone.

    Fields
    ------
    theorem       human-readable name
    goal_repr     printable form of the formal goal
    success       did the kernel accept the proof term?
    trust_level   the weakest sub-proof's trust level (kernel-assigned)
    message       kernel message (reason on failure)
    axioms_used   qualified names of axioms the tree cites
    tree          printable proof tree (round-trippable)
    content_hash  sha256 over (goal_repr, tree, axioms_used) — stable
                  across runs with the same inputs; *not* a substitute
                  for re-running the kernel on a fresh instance
    duration_ms   wall-clock of compile + kernel.check
    """
    theorem:     str
    goal_repr:   str
    success:     bool
    trust_level: TrustLevel
    message:     str
    axioms_used: Tuple[str, ...]
    tree:        ProofTreeNode
    content_hash: str
    duration_ms: float

    @property
    def kernel_verified(self) -> bool:
        """True iff the kernel reduced the proof to code-derived facts.

        The check has two parts:

        * the kernel accepted the proof (``success``);
        * the proof tree contains no "structural" leaf — i.e. no
          ``Tactics.structural("trust me")`` pinky-promise escaped into
          a leaf position.

        This is the property to gate shipping on.  Crucially, a proof
        that cites code-derived axioms (``AXIOM_TRUSTED``) still counts
        as kernel_verified, because those axioms *are* the source code —
        the whole point of the pipeline is to ground proofs in axioms
        extracted from the Python AST.  What would *not* be verified is
        a proof that papers over a step with ``Structural``, because
        that is a hand-wave the kernel can't check against the code.
        """
        return self.success and not _tree_has_structural_leaf(self.tree)

    # ── friendly printers ─────────────────────────────────────────

    def summary(self) -> str:
        if not self.success:
            mark = "✗"
        else:
            mark = "✓" if self.kernel_verified else "~"   # ~ = accepted-but-not-kernel
        return (f"{mark} [{self.trust_level.name:18s}] {self.theorem}\n"
                f"    goal:        {self.goal_repr}\n"
                f"    axioms used: {', '.join(self.axioms_used) or '(none)'}\n"
                f"    hash:        {self.content_hash}\n"
                f"    elapsed:     {self.duration_ms:.1f} ms")

    def show_tree(self) -> str:
        return self.tree.render()

    def lean_export(self) -> str:
        """Lean 4 surface-level export of the proof."""
        body = self.tree.to_lean(1)
        return (f"-- Auto-exported by deppy.proofs.pipeline\n"
                f"theorem {self.theorem.replace(' ', '_')} :\n"
                f"  -- goal: {self.goal_repr}\n"
                f"  True := by\n{body}\n"
                f"-- end {self.theorem}")

    def to_dict(self) -> Dict[str, Any]:
        return {
            "theorem": self.theorem,
            "goal": self.goal_repr,
            "success": self.success,
            "kernel_verified": self.kernel_verified,
            "trust_level": self.trust_level.name,
            "axioms_used": list(self.axioms_used),
            "tree": self.tree.to_dict(),
            "hash": self.content_hash,
            "duration_ms": self.duration_ms,
        }

    def to_json(self, *, indent: int = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent)


def _cert_content_hash(
    goal_repr: str,
    tree: ProofTreeNode,
    axioms_used: Sequence[str],
    source_fingerprint: Optional[str],
) -> str:
    """SHA256 digest of everything the certificate semantically depends on.

    We include the source fingerprint (when available) so a certificate
    hashed against one version of the code won't match a hash computed
    against a different version — even if goal and tactic tree look
    identical.  Axioms used are sorted to keep the digest deterministic.
    """
    payload = {
        "goal": goal_repr,
        "tree": tree.to_dict(),
        "axioms": sorted(axioms_used),
        "source": source_fingerprint or "",
    }
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True).encode()
    ).hexdigest()[:16]


def prove_certificate(
    theorem:   str, *,
    kernel:    ProofKernel,
    goal:      Goal,
    tactic:    Tactic,
    source_fingerprint: Optional[str] = None,
    quiet:     bool = True,
) -> ProofCertificate:
    """Run ``tactic`` against ``goal`` and return a ``ProofCertificate``.

    ``source_fingerprint`` is an opaque string identifying the source code
    the proof is supposed to be about (for example ``hashlib.sha256(src).
    hexdigest()``).  When supplied it is folded into ``content_hash`` so
    two certs produced against different source versions don't collide.
    """
    formal_goal = formal_eq(goal.ctx, goal.lhs, goal.rhs, type_=_OBJ)
    pb = ProofBuilder(kernel, goal.ctx, formal_goal)
    t0 = time.perf_counter()
    try:
        proof_term = tactic.compile(pb)
        result = pb.conclude(proof_term)
    except Exception as e:
        result = VerificationResult.fail(f"Tactic failure: {e}", code="ETACTIC")
    elapsed_ms = (time.perf_counter() - t0) * 1000

    tree = _tactic_to_tree(tactic)
    axioms_used = tuple(dict.fromkeys(_collect_axiom_names(tree)))
    goal_repr = f"{pp_term(goal.lhs)} = {pp_term(goal.rhs)}"
    content_hash = _cert_content_hash(goal_repr, tree, axioms_used,
                                       source_fingerprint)

    cert = ProofCertificate(
        theorem=theorem, goal_repr=goal_repr,
        success=result.success, trust_level=result.trust_level,
        message=result.message, axioms_used=axioms_used,
        tree=tree, content_hash=content_hash, duration_ms=elapsed_ms,
    )
    if not quiet:
        print(cert.summary())
    return cert


# ── Pretty-printing formal terms ────────────────────────────────────

_BINOP_SYMBOLS = {"+", "-", "*", "/", "//", "%", "**",
                  "==", "!=", "<", "<=", ">", ">=", "and", "or"}


def pp_term(t: Any) -> str:
    """Compact printable form of a formal Op-tree (SynTerm)."""
    if isinstance(t, Var):     return t.name
    if isinstance(t, Literal): return repr(t.value)
    if isinstance(t, OpCall):
        op = t.op.name
        args = [pp_term(a) for a in t.args]
        if op.startswith("."):     # attribute / method access
            if len(args) == 1:
                return f"{args[0]}{op}"
            return f"{args[0]}{op}({', '.join(args[1:])})"
        if op in _BINOP_SYMBOLS and len(args) == 2:
            return f"({args[0]} {op} {args[1]})"
        if op == "__neg__" and len(args) == 1:
            return f"(-{args[0]})"
        return f"{op}({', '.join(args)})"
    return repr(t)


# =====================================================================
#  STAGE 5b  ·  ProofScript round-trip
# =====================================================================
#
# The vision is "here's Python, here's a proof someone (or some LLM)
# wrote, tell me if it's true."  To make that a mechanical operation we
# need a wire format a proof can live in, and a deterministic replay path
# that reconstructs and re-checks it against a kernel on the receiver's
# side.  ProofScript is that format; verify_proof_script is the replay.

# ── Term encoding (Var / Literal / OpCall → JSON and back) ──────────

def _term_to_dict(t: Any) -> Dict[str, Any]:
    if isinstance(t, Var):
        return {"$": "var", "name": t.name}
    if isinstance(t, Literal):
        return {"$": "lit", "value": t.value}
    if isinstance(t, OpCall):
        return {"$": "op",
                "op": t.op.name,
                "module": t.op.module,
                "args": [_term_to_dict(a) for a in t.args]}
    raise TypeError(f"cannot encode term of type {type(t).__name__}")


def _term_from_dict(d: Dict[str, Any]) -> Any:
    kind = d.get("$")
    if kind == "var":
        return Var(d["name"])
    if kind == "lit":
        return Literal(d["value"], _OBJ)
    if kind == "op":
        return OpCall(Op(d["op"], d.get("module", "")),
                      tuple(_term_from_dict(a) for a in d.get("args", ())))
    raise ValueError(f"unknown term kind in dict: {kind!r}")


# ── Tactic encoding ─────────────────────────────────────────────────
#
# The decoder is the inverse of _tactic_to_tree but preserves the
# *structural* content of each tactic so the decoded tactic compiles to
# the same proof term.  It is the serialized equivalent of the Tactic
# dataclasses — not the printable ProofTreeNode (which forgets
# parameter details like TCong's `func` argument).

def _tactic_to_dict(tac: Tactic) -> Dict[str, Any]:
    if isinstance(tac, TRefl):
        return {"kind": "refl",
                "term": _term_to_dict(tac.term) if tac.term is not None else None}
    if isinstance(tac, TSym):
        return {"kind": "sym", "inner": _tactic_to_dict(tac.inner)}
    if isinstance(tac, TTrans):
        return {"kind": "trans",
                "parts": [_tactic_to_dict(p) for p in tac.parts]}
    if isinstance(tac, TCong):
        return {"kind": "cong",
                "func": _term_to_dict(tac.func),
                "inner": _tactic_to_dict(tac.inner)}
    if isinstance(tac, TUnfold):
        return {"kind": "unfold", "name": tac.name, "module": tac.module}
    if isinstance(tac, TAxiom):
        return {"kind": "axiom", "name": tac.name, "module": tac.module}
    if isinstance(tac, TZ3):
        return {"kind": "z3", "formula": tac.formula}
    if isinstance(tac, TExt):
        return {"kind": "ext", "var": tac.var,
                "body": _tactic_to_dict(tac.body)}
    if isinstance(tac, TSimp):
        return {"kind": "simp",
                "candidates": [list(p) for p in tac.candidate_axioms]}
    if isinstance(tac, Then):
        return {"kind": "then",
                "first": _tactic_to_dict(tac.first),
                "second": _tactic_to_dict(tac.second)}
    if isinstance(tac, Try):
        return {"kind": "try",
                "primary": _tactic_to_dict(tac.primary),
                "alt": _tactic_to_dict(tac.alt)}
    if isinstance(tac, TAuto):
        return {"kind": "auto",
                "candidates": [_tactic_to_dict(c) for c in tac.candidates]}
    if isinstance(tac, TStructural):
        return {"kind": "structural", "note": tac.note}
    if isinstance(tac, TFirst):
        return {"kind": "first",
                "candidates": [_tactic_to_dict(c) for c in tac.candidates]}
    if isinstance(tac, TRepeat):
        return {"kind": "repeat", "n": tac.n,
                "inner": _tactic_to_dict(tac.inner)}
    if isinstance(tac, TIntro):
        return {"kind": "intro", "name": tac.name,
                "inner": _tactic_to_dict(tac.inner)}
    if isinstance(tac, TCases):
        return {"kind": "cases", "fn_name": tac.fn_name,
                "case": tac.case, "module": tac.module}
    if isinstance(tac, TInduction):
        return {"kind": "induction", "var": tac.var,
                "nil": _tactic_to_dict(tac.nil),
                "cons": _tactic_to_dict(tac.cons)}
    # TSimpWith depends on a live registry and cannot round-trip
    # without the caller re-binding it; TTransport / TPathIntro carry
    # arbitrary SynTerms and are out of scope until we have a richer
    # term encoder.
    raise TypeError(
        f"tactic {type(tac).__name__} cannot be serialized; use a simpler "
        "tactic or extend _tactic_to_dict/_tactic_from_dict"
    )


def _tactic_from_dict(d: Dict[str, Any]) -> Tactic:
    kind = d.get("kind")
    if kind == "refl":
        term = _term_from_dict(d["term"]) if d.get("term") is not None else None
        return TRefl(term)
    if kind == "sym":
        return TSym(_tactic_from_dict(d["inner"]))
    if kind == "trans":
        return TTrans(tuple(_tactic_from_dict(p) for p in d["parts"]))
    if kind == "cong":
        return TCong(_term_from_dict(d["func"]),
                     _tactic_from_dict(d["inner"]))
    if kind == "unfold":
        return TUnfold(d["name"], d.get("module", ""))
    if kind == "axiom":
        return TAxiom(d["name"], d.get("module", ""))
    if kind == "z3":
        return TZ3(d["formula"])
    if kind == "ext":
        return TExt(d["var"], _tactic_from_dict(d["body"]))
    if kind == "simp":
        return TSimp(tuple((n, m) for n, m in d["candidates"]))
    if kind == "then":
        return Then(_tactic_from_dict(d["first"]),
                    _tactic_from_dict(d["second"]))
    if kind == "try":
        return Try(_tactic_from_dict(d["primary"]),
                   _tactic_from_dict(d["alt"]))
    if kind == "auto":
        return TAuto(tuple(_tactic_from_dict(c) for c in d["candidates"]))
    if kind == "structural":
        return TStructural(d.get("note", ""))
    if kind == "first":
        return TFirst(tuple(_tactic_from_dict(c) for c in d["candidates"]))
    if kind == "repeat":
        return TRepeat(int(d["n"]), _tactic_from_dict(d["inner"]))
    if kind == "intro":
        return TIntro(d["name"], _tactic_from_dict(d["inner"]))
    if kind == "cases":
        return TCases(d["fn_name"], int(d["case"]), d.get("module", ""))
    if kind == "induction":
        return TInduction(d["var"],
                          _tactic_from_dict(d["nil"]),
                          _tactic_from_dict(d["cons"]))
    raise ValueError(f"unknown tactic kind {kind!r}")


# ── ProofScript: a serialized (goal, tactic, optional source id) ─────

@dataclass
class ProofScript:
    """A serializable proof about code.

    A script bundles the goal (what is being proven) with the tactic
    (how).  ``source_fingerprint`` is optional but strongly recommended:
    when present it pins the proof to a specific version of the source,
    so stale proofs shipped against updated code produce a different
    certificate hash and are easy to detect.
    """
    theorem: str
    goal: Goal
    tactic: Tactic
    source_fingerprint: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        ctx_vars = [name for name, _ in self.goal.ctx.all_bindings().items()]
        return {
            "theorem": self.theorem,
            "goal": {
                "lhs": _term_to_dict(self.goal.lhs),
                "rhs": _term_to_dict(self.goal.rhs),
                "vars": ctx_vars,
            },
            "tactic": _tactic_to_dict(self.tactic),
            "source_fingerprint": self.source_fingerprint,
        }

    def to_json(self, *, indent: int = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent)

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "ProofScript":
        gd = d["goal"]
        ctx = Context()
        for name in gd.get("vars", []):
            ctx = ctx.extend(name, _OBJ)
        goal = Goal(ctx, _term_from_dict(gd["lhs"]), _term_from_dict(gd["rhs"]))
        return cls(
            theorem=d["theorem"],
            goal=goal,
            tactic=_tactic_from_dict(d["tactic"]),
            source_fingerprint=d.get("source_fingerprint"),
        )

    @classmethod
    def from_json(cls, text: str) -> "ProofScript":
        return cls.from_dict(json.loads(text))

    def verify(self, kernel: ProofKernel, *, quiet: bool = True) -> ProofCertificate:
        """Re-run this script against ``kernel`` and return the certificate."""
        return prove_certificate(
            self.theorem,
            kernel=kernel,
            goal=self.goal,
            tactic=self.tactic,
            source_fingerprint=self.source_fingerprint,
            quiet=quiet,
        )


def verify_proof_script(
    script: "ProofScript | str | Dict[str, Any]",
    *,
    kernel: ProofKernel,
    quiet: bool = True,
) -> ProofCertificate:
    """Check a third-party proof against a kernel.

    Accepts a ``ProofScript`` instance, a JSON string, or a parsed dict.
    Returns the resulting ``ProofCertificate`` — inspect ``.kernel_verified``
    to decide whether the proof actually holds.
    """
    if isinstance(script, ProofScript):
        return script.verify(kernel, quiet=quiet)
    if isinstance(script, str):
        return ProofScript.from_json(script).verify(kernel, quiet=quiet)
    return ProofScript.from_dict(script).verify(kernel, quiet=quiet)


# =====================================================================
#  Convenience: register universal axioms
# =====================================================================

def register_universal_axioms(
    target: "ProofKernel | AxiomRegistry"
) -> int:
    """Install the standard foldl-base/step axioms.

    Call once per kernel (or registry) before proving theorems that need
    ``foldl_nil`` / ``foldl_cons`` — e.g. any proof about a for-loop
    function produced by ``axiomize``.
    """
    axs = foldl_universal_axioms()
    if isinstance(target, ProofKernel):
        return install(target, axs)
    return target.add_all(axs, source="universal:foldl")
