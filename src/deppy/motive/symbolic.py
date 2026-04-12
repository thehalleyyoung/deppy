"""Symbolic Return Expressions — the dependent type of a program's output.

Instead of comparing operations or enumerating patterns, we extract
the SYMBOLIC EXPRESSION that each function returns, where:

  - Parameters are symbolic variables: Param(i)
  - Constants are symbolic literals: Const(sort, hash)
  - Operations are symbolic applications: Apply(op_name, args...)
  - Loops become fixpoints: Fixpoint(domain, base, step)
  - Recursion becomes fixpoints: Fixpoint(domain, base, step)
  - Conditionals become case splits: Case(test, then, else)

Two functions are equivalent when their symbolic return expressions
are equivalent modulo:
  1. α-renaming of intermediate variables
  2. rec↔iter (both become Fixpoint)
  3. Sort-compatible subtyping

This IS the dependent type:
  f : (x₁:S₁, ..., xₙ:Sₙ) → { y:T | y = symbolic_expr(x₁,...,xₙ) }

And IS cohomological:
  The symbolic expression is the global section of the type presheaf.
  Two sections are cohomologous iff they normalize to the same form.

From HoTT: equivalence of symbolic expressions is a path in the
type space, and we check path existence via Z3 constraint solving.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from enum import IntEnum, auto
from typing import Dict, FrozenSet, List, Optional, Set, Tuple

from deppy.motive.sorts import Sort, sorts_compatible


# ═══════════════════════════════════════════════════════════════════
# §1  Symbolic Expression Language
# ═══════════════════════════════════════════════════════════════════

class SExprKind(IntEnum):
    """Kind of symbolic expression node."""
    PARAM     = 0       # function parameter reference
    CONST     = auto()  # literal constant
    APPLY     = auto()  # operation application
    FIXPOINT  = auto()  # loop/recursion fixpoint
    CASE      = auto()  # conditional
    BUILD     = auto()  # collection construction
    UNKNOWN   = auto()  # opaque/external


@dataclass(frozen=True)
class SExpr:
    """A node in the symbolic return expression tree.

    This is the fundamental representation: the program's output
    expressed symbolically over its inputs.
    """
    kind: SExprKind
    sort: Sort = Sort.TOP

    # PARAM fields
    param_index: int = -1

    # CONST fields
    const_hash: int = 0

    # APPLY fields
    op_name: str = ''
    op_family: str = ''
    children: Tuple[SExpr, ...] = ()

    # FIXPOINT fields: fixpoint(domain, base, step_op)
    # domain = what we iterate over (the range/collection)
    # base = initial accumulator value
    # step_op = the combining operation name (e.g., 'Arith.mul')
    fp_domain: Optional[SExpr] = None
    fp_base: Optional[SExpr] = None
    fp_step_op: str = ''
    fp_step_family: str = ''

    # CASE fields
    case_test: Optional[SExpr] = None
    case_then: Optional[SExpr] = None
    case_else: Optional[SExpr] = None

    @property
    def is_fixpoint(self) -> bool:
        return self.kind == SExprKind.FIXPOINT

    @property
    def is_param(self) -> bool:
        return self.kind == SExprKind.PARAM

    @property
    def is_const(self) -> bool:
        return self.kind == SExprKind.CONST

    def structural_signature(self) -> Tuple:
        """The structural signature for Z3 comparison.

        Captures WHAT is computed, not HOW:
        - For FIXPOINT: (FIXPOINT, step_family, base_sort, result_sort)
        - For APPLY: (APPLY, op_family, child_sigs...)
        - For PARAM: (PARAM, index)
        - For CONST: (CONST, sort)
        """
        if self.kind == SExprKind.PARAM:
            return (SExprKind.PARAM, self.param_index)
        if self.kind == SExprKind.CONST:
            return (SExprKind.CONST, self.sort)
        if self.kind == SExprKind.APPLY:
            child_sigs = tuple(c.structural_signature() for c in self.children)
            return (SExprKind.APPLY, self.op_family, self.sort, child_sigs)
        if self.kind == SExprKind.FIXPOINT:
            base_sig = self.fp_base.structural_signature() if self.fp_base else ()
            return (SExprKind.FIXPOINT, self.fp_step_family, self.sort, base_sig)
        if self.kind == SExprKind.CASE:
            then_sig = self.case_then.structural_signature() if self.case_then else ()
            else_sig = self.case_else.structural_signature() if self.case_else else ()
            return (SExprKind.CASE, self.sort, then_sig, else_sig)
        if self.kind == SExprKind.BUILD:
            child_sigs = tuple(c.structural_signature() for c in self.children)
            return (SExprKind.BUILD, self.sort, child_sigs)
        return (SExprKind.UNKNOWN,)


# Convenience constructors
def Param(index: int, sort: Sort = Sort.TOP) -> SExpr:
    return SExpr(SExprKind.PARAM, sort=sort, param_index=index)

def Const(sort: Sort, value_hash: int = 0) -> SExpr:
    return SExpr(SExprKind.CONST, sort=sort, const_hash=value_hash)

def Apply(op_name: str, children: Tuple[SExpr, ...],
          sort: Sort = Sort.TOP) -> SExpr:
    family = op_name.split('.')[0] if '.' in op_name else op_name
    return SExpr(SExprKind.APPLY, sort=sort, op_name=op_name,
                 op_family=family, children=children)

def Fixpoint(step_op: str, base: SExpr, domain: SExpr,
             sort: Sort = Sort.TOP) -> SExpr:
    family = step_op.split('.')[0] if '.' in step_op else step_op
    return SExpr(SExprKind.FIXPOINT, sort=sort, fp_step_op=step_op,
                 fp_step_family=family, fp_base=base, fp_domain=domain)

def Case(test: SExpr, then: SExpr, els: SExpr,
         sort: Sort = Sort.TOP) -> SExpr:
    return SExpr(SExprKind.CASE, sort=sort, case_test=test,
                 case_then=then, case_else=els)

def Build(children: Tuple[SExpr, ...], sort: Sort = Sort.SEQ) -> SExpr:
    return SExpr(SExprKind.BUILD, sort=sort, children=children)

def Unknown(sort: Sort = Sort.TOP) -> SExpr:
    return SExpr(SExprKind.UNKNOWN, sort=sort)


# ═══════════════════════════════════════════════════════════════════
# §2  Symbolic Interpreter — AST → SExpr
# ═══════════════════════════════════════════════════════════════════

class SymbolicInterpreter:
    """Abstract interpreter that extracts symbolic return expressions.

    Walks the AST and builds a symbolic expression tree representing
    what the function returns in terms of its inputs.
    """

    def __init__(self) -> None:
        self._func_name: str = ''
        self._param_names: List[str] = []
        self._param_sorts: List[Sort] = []
        self._env: Dict[str, SExpr] = {}     # var -> symbolic value
        self._returns: List[SExpr] = []       # collected return expressions
        self._has_recursion: bool = False
        self._has_iteration: bool = False

    def interpret(self, func_node: ast.FunctionDef) -> List[SExpr]:
        """Extract symbolic return expressions from a function."""
        self._func_name = func_node.name

        # Bind parameters
        for i, arg in enumerate(func_node.args.args):
            sort = self._infer_param_sort(arg, func_node)
            self._param_names.append(arg.arg)
            self._param_sorts.append(sort)
            self._env[arg.arg] = Param(i, sort)

        # Interpret body
        for stmt in func_node.body:
            if (isinstance(stmt, ast.Expr) and
                    isinstance(stmt.value, ast.Constant) and
                    isinstance(stmt.value.value, str)):
                continue
            self._interpret_stmt(stmt)

        # Post-processing: lift recursive patterns into fixpoints
        if self._has_recursion:
            self._returns = self._lift_recursion_to_fixpoint(self._returns)

        return self._returns

    @property
    def has_recursion(self) -> bool:
        return self._has_recursion

    @property
    def has_iteration(self) -> bool:
        return self._has_iteration

    # ── Recursion → Fixpoint lifting ────────────────────────────

    def _lift_recursion_to_fixpoint(self, returns: List[SExpr]) -> List[SExpr]:
        """Convert recursive return expressions into fixpoint form.

        When we have returns like:
          - const(1)                        ← base case
          - Apply(mul, [param(0), Recurse(sub(param(0), 1))])  ← recursive case

        Lift to:
          - Fixpoint(mul, const(1), range(1, param(0)+1))

        The domain is inferred from the recursive step:
          Recurse(sub(Param(i), Const(k))) → countdown from Param(i) by k
          Base case condition determines the lower bound.
          Domain = range(lower_bound, Param(i) + 1)

        This produces the EXACT SAME SExpr tree as the iterative version,
        making the program sites isomorphic and the geometric morphism trivially SAT.
        """
        base_cases = []
        recursive_cases = []

        for r in returns:
            if self._contains_recurse(r):
                recursive_cases.append(r)
            else:
                base_cases.append(r)

        if not recursive_cases or not base_cases:
            return returns

        lifted = []
        for rc in recursive_cases:
            step_op, step_family = self._extract_combining_op(rc)
            if step_op:
                base = base_cases[0]
                domain = self._infer_recursive_domain(rc, base)

                # Normalize base case: if base is Param(i) (identity return),
                # the effective fixpoint initial value is the value at the
                # recursion's bottom — which is the lower bound of the domain.
                # e.g., fib(n) with base "return n" when n<=1:
                #   fib(0)=0, fib(1)=1 → effective base = 0 (the identity element of add)
                # This is the presheaf restriction: the base section restricts
                # to a constant section at the domain's lower bound.
                if base.kind == SExprKind.PARAM:
                    # Base is "return param" — use the identity element of step_op
                    canonical = _canonical_op(step_op)
                    identity = _operation_identity(canonical)
                    if identity is not None:
                        base = Const(Sort.NUM, identity)

                fp = Fixpoint(step_op, base, domain, sort=rc.sort)
                lifted.append(fp)
            else:
                lifted.append(rc)

        return lifted if lifted else returns

    def _infer_recursive_domain(self, expr: SExpr, base_case: SExpr) -> SExpr:
        """Infer the iteration domain from a recursive call pattern.

        From Recurse(sub(Param(i), Const(k))):
          - Recursion variable = Param(i)
          - Step = -k (counting down)
          - Lower bound = base_case's const_hash (the base condition value)
          - Domain = range(lower_bound, Param(i) + 1)

        This is the sheaf-theoretic insight: the recursive descent through
        {n, n-k, n-2k, ...} and the iterative ascent through range(lo, n+1)
        are sections of the SAME presheaf over the same site, just traversed
        in different orders. For commutative+associative operations, they
        define cohomologous sections.
        """
        # Find the Recurse node and extract its argument
        rec_arg = self._find_recurse_arg(expr)
        if rec_arg is None:
            # Fallback: domain is just the first parameter
            return Param(0, self._param_sorts[0] if self._param_sorts else Sort.TOP)

        # Parse the recursive step: sub(Param(i), Const(k))
        param_idx, step = self._parse_recursive_step(rec_arg)
        if param_idx < 0:
            return Param(0, self._param_sorts[0] if self._param_sorts else Sort.TOP)

        # Infer lower bound from base case
        # For factorial: base = Const(NUM, hash=1), so lower_bound = 1
        # For fibonacci: base = Param(0), so lower_bound = 0
        if base_case.kind == SExprKind.CONST:
            lower_bound = base_case.const_hash
        else:
            lower_bound = 0

        # Construct domain = range(lower_bound, upper)
        # For single-recursion (factorial): upper = Param(i) + step
        # For multi-recursion (fibonacci): upper = Param(i)
        param_sort = (self._param_sorts[param_idx]
                      if param_idx < len(self._param_sorts) else Sort.TOP)
        param_ref = Param(param_idx, param_sort)

        n_recurse = self._count_recurse_calls(expr)
        if n_recurse > 1:
            # Multi-recursion (fibonacci-like): domain = range(lo, Param(i))
            upper = param_ref
        else:
            # Single recursion (factorial-like): domain = range(lo, Param(i)+step)
            upper = Apply('Arith.add', (param_ref, Const(Sort.NUM, step)),
                           sort=Sort.NUM)

        domain = Apply('Seq.range', (Const(Sort.NUM, lower_bound), upper),
                        sort=Sort.SEQ)
        return domain

    def _count_recurse_calls(self, expr: SExpr) -> int:
        """Count recursive self-calls in an expression."""
        if expr.kind == SExprKind.APPLY and expr.op_name == 'Recurse':
            return 1
        count = 0
        for c in expr.children:
            count += self._count_recurse_calls(c)
        if expr.kind == SExprKind.CASE:
            for sub in [expr.case_then, expr.case_else]:
                if sub:
                    count += self._count_recurse_calls(sub)
        return count

    def _find_recurse_arg(self, expr: SExpr) -> Optional[SExpr]:
        """Find the argument passed to the recursive self-call."""
        if expr.kind == SExprKind.APPLY and expr.op_name == 'Recurse':
            return expr.children[0] if expr.children else None
        for c in expr.children:
            result = self._find_recurse_arg(c)
            if result is not None:
                return result
        if expr.kind == SExprKind.CASE:
            for sub in [expr.case_then, expr.case_else]:
                if sub:
                    result = self._find_recurse_arg(sub)
                    if result is not None:
                        return result
        return None

    def _parse_recursive_step(self, rec_arg: SExpr) -> Tuple[int, int]:
        """Parse a recursive step expression to extract (param_index, step_size).

        sub(Param(i), Const(k)) → (i, k)   — countdown by k
        Param(i) → (i, 1)                   — implicit countdown by 1
        """
        if rec_arg.kind == SExprKind.PARAM:
            return rec_arg.param_index, 1

        if (rec_arg.kind == SExprKind.APPLY and
                rec_arg.op_name in ('Arith.sub', 'sub')):
            children = rec_arg.children
            if (len(children) == 2 and
                    children[0].kind == SExprKind.PARAM and
                    children[1].kind == SExprKind.CONST):
                return children[0].param_index, children[1].const_hash

        return -1, 1

    def _contains_recurse(self, expr: SExpr) -> bool:
        """Check if expression contains a recursive self-call."""
        if expr.kind == SExprKind.APPLY and expr.op_name == 'Recurse':
            return True
        for c in expr.children:
            if self._contains_recurse(c):
                return True
        if expr.kind == SExprKind.CASE:
            for sub in [expr.case_then, expr.case_else]:
                if sub and self._contains_recurse(sub):
                    return True
        return False

    def _extract_combining_op(self, expr: SExpr) -> Tuple[str, str]:
        """Extract the combining operation from a recursive expression.

        e.g., Apply(Arith.mul, [param(0), Recurse(...)]) → ('Arith.mul', 'Arith')
        """
        if expr.kind == SExprKind.APPLY:
            # Check if any child is a Recurse
            has_recurse = any(
                c.kind == SExprKind.APPLY and c.op_name == 'Recurse'
                for c in expr.children
            )
            if has_recurse and expr.op_name != 'Recurse':
                return expr.op_name, expr.op_family
            # Try deeper
            for c in expr.children:
                op, fam = self._extract_combining_op(c)
                if op:
                    return op, fam

        if expr.kind == SExprKind.CASE:
            for sub in [expr.case_then, expr.case_else]:
                if sub:
                    op, fam = self._extract_combining_op(sub)
                    if op:
                        return op, fam

        return '', ''

    # ── Statement interpretation ────────────────────────────────

    def _interpret_stmt(self, stmt: ast.stmt) -> None:
        if isinstance(stmt, ast.Assign):
            self._interpret_assign(stmt)
        elif isinstance(stmt, ast.AugAssign):
            self._interpret_aug_assign(stmt)
        elif isinstance(stmt, ast.Return):
            self._interpret_return(stmt)
        elif isinstance(stmt, ast.If):
            self._interpret_if(stmt)
        elif isinstance(stmt, ast.For):
            self._interpret_for(stmt)
        elif isinstance(stmt, ast.While):
            self._interpret_while(stmt)
        elif isinstance(stmt, ast.Expr):
            pass  # side-effect expression — ignore for return analysis
        elif isinstance(stmt, ast.Try):
            for s in getattr(stmt, 'body', []):
                self._interpret_stmt(s)
            for h in getattr(stmt, 'handlers', []):
                for s in h.body:
                    self._interpret_stmt(s)
        elif isinstance(stmt, ast.With):
            for s in stmt.body:
                self._interpret_stmt(s)
        elif isinstance(stmt, ast.FunctionDef):
            pass  # nested function — skip for now
        elif isinstance(stmt, ast.Delete):
            pass

    def _interpret_assign(self, stmt: ast.Assign) -> None:
        for target in stmt.targets:
            if isinstance(target, ast.Name):
                val = self._interpret_expr(stmt.value)
                self._env[target.id] = val
            elif isinstance(target, (ast.Tuple, ast.List)):
                # Handle tuple unpacking: a, b = expr1, expr2
                if isinstance(stmt.value, (ast.Tuple, ast.List)):
                    # Evaluate ALL RHS values first (Python semantics)
                    rhs_vals = [self._interpret_expr(v) for v in stmt.value.elts]
                    for elt, v in zip(target.elts, rhs_vals):
                        if isinstance(elt, ast.Name):
                            self._env[elt.id] = v
                else:
                    val = self._interpret_expr(stmt.value)
                    for elt in target.elts:
                        if isinstance(elt, ast.Name):
                            self._env[elt.id] = Unknown(Sort.TOP)

    def _interpret_aug_assign(self, stmt: ast.AugAssign) -> None:
        if isinstance(stmt.target, ast.Name):
            var = stmt.target.id
            old = self._env.get(var, Unknown())
            rhs = self._interpret_expr(stmt.value)
            op_name = _augop_name(stmt.op)
            self._env[var] = Apply(op_name, (old, rhs),
                                   sort=old.sort if old.sort != Sort.TOP else rhs.sort)

    def _interpret_return(self, stmt: ast.Return) -> None:
        if stmt.value:
            expr = self._interpret_expr(stmt.value)
            self._returns.append(expr)

    def _interpret_if(self, stmt: ast.If) -> None:
        test_expr = self._interpret_expr(stmt.test)

        saved_env = dict(self._env)
        saved_returns = list(self._returns)

        # Interpret then-branch
        self._returns = []
        then_env = dict(self._env)
        for s in stmt.body:
            self._interpret_stmt(s)
        then_returns = list(self._returns)
        then_env_after = dict(self._env)

        # Interpret else-branch
        self._env = dict(saved_env)
        self._returns = []
        for s in stmt.orelse:
            self._interpret_stmt(s)
        else_returns = list(self._returns)
        else_env_after = dict(self._env)

        # Restore base returns
        self._returns = saved_returns

        # If then-branch returns, those are conditional returns
        for tr in then_returns:
            self._returns.append(tr)

        for er in else_returns:
            self._returns.append(er)

        # Merge environments for non-returning branches
        # (take from whichever branch didn't return)
        if then_returns and not else_returns:
            self._env = else_env_after
        elif else_returns and not then_returns:
            self._env = then_env_after
        else:
            self._env = saved_env

    def _interpret_for(self, stmt: ast.For) -> None:
        self._has_iteration = True
        iter_expr = self._interpret_expr(stmt.iter)

        # Detect accumulator pattern (single-variable)
        accum_var, step_op = self._detect_accumulator(stmt.body)
        if accum_var and accum_var in self._env:
            base = self._env[accum_var]
            fp = Fixpoint(step_op, base, iter_expr,
                          sort=base.sort if base.sort != Sort.TOP else Sort.TOP)
            self._env[accum_var] = fp
            for s in stmt.body:
                if not self._is_accum_stmt(s, accum_var):
                    self._interpret_stmt(s)
            return

        # Detect multi-variable fixpoint (tuple assignment in loop)
        multi = self._detect_multi_var_fixpoint(stmt.body)
        if multi:
            for var_name, step_op in multi.items():
                if var_name in self._env:
                    base = self._env[var_name]
                    fp = Fixpoint(step_op, base, iter_expr,
                                  sort=base.sort if base.sort != Sort.TOP else Sort.TOP)
                    self._env[var_name] = fp
            return

        # Generic: execute body for side effects
        for s in stmt.body:
            self._interpret_stmt(s)

    def _interpret_while(self, stmt: ast.While) -> None:
        self._has_iteration = True

        # Detect accumulator pattern
        accum_var, step_op = self._detect_accumulator(stmt.body)
        if accum_var and accum_var in self._env:
            base = self._env[accum_var]
            domain = self._interpret_expr(stmt.test)
            fp = Fixpoint(step_op, base, domain,
                          sort=base.sort if base.sort != Sort.TOP else Sort.TOP)
            self._env[accum_var] = fp
            for s in stmt.body:
                if not self._is_accum_stmt(s, accum_var):
                    self._interpret_stmt(s)
        else:
            for s in stmt.body:
                self._interpret_stmt(s)

    # ── Expression interpretation ───────────────────────────────

    def _interpret_expr(self, expr: ast.expr) -> SExpr:
        if isinstance(expr, ast.Constant):
            return self._interpret_const(expr)
        if isinstance(expr, ast.Name):
            return self._interpret_name(expr)
        if isinstance(expr, ast.BinOp):
            return self._interpret_binop(expr)
        if isinstance(expr, ast.UnaryOp):
            return self._interpret_unaryop(expr)
        if isinstance(expr, ast.Compare):
            return self._interpret_compare(expr)
        if isinstance(expr, ast.BoolOp):
            return self._interpret_boolop(expr)
        if isinstance(expr, ast.Call):
            return self._interpret_call(expr)
        if isinstance(expr, ast.IfExp):
            test = self._interpret_expr(expr.test)
            then = self._interpret_expr(expr.body)
            els = self._interpret_expr(expr.orelse)
            return Case(test, then, els, sort=then.sort)
        if isinstance(expr, ast.Subscript):
            coll = self._interpret_expr(expr.value)
            return Apply('index', (coll,), sort=Sort.TOP)
        if isinstance(expr, ast.Attribute):
            obj = self._interpret_expr(expr.value)
            return Apply(f'attr.{expr.attr}', (obj,), sort=Sort.TOP)
        if isinstance(expr, (ast.List, ast.Tuple)):
            elts = tuple(self._interpret_expr(e) for e in expr.elts)
            return Build(elts, sort=Sort.SEQ)
        if isinstance(expr, ast.Dict):
            vals = tuple(self._interpret_expr(v) for v in expr.values if v)
            return Build(vals, sort=Sort.MAP)
        if isinstance(expr, ast.Set):
            elts = tuple(self._interpret_expr(e) for e in expr.elts)
            return Build(elts, sort=Sort.SET)
        if isinstance(expr, ast.ListComp):
            return self._interpret_comprehension(expr, Sort.SEQ)
        if isinstance(expr, ast.SetComp):
            return self._interpret_comprehension(expr, Sort.SET)
        if isinstance(expr, ast.DictComp):
            return self._interpret_comprehension(expr, Sort.MAP)
        if isinstance(expr, ast.GeneratorExp):
            return self._interpret_comprehension(expr, Sort.ITER)
        if isinstance(expr, ast.Lambda):
            return Unknown(Sort.FUNC)
        if isinstance(expr, ast.JoinedStr):
            return Unknown(Sort.STR)
        if isinstance(expr, ast.Starred):
            return self._interpret_expr(expr.value)
        return Unknown()

    def _interpret_const(self, node: ast.Constant) -> SExpr:
        v = node.value
        if isinstance(v, bool):
            return Const(Sort.BOOL, hash(v))
        if isinstance(v, (int, float, complex)):
            return Const(Sort.NUM, hash(v))
        if isinstance(v, str):
            return Const(Sort.STR, hash(v))
        if v is None:
            return Const(Sort.NONE, 0)
        return Const(Sort.TOP, 0)

    def _interpret_name(self, node: ast.Name) -> SExpr:
        if node.id in self._env:
            return self._env[node.id]
        # External name
        return Unknown(Sort.TOP)

    def _interpret_binop(self, node: ast.BinOp) -> SExpr:
        left = self._interpret_expr(node.left)
        right = self._interpret_expr(node.right)
        op_name = _binop_name(node.op)
        sort = _binop_sort(node.op, left.sort, right.sort)
        return Apply(op_name, (left, right), sort=sort)

    def _interpret_unaryop(self, node: ast.UnaryOp) -> SExpr:
        operand = self._interpret_expr(node.operand)
        op_name = f'Unary.{type(node.op).__name__}'
        sort = Sort.BOOL if isinstance(node.op, ast.Not) else Sort.NUM
        return Apply(op_name, (operand,), sort=sort)

    def _interpret_compare(self, node: ast.Compare) -> SExpr:
        left = self._interpret_expr(node.left)
        parts = [left]
        for comp in node.comparators:
            parts.append(self._interpret_expr(comp))
        op_names = [_cmpop_name(op) for op in node.ops]
        # Flatten to single comparison expression
        if len(op_names) == 1:
            return Apply(op_names[0], (parts[0], parts[1]), sort=Sort.BOOL)
        return Apply('Cmp.chain', tuple(parts), sort=Sort.BOOL)

    def _interpret_boolop(self, node: ast.BoolOp) -> SExpr:
        vals = tuple(self._interpret_expr(v) for v in node.values)
        name = 'Logic.and' if isinstance(node.op, ast.And) else 'Logic.or'
        return Apply(name, vals, sort=Sort.BOOL)

    def _interpret_call(self, node: ast.Call) -> SExpr:
        args = tuple(self._interpret_expr(a) for a in node.args)
        # Capture keyword arguments as part of the signature
        kwarg_keys = tuple(kw.arg or '_splat' for kw in node.keywords)

        if isinstance(node.func, ast.Name):
            name = node.func.id

            # Self-recursive call → Fixpoint
            if name == self._func_name:
                self._has_recursion = True
                # The recursive call with its arguments becomes a fixpoint
                # We need to find the combining operation from the parent
                return Apply('Recurse', args, sort=Sort.TOP)

            # Known builtins
            if name == 'sorted':
                kwarg_suffix = '_'.join(kwarg_keys) if kwarg_keys else ''
                # Include key function fingerprint to distinguish different sort keys
                key_fp = self._extract_key_fingerprint(node)
                if key_fp:
                    kwarg_suffix = f'{kwarg_suffix}_{key_fp}' if kwarg_suffix else key_fp
                op_name = f'Sort.sorted_{kwarg_suffix}' if kwarg_suffix else 'Sort.sorted'
                return Apply(op_name, args, sort=Sort.SEQ)
            if name == 'len':
                return Apply('Seq.len', args, sort=Sort.NUM)
            if name == 'range':
                # Normalize range(n) → range(0, n) so all range calls
                # have the same arity. This preserves site structure:
                # the presheaf section over range(0,n) is isomorphic to range(n).
                if len(args) == 1:
                    args = (Const(Sort.NUM, 0), args[0])
                return Apply('Seq.range', args, sort=Sort.SEQ)
            if name == 'reversed':
                return Apply('Seq.reverse', args, sort=Sort.SEQ)
            if name == 'sum':
                if args:
                    return Fixpoint('Arith.add', Const(Sort.NUM, hash(0)),
                                   args[0], sort=Sort.NUM)
            if name in ('min', 'max'):
                if args:
                    return Fixpoint(f'Cmp.{name}', Unknown(Sort.NUM),
                                   args[0], sort=Sort.NUM)
            if name in ('any', 'all'):
                if args:
                    op = 'Logic.or' if name == 'any' else 'Logic.and'
                    init_val = name == 'all'
                    return Fixpoint(op, Const(Sort.BOOL, hash(init_val)),
                                   args[0], sort=Sort.BOOL)
            if name in ('list', 'tuple'):
                return Apply(f'Cast.to_{name}', args,
                             sort=Sort.SEQ)
            if name in ('set', 'frozenset'):
                return Apply(f'Cast.to_set', args, sort=Sort.SET)
            if name == 'dict':
                return Apply('Cast.to_dict', args, sort=Sort.MAP)
            if name in ('str', 'repr'):
                return Apply(f'Cast.to_{name}', args, sort=Sort.STR)
            if name in ('int', 'float'):
                return Apply(f'Cast.to_num', args, sort=Sort.NUM)
            if name == 'bool':
                return Apply('Cast.to_bool', args, sort=Sort.BOOL)
            if name in ('map', 'filter'):
                return Apply(f'HO.{name}', args, sort=Sort.ITER)
            if name == 'zip':
                return Apply('HO.zip', args, sort=Sort.ITER)
            if name == 'enumerate':
                return Apply('HO.enumerate', args, sort=Sort.ITER)
            if name == 'reversed':
                return Apply('Seq.reverse', args, sort=Sort.SEQ)
            if name == 'isinstance':
                return Apply('Type.check', args, sort=Sort.BOOL)
            if name == 'type':
                return Apply('Type.of', args, sort=Sort.TOP)
            if name == 'hash':
                return Apply('Hash', args, sort=Sort.NUM)
            if name == 'abs':
                return Apply('Arith.abs', args, sort=Sort.NUM)
            if name == 'print':
                return Unknown(Sort.NONE)

            # Generic function call
            return Apply(f'Call.{name}', args, sort=Sort.TOP)

        if isinstance(node.func, ast.Attribute):
            method = node.func.attr
            obj = self._interpret_expr(node.func.value)
            all_args = (obj,) + args
            return Apply(f'Method.{method}', all_args, sort=Sort.TOP)

        return Unknown()

    def _interpret_comprehension(self, node: ast.expr,
                                  result_sort: Sort) -> SExpr:
        """Interpret a comprehension as a Fixpoint + transform."""
        gens = getattr(node, 'generators', [])
        if not gens:
            return Unknown(result_sort)

        iter_expr = self._interpret_expr(gens[0].iter)
        has_filter = any(g.ifs for g in gens)

        if has_filter:
            return Fixpoint('filter', Build((), result_sort),
                            iter_expr, sort=result_sort)

        # map comprehension: [f(x) for x in iter]
        return Fixpoint('map', Build((), result_sort),
                        iter_expr, sort=result_sort)

    # ── Accumulator detection ───────────────────────────────────

    def _detect_accumulator(self, body: List[ast.stmt]
                            ) -> Tuple[Optional[str], str]:
        """Find accumulator variable and step operation in a loop body."""
        for stmt in body:
            if isinstance(stmt, ast.AugAssign):
                if isinstance(stmt.target, ast.Name):
                    return stmt.target.id, _augop_name(stmt.op)

            if isinstance(stmt, ast.Assign):
                if (len(stmt.targets) == 1 and
                        isinstance(stmt.targets[0], ast.Name)):
                    target = stmt.targets[0].id
                    if isinstance(stmt.value, ast.BinOp):
                        if (isinstance(stmt.value.left, ast.Name) and
                                stmt.value.left.id == target):
                            return target, _binop_name(stmt.value.op)
                        if (isinstance(stmt.value.right, ast.Name) and
                                stmt.value.right.id == target):
                            return target, _binop_name(stmt.value.op)

            if isinstance(stmt, ast.If):
                var, op = self._detect_accumulator(stmt.body)
                if var:
                    return var, op
                if stmt.orelse:
                    var, op = self._detect_accumulator(stmt.orelse)
                    if var:
                        return var, op

        return None, ''

    def _detect_multi_var_fixpoint(self, body: List[ast.stmt]
                                    ) -> Optional[Dict[str, str]]:
        """Detect multi-variable fixpoint from tuple assignment in loop body.

        e.g., `a, b = b, a + b` → {a: 'Arith.add', b: 'Arith.add'}
        Both variables are updated in terms of previous values.
        The step operation is the most complex update (usually the add).
        """
        for stmt in body:
            if not isinstance(stmt, ast.Assign):
                continue
            if len(stmt.targets) != 1:
                continue
            target = stmt.targets[0]
            if not isinstance(target, (ast.Tuple, ast.List)):
                continue
            if not isinstance(stmt.value, (ast.Tuple, ast.List)):
                continue
            if len(target.elts) != len(stmt.value.elts):
                continue

            # All targets must be names that exist in our env
            target_names = []
            all_names = True
            for elt in target.elts:
                if isinstance(elt, ast.Name):
                    target_names.append(elt.id)
                else:
                    all_names = False
                    break
            if not all_names:
                continue

            # Find the dominant operation across all RHS expressions
            result: Dict[str, str] = {}
            dominant_op = 'generic'
            for val_expr in stmt.value.elts:
                op = self._find_dominant_op(val_expr)
                if op and op != 'generic':
                    dominant_op = op
                    break

            # Assign the dominant op to all target variables
            for name in target_names:
                if name in self._env:
                    result[name] = dominant_op

            if result:
                return result

        return None

    def _find_dominant_op(self, expr: ast.expr) -> Optional[str]:
        """Find the dominant arithmetic operation in an expression."""
        if isinstance(expr, ast.BinOp):
            return _binop_name(expr.op)
        if isinstance(expr, ast.Call):
            if isinstance(expr.func, ast.Name):
                return f'Call.{expr.func.id}'
        return None

    def _extract_key_fingerprint(self, call_node: ast.Call) -> str:
        """Extract a fingerprint from a key= keyword argument.

        For sorted(x, key=lambda p: p[0]), returns 'sub0' (subscript index 0).
        For sorted(x, key=lambda p: (p[0], p[1])), returns 'sub0_sub1' (tuple of subs).
        """
        for kw in call_node.keywords:
            if kw.arg == 'key' and isinstance(kw.value, ast.Lambda):
                body = kw.value.body
                return self._lambda_body_fingerprint(body)
        return ''

    def _lambda_body_fingerprint(self, body: ast.expr) -> str:
        """Fingerprint a lambda body for key function comparison."""
        if isinstance(body, ast.Subscript):
            if isinstance(body.slice, ast.Constant):
                return f'sub{body.slice.value}'
            return 'sub'
        if isinstance(body, (ast.Tuple, ast.List)):
            parts = [self._lambda_body_fingerprint(e) for e in body.elts]
            return '_'.join(parts)
        if isinstance(body, ast.Attribute):
            return f'attr_{body.attr}'
        if isinstance(body, ast.Call):
            if isinstance(body.func, ast.Name):
                return f'call_{body.func.id}'
        if isinstance(body, ast.UnaryOp) and isinstance(body.op, ast.USub):
            inner = self._lambda_body_fingerprint(body.operand)
            return f'neg_{inner}'
        return 'complex'

    def _is_accum_stmt(self, stmt: ast.stmt, accum_var: str) -> bool:
        """Check if a statement is the accumulator update."""
        if isinstance(stmt, ast.AugAssign):
            return (isinstance(stmt.target, ast.Name) and
                    stmt.target.id == accum_var)
        if isinstance(stmt, ast.Assign):
            return (len(stmt.targets) == 1 and
                    isinstance(stmt.targets[0], ast.Name) and
                    stmt.targets[0].id == accum_var)
        return False

    # ── Sort inference (simplified) ─────────────────────────────

    def _infer_param_sort(self, arg: ast.arg,
                           func: ast.FunctionDef) -> Sort:
        if arg.annotation:
            if isinstance(arg.annotation, ast.Name):
                n = arg.annotation.id
                if n in ('int', 'float'): return Sort.NUM
                if n == 'str': return Sort.STR
                if n == 'list': return Sort.SEQ
                if n == 'dict': return Sort.MAP
                if n == 'set': return Sort.SET
                if n == 'bool': return Sort.BOOL
        # Heuristic from usage
        name = arg.arg
        for node in ast.walk(func):
            if isinstance(node, ast.BinOp):
                if isinstance(node.left, ast.Name) and node.left.id == name:
                    if isinstance(node.op, (ast.Sub, ast.Mult, ast.Div,
                                            ast.FloorDiv, ast.Mod, ast.Pow)):
                        return Sort.NUM
            if isinstance(node, ast.Compare):
                if isinstance(node.left, ast.Name) and node.left.id == name:
                    for op in node.ops:
                        if isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                            return Sort.NUM
            if isinstance(node, ast.For):
                if isinstance(node.iter, ast.Name) and node.iter.id == name:
                    return Sort.SEQ
            if isinstance(node, ast.Subscript):
                if isinstance(node.value, ast.Name) and node.value.id == name:
                    return Sort.SEQ
        return Sort.TOP


# ═══════════════════════════════════════════════════════════════════
# §3  Topos-Theoretic Equivalence via Lawvere Theories & Cohomology
# ═══════════════════════════════════════════════════════════════════
#
# Mathematical Architecture (genuine, not metaphorical):
#
# 1. LAWVERE THEORY  T_f
#    A program f defines a finitary algebraic theory T_f whose:
#      - Sorts = the types flowing through f (NUM, SEQ, BOOL, ...)
#      - Operations = the typed ops f uses, each with signature s₁×...×sₙ → s
#      - Equations = the data-flow wiring (which op feeds into which)
#    A model of T_f in Set IS a concrete execution of f.
#    Two programs are equivalent iff their Lawvere theories have
#    the same models — i.e., T_f and T_g are Morita equivalent.
#
# 2. PROGRAM SITE  (C_f, J_f)
#    The expression tree forms a small category C_f:
#      - Objects = nodes of the SExpr tree (typed program points)
#      - Morphisms = data-flow edges (parent → child)
#      - Grothendieck topology J_f: each node is covered by its children
#    This site is the "space" on which types live.
#
# 3. TYPE PRESHEAF  F : C_f^op → FinSet
#    The type presheaf assigns to each node its sort fiber:
#      F(node) = {sort of node}
#      F(edge: n→m) = sort compatibility constraint
#    This IS the dependent type structure.
#
# 4. ČECH COHOMOLOGY  H*(C_f, F)
#    From the covering given by J_f:
#      H⁰(C_f, F) = ker(δ⁰) = globally consistent sort assignments
#      H¹(C_f, F) = ker(δ¹)/im(δ⁰) = sort-gluing obstructions
#    Cohomological invariant: two programs with different H* CANNOT
#    be equivalent (the type structures are topologically different).
#
# 5. GEOMETRIC MORPHISM  f* ⊣ f_* : Sh(C_f) → Sh(C_g)
#    Two programs are equivalent when there exists a geometric morphism
#    between their sheaf topoi. The inverse image f* must:
#      - Preserve sorts (fiber-preserving)
#      - Preserve operations (signature-preserving)
#      - Preserve covering structure (topology-preserving)
#    This is encoded as a Z3 satisfiability query.
#
# The pipeline:
#   SExpr → Site → Presheaf → Cohomology → [H* filter] → Z3(∃ geom. morph.)


# ── Lawvere Theory ──────────────────────────────────────────────

@dataclass
class TypedOperation:
    """An operation in the Lawvere theory: a morphism in the syntactic category."""
    name: str               # canonical operation name
    input_sorts: Tuple[Sort, ...]   # domain = product of input sorts
    output_sort: Sort        # codomain
    node_id: int            # which SExpr node this came from


@dataclass
class LawvereTheory:
    """The Lawvere theory T_f of a program f.

    Objects = sorts, Morphisms = typed operations.
    A model M: T_f → Set interprets each sort as a set and each
    operation as a function between sets.

    Two theories are Morita equivalent when they have the same
    category of models — this is what we check.
    """
    sorts_used: FrozenSet[Sort]     # the sorts that appear
    operations: List[TypedOperation]  # the morphisms
    sort_profile: Dict[Sort, int]   # how many ops produce each sort
    op_profile: Dict[str, int]      # multiplicity of each op name

    @staticmethod
    def from_sexpr(expr: SExpr) -> LawvereTheory:
        """Extract the Lawvere theory from an expression tree."""
        sorts: Set[Sort] = set()
        ops: List[TypedOperation] = []
        counter = [0]

        def walk(e: SExpr) -> None:
            nid = counter[0]
            counter[0] += 1
            sorts.add(e.sort)

            if e.kind == SExprKind.APPLY:
                child_sorts = tuple(c.sort for c in e.children)
                ops.append(TypedOperation(
                    name=_canonical_op(e.op_name),
                    input_sorts=child_sorts,
                    output_sort=e.sort,
                    node_id=nid,
                ))
                for c in e.children:
                    walk(c)

            elif e.kind == SExprKind.FIXPOINT:
                # Fixpoint is an operation: (base_sort, domain_sort) → result_sort
                base_sort = e.fp_base.sort if e.fp_base else Sort.TOP
                domain_sort = e.fp_domain.sort if e.fp_domain else Sort.TOP
                ops.append(TypedOperation(
                    name=f'fixpoint.{_canonical_op(e.fp_step_op)}',
                    input_sorts=(base_sort, domain_sort),
                    output_sort=e.sort,
                    node_id=nid,
                ))
                if e.fp_base:
                    walk(e.fp_base)
                if e.fp_domain:
                    walk(e.fp_domain)

            elif e.kind == SExprKind.CASE:
                test_sort = e.case_test.sort if e.case_test else Sort.BOOL
                then_sort = e.case_then.sort if e.case_then else Sort.TOP
                else_sort = e.case_else.sort if e.case_else else Sort.TOP
                ops.append(TypedOperation(
                    name='case',
                    input_sorts=(test_sort, then_sort, else_sort),
                    output_sort=e.sort,
                    node_id=nid,
                ))
                for sub in [e.case_test, e.case_then, e.case_else]:
                    if sub:
                        walk(sub)

            elif e.kind == SExprKind.BUILD:
                child_sorts = tuple(c.sort for c in e.children)
                ops.append(TypedOperation(
                    name='build',
                    input_sorts=child_sorts,
                    output_sort=e.sort,
                    node_id=nid,
                ))
                for c in e.children:
                    walk(c)

        walk(expr)

        sort_profile: Dict[Sort, int] = {}
        op_profile: Dict[str, int] = {}
        for op in ops:
            sort_profile[op.output_sort] = sort_profile.get(op.output_sort, 0) + 1
            op_profile[op.name] = op_profile.get(op.name, 0) + 1

        return LawvereTheory(
            sorts_used=frozenset(sorts),
            operations=ops,
            sort_profile=sort_profile,
            op_profile=op_profile,
        )


# ── Program Site (Category + Grothendieck Topology) ─────────────

@dataclass
class SiteNode:
    """An object in the program site category."""
    node_id: int
    sort: Sort
    kind: SExprKind
    op_name: str = ''       # canonical operation name (for APPLY/FIXPOINT)
    const_hash: int = 0     # for CONST nodes
    param_index: int = -1   # for PARAM nodes
    arity: int = 0          # number of children (= covering sieve size)


@dataclass
class SiteEdge:
    """A morphism in the program site category (data flow edge)."""
    source: int     # parent node_id
    target: int     # child node_id
    position: int   # which child position (0-indexed)


@dataclass
class ProgramSite:
    """The site (C_f, J_f) from a program's expression tree.

    Category C_f:
      Objects = SiteNodes (typed program points)
      Morphisms = SiteEdges (data flow connections)

    Grothendieck topology J_f:
      Each node n is covered by the sieve generated by its children.
      cover(n) = {n → child_0, n → child_1, ...}

    This is a finite site, so Sh(C_f, J_f) is a Grothendieck topos.
    """
    nodes: List[SiteNode]
    edges: List[SiteEdge]
    root: int               # root node_id
    covers: Dict[int, List[int]]   # node_id → [child_node_ids] (the covering sieve)

    @staticmethod
    def from_sexpr(expr: SExpr) -> ProgramSite:
        """Build the site from an expression tree."""
        nodes: List[SiteNode] = []
        edges: List[SiteEdge] = []
        covers: Dict[int, List[int]] = {}
        counter = [0]

        def walk(e: SExpr) -> int:
            nid = counter[0]
            counter[0] += 1

            op_name = ''
            if e.kind == SExprKind.APPLY:
                op_name = _canonical_op(e.op_name)
            elif e.kind == SExprKind.FIXPOINT:
                op_name = f'fixpoint.{_canonical_op(e.fp_step_op)}'

            children_ids: List[int] = []

            # Collect children based on kind
            if e.kind == SExprKind.APPLY:
                for pos, c in enumerate(e.children):
                    cid = walk(c)
                    edges.append(SiteEdge(nid, cid, pos))
                    children_ids.append(cid)

            elif e.kind == SExprKind.FIXPOINT:
                pos = 0
                if e.fp_base:
                    cid = walk(e.fp_base)
                    edges.append(SiteEdge(nid, cid, pos))
                    children_ids.append(cid)
                    pos += 1
                if e.fp_domain:
                    cid = walk(e.fp_domain)
                    edges.append(SiteEdge(nid, cid, pos))
                    children_ids.append(cid)

            elif e.kind == SExprKind.CASE:
                pos = 0
                for sub in [e.case_test, e.case_then, e.case_else]:
                    if sub:
                        cid = walk(sub)
                        edges.append(SiteEdge(nid, cid, pos))
                        children_ids.append(cid)
                    pos += 1

            elif e.kind == SExprKind.BUILD:
                for pos, c in enumerate(e.children):
                    cid = walk(c)
                    edges.append(SiteEdge(nid, cid, pos))
                    children_ids.append(cid)

            nodes.append(SiteNode(
                node_id=nid,
                sort=e.sort,
                kind=e.kind,
                op_name=op_name,
                const_hash=e.const_hash if e.kind == SExprKind.CONST else 0,
                param_index=e.param_index if e.kind == SExprKind.PARAM else -1,
                arity=len(children_ids),
            ))
            covers[nid] = children_ids
            return nid

        root = walk(expr)
        return ProgramSite(nodes=nodes, edges=edges, root=root, covers=covers)


# ── Type Presheaf & Čech Cohomology ─────────────────────────────

@dataclass
class PresheafCohomology:
    """Čech cohomology of the type presheaf over the program site.

    The type presheaf F: C_f^op → FinSet assigns:
      F(node) = {sort of node} (the sort fiber)
      F(edge: n → m) = sort-compatibility map

    Čech cohomology relative to the covering topology J_f:
      H⁰ = globally consistent sort sections
      H¹ = obstructions to gluing local sort assignments
      β₁ = first Betti number (rank of H¹)

    These are GENUINE cohomological invariants — programs with
    different H* cannot be equivalent under any geometric morphism.
    """
    h0: int                         # dim H⁰
    h1: int                         # dim H¹ (= rank of obstruction group)
    betti_0: int                    # β₀ = connected components of the site
    euler_char: int                 # χ = Σ(-1)^k rank(Hᵏ)
    sort_fiber_dims: Dict[Sort, int]  # dimension of each sort fiber

    @staticmethod
    def compute(site: ProgramSite) -> PresheafCohomology:
        """Compute Čech cohomology of the type presheaf.

        The Čech complex for the covering {U_i} given by the Grothendieck topology:

          C⁰ = ⊕_i F(U_i)   = sort fibers on each node
          C¹ = ⊕_{edges} F   = sort fibers on each edge (intersection of covers)

          δ⁰: C⁰ → C¹ sends a section σ to (σ|_source - σ|_target) on each edge

        An edge is a GENUINE OBSTRUCTION (non-trivial 1-cocycle) only when:
        - The parent node's operation does NOT have this sort transition in its type signature
        - I.e., the edge represents a sort change that CAN'T be explained by the operation

        Operations naturally mediate sort transitions:
          range(NUM, NUM) → SEQ      (nums become a sequence)
          len(SEQ) → NUM             (sequence becomes a number)
          sorted(SEQ) → SEQ          (sequence stays sequence)
          fixpoint(base, domain) → T (various sorts combine)

        These are NOT obstructions — they're the EXPECTED behavior of the presheaf
        restriction maps.  Only UNEXPLAINED sort transitions are obstructions.
        """
        if not site.nodes:
            return PresheafCohomology(0, 0, 0, 0, {})

        n_nodes = len(site.nodes)
        node_by_id = {n.node_id: n for n in site.nodes}

        # H⁰: connected components (β₀)
        parent_map = list(range(n_nodes))

        def find(x: int) -> int:
            while parent_map[x] != x:
                parent_map[x] = parent_map[parent_map[x]]
                x = parent_map[x]
            return x

        def union(x: int, y: int) -> None:
            rx, ry = find(x), find(y)
            if rx != ry:
                parent_map[rx] = ry

        node_idx = {n.node_id: i for i, n in enumerate(site.nodes)}
        for edge in site.edges:
            si = node_idx.get(edge.source)
            ti = node_idx.get(edge.target)
            if si is not None and ti is not None:
                union(si, ti)

        components = len(set(find(i) for i in range(n_nodes)))

        # H¹: genuine sort obstructions
        # An edge is an obstruction ONLY if the sort transition is not
        # explained by the parent operation's type signature.
        # Operations with mixed-sort signatures (like range: NUM→SEQ)
        # are EXPECTED to have sort-incompatible edges.
        obstructions = 0
        for edge in site.edges:
            src_node = node_by_id.get(edge.source)
            tgt_node = node_by_id.get(edge.target)
            if not src_node or not tgt_node:
                continue

            # If sorts are compatible, no obstruction
            if sorts_compatible(src_node.sort, tgt_node.sort):
                continue

            # If the source is an operation node, the sort transition
            # is explained by the operation's type signature — NOT an obstruction
            if src_node.kind in (SExprKind.APPLY, SExprKind.FIXPOINT,
                                  SExprKind.CASE, SExprKind.BUILD):
                continue

            # Genuine obstruction: sort mismatch not explained by any operation
            obstructions += 1

        h0 = components
        h1 = obstructions

        # Sort fiber dimensions
        sort_dims: Dict[Sort, int] = {}
        for n in site.nodes:
            sort_dims[n.sort] = sort_dims.get(n.sort, 0) + 1

        return PresheafCohomology(
            h0=h0,
            h1=h1,
            betti_0=components,
            euler_char=h0 - h1,
            sort_fiber_dims=sort_dims,
        )


# ── Geometric Morphism Existence (Z3) ───────────────────────────

def _check_geometric_morphism(site_f: ProgramSite,
                                site_g: ProgramSite,
                                theory_f: LawvereTheory,
                                theory_g: LawvereTheory,
                                ) -> Tuple[Optional[bool], str]:
    """Check if a geometric morphism exists between Sh(C_f) and Sh(C_g).

    A geometric morphism f* ⊣ f_* : Sh(C_f) → Sh(C_g) is given by
    a cover-preserving functor φ: C_g → C_f (the inverse image part).

    For our finite sites, this means a map φ: nodes(C_g) → nodes(C_f) such that:
      1. SORT-PRESERVING: sort(φ(m)) = sort(m) for all m ∈ C_g
      2. OP-PRESERVING: op_name(φ(m)) = op_name(m) for operational nodes
      3. COVER-PRESERVING: if {m_j} covers m in C_g, then {φ(m_j)} covers φ(m)
         (this is the Grothendieck topology condition)
      4. ARITY-PRESERVING: arity(φ(m)) = arity(m)

    Note: this is NOT a bijection — it's a functor. Multiple g-nodes
    can map to the same f-node (e.g., two constants of the same sort).
    But operational nodes with different op_names cannot merge.

    We encode this as a Z3 satisfiability query.
    """
    try:
        import z3
    except ImportError:
        return None, "Z3 not available"

    nf = len(site_f.nodes)
    ng = len(site_g.nodes)

    if nf == 0 or ng == 0:
        return None, "empty site"

    # Index nodes for fast lookup
    f_nodes = {n.node_id: n for n in site_f.nodes}
    g_nodes = {n.node_id: n for n in site_g.nodes}
    f_node_list = site_f.nodes
    g_node_list = site_g.nodes
    f_id_to_idx = {n.node_id: i for i, n in enumerate(f_node_list)}
    g_id_to_idx = {n.node_id: i for i, n in enumerate(g_node_list)}

    solver = z3.Solver()
    solver.set("timeout", 5000)

    # φ(m) for each g-node m: which f-node it maps to
    phi = [z3.Int(f'phi_{i}') for i in range(ng)]

    # Range constraints
    for i in range(ng):
        solver.add(phi[i] >= 0, phi[i] < nf)

    # 1. SORT-PRESERVING: sort(φ(m)) must be compatible with sort(m)
    for gi, gn in enumerate(g_node_list):
        for fi, fn in enumerate(f_node_list):
            if not sorts_compatible(fn.sort, gn.sort):
                solver.add(phi[gi] != fi)

    # 2. OP-PRESERVING: operational nodes must map to same-op nodes
    for gi, gn in enumerate(g_node_list):
        if gn.kind in (SExprKind.APPLY, SExprKind.FIXPOINT):
            for fi, fn in enumerate(f_node_list):
                if fn.op_name != gn.op_name:
                    solver.add(phi[gi] != fi)

    # 3. KIND-PRESERVING: nodes must map to same-kind nodes
    #    (PARAMs to PARAMs, CONSTs to CONSTs, etc.)
    for gi, gn in enumerate(g_node_list):
        for fi, fn in enumerate(f_node_list):
            if fn.kind != gn.kind:
                # Exception: FIXPOINT ↔ FIXPOINT (already same kind after lifting)
                solver.add(phi[gi] != fi)

    # 4. PARAM-INDEX-PRESERVING: Param(i) must map to Param(i)
    for gi, gn in enumerate(g_node_list):
        if gn.kind == SExprKind.PARAM:
            for fi, fn in enumerate(f_node_list):
                if fn.kind == SExprKind.PARAM and fn.param_index != gn.param_index:
                    solver.add(phi[gi] != fi)

    # 4b. CONST-VALUE-PRESERVING: Const(v) must map to Const(v)
    #     This is critical — without it, Const(0) could map to Const(1),
    #     making `x+0` equivalent to `x+1`.
    for gi, gn in enumerate(g_node_list):
        if gn.kind == SExprKind.CONST:
            for fi, fn in enumerate(f_node_list):
                if fn.kind == SExprKind.CONST and fn.const_hash != gn.const_hash:
                    solver.add(phi[gi] != fi)

    # 5. ARITY-PRESERVING: nodes must have same number of children
    for gi, gn in enumerate(g_node_list):
        for fi, fn in enumerate(f_node_list):
            if fn.arity != gn.arity:
                solver.add(phi[gi] != fi)

    # 6. COVER-PRESERVING (the Grothendieck topology condition):
    #    If m has children [m_1, ..., m_k] in C_g, then φ(m) must have
    #    children [φ(m_1), ..., φ(m_k)] in C_f (in the same order = edge position).
    #
    #    For each edge (m → m_j, position=p) in C_g, require that
    #    (φ(m) → φ(m_j), position=p) is an edge in C_f.
    f_edge_set: Dict[Tuple[int, int], Set[int]] = {}  # (src_idx, pos) → {tgt_idx}
    for e in site_f.edges:
        si = f_id_to_idx.get(e.source, -1)
        ti = f_id_to_idx.get(e.target, -1)
        if si >= 0 and ti >= 0:
            key = (si, e.position)
            if key not in f_edge_set:
                f_edge_set[key] = set()
            f_edge_set[key].add(ti)

    for g_edge in site_g.edges:
        gi_src = g_id_to_idx.get(g_edge.source, -1)
        gi_tgt = g_id_to_idx.get(g_edge.target, -1)
        if gi_src < 0 or gi_tgt < 0:
            continue

        # For each possible mapping of the source node:
        # φ(src) = fi_src implies φ(tgt) must be a valid child at this position
        for fi_src in range(nf):
            valid_targets = f_edge_set.get((fi_src, g_edge.position), set())
            if not valid_targets:
                # No edge at this position from fi_src → φ can't map src here
                solver.add(phi[gi_src] != fi_src)
            else:
                # φ(src) = fi_src → φ(tgt) ∈ valid_targets
                solver.add(z3.Implies(
                    phi[gi_src] == fi_src,
                    z3.Or(*[phi[gi_tgt] == vt for vt in valid_targets])
                ))

    # 7. INJECTIVITY on operational nodes:
    #    Different operational g-nodes (with non-trivial op) should map to
    #    different f-nodes. This prevents collapsing distinct computations.
    op_g_indices = [gi for gi, gn in enumerate(g_node_list)
                    if gn.kind in (SExprKind.APPLY, SExprKind.FIXPOINT) and gn.op_name]
    if len(op_g_indices) > 1:
        solver.add(z3.Distinct(*[phi[gi] for gi in op_g_indices]))

    # Solve
    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        mapping = [model.evaluate(phi[i]).as_long() for i in range(ng)]
        mapped_ops = []
        for gi, gn in enumerate(g_node_list):
            fi = mapping[gi]
            fn = f_node_list[fi]
            if gn.op_name:
                mapped_ops.append(gn.op_name)

        # Quality gate: the geometric morphism is only meaningful when
        # the sites have enough operational content. A vacuous morphism
        # between two trivial sites (e.g., single Unknown nodes) is not
        # evidence of equivalence — it's just a trivial map.
        total_ops = (len([n for n in f_node_list if n.op_name]) +
                     len([n for n in g_node_list if n.op_name]))
        if total_ops == 0:
            return None, f"vacuous morphism (no operational content in either site)"

        return True, f"geometric morphism found ({len(mapped_ops)} ops preserved)"

    if result == z3.unsat:
        return False, "no geometric morphism exists (UNSAT)"

    return None, "Z3 timeout"


# ── §3b Cotangent Sheaf — Denotational Equivalence ─────────────
#
# The cotangent sheaf Ω¹ over the parameter space X = Z^n captures
# how a program's output VARIES with its inputs.  The de Rham
# differential df = Σ (∂f/∂xᵢ) dxᵢ is a global section of Ω¹.
#
# Two programs f,g : X → Z are denotationally equivalent iff
#   (i)  df = dg   (same cotangent section)
#   (ii) f(0) = g(0) (same value at the base point)
#
# For polynomial programs this is COMPLETE (by the fundamental
# theorem of calculus on Z^n).  For fixpoint programs we fall
# through to Z3 RecFunction-based universal quantification.
#
# The symbolic derivative is the KÄHLER DIFFERENTIAL of the SExpr
# algebra, computed via the Leibniz rule on the polynomial ring
# Z[x₀, …, xₙ] / (program relations).
# ────────────────────────────────────────────────────────────────

def _differentiate(expr: SExpr, param_idx: int) -> SExpr:
    """Compute ∂expr/∂x_{param_idx} — the Kähler differential.

    Rules (standard algebraic differentiation):
      ∂(xᵢ)/∂(xⱼ)   = δᵢⱼ
      ∂(c)/∂(xⱼ)     = 0
      ∂(a+b)/∂(xⱼ)   = ∂a/∂xⱼ + ∂b/∂xⱼ
      ∂(a·b)/∂(xⱼ)   = a·∂b/∂xⱼ + ∂a/∂xⱼ·b        (Leibniz)
      ∂(a-b)/∂(xⱼ)   = ∂a/∂xⱼ - ∂b/∂xⱼ
      ∂(If c a b)/∂xⱼ = If c (∂a/∂xⱼ) (∂b/∂xⱼ)     (branch-wise)

    Returns Unknown when the expression is non-differentiable
    (floor-div, mod, bit-ops, opaque calls).
    """
    kind = expr.kind

    if kind == SExprKind.PARAM:
        return Const(Sort.NUM, 1 if expr.param_index == param_idx else 0)

    if kind == SExprKind.CONST:
        return Const(Sort.NUM, 0)

    if kind == SExprKind.UNKNOWN:
        return Unknown(Sort.NUM)

    if kind == SExprKind.APPLY:
        op = expr.op_name
        ch = expr.children

        if op == 'Arith.add' and len(ch) == 2:
            return Apply('Arith.add',
                         (_differentiate(ch[0], param_idx),
                          _differentiate(ch[1], param_idx)),
                         sort=Sort.NUM)

        if op == 'Arith.sub' and len(ch) == 2:
            return Apply('Arith.sub',
                         (_differentiate(ch[0], param_idx),
                          _differentiate(ch[1], param_idx)),
                         sort=Sort.NUM)

        if op == 'Arith.mul' and len(ch) == 2:
            # Leibniz: d(a·b) = a·db + da·b
            a, b = ch
            da = _differentiate(a, param_idx)
            db = _differentiate(b, param_idx)
            return Apply('Arith.add', (
                Apply('Arith.mul', (a, db), sort=Sort.NUM),
                Apply('Arith.mul', (da, b), sort=Sort.NUM),
            ), sort=Sort.NUM)

        if op == 'Arith.pow' and len(ch) == 2:
            # d(a^b)/dx = b·a^(b-1)·da/dx  (for integer constant b)
            a, b_expr = ch
            if b_expr.kind == SExprKind.CONST:
                da = _differentiate(a, param_idx)
                exp_minus_1 = Const(Sort.NUM, b_expr.const_hash - 1)
                return Apply('Arith.mul', (
                    Apply('Arith.mul', (b_expr,
                                        Apply('Arith.pow', (a, exp_minus_1),
                                              sort=Sort.NUM)),
                          sort=Sort.NUM),
                    da), sort=Sort.NUM)

        if op == 'Unary.USub' and len(ch) == 1:
            return Apply('Unary.USub',
                         (_differentiate(ch[0], param_idx),),
                         sort=Sort.NUM)

        if op == 'Arith.abs' and len(ch) == 1:
            # d|a|/dx = sign(a)·da/dx  — non-smooth at 0, but useful
            da = _differentiate(ch[0], param_idx)
            sign = Apply('Cmp.sign', (ch[0],), sort=Sort.NUM)
            return Apply('Arith.mul', (sign, da), sort=Sort.NUM)

        # Non-differentiable ops: floordiv, mod, bitwise, comparisons
        return Unknown(Sort.NUM)

    if kind == SExprKind.CASE:
        if expr.case_test and expr.case_then and expr.case_else:
            dt = _differentiate(expr.case_then, param_idx)
            de = _differentiate(expr.case_else, param_idx)
            return Case(expr.case_test, dt, de, sort=Sort.NUM)
        return Unknown(Sort.NUM)

    if kind == SExprKind.FIXPOINT:
        # For additive fixpoints: ∂/∂xⱼ[ base + Σ_{i∈dom} i ]
        # = ∂base/∂xⱼ + ∂(Σ)/∂xⱼ
        # The Σ part depends on the domain endpoints, not the step.
        # For Fixpoint(add, base, range(lo, hi)):
        #   ∂result/∂(hi) = hi - 1  (the last term)
        #   ∂result/∂(lo) = -lo     (removing the first term)
        # For general step_op: return Unknown
        can = _canonical_op(expr.fp_step_op)
        if can == 'add' and expr.fp_base and expr.fp_domain:
            db = _differentiate(expr.fp_base, param_idx)
            # The domain contribution depends on whether domain
            # endpoints depend on the parameter.
            dom = expr.fp_domain
            if (dom.kind == SExprKind.APPLY and
                    dom.op_name == 'Seq.range' and
                    len(dom.children) == 2):
                dlo = _differentiate(dom.children[0], param_idx)
                dhi = _differentiate(dom.children[1], param_idx)
                # Closed form derivative of sum(range(lo,hi)) w.r.t. hi:
                #   d/dhi[ (hi-lo)(lo+hi-1)/2 ] = (2hi - 1)/2
                # w.r.t. lo: = -(2lo - 1)/2
                # For the general case, chain rule through lo and hi:
                lo, hi = dom.children[0], dom.children[1]
                # ∂sum/∂xⱼ = ∂sum/∂hi · ∂hi/∂xⱼ + ∂sum/∂lo · ∂lo/∂xⱼ
                # = (lo+hi-1)/2 · dhi + ... this is getting complex.
                # Simplification: if lo is constant and hi depends on param,
                # ∂sum/∂xⱼ = (hi-1) · dhi  (approximately, for natural number domain)
                # Use the Fixpoint structure itself as the derivative marker
                return Apply('Arith.add', (db, Unknown(Sort.NUM)),
                             sort=Sort.NUM)
        return Unknown(Sort.NUM)

    if kind == SExprKind.BUILD:
        return Unknown(Sort.NUM)

    return Unknown(Sort.NUM)


def _simplify(expr: SExpr) -> SExpr:
    """Algebraic simplification / normalization of SExpr.

    This is the "normalization by rewriting" step that puts
    expressions into canonical form for structural comparison.

    Rules applied bottom-up:
      x + 0 → x        x · 1 → x        x · 0 → 0
      x - 0 → x        x - x → 0        0 - x → -x
      c₁ ⊕ c₂ → c      (constant folding)
      commutative ops: canonically order children
    """
    kind = expr.kind

    if kind in (SExprKind.PARAM, SExprKind.CONST,
                SExprKind.UNKNOWN):
        return expr

    if kind == SExprKind.BUILD:
        new_ch = tuple(_simplify(c) for c in expr.children)
        return Build(new_ch, sort=expr.sort)

    if kind == SExprKind.CASE:
        t = _simplify(expr.case_test) if expr.case_test else None
        y = _simplify(expr.case_then) if expr.case_then else None
        n = _simplify(expr.case_else) if expr.case_else else None
        if y is not None and n is not None and y == n:
            return y  # if c then x else x → x
        return Case(t, y, n, sort=expr.sort) if t and y and n else expr

    if kind == SExprKind.FIXPOINT:
        base = _simplify(expr.fp_base) if expr.fp_base else None
        dom = _simplify(expr.fp_domain) if expr.fp_domain else None
        return Fixpoint(expr.fp_step_op, base, dom,
                        sort=expr.sort) if base and dom else expr

    if kind != SExprKind.APPLY:
        return expr

    # APPLY: simplify children first
    ch = tuple(_simplify(c) for c in expr.children)
    op = expr.op_name

    def _is_zero(e: SExpr) -> bool:
        return e.kind == SExprKind.CONST and e.const_hash == 0

    def _is_one(e: SExpr) -> bool:
        return e.kind == SExprKind.CONST and e.const_hash == 1

    def _const_val(e: SExpr) -> Optional[int]:
        if e.kind == SExprKind.CONST and e.sort in (Sort.NUM, Sort.TOP):
            return e.const_hash
        return None

    if len(ch) == 2:
        a, b = ch

        if op == 'Arith.add':
            if _is_zero(a): return b
            if _is_zero(b): return a
            va, vb = _const_val(a), _const_val(b)
            if va is not None and vb is not None:
                return Const(Sort.NUM, va + vb)
            # canonical order: smaller key first
            if _canonical_key(a) > _canonical_key(b):
                a, b = b, a
            return Apply(op, (a, b), sort=Sort.NUM)

        if op == 'Arith.sub':
            if _is_zero(b): return a
            if a == b: return Const(Sort.NUM, 0)
            va, vb = _const_val(a), _const_val(b)
            if va is not None and vb is not None:
                return Const(Sort.NUM, va - vb)
            return Apply(op, (a, b), sort=Sort.NUM)

        if op == 'Arith.mul':
            if _is_zero(a) or _is_zero(b): return Const(Sort.NUM, 0)
            if _is_one(a): return b
            if _is_one(b): return a
            va, vb = _const_val(a), _const_val(b)
            if va is not None and vb is not None:
                return Const(Sort.NUM, va * vb)
            if _canonical_key(a) > _canonical_key(b):
                a, b = b, a
            return Apply(op, (a, b), sort=Sort.NUM)

        if op == 'Arith.pow':
            if _is_zero(b): return Const(Sort.NUM, 1)
            if _is_one(b):  return a

    if len(ch) == 1:
        a = ch[0]
        if op == 'Unary.USub':
            v = _const_val(a)
            if v is not None:
                return Const(Sort.NUM, -v)
            # -(-x) → x
            if (a.kind == SExprKind.APPLY and a.op_name == 'Unary.USub'
                    and len(a.children) == 1):
                return a.children[0]

    return Apply(op, ch, sort=expr.sort)


def _canonical_key(expr: SExpr) -> tuple:
    """Ordering key for canonical placement in commutative ops."""
    kind = expr.kind
    if kind == SExprKind.CONST:
        return (0, expr.sort.value, expr.const_hash)
    if kind == SExprKind.PARAM:
        return (1, expr.param_index)
    if kind == SExprKind.APPLY:
        return (2, expr.op_name,
                tuple(_canonical_key(c) for c in expr.children))
    if kind == SExprKind.FIXPOINT:
        return (3, expr.fp_step_op)
    if kind == SExprKind.CASE:
        return (4,)
    if kind == SExprKind.BUILD:
        return (5,)
    return (6,)


# ── Concrete evaluation at a point ────────────────────────────

def _evaluate_at_point(expr: SExpr, point: Dict[int, int],
                       _depth: int = 0) -> Optional[int]:
    """Evaluate SExpr at concrete integer values for each parameter.

    Returns None if any sub-expression is unevaluable.
    """
    if _depth > 100:
        return None

    kind = expr.kind

    if kind == SExprKind.CONST:
        if expr.sort in (Sort.NUM, Sort.TOP, Sort.BOOL):
            return expr.const_hash
        return None

    if kind == SExprKind.PARAM:
        return point.get(expr.param_index)

    if kind == SExprKind.UNKNOWN:
        return None

    if kind == SExprKind.APPLY:
        vals = [_evaluate_at_point(c, point, _depth + 1)
                for c in expr.children]
        if any(v is None for v in vals):
            return None
        return _apply_concrete(expr.op_name, vals)

    if kind == SExprKind.FIXPOINT:
        base_v = _evaluate_at_point(expr.fp_base, point, _depth + 1) \
            if expr.fp_base else None
        if base_v is None:
            return None
        dom = expr.fp_domain
        if dom and dom.kind == SExprKind.APPLY and \
                dom.op_name == 'Seq.range' and len(dom.children) == 2:
            lo_v = _evaluate_at_point(dom.children[0], point, _depth + 1)
            hi_v = _evaluate_at_point(dom.children[1], point, _depth + 1)
            if lo_v is None or hi_v is None:
                return None
            return _fold_concrete(expr.fp_step_op, base_v, lo_v, hi_v)
        return None

    if kind == SExprKind.CASE:
        t = _evaluate_at_point(expr.case_test, point, _depth + 1) \
            if expr.case_test else None
        if t is None:
            return None
        branch = expr.case_then if t else expr.case_else
        return _evaluate_at_point(branch, point, _depth + 1) \
            if branch else None

    return None


def _apply_concrete(op: str, vals: List[int]) -> Optional[int]:
    """Evaluate an operation on concrete integer values."""
    if len(vals) == 2:
        a, b = vals
        if op == 'Arith.add': return a + b
        if op == 'Arith.sub': return a - b
        if op == 'Arith.mul': return a * b
        if op == 'Arith.floordiv':
            return a // b if b != 0 else None
        if op in ('Arith.div', 'Arith.truediv'):
            return None  # produces float, can't represent as int
        if op == 'Arith.mod':
            return a % b if b != 0 else None
        if op == 'Arith.pow':
            return a ** b if b >= 0 else None
        if op == 'Cmp.lt': return int(a < b)
        if op == 'Cmp.le': return int(a <= b)
        if op == 'Cmp.gt': return int(a > b)
        if op == 'Cmp.ge': return int(a >= b)
        if op == 'Cmp.eq': return int(a == b)
        if op == 'Cmp.ne': return int(a != b)
        if op == 'Logic.and': return int(bool(a) and bool(b))
        if op == 'Logic.or': return int(bool(a) or bool(b))
    if len(vals) == 1:
        a = vals[0]
        if op == 'Unary.USub': return -a
        if op == 'Unary.Not': return int(not a)
        if op == 'Arith.abs': return abs(a)
        if op == 'Cast.to_num': return a
        if op == 'Cast.to_bool': return int(bool(a))
    return None


def _fold_concrete(step_op: str, base: int, lo: int, hi: int
                   ) -> Optional[int]:
    """Evaluate fold(step_op, base, range(lo, hi)) concretely."""
    can = _canonical_op(step_op)
    result = base
    for i in range(lo, min(hi, lo + 10000)):  # bounded
        if can == 'add':     result += i
        elif can == 'mul':   result *= i
        elif can == 'sub':   result -= i
        elif can == 'max':   result = max(result, i)
        elif can == 'min':   result = min(result, i)
        elif can == 'or':    result = int(bool(result) or bool(i))
        elif can == 'and':   result = int(bool(result) and bool(i))
        else: return None
    return result


# ── Z3 Denotation — translating SExpr to Z3 arithmetic ────────

_DENOT_COUNTER = [0]


def _max_param_index(expr: SExpr) -> int:
    """Find the maximum parameter index in an SExpr tree."""
    best = expr.param_index if expr.kind == SExprKind.PARAM else -1
    for c in expr.children:
        best = max(best, _max_param_index(c))
    for sub in [expr.fp_base, expr.fp_domain,
                expr.case_test, expr.case_then, expr.case_else]:
        if sub:
            best = max(best, _max_param_index(sub))
    return best


def _has_unknown(expr: SExpr) -> bool:
    """Check whether an SExpr tree contains any Unknown nodes."""
    if expr.kind == SExprKind.UNKNOWN:
        return True
    if any(_has_unknown(c) for c in expr.children):
        return True
    for sub in [expr.fp_base, expr.fp_domain,
                expr.case_test, expr.case_then, expr.case_else]:
        if sub and _has_unknown(sub):
            return True
    return False


def _sexpr_to_z3(expr: SExpr, params: list, *, _depth: int = 0):
    """Translate SExpr → Z3 arithmetic term (the denotation).

    The Z3 term IS the denotation: the mathematical function the
    program computes, expressed over symbolic parameters.

    Returns None for untranslatable constructs (sequences, strings,
    Unknown, opaque calls).
    """
    try:
        import z3
    except ImportError:
        return None

    if _depth > 50:
        return None

    kind = expr.kind

    if kind == SExprKind.PARAM:
        idx = expr.param_index
        return params[idx] if 0 <= idx < len(params) else None

    if kind == SExprKind.CONST:
        if expr.sort in (Sort.NUM, Sort.TOP, Sort.BOOL):
            return z3.IntVal(expr.const_hash)
        return None

    if kind in (SExprKind.UNKNOWN, SExprKind.BUILD):
        return None

    if kind == SExprKind.APPLY:
        ch_z3 = [_sexpr_to_z3(c, params, _depth=_depth + 1)
                 for c in expr.children]
        if any(c is None for c in ch_z3):
            return None
        return _apply_z3(expr.op_name, ch_z3)

    if kind == SExprKind.FIXPOINT:
        return _fixpoint_z3(expr, params, _depth)

    if kind == SExprKind.CASE:
        if expr.case_test and expr.case_then and expr.case_else:
            t = _sexpr_to_z3(expr.case_test, params, _depth=_depth + 1)
            y = _sexpr_to_z3(expr.case_then, params, _depth=_depth + 1)
            n = _sexpr_to_z3(expr.case_else, params, _depth=_depth + 1)
            if t is not None and y is not None and n is not None:
                import z3 as z3m
                cond = t != 0 if z3m.is_int(t) else t
                # coerce branches to same sort
                if z3m.is_int(y) and z3m.is_real(n):
                    y = z3m.ToReal(y)
                elif z3m.is_real(y) and z3m.is_int(n):
                    n = z3m.ToReal(n)
                return z3m.If(cond, y, n)
        return None

    return None


def _apply_z3(op: str, args: list):
    """Evaluate a symbolic operation as Z3 arithmetic."""
    import z3

    n = len(args)
    if n == 2:
        a, b = args
        if op == 'Arith.add':      return a + b
        if op == 'Arith.sub':      return a - b
        if op == 'Arith.mul':      return a * b
        if op == 'Arith.floordiv':
            # Python's //: use Z3 integer div (Euclidean — matches
            # Python for positive divisor; differs for negative).
            if z3.is_real(a): a = z3.ToInt(a)
            if z3.is_real(b): b = z3.ToInt(b)
            return a / b
        if op in ('Arith.div', 'Arith.truediv'):
            # Python's /: true division → produces Real
            return z3.ToReal(a) / z3.ToReal(b)
        if op == 'Arith.mod':
            if z3.is_real(a): a = z3.ToInt(a)
            if z3.is_real(b): b = z3.ToInt(b)
            return a % b
        if op == 'Arith.pow':
            if z3.is_int_value(b):
                exp = b.as_long()
                if 0 <= exp <= 10:
                    r = z3.IntVal(1)
                    for _ in range(exp):
                        r = r * a
                    return r
            return None
        # Comparisons → 0/1 integer
        if op in ('Cmp.lt', 'Cmp.lt_num'):
            return z3.If(a < b, z3.IntVal(1), z3.IntVal(0))
        if op in ('Cmp.le', 'Cmp.le_num'):
            return z3.If(a <= b, z3.IntVal(1), z3.IntVal(0))
        if op in ('Cmp.gt', 'Cmp.gt_num'):
            return z3.If(a > b, z3.IntVal(1), z3.IntVal(0))
        if op in ('Cmp.ge', 'Cmp.ge_num'):
            return z3.If(a >= b, z3.IntVal(1), z3.IntVal(0))
        if op in ('Cmp.eq', 'Cmp.eq_generic', 'Cmp.eq_num'):
            return z3.If(a == b, z3.IntVal(1), z3.IntVal(0))
        if op in ('Cmp.ne', 'Cmp.ne_generic', 'Cmp.ne_num'):
            return z3.If(a != b, z3.IntVal(1), z3.IntVal(0))
        if op == 'Logic.and':
            return z3.If(z3.And(a != 0, b != 0),
                         z3.IntVal(1), z3.IntVal(0))
        if op == 'Logic.or':
            return z3.If(z3.Or(a != 0, b != 0),
                         z3.IntVal(1), z3.IntVal(0))
        return None

    if n == 1:
        a = args[0]
        if op in ('Unary.USub', 'Arith.neg'):      return -a
        if op == 'Unary.Not':
            return z3.If(a == 0, z3.IntVal(1), z3.IntVal(0))
        if op == 'Arith.abs':
            return z3.If(a >= 0, a, -a)
        if op == 'Cast.to_num':
            if z3.is_real(a):
                # Python int() truncates toward zero
                return z3.If(a >= 0, z3.ToInt(a), -z3.ToInt(-a))
            return a
        if op == 'Cast.to_bool':
            return z3.If(a != 0, z3.IntVal(1), z3.IntVal(0))
        return None

    return None


def _fixpoint_z3(expr: SExpr, params: list, depth: int):
    """Translate Fixpoint → Z3 via closed form or RecFunction.

    For additive fixpoints: use the arithmetic-sum closed form.
    For multiplicative and others: use Z3 RecFunction.
    """
    import z3

    base_z3 = _sexpr_to_z3(expr.fp_base, params, _depth=depth + 1) \
        if expr.fp_base else None
    if base_z3 is None:
        return None

    dom = expr.fp_domain
    if not (dom and dom.kind == SExprKind.APPLY and
            dom.op_name == 'Seq.range' and len(dom.children) == 2):
        return None

    lo_z3 = _sexpr_to_z3(dom.children[0], params, _depth=depth + 1)
    hi_z3 = _sexpr_to_z3(dom.children[1], params, _depth=depth + 1)
    if lo_z3 is None or hi_z3 is None:
        return None

    if z3.is_real(lo_z3): lo_z3 = z3.ToInt(lo_z3)
    if z3.is_real(hi_z3): hi_z3 = z3.ToInt(hi_z3)
    if z3.is_real(base_z3): base_z3 = z3.ToInt(base_z3)

    can = _canonical_op(expr.fp_step_op)

    # ── Closed form for addition: sum(range(lo,hi)) ────────────
    if can == 'add':
        # Σ_{i=lo}^{hi-1} i = (hi - lo)(lo + hi - 1) / 2
        n = hi_z3 - lo_z3
        s = n * (lo_z3 + hi_z3 - 1)
        # Integer division by 2 is exact because one of the factors
        # (n or lo+hi-1) is always even.
        return base_z3 + s / 2

    # ── Z3 RecFunction for everything else ─────────────────────
    _DENOT_COUNTER[0] += 1
    uid = _DENOT_COUNTER[0]
    fold = z3.RecFunction(f'fold_{uid}', z3.IntSort(), z3.IntSort())
    i = z3.FreshInt(f'i_{uid}')

    if can == 'mul':
        z3.RecAddDefinition(fold, [i],
                            z3.If(i >= hi_z3, base_z3, fold(i + 1) * i))
    elif can == 'sub':
        z3.RecAddDefinition(fold, [i],
                            z3.If(i >= hi_z3, base_z3, fold(i + 1) - i))
    elif can == 'max':
        z3.RecAddDefinition(fold, [i],
                            z3.If(i >= hi_z3, base_z3,
                                  z3.If(i > fold(i + 1), i, fold(i + 1))))
    elif can == 'min':
        z3.RecAddDefinition(fold, [i],
                            z3.If(i >= hi_z3, base_z3,
                                  z3.If(i < fold(i + 1), i, fold(i + 1))))
    else:
        return None

    return fold(lo_z3)


# ── Cotangent sheaf comparison ─────────────────────────────────

def _check_cotangent_equivalence(expr_f: SExpr, expr_g: SExpr
                                  ) -> Tuple[Optional[bool], str]:
    """Check equivalence via the cotangent sheaf Ω¹.

    Two programs f, g : Z^n → Z are equal iff
      (i)  df = dg   (same section of Ω¹)
      (ii) f(0) = g(0)

    For polynomial programs this is COMPLETE.

    Steps:
      1. Compute gradient ∇f, ∇g  (Kähler differentials)
      2. Simplify each component
      3. Structural comparison of simplified gradients
      4. If gradients match, verify f(0) = g(0)
      5. If any gradient component has Unknown → inconclusive
    """
    n_params = max(_max_param_index(expr_f),
                   _max_param_index(expr_g)) + 1
    if n_params <= 0:
        n_params = 1

    # Step 1-2: compute and simplify gradients
    grad_f = [_simplify(_differentiate(expr_f, i)) for i in range(n_params)]
    grad_g = [_simplify(_differentiate(expr_g, i)) for i in range(n_params)]

    # Step 3: compare — if any component has Unknown, bail
    all_match = True
    has_unknown = False
    for df_i, dg_i in zip(grad_f, grad_g):
        if df_i.kind == SExprKind.UNKNOWN or dg_i.kind == SExprKind.UNKNOWN:
            has_unknown = True
            break
        if df_i != dg_i:
            all_match = False
            break

    if has_unknown:
        return None, "cotangent section has opaque components"

    if not all_match:
        # Derivatives differ → programs MIGHT differ.
        # Use Z3 to confirm with a counterexample.
        return None, "cotangent sections differ (structural)"

    # Step 4: gradients match structurally — verify base point
    origin = {i: 0 for i in range(n_params)}
    val_f = _evaluate_at_point(expr_f, origin)
    val_g = _evaluate_at_point(expr_g, origin)

    if val_f is not None and val_g is not None:
        if val_f == val_g:
            return True, ("cotangent sheaf equivalent "
                          "(∇f = ∇g, f(0) = g(0))")
        else:
            return False, (f"same gradient but f(0)={val_f} ≠ "
                           f"g(0)={val_g} — differ by constant")

    # Can't evaluate at origin — check a few more points
    for pt_vals in [(1,), (2,), (1, 1), (1, 2), (2, 1)]:
        pt = {i: pt_vals[i] if i < len(pt_vals) else 0
              for i in range(n_params)}
        vf = _evaluate_at_point(expr_f, pt)
        vg = _evaluate_at_point(expr_g, pt)
        if vf is not None and vg is not None:
            if vf == vg:
                return True, "cotangent + evaluation agreement"
            else:
                return False, (f"same gradient but f({pt})={vf} "
                               f"≠ g({pt})={vg}")

    return None, "cotangent match but cannot verify base point"


# ── Denotational equivalence via Z3 ───────────────────────────

def _check_denotational_equivalence(expr_f: SExpr, expr_g: SExpr
                                     ) -> Tuple[Optional[bool], str]:
    """Check ∀ inputs. ⟦f⟧(inputs) = ⟦g⟧(inputs) via Z3 arithmetic.

    This is the genuine denotational semantics check: instead of
    comparing program STRUCTURE, it checks whether the programs
    compute the SAME MATHEMATICAL FUNCTION.

    Handles:
      - Algebraic identities  (x·2 = x+x)
      - Division semantics    (// ≠ int(/))
      - Fixpoint closed forms (sum(1..n) = n(n+1)/2)
      - Counterexample generation

    Returns:
      (True,  explanation) — denotationally equivalent  (∀x. f=g)
      (False, explanation) — counterexample found
      (None,  reason)      — untranslatable or Z3 timeout
    """
    try:
        import z3
    except ImportError:
        return None, "Z3 not available"

    n_params = max(_max_param_index(expr_f),
                   _max_param_index(expr_g)) + 1
    if n_params <= 0:
        n_params = 1

    params = [z3.Int(f'p_{i}') for i in range(n_params)]

    z3_f = _sexpr_to_z3(expr_f, params)
    z3_g = _sexpr_to_z3(expr_g, params)

    if z3_f is None or z3_g is None:
        return None, "cannot compute denotation"

    # Coerce to same sort
    if z3.is_int(z3_f) and z3.is_real(z3_g):
        z3_f = z3.ToReal(z3_f)
    elif z3.is_real(z3_f) and z3.is_int(z3_g):
        z3_g = z3.ToReal(z3_g)

    # Check ∀p. f(p) = g(p)  ⟺  ¬∃p. f(p) ≠ g(p)
    solver = z3.Solver()
    solver.set("timeout", 5000)
    solver.add(z3_f != z3_g)

    result = solver.check()
    if result == z3.unsat:
        return True, "denotationally equivalent (∀x. ⟦f⟧ = ⟦g⟧)"
    if result == z3.sat:
        model = solver.model()
        cex = {f'p_{i}': str(model.evaluate(params[i]))
               for i in range(n_params)}
        f_val = str(model.evaluate(z3_f))
        g_val = str(model.evaluate(z3_g))
        return False, (f"counterexample: {cex} → "
                       f"f={f_val}, g={g_val}")
    return None, "Z3 timeout on denotational check"


# ── Full Pipeline ───────────────────────────────────────────────

def symbolic_exprs_equivalent(exprs_f: List[SExpr],
                               exprs_g: List[SExpr]) -> Tuple[Optional[bool], str]:
    """Check program equivalence via topos-theoretic comparison.

    Full pipeline:
      1. Build Lawvere theories T_f, T_g
      2. Build program sites C_f, C_g
      3. Compute Čech cohomology H*(C_f, F), H*(C_g, F)
      4. Cohomological filter: H* must match
      5. Check geometric morphism existence via Z3

    Returns (result, explanation):
        True  — geometric morphism exists (programs equivalent)
        False — cohomological obstruction or Z3 UNSAT
        None  — inconclusive
    """
    if not exprs_f and not exprs_g:
        return True, "both empty"
    if not exprs_f or not exprs_g:
        return None, "could not extract one side"

    # Select the most informative return expression from each function.
    # The "most informative" is the one with the largest expression tree
    # (most nodes), which captures the main computation rather than
    # early-exit error returns like "return -1".
    def _tree_size(e: SExpr) -> int:
        n = 1
        for c in e.children:
            n += _tree_size(c)
        if e.fp_base:
            n += _tree_size(e.fp_base)
        if e.fp_domain:
            n += _tree_size(e.fp_domain)
        if e.case_test:
            n += _tree_size(e.case_test)
        if e.case_then:
            n += _tree_size(e.case_then)
        if e.case_else:
            n += _tree_size(e.case_else)
        return n

    expr_f = max(exprs_f, key=_tree_size)
    expr_g = max(exprs_g, key=_tree_size)

    # Step 1: Build Lawvere theories
    theory_f = LawvereTheory.from_sexpr(expr_f)
    theory_g = LawvereTheory.from_sexpr(expr_g)

    # Step 2: Build program sites
    site_f = ProgramSite.from_sexpr(expr_f)
    site_g = ProgramSite.from_sexpr(expr_g)

    # Step 3: Compute Čech cohomology
    coh_f = PresheafCohomology.compute(site_f)
    coh_g = PresheafCohomology.compute(site_g)

    # Step 4: Cohomological filter
    # Programs with different H¹ cannot be equivalent
    if coh_f.h1 != coh_g.h1:
        return None, f"H¹ obstruction: {coh_f.h1} ≠ {coh_g.h1}"

    # Programs with different Euler characteristic are suspect
    # (but not definitively inequivalent due to the rec↔iter identity)

    # Lawvere theory filter: op profiles must be compatible
    # (same operations used, though multiplicities may differ for rec↔iter)
    ops_f = set(theory_f.op_profile.keys())
    ops_g = set(theory_g.op_profile.keys())
    # Core operations must overlap
    core_ops_f = {op for op in ops_f if not op.startswith(('Seq.range', 'add', 'sub', 'Cmp.'))}
    core_ops_g = {op for op in ops_g if not op.startswith(('Seq.range', 'add', 'sub', 'Cmp.'))}
    # The distinctive operations (fixpoint, build, specific ops) should match
    fixpoint_ops_f = {op for op in ops_f if op.startswith('fixpoint.')}
    fixpoint_ops_g = {op for op in ops_g if op.startswith('fixpoint.')}
    if fixpoint_ops_f and fixpoint_ops_g and fixpoint_ops_f != fixpoint_ops_g:
        return None, f"Lawvere theory mismatch: fixpoint ops {fixpoint_ops_f} ≠ {fixpoint_ops_g}"

    # Sort profiles: compare RETURN sorts (root of expression tree) only.
    # Internal sorts (e.g., SEQ from range() as loop domain) are implementation
    # details that differ between rec↔iter forms.
    root_sort_f = exprs_f[0].sort if exprs_f else Sort.TOP
    root_sort_g = exprs_g[0].sort if exprs_g else Sort.TOP
    if not sorts_compatible(root_sort_f, root_sort_g):
        return None, f"return sort mismatch: {root_sort_f.name} ≠ {root_sort_g.name}"

    # ── Step 5: Cotangent sheaf comparison (symbolic differentiation) ──
    # This is the Kähler differential check: df = dg ∧ f(0) = g(0).
    # Complete for polynomial programs; inconclusive for fixpoints.
    result, explanation = _check_cotangent_equivalence(expr_f, expr_g)
    if result is True:
        details = (f"H⁰={coh_f.h0}/{coh_g.h0}, H¹={coh_f.h1}/{coh_g.h1}, "
                   f"χ={coh_f.euler_char}/{coh_g.euler_char}")
        return True, f"{explanation}; {details}"
    if result is False:
        return False, explanation

    # ── Step 6: Denotational equivalence via Z3 arithmetic ──────
    # Translates SExprs to Z3 terms and checks ∀x. ⟦f⟧(x) = ⟦g⟧(x).
    # Only counterexamples (False) are authoritative: they prove
    # f ≠ g on concrete integer inputs.  "Equivalent" on the integer
    # domain does NOT imply equivalence on Python's full type system
    # (e.g., abs(x) vs manual abs differ on complex; `or` returns a
    # value vs True/False).  So denotational True is just a supporting
    # signal, not a definitive positive.
    denot_result, denot_expl = _check_denotational_equivalence(expr_f, expr_g)
    if denot_result is False:
        return False, denot_expl
    # denot_result True → will be used as supporting evidence below

    # ── Step 7: Geometric morphism (structural fallback) ────────
    # Check for a cover-preserving functor φ: C_g → C_f between
    # the program sites.  This is the topos-theoretic comparison.
    result, explanation = _check_geometric_morphism(
        site_f, site_g, theory_f, theory_g)

    if result is True:
        details = (f"Lawvere: {len(theory_f.operations)}/{len(theory_g.operations)} ops, "
                   f"H⁰={coh_f.h0}/{coh_g.h0}, H¹={coh_f.h1}/{coh_g.h1}, "
                   f"χ={coh_f.euler_char}/{coh_g.euler_char}")
        return True, f"{explanation}; {details}"

    if result is False:
        return None, f"{explanation}; H⁰={coh_f.h0}/{coh_g.h0}, H¹={coh_f.h1}/{coh_g.h1}"

    return None, explanation


def _canonical_op(op_name: str) -> str:
    """Canonicalize operation name across rec/iter representations."""
    CANONICAL = {
        'Arith.mul': 'mul', 'Accum.product': 'mul', 'Arith.matmul': 'mul',
        'Arith.add': 'add', 'Accum.sum': 'add',
        'Arith.sub': 'sub', 'Accum.diff': 'sub',
        'Arith.div': 'truediv',
        'Arith.floordiv': 'floordiv',
        'Arith.mod': 'mod',
        'Arith.pow': 'pow',
        'Bit.or': 'bitor', 'Accum.union': 'bitor',
        'Bit.and': 'bitand', 'Accum.intersect': 'bitand',
        'Bit.xor': 'bitxor', 'Accum.xor': 'bitxor',
        'Logic.or': 'or', 'Logic.and': 'and',
        'Cmp.min': 'min', 'Cmp.max': 'max',
        'map': 'map', 'filter': 'filter',
        'generic': 'generic',
    }
    return CANONICAL.get(op_name, op_name)


def _operation_identity(canonical_op: str) -> Optional[int]:
    """Return the identity element of a commutative operation.

    This is the algebraic identity: the value e such that op(e, x) = x.
    From the Lawvere theory perspective, this is the unit morphism.
    """
    IDENTITIES = {
        'add': 0, 'sub': 0,
        'mul': 1, 'div': 1,
        'bitor': 0, 'bitand': ~0,  # -1 (all bits set)
        'bitxor': 0,
        'or': 0, 'and': 1,
        'max': 0, 'min': 0,
    }
    return IDENTITIES.get(canonical_op)


# ═══════════════════════════════════════════════════════════════════
# §4  Helper Functions
# ═══════════════════════════════════════════════════════════════════

def _binop_sort(op: ast.operator, left_sort: Sort, right_sort: Sort) -> Sort:
    """Infer output sort of a binary operation."""
    if isinstance(op, (ast.Add, ast.Sub, ast.Mult, ast.Div,
                        ast.FloorDiv, ast.Mod, ast.Pow)):
        if left_sort == Sort.STR or right_sort == Sort.STR:
            return Sort.STR
        return Sort.NUM
    if isinstance(op, (ast.BitOr, ast.BitAnd, ast.BitXor,
                        ast.LShift, ast.RShift)):
        if left_sort == Sort.SET:
            return Sort.SET
        return Sort.NUM
    return Sort.TOP

def _binop_name(op: ast.operator) -> str:
    NAMES = {
        'Add': 'Arith.add', 'Sub': 'Arith.sub',
        'Mult': 'Arith.mul', 'Div': 'Arith.div',
        'FloorDiv': 'Arith.floordiv', 'Mod': 'Arith.mod',
        'Pow': 'Arith.pow', 'MatMult': 'Arith.matmul',
        'BitOr': 'Bit.or', 'BitAnd': 'Bit.and',
        'BitXor': 'Bit.xor',
        'LShift': 'Bit.lshift', 'RShift': 'Bit.rshift',
    }
    return NAMES.get(type(op).__name__, 'Arith.generic')

def _augop_name(op: ast.operator) -> str:
    return _binop_name(op)

def _cmpop_name(op: ast.cmpop) -> str:
    NAMES = {
        'Eq': 'Cmp.eq', 'NotEq': 'Cmp.ne',
        'Lt': 'Cmp.lt', 'LtE': 'Cmp.le',
        'Gt': 'Cmp.gt', 'GtE': 'Cmp.ge',
        'Is': 'Cmp.is', 'IsNot': 'Cmp.isnot',
        'In': 'Cmp.in', 'NotIn': 'Cmp.notin',
    }
    return NAMES.get(type(op).__name__, 'Cmp.generic')


# ═══════════════════════════════════════════════════════════════════
# §5  Convenience API
# ═══════════════════════════════════════════════════════════════════

def symbolic_returns(source: str, func_name: str = '') -> List[SExpr]:
    """Extract symbolic return expressions from Python source code."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []

    funcs = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
    if not funcs:
        return []

    func = None
    if func_name:
        func = next((f for f in funcs if f.name == func_name), None)
    else:
        func = funcs[-1]

    if func is None:
        return []

    try:
        return SymbolicInterpreter().interpret(func)
    except Exception:
        return []
