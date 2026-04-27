# Python semantics coverage audit (psdl.py)

Audit target: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/deppy/proofs/psdl.py` (2293 lines).
Reference grammar: CPython 3.13 [Abstract Grammar](https://docs.python.org/3/library/ast.html#abstract-grammar).
Method: every dispatch in `_compile_stmt` (psdl.py:538–584), `_compile_expr` (psdl.py:1133–1499), `_compile_call` (psdl.py:1511–1520), `_compile_func_call` (psdl.py:1573–2134), and `_compile_method_call` (psdl.py:1522–1571) was mapped to the corresponding AST node class.

Legend:
- `OK` — full handler exists in psdl.py for the surface form.
- `partial` — handler exists but ignores or mishandles a documented sub-feature.
- `MISSING` — falls through to the catch-all `unsupported PSDL statement: <type>` (psdl.py:578–584) or `unsupported PSDL expression: <type>` (psdl.py:1492–1499).
- `parsed-only` — the surface form is accepted but produces a `Structural(...)` placeholder with no semantic content.

---

## 1. AST statement nodes

| Node | Handled? | Notes |
|---|---|---|
| `FunctionDef` | partial (psdl.py:575, 644–677) | Recognises `@inductive` (only via class), `@axiom`, `@theorem`, `@protocol` decorators by name (psdl.py:649). All other decorators silently ignored. Default args, `*args`, `**kwargs`, positional-only/keyword-only markers, annotations on params, type-param brackets `def f[T](...)` ignored. Generic `def` falls through to `compile_block(stmt.body)` — the function body is compiled but the binders are dropped. |
| `AsyncFunctionDef` | MISSING | No handler — emits `sorry` placeholder + `unsupported PSDL statement: AsyncFunctionDef` error. |
| `ClassDef` | partial (psdl.py:573, 587–642) | Recognises `@inductive` (psdl.py:592), `@protocol` (psdl.py:618), and treats unrecognised classes as a sigma-record (psdl.py:632–642). Bases/multi-inheritance, keyword args (`metaclass=`), generic syntax `class C[T]:` (PEP 695), `__init_subclass__`, `__slots__`, decorators other than `@inductive`/`@protocol` are all dropped silently. Inductive bodies only recognise `AnnAssign` constructors and `FunctionDef` constructors; nested classes / module-level statements in the body are skipped. Methods of plain records are dropped. |
| `Return` | OK (psdl.py:551, 1023–1029) | Maps to `Refl(Var(_safe(text)))`. The returned expression is *not* recursively compiled — only its source text is stored as a name. So `return cong(f, p)` becomes `Refl(Var("cong_f_p"))`, losing the proof structure. |
| `Delete` | MISSING | No handler. Falls through to `unsupported PSDL statement: Delete`. |
| `Assign` | partial (psdl.py:557, 1077–1126) | Single `Name` target → `Cut(hyp_name, PyObjType, lemma=compile(rhs), body=Refl(_let_body))`. Tuple/list target → builds a `Cut` chain but every component shares the *same* `inner` proof of the RHS — tuple-unpack is not modeled with projections, just shared (psdl.py:1101–1110). Multiple-target chained assignment (`a = b = expr`) silently drops all targets except `targets[0]` (psdl.py:1080). `Subscript` / `Attribute` / `Starred` LHS targets all return `Structural("non-name assign")`. |
| `TypeAlias` (PEP 695, `type T = ...`) | MISSING | No handler. |
| `AugAssign` (`+=`, `-=`, `@=`, etc.) | MISSING | No handler. |
| `AnnAssign` (`x: T = v`) | OK-ish (psdl.py:555, 1055–1074) | `Name`-only target. RHS compiled and wrapped as `Cut`. Non-Name target returns `Structural("non-name annotated target")`. |
| `For` | partial (psdl.py:543, 860–877) | Mapped to `ListInduction`. Loop body becomes the cons-case proof; nil-case is hard-coded `Refl(Var("_nil"))` (psdl.py:871). Iter expression text is captured but its *value* isn't analysed (no detection of `range(n)`, generators, etc.). Loop `target` is only honoured when it's a `Name` — tuple-unpacking targets (`for x, y in pairs:`) collapse to `"x"` (psdl.py:861–863). `else:` clause silently dropped. `break` / `continue` inside body silently dropped (no AST handlers exist). |
| `AsyncFor` | MISSING | No handler. |
| `While` | partial (psdl.py:545, 880–901) | Mapped to `NatInduction`. Induction variable is `ast.walk(stmt.test)`'s first `Name` node (psdl.py:888–891), which can pick up an unrelated identifier (e.g. in `while not done(x):` it picks `done`, not `x`). Base case is `Refl(_zero_<var>)`; *no termination measure is checked* — any while-loop is admitted regardless of whether it terminates. `else:` dropped. |
| `If` | OK (psdl.py:539, 776–809) | `isinstance(var, T)` test → `Fiber` (psdl.py:802–809). Other tests → `Cases` (psdl.py:789). `elif` chain handled because Python parses `elif` as nested `If` in `orelse` — recursion handles it. `exhaustive` flag on `Fiber` only set when `orelse` non-empty; that's a soundness concern (an `if isinstance(...)` with no else is non-exhaustive but `Fiber` still records both branches). |
| `With` | OK-ish (psdl.py:564, 715–773) | Three head names recognised: `goal(...)`, `case(...)`, `hypothesis(h=..., T=...)`. Multiple `withitems` reduce to `stmt.items[0]` only (psdl.py:725) — `with A, B:` drops B. `as alias:` clauses ignored. Unknown context manager → pass-through (compile body only). No `__enter__`/`__exit__` semantics. |
| `AsyncWith` | MISSING | No handler. |
| `Match` | partial (psdl.py:547, 904–913) | Mapped to `Cases`. Pattern is captured via `ast.unparse(case.pattern)` *as a string* — the kernel sees only the source text. `case.guard` (`case X if cond:`) silently dropped. All pattern variants (`MatchAs`, `MatchClass`, `MatchMapping`, `MatchOr`, `MatchSequence`, `MatchSingleton`, `MatchStar`, `MatchValue`) are unparsed without any semantic interpretation. |
| `Raise` | partial (psdl.py:553, 1032–1052) | `raise NotImplementedError` → `Structural("vacuous: ...")` (psdl.py:1037–1041). Other exceptions → `EffectWitness(effect="exception:<text>", ...)`. Bare `raise` (re-raise) → `Structural("bare raise")` (psdl.py:1033–1035). The `from <cause>` clause (`stmt.cause`) is silently dropped — no exception chaining. |
| `Try` | partial (psdl.py:541, 812–857) | `try/except` chained as `EffectWitness` + `ConditionalEffectWitness`. **`else:` clause silently dropped** (`stmt.orelse` is never read). **`finally:` clause silently dropped** (`stmt.finalbody` is never read). Multiple `except` clauses are processed but `ExceptHandler.name` (`except E as e:`) is dropped — handler bodies cannot reference the bound exception object. |
| `TryStar` (`try/except*`, PEP 654) | MISSING | No handler. |
| `Assert` | OK (psdl.py:549, 916–1020) | Recognises `"z3"`, closer keywords (`qed`/`auto`/`done`/`omega`/`rfl`/`trivial`/`decide`/`simp`), `"by F"`, `"by lemma L"`. Bare `assert P` defaults to `z3` (psdl.py:923). Non-string `msg` argument silently ignored. |
| `Import` | MISSING | No handler. Bare `import x` falls through to `unsupported PSDL statement: Import`. |
| `ImportFrom` | parsed-only (psdl.py:566–571) | Records names in `foundations_referenced` but doesn't validate them. `as alias` ignored. Relative imports (`from . import x`) accepted but not resolved. |
| `Global` | MISSING | No handler. |
| `Nonlocal` | MISSING | No handler. |
| `Expr` (expression statement) | OK (psdl.py:559, 1129–1130) | Delegates to `_compile_expr`. |
| `Pass` | OK (psdl.py:561–563) | Maps to `Structural("trivial")` + Lean `trivial`. |
| `Break` | MISSING | No handler. Inside a `For`/`While` body, the body is compiled by `compile_block` and `Break` falls through to `unsupported`. **Soundness-relevant**: `break` is *silently dropped* if it falls inside a block whose error reporting goes elsewhere; but the `errors` list does collect a `PSDLError`. The kernel still gets the loop's `cons_proof` / `step_proof` even though the user's actual semantics ended early. |
| `Continue` | MISSING | Same as `Break`. |

**Statement-node total: 12 of 22 statement-class handlers exist** (FunctionDef, ClassDef, Return, Assign, AnnAssign, For, While, If, With, Match, Raise, Try, Assert, ImportFrom, Expr, Pass — 16 partial-or-full handlers; 22 statement classes total in 3.13 grammar). **6 fully missing** (AsyncFunctionDef, Delete, TypeAlias, AugAssign, AsyncFor, AsyncWith, TryStar, Import, Global, Nonlocal, Break, Continue — actually 12 missing). Net: roughly **16/22 partial-or-better, 6 of those 16 lose substantial semantics**.

---

## 2. AST expression nodes

| Node | Handled? | Notes |
|---|---|---|
| `BoolOp` | OK (psdl.py:1377–1421) | `And` → conjunction via `Cut` chain. `Or` → `Cases` with branches per disjunct. Lazy/short-circuit semantics not modeled. `bool(x)` coercion of operands not modeled. |
| `NamedExpr` (walrus `(h := proof)`) | OK (psdl.py:1174–1187) | Becomes `Cut(hyp_name=target.id, ...)`. Non-Name target ignored. |
| `BinOp` | partial (psdl.py:1207–1259) | See §3 below. Only `MatMult`, `Mult` (left=Name only), `Pow`, `RShift` mapped. `Add`/`Sub`/`Div`/`FloorDiv`/`Mod`/`LShift`/`BitAnd`/`BitOr`/`BitXor` all fall through to the catch-all `unsupported PSDL expression: BinOp` error. |
| `UnaryOp` | partial (psdl.py:1189–1206) | Only `Invert` (~) and `Not` mapped. `USub` and `UAdd` fall through. |
| `Lambda` | parsed-only (psdl.py:1478–1485) | Returns `Structural(f"lambda({arg_names})")` — neither parameters nor body get compiled into the proof. |
| `IfExp` (`a if c else b`) | OK (psdl.py:1261–1271) | Becomes `Cases` keyed on `cond_text`. Same caveat as `If`: condition text is captured as a string, not as a proof of a hypothesis. |
| `Dict` | partial (psdl.py:1444–1465) | Treated as conjunction-introduction (`⟨v1, v2, ...⟩`), keys used as `hyp_name` strings. `**unpacking` (`{**a, **b}`) — `key=None` entries are filtered out (psdl.py:1446–1448) without warning. |
| `Set` | MISSING | Not in `_compile_expr` dispatch; falls through. |
| `ListComp` | partial (psdl.py:1273–1290) | Compiles only the `elt` expression once, wraps in `ListInduction`. `generators[1:]` (multi-`for`) silently dropped. `if` filters in generators silently dropped. Nested generators not handled. |
| `SetComp` | partial | Same path as `ListComp` (psdl.py:1273) — same caveats. |
| `DictComp` | MISSING | Not listed in `(ast.ListComp, ast.GeneratorExp, ast.SetComp)` test (psdl.py:1273); falls through. |
| `GeneratorExp` | partial | Same path as `ListComp` — same caveats. |
| `Await` | MISSING | No handler. |
| `Yield` | MISSING | No handler. |
| `YieldFrom` | MISSING | No handler. |
| `Compare` | MISSING | No handler in `_compile_expr` — `a == b`, `a < b`, `a is b`, `a in b` etc. all fall through to the catch-all. (Compare *is* used inside string literals like `assert x >= 0`, but those are handled at the assert level, not the expression level.) |
| `Call` | OK (psdl.py:1135, 1511–2134) | The main tactic site. Dispatches to `_compile_method_call` (`obj.method(args)`) or `_compile_func_call` (`f(args)`). `**kwargs` and `*args` in calls: `_compile_func_call` only inspects positional `args` and a few `keywords` (e.g. `induction(base=, step=)` at psdl.py:1851–1855). Most call sites silently drop kwargs and starred args. |
| `FormattedValue` | parsed-only via JoinedStr | Inside an `f"..."`, `FormattedValue` nodes carry the embedded expression — PSDL just unparses the whole `JoinedStr` and emits a Lean comment (psdl.py:1468–1474). |
| `JoinedStr` (f-strings) | parsed-only (psdl.py:1468–1474) | Returns `Structural(f"f-string ...")`. The interpolated values are never compiled as proofs; format-spec / conversion-flags ignored. |
| `Constant` | OK-ish (psdl.py:1426–1441) | Three cases: `Ellipsis` → `sorry` placeholder + hint (psdl.py:1426–1432); `str` → comment (psdl.py:1434–1436); other (`int`, `float`, `complex`, `bool`, `None`, `bytes`) → `Refl(Var(f"_const_<repr>"))` (psdl.py:1438–1441). |
| `Attribute` | partial (psdl.py:1143–1172) | Only handles `<Name>.<attr>` — `obj.method` where `obj` is a chain (`a.b.c`) goes through `node.value=Attribute`, falls through, and only matches inside the surrounding `_compile_method_call` (Call → Attribute path). Recognised attrs: `symm`, `inv`, `lhs`, `rhs`, `sides`, `unfold`, `rewrite`. Anything else falls through to the catch-all error. |
| `Subscript` | OK (psdl.py:1295–1367) | Recognises `Refl[x]`, `Path[A,x,y]`, `Pi[x:T]`, `Sigma[x:T]`, `Equiv[A,B]`, `Diamond[A]`, `Box[A]`, `Refinement[T,P]` as type-level forms. Anything else → `Structural("type-level ...")`. Note that *every* unrecognised subscript still returns a structural placeholder (no error), unlike unrecognised `Call` which falls through to error. So `xs[0]` and `dict[key]` both produce silent placeholders. |
| `Starred` | parsed-only (psdl.py:1489–1490) | Unwraps and compiles the operand. Star-context (unpack into list, into call) is not modeled. |
| `Name` | OK (psdl.py:1138–1139, 1501–1509) | Bare names treated as `AxiomInvocation`. If the name is in `foundations`, becomes `Foundation_<name>`. |
| `List` | MISSING | Not in `_compile_expr` dispatch. (It's only matched as a tuple-target in `_compile_assign` at psdl.py:1085 and as the args list of `fibre_split` at psdl.py:2016.) Bare list literals as expressions → catch-all error. |
| `Tuple` | partial (psdl.py:1369–1373) | Only at expression level: returns the last element's compiled proof. The other elements *are* compiled (so side effects happen) but are dropped. Tuple-as-Assign-target handled separately at psdl.py:1085. |
| `Slice` | MISSING | Not in `_compile_expr`. (Slicing inside `Subscript[...]` is also not supported — the `slice_node` is checked for `Tuple` only at psdl.py:1302.) |

**Expression-node total: 14 of 28 expression classes have handlers**. Of those, 6 are parsed-only / structural placeholders (`Lambda`, `JoinedStr`, `FormattedValue`, `Tuple`, `Starred`, generic `Subscript`), and another 5 are partial (`BinOp`, `UnaryOp`, `Dict`, comprehensions, `Attribute`). Soundly handled: `BoolOp`, `NamedExpr`, `IfExp`, `Call`, `Name`, `Constant`, structured `Subscript`.

---

## 3. Operators

For BinOp / UnaryOp / Compare, list every operator and where PSDL maps it:

| Operator | AST node | PSDL handler | Maps to |
|---|---|---|---|
| `+` | `BinOp(Add)` | MISSING | catch-all error |
| `-` (binary) | `BinOp(Sub)` | MISSING | catch-all error |
| `*` | `BinOp(Mult)` | psdl.py:1221–1228 (only when LHS is `Name`) | `Ap(function=Name, path_proof=RHS)` — congruence |
| `/` | `BinOp(Div)` | MISSING | catch-all error |
| `//` | `BinOp(FloorDiv)` | MISSING | catch-all error |
| `%` | `BinOp(Mod)` | MISSING | catch-all error |
| `**` | `BinOp(Pow)` | psdl.py:1233–1249 | k-fold `PathComp(p, p, ..., p)` (k clamped ≥ 1) |
| `<<` | `BinOp(LShift)` | MISSING | catch-all error |
| `>>` | `BinOp(RShift)` | psdl.py:1251–1259 | `Cut(_chain_<lineno>, lemma=L, body=R)` — sequential chaining |
| `&` | `BinOp(BitAnd)` | MISSING | catch-all error |
| `|` | `BinOp(BitOr)` | MISSING | catch-all error |
| `^` | `BinOp(BitXor)` | MISSING | catch-all error |
| `@` | `BinOp(MatMult)` | psdl.py:1209–1217 | `PathComp(left, right)` — path composition |
| `~` | `UnaryOp(Invert)` | psdl.py:1191–1197 | `Sym(proof)` |
| `-` (unary) | `UnaryOp(USub)` | MISSING | catch-all error |
| `+` (unary) | `UnaryOp(UAdd)` | MISSING | catch-all error |
| `not` | `UnaryOp(Not)` | psdl.py:1199–1206 | `Structural(f"negation of ...")` (parsed-only) |
| `and` | `BoolOp(And)` | psdl.py:1379–1395 | conjunction via `Cut` chain |
| `or` | `BoolOp(Or)` | psdl.py:1396–1421 | `Cases` with disjunct branches |
| `==` | `Compare(Eq)` | MISSING | catch-all error |
| `!=` | `Compare(NotEq)` | MISSING | catch-all error |
| `<` | `Compare(Lt)` | MISSING | catch-all error |
| `<=` | `Compare(LtE)` | MISSING | catch-all error |
| `>` | `Compare(Gt)` | MISSING | catch-all error |
| `>=` | `Compare(GtE)` | MISSING | catch-all error |
| `is` | `Compare(Is)` | MISSING | catch-all error |
| `is not` | `Compare(IsNot)` | MISSING | catch-all error |
| `in` | `Compare(In)` | MISSING | catch-all error |
| `not in` | `Compare(NotIn)` | MISSING | catch-all error |

**BinOp ops: 4 of 13 handled** (`*` partial, `**`, `>>`, `@`). **UnaryOp ops: 2 of 4 handled** (`~`, `not`). **BoolOp ops: 2 of 2 handled**. **Compare ops: 0 of 10 handled at expression level**. (Compare expressions inside `assert` are passed through as text by `ast.unparse(stmt.test)` at psdl.py:949 and discharged by Z3, but `_compile_expr(Compare)` itself produces no ProofTerm.)

Important: chained comparisons `a < b < c` are a single `Compare` node with multiple `ops`/`comparators`; PSDL has no handler at all, so they error out.

---

## 4. Python semantic protocols (not just syntax)

For each, state whether PSDL can prove anything about the semantics, or whether it just parses the surface form:

- **Iterator protocol** (`__iter__` / `__next__`) — **not modeled**. `for x in xs:` is mapped to `ListInduction` (psdl.py:875) with no consideration of `xs` being an iterable, generator, dict view, or finite set. Iterators that aren't list-shaped are admitted as if they were lists. The induction is over the *Python expression* `xs` text, not over a witness of an inductive type.

- **Context manager protocol** (`__enter__` / `__exit__`) — **not modeled**. `with` recognises three hard-coded heads (`goal`, `case`, `hypothesis` at psdl.py:729–770); other context managers pass through with the body compiled but no `__enter__` / `__exit__` semantics, no exception suppression, no `as` binding. Multiple withitems collapse to the first.

- **Descriptor protocol** (`__get__` / `__set__` / `__delete__`) — **not modeled at all**. Attribute access is parsed as `ast.Attribute` (psdl.py:1143–1172) with seven hard-coded postfix sugars; no descriptor / property / classmethod / staticmethod awareness.

- **MRO / multiple inheritance** — **not modeled**. `ClassDef.bases` is read only via `decorator_list` for `@inductive` / `@protocol` / fall-through (psdl.py:587). `bases` and `keywords` (the `metaclass=` slot) are silently dropped.

- **Method Resolution Order in attribute lookup** — **not modeled**. There is no resolver; `obj.method(args)` is just text-spliced into Lean (psdl.py:1525, `recv = ast.unparse(f.value)`).

- **Operator overloading** (`__add__`, `__radd__`, `__iadd__`, etc.) — **partly modeled, but only as PSDL-level sugar**. `@`, `**`, `~`, `*`, `>>` are repurposed for proof-composition primitives; the user's `__add__` etc. are *not* honoured (PSDL treats `+` as unsupported, regardless of whether the user defined `__add__`). No reflected ops, no in-place ops (`AugAssign` missing).

- **Exception chaining** (`raise X from Y`) — **not modeled**. `_compile_raise` (psdl.py:1032–1052) reads `stmt.exc` only; `stmt.cause` is silently ignored. So `raise A from B` and `raise A` are indistinguishable to PSDL.

- **Generator semantics** (yield-pause-resume, finalizers) — **not modeled**. `Yield` / `YieldFrom` are MISSING — any function body containing `yield` falls through to the catch-all error at the expression-statement level.

- **Coroutines / async** (`await`, `async for`, `async with`) — **not modeled**. `Await`, `AsyncFor`, `AsyncWith`, `AsyncFunctionDef` are all MISSING.

- **Decorators on classes/functions** — **selectively recognised by name**. Decorators are reduced to a string set via `_dec_name` (psdl.py:679–690) and the only recognised names are `inductive`, `axiom`, `theorem`, `protocol` (psdl.py:592, 618, 649, 660). Decorators with arguments (`@axiom("name")`) reduce to the function name (`axiom`) but the arguments are dropped. Stacked decorators are all in the set, so `@axiom @theorem` is ambiguous and the first matching branch wins (axiom precedes theorem in `_compile_function_def`). `@dataclass`, `@property`, `@classmethod`, `@staticmethod`, `@functools.wraps`, etc. are silently ignored.

- **Type annotations / `__class_getitem__`** — **partly modeled**. PSDL has its own subscript-type vocabulary (`Path[A,x,y]`, `Pi`, `Sigma`, `Equiv`, etc., psdl.py:1295–1367). User-defined generics (`MyClass[T]`) fall into the generic-subscript branch (psdl.py:1364–1367) and produce `Structural("type-level ...")`. The annotation strings on `AnnAssign` are captured as text only (psdl.py:1059, 1064).

- **String formatting** — **not modeled**. f-strings produce `Structural` placeholders (psdl.py:1468–1474). `%`-formatting and `.format()` go through generic `Call` / `BinOp` paths, neither of which model the semantics — `"x %s" % y` is `BinOp(Mod)` which is MISSING.

- **Comprehension scoping** (the implicit lambda) — **not modeled**. The comprehension iterator's scope is conflated with the surrounding scope (psdl.py:1273–1290 just compiles `node.elt`). Nested generators not handled. `if` filters dropped. The Python rule that comprehension targets don't leak (since 3.0) isn't relevant because PSDL doesn't track scoping at all.

- **Closure semantics** (free variables in nested defs) — **not modeled**. Nested `def`s call `compile_block(stmt.body, indent+1)` without binder introduction (psdl.py:677). Free variables in the body resolve against the same `foundations` dict as the enclosing scope. There is no de Bruijn-style closure capture or environment threading.

- **`global` / `nonlocal`** — **not modeled** (MISSING handlers).

- **`__slots__`** — **not modeled**. PSDL never reads class body for `__slots__`.

- **`__init_subclass__`** — **not modeled**.

- **Metaclasses** (`metaclass=`) — **not modeled**. `ClassDef.keywords` is never read.

- **Pattern matching** — **parsed-only** (psdl.py:904–913). Each `case.pattern` is unparsed as a string and stored in `Cases.branches`. The kernel sees only the source text, so:
  - `MatchAs` (`case x:`, `case _ as x:`): captured as text.
  - `MatchOr` (`case A | B:`): captured as text.
  - `MatchSequence` (`case [a, b, *rest]:`): captured as text, no destructuring.
  - `MatchMapping` (`case {"k": v}:`): same.
  - `MatchClass` (`case Point(x=0):`): same.
  - `MatchStar` (`case [*xs]:`): same.
  - `MatchSingleton` (`case None:` / `case True:`): same.
  - `MatchValue` (`case 0:`): same.
  - **`case.guard`** (`case X if cond:`): **silently dropped** — the guard expression is in `case.guard` but `_compile_match` never reads it (psdl.py:908–912).

---

## 5. Python language features beyond AST

- **PEP 695 generic syntax** (`class Foo[T]:`, `def f[T](...)`, `type T = ...`) — **not modeled**. `ClassDef.type_params` and `FunctionDef.type_params` are never read. `TypeAlias` AST node is MISSING.

- **TypeVar / ParamSpec / TypeVarTuple** — **not modeled** (instances appear only in `type_params` lists, which are dropped).

- **Walrus assignment in comprehensions** (`[y := x for x in xs]`) — **not specifically handled**. The comprehension path only compiles `node.elt`, so a `NamedExpr` inside the comprehension's elt would go through `_compile_expr` and become a `Cut`, but the iteration semantics are still dropped.

- **Augmented assignment in tuple targets** — Python doesn't permit `(a, b) += ...` syntactically. Plain `AugAssign` MISSING (psdl.py:1077-onward only handles `Assign`).

- **Star-unpacking in expressions** (`[*xs, *ys]`, `{**a, **b}`) — **not modeled**. List literal `*xs` MISSING because `List` itself is MISSING. Dict `**a` is filtered out at psdl.py:1446–1448 (entries with `key=None`) without warning.

- **Positional-only / keyword-only parameters** — **not modeled**. `FunctionDef.args` is parsed via `[a.arg for a in member.args.args]` (psdl.py:608) — only the simple `args` list. `posonlyargs`, `kwonlyargs`, `kw_defaults`, `defaults`, `vararg`, `kwarg` are all silently dropped.

- **Default arguments** — **not modeled**. `FunctionDef.args.defaults` and `kw_defaults` are never read. Inductive constructor default arg values (e.g., `class T: x: int = 0`) are silently dropped.

- **`__future__` imports** — handled trivially as `ImportFrom` (psdl.py:566–571). Names recorded but not honoured.

- **Type comments** (legacy `# type: ...`) — **not modeled**. PSDL uses `ast.parse(src, mode="exec")` (psdl.py:2185) without `type_comments=True`, so the parser doesn't even surface them.

- **Annotations of class variables** — recognised in `@inductive` bodies (psdl.py:597–605) and plain class records (psdl.py:634–641). Forward-reference strings (`x: "MyType"`) are unparsed verbatim.

- **`match` guards** (`case X if cond:`) — **silently dropped** (psdl.py:908–912 reads only `case.pattern` and `case.body`).

---

## 6. Summary

- **Statement nodes**: 16 of 22 have a dispatch (FunctionDef, ClassDef, Return, Assign, AnnAssign, For, While, If, With, Match, Raise, Try, Assert, ImportFrom, Expr, Pass). Of those, 9 are partial in soundness-relevant ways (FunctionDef, ClassDef, Assign, For, While, With, Match, Raise, Try). 6 are MISSING (AsyncFunctionDef, Delete, TypeAlias, AugAssign, AsyncFor, AsyncWith, TryStar, Import, Global, Nonlocal, Break, Continue — net 12 missing).
- **Expression nodes**: 14 of 28 have a dispatch. 6 are parsed-only placeholders. 14 are MISSING (Set, DictComp, Await, Yield, YieldFrom, Compare, List, Slice, plus most of UnaryOp/BinOp branches).
- **BinOp ops**: 4 of 13 mapped (`*`, `**`, `>>`, `@`).
- **UnaryOp ops**: 2 of 4 mapped (`~`, `not`).
- **Compare ops**: 0 of 10 mapped at expression level.
- **BoolOp ops**: 2 of 2 mapped.
- **Semantic protocols**: 0 of ~17 fully reasoned about. Operator overloading is the only one with even partial coverage, and only for the proof-composition repurposing of `@`/`**`/`~`/`>>`.

---

## 7. Pythonic-but-unsupported idioms (top 10 most common)

1. **`break` / `continue` in loops are MISSING** — `For`/`While` admits the loop body even when control flow can exit early. `_compile_stmt` has no handler for `ast.Break`/`ast.Continue`; they generate a "unsupported" error but the surrounding loop's `ListInduction`/`NatInduction` proof term is *still constructed and returned* (psdl.py:872, 896). **Soundness gap**: a user can write `for x in xs: break` and PSDL emits a `ListInduction` whose `cons_proof` includes the unsupported error but whose Lean tactic still claims induction.

2. **`finally:` clause silently dropped** — `_compile_try` reads only `stmt.body` and `stmt.handlers` (psdl.py:829–836). `stmt.finalbody` is never consulted. **Soundness gap**: `finally:` is the *only* part of try/except that always runs; dropping it means PSDL cannot reason about cleanup.

3. **`else:` clause silently dropped on `for`/`while`/`try`** — `For.orelse`, `While.orelse`, `Try.orelse` are all unread. **Common idiom**: `for ...: ...; else: not_found()`.

4. **Comparisons (`==`, `<`, `>`, `is`, `in`) at expression level have no handler** — `Compare` produces a catch-all error. Users naturally write `assert x == y` (works, via z3 from text) but `if x == y:` falls into the generic-`If` path that uses the *string* of the test and a `Cases` (psdl.py:780–792) — the equality is not lifted to a kernel-level proof term.

5. **Default args / `*args` / `**kwargs` ignored** — `FunctionDef.args.defaults`, `vararg`, `kwarg`, `posonlyargs`, `kwonlyargs` all dropped at psdl.py:608. Inductive constructor declarations lose their defaults; theorem signatures lose variadic / keyword params.

6. **`raise X from Y` chaining lost** — `stmt.cause` ignored at psdl.py:1032–1052. PSDL cannot distinguish `raise A` (fresh) from `raise A from B` (chained).

7. **Tuple-unpacking assignment treats components as the same proof** — psdl.py:1101–1110 reuses the same `inner` proof for every name. `a, b = pair` produces *two* `Cut`s with the same lemma. **Soundness gap**: the components' types/witnesses are different, but PSDL gives them the same proof object.

8. **For-loop with non-list iter, comprehension's `if` filter, multi-`for` comprehension** — all parsed but their semantics dropped (psdl.py:864, 1273–1290).

9. **`break`/`continue`/`else` on loops — repeating because it's the most-cited soundness hole**: `for n in range(10): if n > 5: break` is admitted as a complete `ListInduction` over `range(10)` whose body includes a structural error.

10. **`as` clauses ignored** — `with x as y:` (the `withitem.optional_vars`), `except E as e:` (the `excepthandler.name`), `import x as y:` (the `alias.asname`) are all dropped. Subsequent references to `y`/`e` in handler bodies treat them as undefined → `_compile_name_ref` makes them `AxiomInvocation` placeholders (psdl.py:1501–1509).

---

## Appendix A — Path through the catch-all

When a node falls through the `_compile_stmt` dispatch (psdl.py:578–584), PSDL:
1. Records a `PSDLError` with `message=f"unsupported PSDL statement: {type(stmt).__name__}"`.
2. Emits Lean `sorry`.
3. Returns `Structural(f"unsupported {type(stmt).__name__}")`.

This is *visible* (the `errors` list will be non-empty), so `result.ok` is `False`. So unsupported statements don't silently produce false proofs *at the top level*. **But**: if the unsupported statement is nested inside a handled construct (e.g., a `break` inside a `For` body, a `finally` block inside a `Try`), the surrounding construct's ProofTerm is still built and returned alongside the error. The kernel may receive a complete-looking ProofTerm even though `errors` is non-empty. Consumers must check `result.ok` (psdl.py:489–491) before trusting the proof term.

## Appendix B — Statement / expression catch-all asymmetry

- Catch-all expressions (`_compile_expr`, psdl.py:1492–1499) emit a `PSDLError` and return `Structural`.
- Catch-all `Subscript` (psdl.py:1364–1367) emits no error, just `Structural("type-level ...")`. So unrecognised subscript expressions are silent.
- Catch-all `_compile_func_call` (psdl.py:2131–2134) emits no error — just emits Lean `sorry` in a comment. Returns `Structural(f"unknown function {fname}")`. **Soundness gap**: unknown function calls produce a structural placeholder *with no `errors` entry*, so `result.ok` may be `True` despite the proof being a placeholder.
- Catch-all `_compile_method_call` (psdl.py:1568–1571) similarly emits no error.

So calls to unknown functions or methods *bypass* the `errors` list while still producing a `Structural` placeholder. This is the single most-impactful soundness-adjacent reporting gap.

---

## 8. Runtime semantic properties PSDL doesn't model

Sections 1–7 audit PSDL's coverage of the AST surface. This section audits
properties of Python's *runtime semantics* that are invisible at the AST
level: the same node may mean different things at runtime depending on heap
state, object identity, or dispatch tables. PSDL never executes the proof
script, never models a heap, and only inspects the AST text — so any
property that requires runtime reasoning is silently elided.

For each item below: (a) what Python actually does, (b) what PSDL's
compiler does or doesn't model, (c) the soundness consequence.

### Soundness-relevant gaps (could let users "prove" false claims)

- **Late closure binding (List/Set/GeneratorExp)** — Python: `fs =
  [lambda: i for i in range(3)]; [f() for f in fs]` returns `[2, 2,
  2]`, *not* `[0, 1, 2]`, because the lambdas close over the *binding*
  `i`, not the value. PSDL's comprehension handler at psdl.py:1273-1290
  emits `ListInduction(var=gen.target.id, nil_proof=Refl,
  cons_proof=elt_pf)` by recursing once into `node.elt` and treating
  the iterator name as the universally-quantified binder. The `elt`
  expression — the lambda — is compiled as if `i` were *substituted* at
  each iteration, collapsing the late-binding semantics. The standalone
  Lambda handler at psdl.py:1478-1485 itself returns
  `Structural(f"lambda({arg_names})")` without compiling the body, so
  even the `lambda` body's `i` reference is opaque. **Soundness
  consequence**: a user proving "`f(i) = i` for every `f` in this
  comprehension" is accepted by PSDL and false at runtime — every `f`
  in `fs` returns `2`, not the iteration index. **Fix surface**:
  psdl.py:1280 (comprehension elt compilation) + psdl.py:1478-1485
  (Lambda body never compiled).

- **Mutability through aliases** — Python: `a = []; b = a;
  a.append(1)` leaves `b == [1]` because `a` and `b` reference the same
  list object. PSDL's `_compile_assign` at psdl.py:1117-1126 emits
  `Cut(hyp_name=h, hyp_type=PyObjType(), lemma_proof=<inner>,
  body_proof=Refl(Var("_let_body")))` — a name binding whose
  `lemma_proof` is derived purely from the RHS *expression*. There
  is no kernel-level model of object identity vs structural value;
  PSDL's `PyObjType` is unitary. Subsequent mutations through any
  alias never flow back into earlier-bound names; the kernel sees `b`
  as whatever the RHS expression compiled to at bind-time, not the
  current heap state. **Soundness consequence**: any proof of the form
  `assert len(b) == 0, "z3"` after `a.append(1)` is accepted (Z3 sees
  `b = []` from the bind-time lemma). False at runtime. The same
  failure mode applies to dicts, sets, bytearrays, and any custom
  mutable class — PSDL treats all values as immutable proof terms.
  **Fix surface**: psdl.py:1077-1126 — kernel has no aliasing
  analysis, no heap.

- **Order of evaluation and short-circuit semantics** — Python: `f()
  + g()` evaluates `f()` first; `f() and g()` evaluates `g()` only if
  `f()` is truthy; `f() or g()` evaluates `g()` only if `f()` is
  falsy; argument evaluation in `h(x, y)` is left-to-right. Side
  effects respect that order. PSDL's `BinOp` handler at
  psdl.py:1207-1259 only handles proof-overloaded operators
  (`MatMult`, `Mult`, `Pow`, `RShift`); other arithmetic ops fall
  through to the catch-all. The `BoolOp` handler at psdl.py:1377-1421
  builds `Cut`-chains for `and` (psdl.py:1387-1394) and `Cases` for
  `or` (psdl.py:1396-1421) — neither models the short-circuit:
  ```
  acc = inners[-1]
  for inner in reversed(inners[:-1]):
      acc = Cut(hyp_name="_and", ..., lemma_proof=inner, body_proof=acc)
  ```
  Both inners are *always* compiled — there's no notion that the
  second is conditional on the first being truthy. **Soundness
  consequence**: `assert f() and g(), "z3"` where `g()` raises if
  evaluated builds a Cut whose body assumes both `f()` and `g()`
  succeed. A proof that uses `g()`'s post-condition succeeds in PSDL,
  but at runtime `g()` was never called when `f()` returned False.
  More subtly, `(x is not None and x.foo > 0)` is the canonical
  pattern for guarding attribute access; PSDL's Cut chain proves
  `x.foo > 0` regardless of whether the guard held. **Fix surface**:
  psdl.py:1387-1394 (and-chain) + psdl.py:1396-1421 (or-Cases).

- **Iterator exhaustion (one-shot generators)** — Python: `g = (x
  for x in [1,2,3]); list(g); list(g)` returns `[[1,2,3], []]` —
  generators, `zip`, `map`, `filter` are one-shot. PSDL's
  `_compile_for` at psdl.py:860-877 emits
  `ListInduction(var=x, nil_proof=Refl(_nil), cons_proof=<body>)`
  unconditionally; the iterable identity (`stmt.iter`) is captured
  only via `iter_text = ast.unparse(stmt.iter)` and never inspected
  for type. **Soundness consequence**: a user iterates a generator
  twice and proves the body holds for every element of the second
  iteration; `ListInduction` produces a witness that quantifies
  cons-style over an exhaustive list, so the kernel proof
  "establishes" the body for every list element. The runtime second
  iteration is empty — vacuously true at runtime, but the kernel
  proof actively *commits* to elements PSDL claims to cover. A
  caller of the proof who assumes "for all x in g, P(x)" gets
  false witnesses. **Fix surface**: psdl.py:864 — `iter_text =
  ast.unparse(stmt.iter)` is the only place the iterable is touched.

- **Mutable default arguments** — Python: `def f(x=[]): x.append(1);
  return x` accumulates state across calls because `x=[]` is
  evaluated *once* at `def` time. PSDL's `_compile_function_def` at
  psdl.py:644-677 walks the body recursively but never inspects
  `stmt.args.defaults`. There is no model of "default args evaluated
  once at def time"; PSDL implicitly assumes each call is fresh.
  **Soundness consequence**: a user proves "`f()` returns a list of
  length 1" by reasoning about the body assuming `x` is fresh `[]`;
  the second call returns `[1, 1]`. The proof is wrong on every
  call after the first. **Fix surface**: psdl.py:644 — defaults are
  never read.

- **`break` / `continue` silently dropped** — `_compile_stmt` at
  psdl.py:539-584 has no handler for `ast.Break` / `ast.Continue`;
  they fall through to the catch-all at psdl.py:578-584 which
  *registers an error* in `self.errors` — but the surrounding `for`
  loop's `ListInduction` was already constructed at psdl.py:860-877
  with a `cons_proof` that quantifies the body over every iteration.
  Per Appendix A, the kernel may receive a complete ProofTerm
  alongside the error list, so consumers that don't check
  `result.ok` are exposed. **Soundness consequence**: any consumer
  ignoring the error list takes the kernel proof at face value.
  Even with the error list checked, the kernel proof — once handed
  to downstream tactics or composition operators — claims the body
  holds for every element of the cons-list, when at runtime the
  loop terminates early. **Fix surface**: psdl.py:539-577 (no
  Break/Continue handler) + psdl.py:872 (`cons_proof` built without
  control-flow analysis).

- **`finally` always runs but never compiled** — `_compile_try` at
  psdl.py:812-857 reads `stmt.body` and iterates `stmt.handlers`;
  it never accesses `stmt.finalbody` nor `stmt.orelse`. Python's
  `finally` runs even when the `try` body has `return`, `break`,
  `continue`, or re-raises, and even when an exception is uncaught
  (it runs *before* the exception propagates). **Soundness
  consequence**: a `finally` clause that mutates state (e.g. closes
  a file, releases a lock, decrements a refcount) is invisible. A
  proof "after this `try`, the lock count is 1" while the `finally`
  calls `release()` (decrementing to 0) is proved-true in PSDL and
  false at runtime. Generator finalisation (`try/finally` in
  generator bodies) is doubly invisible: the generator handler is
  missing entirely. **Fix surface**: psdl.py:828-857 — never reads
  `stmt.finalbody` or `stmt.orelse`.

- **`for/else` and `while/else` clauses silently dropped** —
  Python's `else` after a loop runs iff the loop *did not* break.
  PSDL's `_compile_for` at psdl.py:860-877 reads `stmt.body` only;
  `_compile_while` at psdl.py:880-901 same. **Soundness
  consequence**: a user puts the "found-the-element" path in the
  for-body and the "not-found" path in the `else:` clause — PSDL
  ignores `else:` and proves "the property holds for some element"
  assuming the loop is exhaustive. Wrong when an early break
  aborted before the property held. **Fix surface**: psdl.py:864 /
  897 — `stmt.orelse` never read.

- **Implicit exception chaining (`__context__`)** — Python: a `raise`
  inside an `except` body sets `__context__` to the original
  exception (PEP 3134), and `raise X from Y` sets `__cause__`.
  `_compile_raise` at psdl.py:1032-1052 reads only `stmt.exc`;
  `stmt.cause` is silently dropped (the `from` clause is invisible).
  Worse, `_compile_raise` has no awareness of being *inside* an
  `except` body — `_compile_try` at psdl.py:812-857 doesn't pass
  any context flag through `compile_block`. **Soundness
  consequence**: a proof reasoning about the exception's
  `__cause__` or `__context__` (e.g., "this error has no cause")
  succeeds in PSDL but the runtime exception carries the implicit
  context. Inverse: a user-written wrapper that rewraps an
  exception (`raise CustomError() from original`) loses the
  chaining link in PSDL. **Fix surface**: psdl.py:1032-1052 (raise)
  + psdl.py:812-857 (try) — they don't communicate.

- **`__r*__` operator fallback** — Python: `a + b` calls
  `a.__add__(b)`; on `NotImplemented`, falls back to `b.__radd__(a)`.
  `+` / `-` / `/` / `//` / `%` / `<<` / `>>` / `&` / `|` / `^` and
  in-place forms all have reflected fallbacks. PSDL's `BinOp`
  handler at psdl.py:1207-1259 only handles proof-composition
  operators; other binops fall through to "unsupported expression"
  at psdl.py:1491-1499. The user's class-level `__add__` /
  `__radd__` is invisible. Even when PSDL does handle a binop —
  e.g. `f * p` at psdl.py:1221-1228 — it constructs `Ap(function,
  path)` without checking whether `f` even has a `__mul__`; a class
  with no `__mul__` would fall through to `__rmul__` at runtime,
  yielding a different value. **Soundness consequence**: a proof
  using PSDL's commutativity assumption (`a + b = b + a`) is wrong
  if either operand has a non-commutative `__add__`. The catch-all
  error at least surfaces the gap for user-class arithmetic, but
  PSDL's hardcoded sugar for `*` is silent. **Fix surface**:
  psdl.py:1207-1259.

- **`__iadd__` vs `__add__`** — Python: `x += y` calls
  `x.__iadd__(y)` (in-place) if defined, else falls back to `x =
  x + y`. For mutable types (list, set, bytearray) `__iadd__`
  *mutates and rebinds* the same object; for immutable types (int,
  str, tuple) it creates a new object. PSDL doesn't model
  `ast.AugAssign` at all (no handler in psdl.py:539-584; falls
  through to catch-all). **Soundness consequence**: a proof using
  `xs += [1]` (mutates the list aliased elsewhere) treats it as
  `xs = xs + [1]` (creates a new list) — every aliased reference
  diverges. **Fix surface**: psdl.py:539-584 — no AugAssign
  handler.

- **`is` vs `==`** — Python: `a is b` compares identity, `a == b`
  compares value via `__eq__`. They differ for `[] is []` (False)
  but `[] == []` (True), and surprisingly often agree for small
  ints due to interning (`256 is 256` is True in CPython but
  `257 is 257` may be False). PSDL has *no* `Compare` handler at
  expression level (per § 3 — all 10 compare ops MISSING).
  However, `Compare` nodes inside `if` tests, `assert` claims,
  `while` conditions are passed to Z3 as *strings* via
  `ast.unparse(stmt.test)` (see psdl.py:780, 949, 892). Z3's
  arithmetic theory doesn't model `is` — it sees both as `=`.
  **Soundness consequence**: `assert a is b, "z3"` produces the
  same Z3 obligation as `assert a == b`, but the obligations differ
  at runtime. A user who *needs* identity (e.g., for sentinel
  checking) gets misleadingly-discharged Z3 obligations. **Fix
  surface**: psdl.py has no Compare expression handler at all.

- **Truthiness of non-bool tests** — Python: `if []`, `if 0`,
  `if None`, `if ""`, `if {}`, `if 0.0` are all False; custom
  classes consult `__bool__` then fall back to `__len__`. PSDL's
  `_compile_if` at psdl.py:776-792 either dispatches to the
  `isinstance` fibre handler or emits a generic `Cases(scrutinee=
  Var(test_text), branches=[("then", ...), ("else", ...)])` with
  Lean `by_cases h : <test>`. Lean's `by_cases` requires a
  decidable proposition; PSDL silently coerces an arbitrary
  expression. The `__bool__` / `__len__` dispatch is invisible.
  **Soundness consequence**: `if my_obj:` where `my_obj.__bool__`
  is overridden produces a `Cases` whose branches are taken by
  the *truthy text*, not the runtime dispatch. A proof "in the
  `then` branch, `my_obj is not None`" is wrong if `__bool__`
  returns False on a non-None object. **Fix surface**:
  psdl.py:776-792.

- **Branch-conditional definite assignment** — Python: `if c: x =
  1; print(x)` raises `UnboundLocalError` if `c` is False (and
  `x` wasn't bound before). PSDL's `_compile_if` at
  psdl.py:776-809 builds two `Cases` branches independently;
  `compile_block` at psdl.py:530-535 then chains the surrounding
  statements via `Cut` *as if `x` is in scope*. The kernel has no
  definite-assignment analysis. The bare-name handler at
  psdl.py:1501-1509 maps any unknown name to `AxiomInvocation(name=
  nm, module="")` — even names that don't exist:
  ```
  self._emit_lean(indent, f"exact {_safe(nm)}")
  return AxiomInvocation(name=nm, module="")
  ```
  **Soundness consequence**: a user proves "after the `if`, `x =
  1`" via Cut chain; runtime raises NameError. The "axiom"
  invocation produces a kernel-side trust signal for a name that
  doesn't even exist. **Fix surface**: psdl.py:530-535 + 1501-1509.

- **Comprehension scope leakage / walrus leak** — Python 3 wraps
  comprehensions in an implicit nested function: `[x for x in xs]`
  does *not* leak `x` to enclosing scope, but the *iterable
  expression* is evaluated in the enclosing scope. Walrus *inside*
  a comprehension *does* leak (PEP 572). PSDL's `ast.ListComp`
  handler at psdl.py:1273-1290 ignores scope entirely. The
  walrus handler at psdl.py:1174-1187 builds a Cut treating the
  binding as scope-local, never extending the ambient context for
  subsequent statements. **Soundness consequence**: a user writes
  `[(x := f(i)) for i in xs]` and then references `x` afterwards;
  PSDL's Cut for the walrus is *inside* the ListInduction's
  `cons_proof` and doesn't extend to the outer block. Conversely,
  a user references a comprehension binder `i` in the enclosing
  scope (which Python forbids); PSDL's bare-name handler turns it
  into an `AxiomInvocation` placeholder. **Fix surface**:
  psdl.py:1174-1187 + 1273-1290.

- **`with` context manager exception suppression** — Python:
  `__exit__(exc_type, exc_val, tb)` returning truthy *suppresses*
  the exception. `_compile_with` at psdl.py:715-773 only
  recognises three named-call heads (`goal`, `case`,
  `hypothesis`); generic `with foo():` falls through to
  psdl.py:771-773 which emits a `-- with <expr>:` comment and
  recurses into the body unconditionally. The exit protocol is
  invisible. Also: `stmt.items[0]` is the only withitem read
  (psdl.py:725) — `with A, B:` drops B entirely. The `optional_vars`
  field (the `as` binding) is never read. **Soundness
  consequence**: a user wraps an exception-throwing call in
  `with suppress(ValueError): ...` and asserts "no exception was
  raised" — PSDL accepts the assertion, but the exception was
  raised and suppressed. Conversely: `with lock: ...` where the
  body throws — PSDL's recursion into the body builds a proof
  assuming linear flow; the lock release on exception is invisible.
  **Fix surface**: psdl.py:715-773.

- **`__getattr__` / `__getattribute__` / descriptors** — Python's
  attribute lookup: data descriptor in MRO → instance dict →
  non-data descriptor → `__getattr__` fallback. PSDL's attribute
  postfix handler at psdl.py:1143-1172 only special-cases literal
  attr names (`symm`, `inv`, `lhs`, `rhs`, `sides`, `unfold`,
  `rewrite`); arbitrary `obj.attr` falls through to the catch-all
  via the surrounding `_compile_method_call` (psdl.py:1522-1571).
  Either way, `@property foo` is invisible: the same `obj.foo`
  reference produces the same kernel artefact whether `foo` is a
  data field or a property doing arbitrary computation.
  **Soundness consequence**: a class with a stateful `@property`
  (e.g., a counter that increments on each access); a proof
  "`obj.foo` is constant" succeeds in PSDL while at runtime the
  property recomputes. `__getattribute__` overrides (which run for
  *every* attribute access) are doubly invisible. **Fix surface**:
  psdl.py:1143-1172.

- **Method resolution order (MRO) and `super()`** — Python: C3
  linearisation governs which method gets called for diamond
  inheritance; `super()` (zero-arg form, Py3) consults
  `__class__` and the first arg via lexical lookup. PSDL's
  `dispatch` handler at psdl.py:1948-1962 emits
  `DuckPath(type_a=PyObjType(), type_b=PyObjType(),
  method_proofs=[(meth_text, Refl(Var(_safe(recv))))])` —
  `type_a`/`type_b` are unitary `PyObjType` (the actual classes
  aren't tracked); the binding is stringly-typed. The actual MRO,
  `super()` chain, and `__mro_entries__` (PEP 560) are not
  modelled. **Soundness consequence**: for a diamond
  `class D(B, C): pass` where `B` and `C` both define `foo`, a
  user can prove "the method called for `D().foo()` is `B.foo`"
  while C3 picks `C.foo` (depending on order). **Fix surface**:
  psdl.py:1948-1962.

- **`isinstance` with virtual subclasses (ABCMeta) and Union** —
  Python: `isinstance(x, (A, B))` (tuple-of-types),
  `isinstance(x, Union[A, B])`, and `__instancecheck__` overrides
  (e.g. `numbers.Real`, `abc.ABCMeta`) all change fibre semantics
  via virtual subclass registration. PSDL's `_is_isinstance_test`
  at psdl.py:698-712 recognises only the two-argument form
  `isinstance(var, T)` where both args are Names; tuples-of-types
  and Union forms fall through to the generic-if handler at
  psdl.py:776-792. A `Real.register(C)` virtual subclass is not
  recognised. **Soundness consequence**: a user proves "this fibre
  is empty for `C`" (because `C` doesn't textually subclass
  `Real`); `Real.register(C)` was called at module init, making
  `isinstance(c, Real)` True at runtime. PSDL's fibre claims
  emptiness; runtime says non-empty. **Fix surface**:
  psdl.py:698-712 + 776-792.

- **Subscript assignment** — Python: `a[0] = 1` calls
  `a.__setitem__(0, 1)`; for slices, `a[1:5:2] = [...]` is slice
  assignment via `__setitem__(slice(1, 5, 2), [...])`. PSDL's
  `_compile_assign` at psdl.py:1077-1126 only handles single-Name
  and Tuple/List targets; `ast.Subscript` and `ast.Attribute`
  targets fall through to `Structural("non-name assign")` at
  psdl.py:1116. **Soundness consequence**: a user mutates `a[0] =
  new_value` and asserts `a[0] == new_value`; PSDL ignores the
  mutation (the assignment is parsed-only structural). The
  `Structural` doesn't introduce a Cut, so the kernel state is
  unchanged — the assertion asserts the *original* `a[0]`.
  **Fix surface**: psdl.py:1115-1116.

- **`del` statement** — Python: `del x` removes the binding;
  `del a[k]` calls `__delitem__`; `del obj.attr` calls
  `__delattr__` / `__delete__`. None handled in `_compile_stmt`
  at psdl.py:539-584 (no `ast.Delete` case). Falls through to
  catch-all + `sorry`. The surrounding `Cut` chain still has `x`
  bound, and `_compile_name_ref` at psdl.py:1501-1509 still maps
  references to `x` after `del` to an `AxiomInvocation`.
  **Soundness consequence**: a "proof" using `x` after `del x`
  succeeds in PSDL; runtime raises `NameError`. Worse, `del a[k]`
  triggering a custom `__delitem__` with side effects is
  invisible. **Fix surface**: psdl.py:539-584 — no Delete handler.

### Common-idiom gaps (Python programmers expect these to work)

- **`break` / `continue`** — silently dropped; `_compile_stmt` has
  no handler at psdl.py:539-584. Falls through to catch-all.
  (Already covered in soundness section; restated here as it is
  the most common idiom that surprises users.)

- **`yield` / `yield from`** — `ast.Yield` / `ast.YieldFrom` not
  handled at psdl.py:1133-1499 in `_compile_expr`. Falls through
  to catch-all. Generators-as-tactics aren't a concept in PSDL.
  Generator finalisation, `send()` / `throw()` / `close()`, and
  generator-specific `try/finally` semantics are all invisible.

- **`async def` / `await` / `async for` / `async with`** —
  `ast.AsyncFunctionDef` not in dispatcher at psdl.py:539-584;
  `ast.Await`, `ast.AsyncFor`, `ast.AsyncWith` similarly absent.
  `_compile_function_def` at psdl.py:644 is keyed on
  `ast.FunctionDef` only. Coroutine suspension semantics, event
  loop, and async generator protocol are all absent.

- **`global` / `nonlocal`** — `ast.Global` / `ast.Nonlocal`
  declarations not handled at psdl.py:539-584. PSDL's Cut-chain
  treats every name as locally bound. LEGB scoping (Local →
  Enclosing → Global → Builtin) is not modelled at all; nested
  `def`s call `compile_block(stmt.body, indent+1)` without binder
  introduction, so free variables resolve against the same
  `foundations` dict (psdl.py:1501-1509).

- **`AugAssign` (`+=`, `-=`, etc.)** — `ast.AugAssign` not handled
  at psdl.py:539-584. Falls through. The `__iadd__` (in-place) vs
  `__add__` (creating new) dispatch is invisible.

- **f-string format specs / conversions** — psdl.py:1468-1474 has
  a `JoinedStr` case but only emits a Lean comment via
  `ast.unparse`. The `__format__` protocol, format-spec strings
  (`f"{x:.2f}"`), and `!r` / `!s` / `!a` conversions are not
  modelled. The interpolated values aren't compiled as proofs.

- **Lambda standalone proofs** — psdl.py:1478-1485 returns
  `Structural(f"lambda({arg_names})")` without compiling the
  body. Any tactical content inside a lambda (e.g.
  `lambda i: refl(i)`) is dropped. Combined with the late-
  binding gap above, this means lambdas are effectively opaque.

- **`assert` with non-string `msg`** — psdl.py:925-948 only
  handles `ast.Constant` with `isinstance(value, str)` for the
  `msg` argument:
  ```
  if stmt.msg is not None:
      if isinstance(stmt.msg, ast.Constant) and isinstance(
          stmt.msg.value, str,
      ):
          tag = stmt.msg.value.strip()
          ...
  ```
  `assert P, my_var` and `assert P, f"..."` fall through to the
  default `mode = "z3"` branch silently — the user's intended
  discharge mode is ignored.

- **List literals as expressions** — `[f(), g()]` evaluates
  left-to-right with side effects. PSDL's `ast.List` is MISSING
  in `_compile_expr` (per § 2). `ast.Tuple` handler at
  psdl.py:1369-1373 returns `inners[-1]`, dropping all but the
  last; the dropped inners *are* compiled (so the kernel sees
  their proof terms, but they're tossed) — at runtime side
  effects of `f()` and `g()` happen, but PSDL's proof artefact
  only captures `g()`.

- **Star-unpacking in calls** — `f(*args, **kwargs)` evaluates
  args in order. `ast.Starred` at psdl.py:1489-1490 unwraps to
  the inner expr only — the iteration semantics is gone. Dict-
  spread `{**a, **b}` collisions (later keys win) not modelled
  (psdl.py:1446-1448 silently filters None-keyed entries).

- **`set` literals** — `ast.Set` not handled in `_compile_expr`
  (psdl.py:1133-1499 has only `ast.Dict`). Falls through to
  catch-all.

- **Bound methods vs unbound** — `obj.method` (bound) vs
  `Class.method` (unbound function in Py3, descriptor lookup).
  PSDL's attribute postfix at psdl.py:1143-1172 doesn't
  distinguish. The `Class.method(obj, x) == obj.method(x)`
  identity is correct semantically but not carried by PSDL's
  artefacts.

- **`__init__` after `__new__`** — Python's two-stage
  construction. `_compile_class_def` at psdl.py:587-642 handles
  `@inductive` / `@protocol` / plain class but never models the
  metaclass `__call__` → `__new__` → `__init__` chain. A
  `@dataclass`-style `__post_init__` is invisible.

- **`__slots__`** — restricts attribute set; not modelled in
  `_compile_class_def` at psdl.py:587-642. PSDL never reads
  the class body for `__slots__`.

- **Function attributes** — `def f(): ...; f.attr = 1` after the
  def is `ast.Assign` with `ast.Attribute` target on a function
  name. Falls through to `Structural("non-name assign")` at
  psdl.py:1116.

- **Slice expressions** — `a[1:5:2]` produces `ast.Slice` inside
  `ast.Subscript`. PSDL's Subscript handler at psdl.py:1295-1367
  dispatches only on the *head* identifier (`Refl`, `Path`,
  `Pi`, ...); arbitrary slice subscripts fall through to
  `Structural(f"type-level {ast.unparse(node)}")` at
  psdl.py:1364-1367 without an error. Slice semantics —
  start/stop/step defaults, negative indices, slice-assignment —
  never reach the kernel.

- **Pattern-match guards (`case X if cond`) and class patterns
  (`case Point(x=1)`)** — `_compile_match` at psdl.py:903-913
  calls `ast.unparse(case.pattern)` and uses the unparsed string
  as the branch label:
  ```
  for case in stmt.cases:
      pat = ast.unparse(case.pattern)
      ...
      cp = self.compile_block(case.body, indent + 2)
      branches.append((pat, cp))
  ```
  `case.guard` is *never read*. The `__match_args__` protocol is
  invisible. Or-patterns produce one branch labelled `"A | B"`.
  Capture-vs-value (`case 0` vs `case x`) collapses to text,
  losing the binding-vs-test distinction. **Soundness
  consequence (re-categorise)**: a user proves the guarded branch
  body holds; PSDL takes the branch unconditionally, so the
  kernel `Cases` claims the body holds for *every* value matching
  the pattern, ignoring the guard.

- **`except (A, B)` tuple form / `except E as e`** —
  `_compile_try` at psdl.py:831-837 reads `h.type` via
  `ast.unparse`; tuple types become string `"(A, B)"`. The `as e`
  binding (`h.name`) is ignored; `e` is del'd at end of handler
  in CPython 3 but PSDL never sees the binding. A proof using
  `e.args` inside the handler has no kernel-side hypothesis for
  `e` — bare-name `e` references become `AxiomInvocation`
  placeholders.

- **`except*` exception groups (Py 3.11+, PEP 654)** — `ast.TryStar`
  not in dispatcher at psdl.py:539-584. Falls through.

- **Decorators outside the recognised set** — psdl.py:649-677
  inspects only `axiom` / `theorem`; arbitrary decorators
  (`@functools.wraps`, `@classmethod`, `@staticmethod`,
  `@property`, custom decorators with side-effects) are
  silently ignored. `@property foo` is treated as a plain
  method def — descriptor protocol invisible.

- **Number tower** — Python: `int / int → float`; `int // int →
  int`; `bool ⊆ int` (so `True + True == 2`); promotion to
  `Fraction`/`Decimal`/`complex`. PSDL has no arithmetic typing
  in `BinOp` beyond proof-overloaded operators (psdl.py:1207-
  1259). A Z3 obligation `assert (3/2) == 1, "z3"` is sent
  verbatim; Z3's interpretation depends on its sort assignment,
  which doesn't track Python's `__truediv__` vs `__floordiv__`
  semantics.

- **Module import / circular imports** — `_compile_stmt`
  recognises `ast.ImportFrom` at psdl.py:566-571 (and only as
  foundation registration). Plain `import x` (`ast.Import`) is
  MISSING. Top-level execution at import time, partial module
  objects during circular imports, `__init__.py` semantics —
  all invisible.

- **`__init_subclass__` / `__set_name__` / metaclass `__call__`**
  — none modelled. `ClassDef.keywords` (the `metaclass=` slot)
  is never read.

- **String semantics** — `bytes` vs `str`, encoding/decoding,
  Unicode normalisation, the `__contains__` for `in str`/`in
  bytes`. `ast.Constant` with `bytes` value falls into the
  generic constant branch at psdl.py:1438-1441 → `Refl(Var(...))`
  with the repr in the var name. Not distinguished from `str`.

### Niche / out-of-scope (treatise should disclaim)

- **GIL and threading** — PSDL doesn't model concurrency.
  `threading.Lock`, atomic operations (CPython does guarantee
  some atomicity for single bytecode instructions),
  `threading.local` — all invisible. Race conditions and memory
  model issues are out of scope.

- **Pickle / deepcopy / `__reduce__`** — not modelled.

- **`weakref`** — not modelled. Aliasing via weakref would
  mislead any identity reasoning.

- **NaN / -0.0 IEEE quirks** — `nan != nan`, `0.0 == -0.0` but
  `1/0.0 != 1/-0.0`. Z3 obligations sent as strings; float
  semantics depend on Z3's sort. PSDL doesn't intervene.

- **Bytecode optimisation / peephole** — `1 + 2` may be folded
  to `3` at compile time. PSDL's `_compile_expr` at psdl.py:1207-
  1259 doesn't constant-fold. AST-level vs Python-level term
  equality can disagree (usually benign).

- **`__del__` and reference counting** — finalisation order,
  GC cycles. PSDL has no notion of object lifetime.

- **`sys.setrecursionlimit` and stack overflow** — runtime
  resource bounds invisible.

- **`sys.exc_info()` / `traceback`** — exception introspection
  invisible.

- **`__match_args__`** — class patterns consult `__match_args__`;
  PSDL treats patterns as ast.unparse strings (psdl.py:909).

### Operator-semantic gaps

- **`__r*__` fallback** — `a + b` failing through `a.__add__` to
  `b.__radd__` on `NotImplemented` isn't modelled; PSDL's `BinOp`
  handler at psdl.py:1207-1259 either special-cases proof
  composition operators or falls through. A proof of `a + b = b +
  a` based on PSDL's commutativity assumption is wrong if either
  operand has a non-commutative `__add__`.

- **`__iadd__` vs `__add__`** — see soundness section. `+=`
  semantically rebinds-or-mutates; PSDL has no AugAssign handler
  at psdl.py:539-584.

- **Comparison chaining `a < b < c`** — Python expands to
  `a < b and b < c` with `b` evaluated **once** (CPython
  guarantees single-eval). PSDL has no `Compare` handler; the
  `ast.unparse` of a chained comparison goes verbatim into Z3 or
  Lean, which don't natively support Python's chained-compare
  form.

- **`__contains__` for `in`** — `x in c` calls
  `c.__contains__(x)` if defined, else falls back to iteration
  invoking `__iter__` and `__eq__`. PSDL has no
  `ast.Compare(ops=[In])` handler. `assert x in xs, "z3"` is
  sent to Z3 as a string `"x in xs"` which Z3 doesn't understand.

- **`__bool__` / `__len__` fallback for `not x`** —
  `ast.UnaryOp(Not)` at psdl.py:1199-1206 emits
  `Structural(f"negation of ...")` — no decidability is checked,
  no `__bool__` dispatch.

- **`__hash__` and dict-key identity** — PSDL has no model of
  hash semantics; reasoning about dict membership is opaque.
  Custom `__hash__` overrides and the hash/eq contract (objects
  that are `==` must have the same `__hash__`) are invisible.

- **`__eq__` reflexivity / `__lt__` non-strict-total-order** —
  Python doesn't enforce that `==` is reflexive or that `<` is a
  strict total order. NaN famously breaks both. PSDL implicitly
  assumes Z3's equality theory, which *is* reflexive — wrong for
  user classes with custom `__eq__`.

- **Operator on subclasses of `int`/`bool`** — `bool` is a
  subclass of `int`, so `True + True == 2`, `True * 3 == 3`.
  PSDL has no number-tower modelling; `True + True` would be
  sent to Z3 as a string and depends on Z3's coercion.

- **Walrus precedence in expressions** — `(x := f()) + g(x)`
  evaluates `f()` first, binds `x`, then evaluates `g(x)`. PSDL's
  `NamedExpr` at psdl.py:1174-1187 builds a `Cut` but doesn't
  model that the binding *escapes* the enclosing expression. The
  Cut's `body_proof=Refl(Var(_safe(target.id)))` claims the
  walrus-bound name is the proof artefact, but doesn't extend the
  ambient context for subsequent statements at the same lexical
  scope.

### Summary count (section 8)

- **Soundness-relevant**: 19 items
- **Common-idiom gaps**: 22 items
- **Niche/out-of-scope**: 9 items
- **Operator-semantic**: 9 items

Each item is keyed to a `psdl.py` line range in the cited handler, or
explicitly marked "no handler" / "MISSING" when the AST node never
reaches `_compile_stmt` / `_compile_expr` and falls through to the
catch-all at psdl.py:578-584 (statement) or psdl.py:1491-1499
(expression).

The pattern: PSDL is an *AST-shaped* compiler. Any property that
requires runtime inspection — heap state, dispatch tables, identity,
exception context, default-arg evaluation time — is invisible by
construction. The treatise's framing ("Python-shaped tactics") is
honest about syntax coverage but understates the semantic gulf: the
same Python source maps to wildly different runtime behaviours, and
PSDL only ever sees the source.
