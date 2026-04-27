# PSDL implementation audit (treatise vs psdl.py)

Sources audited:

- Treatise: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/docs/psdl_treatise/ch06_psdl.tex`
- Implementation: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/deppy/proofs/psdl.py` (1993 lines, the docstring at lines 1-446 is the second authoritative description)
- Kernel ProofTerm vocabulary: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/deppy/core/kernel.py`
- Sidecar integration: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/deppy/lean/sidecar_verify.py`
- Example: `/Users/halleyyoung/Documents/div/mathdivergence/deppy/sympy_geometry.deppy:492`

The treatise cites concrete line ranges in psdl.py (e.g. "lines 609-642"). Those ranges are now off by ~150 lines because the file grew to 1993 lines. The audit reports the *current* line numbers.

---

## A. Implemented (treatise description matches reality)

### Control flow

- **`if isinstance(x, T)`** — handler `_compile_if` at psdl.py:776-809; calls `_is_isinstance_test` at psdl.py:698-712, emits `Fiber(scrutinee=Var(x), type_branches=[(PyObjType(), then), (PyObjType(), else)], exhaustive=bool(stmt.orelse))`. Lean tactic: `by_cases h : isinstance x T`, with bulleted `·` arms for value- and complement-fibres. Matches ch06_psdl.tex § 6.3.1 (lines 91-127).

- **`if <generic test>`** — handler psdl.py:776-792. Falls through to `Cases(scrutinee=Var(test_text), branches=[("then", ...), ("else", ...)])`. Lean: `by_cases h : <test>`. Matches ch06_psdl.tex § 6.3.1 fall-through case (lines 116-126).

- **`try / except`** — handler `_compile_try` at psdl.py:812-832. Wraps the try-body in `EffectWitness(effect="value", proof=...)` then folds each handler into a `ConditionalEffectWitness(precondition="raises Exc", effect="exception", proof=hp, target=exc_name)`. Lean emits `-- try block (effect modality)` comment + handler body inline. Matches § 6.3.2 (lines 128-148).

- **`for x in xs`** — handler `_compile_for` at psdl.py:835-852. Emits `ListInduction(var=x, nil_proof=Refl(Var("_nil")), cons_proof=<body>)`. Lean: `induction xs with | nil => rfl | cons _ _ ih =>`. Matches § 6.3.3 (lines 149-160).

- **`while n`** — handler `_compile_while` at psdl.py:855-862. Emits `NatInduction(var="n", base_proof=Refl(Var("_zero")), step_proof=<body>)`. Matches § 6.3.3 (lines 162-170).

- **`match x: case A: ... case B: ...`** — handler `_compile_match` at psdl.py:865-874. Emits `Cases(scrutinee=Var(scrutinee), branches=[(pat, proof), ...])` and Lean `match x with | A => ... | B => ...`. Matches § 6.3.4 (lines 172-185).

- **`pass`** — psdl.py:561-563. Emits `Structural("trivial")`, Lean `trivial`. Matches docstring lines 140 and § 6.4.4 (line 251).

### Logical / equality

- **`assert P, "z3"` (and bare `assert P`)** — handler `_compile_assert` at psdl.py:877-944. For `mode == "z3"` emits `Cut(hyp_name=f"h_{lineno}", hyp_type=RefinementType(base_type=PyBoolType(), predicate=claim), lemma_proof=Z3Proof(formula=claim, binders={}), body_proof=Refl(Var("_assert_body")))`. Lean: `have h_<lineno> : <P> := by omega -- z3-discharged`. Matches § 6.4.1 (lines 192-211).

- **`assert P, "by F"`** — psdl.py:914-931. Builds `Cut(...lemma_proof=AxiomInvocation(name=cite, module="foundations"), ...)` and Lean `have h_<n> : P := Foundation_<F>`. Records the foundation in `foundations_referenced`. Matches § 6.4.1 (lines 207-211).

- **`assert P, "by lemma L"`** — psdl.py:932-943. Builds `Cut(...lemma_proof=AxiomInvocation(name=cite, module=""), ...)`. Lean: `have h_<n> : P := L`. Matches § 6.4.1 (lines 209-211).

- **`apply(F)`** — handler in `_compile_func_call` at psdl.py:1305-1314. Returns `AxiomInvocation(name=target, module="foundations" if registered else "")`. Lean: `exact Foundation_F` or `exact F`. Matches § 6.4.2 (lines 215-226).

- **bare-name citation `F`** — handler `_compile_name_ref` at psdl.py:1229-1237. Same `AxiomInvocation` mapping. Matches § 6.4.2.

- **`unfold(method)`** — psdl.py:1316-1322. Emits `Unfold(func_name=target, proof=Refl(Var("_b")))` with Lean `unfold method`. Matches § 6.4.3 (lines 230-246).

- **`method.unfold()` (method-call alias)** — psdl.py:1255-1257 (method-call branch) and psdl.py:1045-1049 (no-args attribute branch). Emits `Unfold(func_name=recv, proof=Refl(Var(recv)))`. Matches § 6.4.3.

- **`inline(method, expected_expr)`** — psdl.py:1324-1336. Emits `Unfold(func_name=target, proof=Refl(Var(_safe(expected))))`. Lean: `unfold method  -- expected: <expected>`. Matches § 6.4.3 (line 238-242).

- **`rewrite(L)`** — psdl.py:1338-1344. Emits `Rewrite(lemma=AxiomInvocation(name=target, module=""), proof=Refl(...))`. Lean: `rw [<L>]`. Matches § 6.4.3.

- **`L.rewrite()` alias** — psdl.py:1258-1263 (method-call) and psdl.py:1050-1055 (attribute). Both emit `Rewrite(...)`. Matches § 6.4.3.

- **`return expr`** — handler `_compile_return` at psdl.py:947-953. Emits `Refl(Var(_safe(text)))` and Lean comment + `rfl`. Matches § 6.4.4 (lines 250-259).

- **`raise NotImplementedError`** — handler `_compile_raise` at psdl.py:956-972. Emits `Structural(f"vacuous: {exc_text}")` with Lean `exact absurd ‹_› (by simp)`. Matches § 6.4.4 (lines 261-268).

- **`raise <other Exception>`** — psdl.py:966-972. Emits `ConditionalEffectWitness(precondition=f"raises {exc_text}", effect="exception", proof=Structural(...), target=exc_text)`. Documented as exception-fibre marker.

- **annotated assignment `h: T = expr`** — handler `_compile_ann_assign` at psdl.py:975-994. Emits `Cut(hyp_name=h, hyp_type=RefinementType(PyBoolType(), predicate=ty), lemma_proof=<inner>, body_proof=Refl(Var("_ann_body")))`. Lean: `have h : T := <RHS>`. Matches § 6.4.5 (lines 270-281).

- **`lemma(name, statement, by)`** — psdl.py:1393-1413. Builds `Cut(hyp_name=lname, hyp_type=RefinementType(...), lemma_proof=AxiomInvocation(name=by_clause), ...)` and Lean `have <name> : <stmt> := <by>`. Matches § 6.4.5 (lines 283-286).

### CIC core

- **`forall(x, T, body)`** — psdl.py:1477-1491. Emits `Cut(hyp_name=xv, hyp_type=RefinementType(PyObjType(), predicate=tt), lemma_proof=Assume(name=xv), body_proof=<body>)` and Lean `intro (x : T)`. Matches § 6.5.1 (lines 297-308).

- **`exists(x, T, witness, body)`** — psdl.py:1493-1510. Emits `Cut(...lemma_proof=Refl(Var(_safe(wn))), body_proof=<body>)` and Lean `refine ⟨witness, ?_⟩`. Matches § 6.5.1 (lines 310-313).

- **`refl(x)`** — psdl.py:1511-1518. Emits `Refl(Var(_safe(tx)))` and Lean `rfl`. Matches § 6.5.2.

- **`sym(eq)`** — psdl.py:1519-1525. Emits `Sym(proof=<inner>)` and Lean `exact (eq).symm`. Matches § 6.5.2 (line 324).

- **`trans(eq1, eq2)`** — psdl.py:1526-1536. Emits `Trans(left=a, right=b)` and Lean `exact (eq1).trans (eq2)`. Matches § 6.5.2 (line 325).

- **`subst(eq, motive, body)` and `rew(eq, body)`** — psdl.py:1547-1569. Both emit `Rewrite(lemma=AxiomInvocation(name=eq_text), proof=<inner>)` and Lean `rw [eq]`. Matches § 6.5.2 (lines 327-328).

- **`induction(n, base=..., step=...)`** — psdl.py:1571-1588. Emits `NatInduction(var=target, base_proof=base_pf, step_proof=step_pf)`. Lean: `induction n with`. Matches § 6.5.1 (lines 315-318).

- **`path_concat(p, q)`** — psdl.py:1590-1599. Emits `PathComp(left_path=a, right_path=b)` and Lean `exact (p).trans (q)`. Matches § 6.5.3 (lines 339-348).

- **`path_inv(p)`** — psdl.py:1600-1607. Emits `Sym(proof=a)` and Lean `exact (p).symm`. Matches § 6.5.3.

- **`path_ap(f, p)`** — psdl.py:1608-1617. Emits `Ap(function=Var(_safe(fn_text)), path_proof=p)` and Lean `exact congrArg f p`. Matches § 6.5.3.

- **`J(motive, refl_case, x, y, p)`** — psdl.py:1619-1635. Emits `TransportProof(type_family=Var(_safe(motive_text)), path_proof=AxiomInvocation(name=p_text, module=""), base_proof=refl_pf)` and Lean `exact @Eq.rec _ _ <motive> <refl> _ <p>`. Matches § 6.5.3 (lines 350-358).

- **`equiv_to_path(e)`** — psdl.py:1656-1670. Builds `TransportProof(type_family=Var("_motive"), path_proof=AxiomInvocation(name="ua", module="psdl_local"), base_proof=<inner>)`. Matches § 6.5.4 (lines 372-378).

- **`transport(p, value)`** — psdl.py:1346-1357. Emits `TransportProof(type_family=Var(f"motive_{p}"), path_proof=AxiomInvocation(name=p, module=...), base_proof=Refl(Var(_safe(v))))`. Implementation present, matches docstring section "Path / homotopy" (line 128-132).

- **`funext(...)`** — psdl.py:1359-1361. Returns `FunExt(var="x", pointwise_proof=Refl(Var("_p")))`. Lean: `funext x`. Documented in docstring line 130.

### Cubical / duck / effect

- **`dispatch(receiver, "method")`** — psdl.py:1675-1689. Emits `DuckPath(type_a=PyObjType(), type_b=PyObjType(), method_proofs=[(meth_text, Refl(Var(_safe(recv))))])` and Lean `exact DuckPath_resolve recv "method"`. Matches § 6.6.1 (lines 387-398).

- **`cocycle(level, witness)`** — psdl.py:1711-1727. Emits `Cocycle(level=lvl_int, components=[Refl(Var(_safe(wit_text)))])`. Lean: comment-only. Matches § 6.6.3 (lines 415-423).

- **`fibre_split(scrutinee, [(T, body), ...])`** — psdl.py:1729-1752. Emits `Fiber(scrutinee=Var(scrut), type_branches=[(PyObjType(), pf), ...], exhaustive=True)`. Matches § 6.6.4 (lines 426-434).

- **`bind(m, k)`** — psdl.py:1754-1769. Emits `Cut(hyp_name="m", hyp_type=PyObjType(), lemma_proof=a, body_proof=b)`. Matches § 6.6.5 (line 451).

- **`expect(m, fallback)`** — psdl.py:1770-1785. Emits `ConditionalEffectWitness(precondition="raises", effect="exception", proof=fallback_pf, target="Exception")`. Matches § 6.6.5 (line 452-453).

- **`lift(v)`** — psdl.py:1786-1795. Emits `EffectWitness(effect="value", proof=<inner>)`. Matches § 6.6.5 (line 448).

- **`lower(m, witness)`** — psdl.py:1796-1802. Returns inner proof of `m`. Matches § 6.6.5 (lines 454-455).

- **`pure()`** — psdl.py:1389-1391. Emits `Structural("pure modality")`. Matches § 6.6.5 (line 456).

- **`homotopy(p, q)`** — psdl.py:1804-1815. Emits `PathComp(left_path=<p>, right_path=<q>)`. Matches § 6.6.6 (line 466).

### Top-level decls

- **`@inductive class T:`** — `_compile_class_def` at psdl.py:587-617. Walks `AnnAssign` and `FunctionDef` members, emits Lean `inductive T where | ctor : ...` lines, returns `Structural(f"inductive T (N ctors)")`. Matches § 6.7.1 (lines 478-499).

- **`@axiom def X() -> T`** — psdl.py:653-659. Emits Lean `axiom X : T`, returns `AxiomInvocation(name=stmt.name, module="psdl_local")`. Adds to `foundations_referenced`. Matches § 6.7.2 (lines 504-516).

- **`@theorem def L() -> T:`** — psdl.py:660-674. Compiles body recursively, returns `Cut(hyp_name=name, hyp_type=RefinementType(...), lemma_proof=<body>, body_proof=Refl(...))` and Lean `theorem L : T := by ...`. Matches § 6.7.2 (lines 518-521).

### Sugar

- **walrus `(h := expr)`** — psdl.py:1057-1070. Emits `Cut(hyp_name=target.id, hyp_type=PyObjType(), lemma_proof=<inner>, body_proof=Refl(Var(_safe(target.id))))` and Lean `have h := <expr>`. Matches docstring lines 337-345.

- **`p @ q`** (matmul = path composition) — psdl.py:1090-1100. Emits `PathComp(left_path=left, right_path=right)`. Matches docstring line 328.

- **`~p`** (unary invert = symmetry) — psdl.py:1072-1080. Emits `Sym(proof=inner)`. Matches docstring line 330.

- **`f * p`** (mult = functorial action) — psdl.py:1102-1111. Emits `Ap(function=Var(_safe(fn_text)), path_proof=p)`. Matches docstring line 332.

- **`proof_a >> proof_b`** (rshift = sequential chaining) — psdl.py:1112-1121. Emits `Cut(...lemma_proof=left, body_proof=right)`. Matches docstring line 335.

- **`with goal(P)` / `with case(L)` / `with hypothesis(h, T)`** — `_compile_with` at psdl.py:715-773. The three heads emit `show <P>`, `case <L> =>`, `intro (h : T)` respectively, and the body recurses. Matches docstring lines 354-366.

- **comprehensions `[refl(x) for x in xs]` and `all(...)`** — psdl.py:1135-1152 (comprehension), psdl.py:1456-1463 (`all`/`any` wrapping). Builds `ListInduction(var=gen.target.id, nil_proof=Refl(Var("_nil")), cons_proof=elt_pf)`. Matches docstring lines 348-352.

- **`a if cond else b`** — psdl.py:1123-1133. Emits `Cases(scrutinee=Var(cond_text), branches=[("then", then_pf), ("else", else_pf)])`. Matches docstring lines 397-402.

- **`Refl[x]`** (subscript shorthand) — psdl.py:1157-1165. Recognises `node.value == "Refl"` and emits `Refl(Var(_safe(tx)))`. Matches docstring line 211.

- **closer sugar `qed()` / `auto()` / `done()` / `omega()` / `rfl_()` / `simp()` / `decide()` / `trivial()`** — psdl.py:1421-1453. Each emits a corresponding terminal Lean tactic and returns `Refl(Var("_<closer_name>"))`. Matches docstring lines 404-414.

- **postfix `eq.symm` / `path.inv` / `eq.lhs` / `eq.rhs` / `eq.sides`** — psdl.py:1026-1044. `symm`/`inv` emit `Sym(proof=AxiomInvocation(name=recv, module=""))`. `lhs`, `rhs`, `sides` emit `Structural`. Matches docstring lines 372-380.

- **postfix `eq.trans(other)`** (method-call form) — psdl.py:1264-1275. Emits `Trans(left=AxiomInvocation(name=recv), right=AxiomInvocation(name=other))`. Matches docstring line 375.

- **postfix `path.cong(f)`** — psdl.py:1276-1285. Emits `Cong(func=Var(_safe(fn_text)), proof=AxiomInvocation(name=recv))`. Matches docstring partially (cong sugar isn't in the docstring postfix list but is implemented).

- **`P and Q` / `P or Q` / `not P`** — psdl.py:1179-1203 (BoolOp and/or), psdl.py:1082-1089 (UnaryOp Not). And-chain via `Cut`s, or-emits `left` Lean tactic and returns the first inner. `not` emits a `Structural`. Matches docstring lines 416-423 (with caveats — see C below).

- **`from foundations import F1, F2`** — psdl.py:566-571. Records names in `foundations_referenced`, emits Lean `-- import ...` comment. Documented implicitly in § 6.4.

### Escape hatches

- **`lean("...raw...")`** — psdl.py:1378-1387. Emits `LeanProof(theorem="", proof_script=raw, expected_goal="", binders=(), theorem_name="", imports=())` and writes the raw text to Lean. Matches § 6.8 (lines 774-778).

- **`tactic[T](raw)`** — psdl.py:1837-1846. Emits same `LeanProof(...)` shape as `lean(...)`. Matches docstring line 310.

- **`term[T](expr)`** — psdl.py:1832-1836. Compiles inner `expr` recursively and emits `exact <expr>`. Matches docstring line 309.

- **`hint("text")`** — psdl.py:1372-1376. Stores in `hints` list, emits Lean comment, returns `Structural`. Matches docstring line 150.

- **`show_goal()` / `show_term()`** — psdl.py:1362-1370. Set flag / emit comment, return `Structural`. Matches docstring line 149.

---

## B. Described but not implemented

- **`Path[A, x, y]` as a first-class type expression** — Treatise § 6.4-6.5 references `Path[A, x, y]` as a Subscript expression that should produce a path type. Implementation at psdl.py:1157-1170 only special-cases `Refl[x]`; `Path[A, x, y]`, `Pi[x: T](B)`, `Sigma[...]`, `Equiv[A, B]`, `Diamond[A]`, `Box[A]`, `Refinement[T, P]` all fall through to the generic `Structural(f"type-level {ast.unparse(node)}")` branch (psdl.py:1166-1170). No equality / Π / Σ / Equiv / modality / refinement term is constructed. Documented in docstring lines 175-185 but never wired up.

- **`@protocol class P:`** — Docstring at psdl.py:589 ("introduces a protocol used by `dispatch`") and treatise § 6.7.2 (line 522-523) advertise `@protocol`. Implementation at psdl.py:618-630 detects the decorator and emits a `-- protocol methods: ...` Lean comment, but the methods are *not* registered anywhere — `dispatch` (psdl.py:1675-1689) does not consult any protocol registry. The treatise's claim that "dispatch resolves against an actual Σ-projection [in a richer preamble]" has no in-code wiring.

- **`Pi[x: T](B(x))`, `Sigma[x: T](B(x))`** — Documented in docstring line 177-178. No handler beyond the generic Subscript fall-through. These do *not* compile to Π / Σ proof terms in any sense; the treatise (§ 6.5) implicitly leans on `forall` / `exists` for these but the docstring lists them as separate forms.

- **`p ** k`** (k-fold path composition) — Documented in docstring line 334. Not implemented. The `_compile_expr` handler for `BinOp` covers `MatMult`, `Mult`, `RShift` but not `Pow` (psdl.py:1090-1121). Falls through to the generic "unsupported expression" error.

- **`lhs, rhs = eq.sides` / `(a, b) = pair`** (tuple unpacking on equations) — Documented in docstring lines 383-388. `eq.sides` returns a `Structural` (psdl.py:1040-1044) but there is no handler for tuple-target `Assign` statements that would actually decompose `eq.sides`; psdl.py:997-1009 only handles single-name targets, returning `Structural("non-name assign")` for tuple targets.

- **`# nil: <nil body>` comment marker for for-loops** — Treatise § 6.3.3 and docstring line 67 promise that a `# nil: ...` comment provides the nil case. Implementation at psdl.py:844-846 says `"# Look for # nil: ... marker..."` but admits `"Without comment introspection, default to Refl in nil case"` — the marker is documented as supported but the parser never reads it. Every `for` produces `nil_proof = Refl(Var("_nil"))` regardless.

- **`induction(n) on Nat: case Z(): ... case S(k, ih): ...`** — Treatise § 6.5.1 (lines 295-302, 511-512) and docstring lines 188-194, 252-256 describe this surface form. Implementation at psdl.py:1571-1588 only honours the kwarg form `induction(n, base=..., step=...)`. The `on Nat: case Z(): ... case S(k, ih): ...` block is invalid Python at the point where `on` would appear and is never parsed; no handler attempts to recognise the structured Tree-of-cases form.

- **`Refl` / `Refinement` in the kernel** — Treatise § 6.4.5 (line 280) describes `RefinementType` predicate as a type-level check. The kernel's `RefinementType` only stores a `predicate: str` (kernel.py — string field), and PSDL just passes the unparsed annotation. Treatise calls this an honest gap (§ 6.9 "Limitations" line 768-770) so this fits B.

- **`induction over List with explicit nil and cons cases`** — `for x in xs:` (psdl.py:835-852) hard-codes `nil_proof = Refl(Var("_nil"))`. The treatise § 6.3.3 implies that an explicit nil body can be supplied (via the `# nil:` comment), but neither the comment nor a kwarg form is parsed.

- **Sort information / universe polymorphism** — Treatise explicitly disclaims this (§ 6.9 line 766). Listed as known gap.

- **Higher inductive types in `@inductive`** — Treatise § 6.9 line 771-772 disclaims this.

- **kernel `KanFill` term** — Treatise § 6.6.2 (line 401-411) says `kan_fill(open_box, filling)` "compiles to a `Patch` term wrapping the filling proof". Implementation at psdl.py:1691-1709 actually emits a `Cut(...)`, *not* `Patch` and *not* `KanFill`. The kernel `KanFill` term (kernel.py:940-983) is never constructed by PSDL at all. (See also C below — this is also a divergence.)

- **`Univalence` kernel term** — Imported into psdl.py:454-461? — actually no, `Univalence` is *not* imported by psdl.py. Treatise § 6.5.4 (line 372-378) describes `equiv_to_path(e)` as compiling to a `TransportProof` with a `ua` axiom, which it does (psdl.py:1656-1670), but the dedicated `Univalence` kernel term (kernel.py:837-846) exists and is never used.

- **`HigherPath` kernel term** — Never constructed by PSDL. The treatise's "n-dimensional homotopy" (§ 6.6.6 line 466-471) explicitly says "There is no native 'Square' ProofTerm; the user obtains the semantically richer form by constructing `KanFill(dimension=2, ...)` directly" — but neither does PSDL construct `HigherPath` (kernel.py:985-1024).

- **`CechGlue` kernel term** — Never constructed by PSDL despite its central role in cohomology (treatise ch10).

---

## C. Implemented but in a conflicting way

- **`if x > 0:` (non-isinstance generic if)** — Treatise § 6.3.1 (lines 116-126) says it should produce `Cases(scrutinee=Var("x > 0"), branches=[("then", ...), ("else", ...)])` and Lean `by_cases h : x > 0`. Implementation at psdl.py:776-792 *does* produce that `Cases`, but if there is *no* `else`, the else-branch becomes `Structural("no else branch")` (psdl.py:786-788). The treatise's narrative about exhaustiveness is built around `Fiber.exhaustive=False`; for the `Cases` path there is no analogue — exhaustiveness is silently dropped, and trust is not adjusted.

- **`while n:` does not consult `n`** — Treatise § 6.3.3 (lines 162-170) says `while n:` compiles to `NatInduction(var=n, base_proof=Refl, step_proof=body)`. Implementation at psdl.py:855-862 hard-codes `var="n"` (literal string) regardless of the loop's actual condition. So `while m:` with variable `m` produces `NatInduction(var="n", ...)`. The treatise example ("`while n:`") happens to use the literal `n`, masking the bug.

- **`raise <Exception>` (non-NotImplementedError)** — Treatise § 6.4.4 (lines 261-263) describes only the NotImplementedError marker. Implementation at psdl.py:966-972 also handles other exceptions by returning a `ConditionalEffectWitness(precondition=f"raises {exc_text}", effect="exception", proof=Structural(f"raises {exc_text}"), target=exc_text)`. The kernel's `ConditionalEffectWitness` is documented in kernel.py:560-581 as "under precondition P, effect E is **absent**" — i.e. a *safety* witness — but PSDL is using it to claim "the exception is **present**". The semantics are inverted: this term is being constructed in a meaning that contradicts its docstring. Line 966-972 should arguably emit an `EffectWitness(effect="exception", ...)` instead. This is a real soundness-relevant divergence.

- **`try / except` only retains the *last* handler** — Treatise § 6.3.2 (lines 137-148) says each `except` clause becomes "a `ConditionalEffectWitness` with `precondition='raises Exc'`". Implementation at psdl.py:824-832 has the loop:
  ```
  ew = EffectWitness(effect="value", proof=value_proof)
  for exc_name, hp in handler_proofs:
      ew = ConditionalEffectWitness(precondition=..., effect=..., proof=hp, target=exc_name)
  ```
  Each iteration **overwrites** `ew`. With multiple `except` clauses, only the *last* one survives in the returned proof term — the earlier handlers (and the original `EffectWitness(value)`) are discarded. The treatise narrative implies a chain. The "+ ConditionalEffectWitness(...)" in the treatise's wording suggests the value witness should compose with the handlers; the code drops it on the floor.

- **`cong(f, eq)`** — Treatise § 6.5.2 (lines 322-336) says "produces `Cong(f, eq)`". Implementation at psdl.py:1538-1545 produces `Cong(func=Var(_safe(fn_text)), proof=inner_eq)` — i.e. the function is wrapped in `Var()` rather than passed as a real `SynTerm`. For `cong(succ, ih)`, the kernel will see `Var("succ")`, not the function `succ`. The kernel's `Cong.func: SynTerm` field (kernel.py:115) is comfortable with `Var`, but the Lean side emits `congrArg succ ih` — those two artifacts differ, so kernel pattern-matching against the goal could accept `Cong(Var("succ"), ...)` for any function named `succ`, even one that has been shadowed.

- **`cong` and other tactics: function arg unparsed *as a name*, not a term** — Same family of issues for `path_ap` (psdl.py:1608-1617), `f * p` (psdl.py:1102-1111), and the `eq.cong(f)` postfix (psdl.py:1276-1285). All wrap `_safe(fn_text)` in `Var(...)`. The treatise narrative (§ 6.5.3 line 348-349) says "`path_ap(f, p)` is `Ap(f, p)`" implying `f` is a term, not a `Var(name)`.

- **`forall(x, T, body)` predicate text** — Treatise § 6.5.1 (lines 304-308) says the cut's hypothesis type is "the refinement `{x : T}`". Implementation at psdl.py:1483-1490 builds `RefinementType(base_type=PyObjType(), predicate=tt)` — i.e. it puts the *type* in the predicate field of a refinement, with the base type left as `PyObjType`. This is structurally inconsistent: `T` is the type, not a predicate; it should either be the `base_type` or the refinement should have an empty predicate. The same pattern appears for `exists` (psdl.py:1502-1509). When the kernel inspects this, the refinement is meaningless.

- **`assert P` annotated-type field** — `_compile_assert` (psdl.py:907-911) writes `RefinementType(base_type=PyBoolType(), predicate=claim)` — the hypothesis type is a refinement of `Bool` whose predicate is the claim string. The treatise § 6.4.1 doesn't describe the internal shape, so this is a soft case: the refinement is structurally well-formed but the kernel's RefinementType (kernel.py-level) does not use `predicate` for anything, so it's dead data. The Lean side gets the right `have h : P := ...` regardless. Not strictly a bug, but the kernel-side type is decorative.

- **`kan_fill(open_box, filling)`** — Treatise § 6.6.2 (lines 401-411) says it should compile to "a `Patch` term wrapping the filling proof". Implementation at psdl.py:1691-1709 actually emits a `Cut(hyp_name="_kan_box", hyp_type=PyObjType(), lemma_proof=<box>, body_proof=<filler>)`. Neither `Patch` (kernel.py:707-716) nor `KanFill` (kernel.py:940-983) is constructed. The treatise's `apply Kan.fill` Lean tactic *is* emitted, but the kernel-side artefact is wrong.

- **`return` without expression** — psdl.py:947-950 emits `Refl(Var("_unit"))` and Lean `rfl`. Treatise doesn't call out the bare-return case. The `Var("_unit")` placeholder is a fictitious name that has no kernel-level meaning.

- **`square(top, bot, left, right)`** — Treatise § 6.6.6 (lines 466-471) explicitly admits "There is no native 'Square' ProofTerm; the user obtains the semantically richer form by constructing `KanFill(dimension=2, faces=...)` directly." Implementation at psdl.py:1816-1830 chains four paths via *two* `PathComp`s: `PathComp(PathComp(t, b), PathComp(l, r))`. The treatise says "chains four paths via two compositions" matching the implementation — but the chain `PathComp(top·bot, left·right)` doesn't model a square boundary commuting; it just glues four arbitrary paths. So the treatise's resigned "chains four paths" matches the bug, but neither matches "square" semantics. (Categorising as C since the implementation is at least documented.)

- **`apply` and Lean tactic for non-foundation names** — Treatise § 6.4.2 (line 224-226) says "Otherwise the module is empty and Lean emits `exact F`." Implementation at psdl.py:1313 emits `exact {_safe(target)}`. The `_safe` call at psdl.py:1858-1872 mangles non-identifier characters into underscores; `apply(Real.sqrt)` would Lean-emit `exact Real_sqrt`, which is *not* the target. The kernel-side `AxiomInvocation(name=target, module="")` keeps the dotted name. Lean and kernel artefacts diverge.

- **`_compile_call` and operator overloading parse heuristics** — `f * p` (psdl.py:1104) only fires when `node.left` is an `ast.Name`. The docstring line 332 says "`f * p` → `Ap(f, p)`" with no such limitation. `(succ_succ * eq)` works; `(f.method * eq)` does not — falls through to the unsupported-expression branch.

- **annotated assignment recompiles RHS twice** — psdl.py:984 emits the Lean `have h : T := <rhs>` from the *unparsed string* of the RHS, **then** psdl.py:986 recursively compiles the RHS with `_compile_expr`. The Lean and kernel artefacts can disagree: if the RHS is `apply(Real_sqrt_nonneg)`, Lean sees `apply(Real_sqrt_nonneg)` literally (which is *not* a Lean tactic), while the kernel sees the intended `AxiomInvocation`. Treatise § 6.4.5 (lines 277-281) says `Lean side emits have h : T := <RHS>` — true literally, but the resulting Lean is broken.

- **`P and Q` Lean emission** — psdl.py:1182-1187 emits `exact ⟨<P>, <Q>⟩` from the *unparsed* operands, while building a `Cut`-chain on the kernel side. The unparsed operands may not be valid Lean (e.g. PSDL identifiers like `Real_sqrt_nonneg` get used directly). Treatise docstring line 421 says "`P and Q` → conjunction (And.intro)" — the kernel-side `Cut(_and, ...)` chain is *not* an And.intro; it's a sequencing with bogus hypothesis name `"_and"`. Both halves diverge from the treatise.

- **`P or Q`** — psdl.py:1198-1203 emits Lean `left  -- or-introduction; pick first witness` and returns the first inner proof. Treatise docstring line 422 says "`P or Q` → disjunction (Or.intro)". The kernel-side artefact is just `inners[0]` — there is no `Or.intro`-shaped term; the user's right disjunct is silently dropped. This is unsound: a user proving `P or Q` by giving witnesses to *both* (perhaps intending Or.intro2 if P fails) gets only the left-witness verified.

- **`induction(n) on Nat: case Z(): ... case S(k, ih): ...`** — Treatise § 6.5.1 (line 295-302, 510-512) describes this Tree-of-cases surface. Implementation does *not* parse it (Python's `on Nat:` is a syntax error in the AST, and `case Z():` outside a `match` statement is also invalid). The treatise example would fail to parse before any compiler logic runs.

- **`compile_block` treats `empty proof block` and `import` as non-noise** — psdl.py:526-528 lists the noise-passthrough whitelist as `("show_goal", "show_term", "trivial", "pure")`. The `from foundations import F` `Structural("import [...]")` and the empty-block `Structural("empty proof block")` are *not* in the whitelist, so they *do* introduce real `Cut(... PyObjType(), Structural("import ...")), ...)` wrappers. Treatise § 6.8 (lines 552-556) says noise should pass through; imports are arguably noise.

---

## Counts

- **A. Implemented**: 56 items
- **B. Described but not implemented**: 11 items
- **C. Implemented in a conflicting way**: 14 items

---

## Honest gaps in the treatise itself

Things the implementation supports that the treatise under-mentions:

- **`from foundations import F1, F2`** — psdl.py:566-571 supports it; treatise doesn't list it.
- **`path.cong(f)` postfix sugar** — psdl.py:1276-1285 supports it; treatise's postfix list (lines 372-380) doesn't include `.cong`.
- **`eq.subst` / `eq.rew` / `eq.rewrite_then` postfix** — psdl.py:1287-1295 supports a unified `Rewrite(...)` for these aliases; not in the treatise.
- **`any(P(x) for x in xs)`** — psdl.py:1465-1472 supports an existential-closure form (delegates to comprehension compilation); not mentioned.
- **`with hypothesis(h="...", T="...")`** keyword shape — psdl.py:751-770 documents only kwargs, not positional; treatise (line 366-367) implies a different syntax (`hypothesis(h="p > 0")`).
- **plain `class T:` (no `@inductive`)** — psdl.py:632-642 treats it as a Σ-record. Not mentioned.
- **`compile_block` produces `Structural("empty proof block")`** for empty blocks. Treatise doesn't say.

Things the treatise OVER-claims:

- **§ 6.7.2 (line 522)** "The `@protocol` decorator declares a structural protocol similar to PEP 544's `Protocol` class." — In reality, `@protocol` only emits Lean comments; it does not register methods anywhere PSDL can consult later. `dispatch` cannot use protocol info.
- **§ 6.5.1 (line 510-512)** the `induction(x) on Nat: case Z(): ...` syntax is presented as supported in a worked example. It is not parseable Python as written; the actual implementation is `induction(n, base=..., step=...)`.
- **§ 6.6.2 (line 407)** "Compiles to a `Patch` term". In reality it compiles to a `Cut`. Neither `Patch` nor `KanFill` is built by the sugar form.
- **§ 6.3.2 (line 144-148)** "EffectWitness(value) + ConditionalEffectWitness(...)". The implementation overwrites; the value witness is lost when there are handlers.
- **Line numbers in the treatise are stale** — Treatise cites `_compile_if` at "lines 609-642"; the actual handler is at psdl.py:776-809. The file grew from 1553 to 1993 lines; every line citation in the treatise is off.
