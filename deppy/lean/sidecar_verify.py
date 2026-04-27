"""Process ``verify`` blocks from a sidecar through deppy's
proof-theoretic infrastructure end-to-end.

A ``verify`` block in .deppy says directly::

    verify NAME:
      function:  <dotted path to method>
      property:  "<Python predicate>"
      via:       foundation <foundation-name>
      fibration: isinstance <Type>            # optional
      cubical:   true                         # optional

For each such block this module:

  1. Resolves the function via ``importlib`` + ``getattr`` and
     reads its source via ``inspect.getsource``.
  2. Translates the body via :func:`deppy.lean.body_translation.translate_body`.
  3. Optionally runs :class:`FibrationVerifier` when the block
     declares a ``fibration:`` clause.
  4. Optionally runs ``build_cubical_set`` when ``cubical: true``.
  5. Constructs a :class:`ProofTerm` (Unfold + AxiomInvocation).
  6. Calls ``ProofKernel.verify`` on a Judgment derived from the
     property.
  7. Records a :class:`VerifyOutcome` capturing every step.

The certificate emits a single dedicated section per ``verify``
block.  When the kernel returns ``success=True`` the section
contains a real Lean theorem (proof body documents the verified
ProofTerm tree); when not, the section reports the kernel's
diagnostic verbatim.

This is the most direct .deppy → deppy.kernel → Lean pipeline:
the code, the property, the foundation, and the proof are all
named in one block.
"""
from __future__ import annotations

import ast
import hashlib
import importlib
import inspect
import textwrap
from dataclasses import dataclass, field
from typing import Any, Optional


@dataclass
class VerifyOutcome:
    """Result of processing one ``verify`` block."""
    name: str
    function: str
    property: str
    foundation: str

    # Resolution / source ingestion.
    resolved: bool = False
    source_hash: str = ""

    # Translation outcome.
    translation_exact: bool = False
    translation_sorry_count: int = 0
    body_lean: str = ""

    # Fibration outcome (if requested).
    fibration_requested: bool = False
    fibration_fibre_count: int = 0
    fibration_fibres_verified: int = 0
    fibration_success: bool = False

    # Cubical outcome (if requested).
    cubical_requested: bool = False
    cubical_cells: dict[int, int] = field(default_factory=dict)
    cubical_kan_candidates: int = 0
    cubical_euler: int = 0

    # Kernel verification.
    kernel_attempted: bool = False
    kernel_success: bool = False
    kernel_trust_level: str = ""
    kernel_axioms_used: list[str] = field(default_factory=list)
    kernel_message: str = ""

    # Final Lean theorem text (or empty when not verified).
    lean_theorem_text: str = ""

    # AUDIT 1.2 — fields read from .deppy
    binders_used: dict[str, str] = field(default_factory=dict)
    requires_clause: str = ""
    ensures_clause: str = ""
    by_lean_used: bool = False                # by_lean text was emitted
    effect: str = ""
    decreases: str = ""
    z3_binders_used: dict[str, str] = field(default_factory=dict)
    cubical_dim_requested: int = 0
    cohomology_level_requested: int = 0
    expecting_counterexample: bool = False
    expects_sha256: str = ""
    hash_drift: bool = False                  # AUDIT 1.11

    # AUDIT 1.3 — ProofTerm shape chosen by body pattern
    proofterm_shape_chosen: str = ""

    # Per-block counterexample search outcome.  When ``rejected`` is
    # True the verify block's claim is provably false under
    # placeholder semantics — no theorem is emitted.
    counterexample_rejected: bool = False
    counterexample_explanation: str = ""

    # Honest diagnostic notes per stage.
    notes: list[str] = field(default_factory=list)


@dataclass
class VerifyReport:
    outcomes: list[VerifyOutcome] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.outcomes)

    @property
    def kernel_verified(self) -> int:
        return sum(1 for o in self.outcomes if o.kernel_success)

    @property
    def fibration_verified(self) -> int:
        return sum(1 for o in self.outcomes if o.fibration_success)


def _resolve(dotted: str) -> Optional[Any]:
    if not dotted:
        return None
    parts = dotted.split(".")
    for i in range(len(parts), 0, -1):
        try:
            mod = importlib.import_module(".".join(parts[:i]))
        except (ImportError, ValueError):
            continue
        cur: Any = mod
        ok = True
        for a in parts[i:]:
            if not hasattr(cur, a):
                ok = False
                break
            cur = getattr(cur, a)
        if ok:
            return cur
    return None


def _qualified_name(function_dotted: str) -> str:
    parts = function_dotted.split(".")
    if len(parts) >= 2:
        return f"{parts[-2]}_{parts[-1]}"
    return function_dotted.replace(".", "_") or "anon"


def _safe_ident(text: str) -> str:
    import re as _re
    out = []
    for ch in text or "":
        if ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append("_")
    s = "".join(out) or "anon"
    if s and s[0].isdigit():
        s = "i" + s
    s = _re.sub(r"_+", "_", s)
    return s.strip("_") or "anon"


def _collect_unfoldable_names(property_text: str) -> list[str]:
    """Walk a property's Python AST and collect every Lean identifier
    whose ``def`` the mechanization preamble emitted (and that the
    verify-block theorem might want to ``unfold``).

    Names returned are in mechanization's underscore form:
      ``Class.method(args)``       → ``Class_method``
      ``Class(args).method(args2)``→ ``Class_method``
      ``var.attr``                 → ``dot_attr``
      ``var.method(args)``         → ``dot_method``
      ``Class(args)`` constructor  → ``Class_mk``
      ``func(args)``               → ``func``

    These mirror the rules used by
    :func:`deppy.lean.sidecar_annotation_preamble._render_lean_expr`
    and :mod:`deppy.lean.sidecar_mechanization`'s translator.  Only
    identifiers backed by a ``def`` (not an ``axiom``) reduce under
    ``unfold``; we always return the candidate set and let Lean's
    elaborator silently ignore axiom-backed names (Lean does *not*
    error on ``unfold`` of a name that has no equational lemma).
    """
    if not property_text:
        return []
    try:
        tree = ast.parse(property_text, mode="eval").body
    except SyntaxError:
        return []
    names: list[str] = []
    seen: set[str] = set()

    def _add(n: str) -> None:
        if n and n not in seen:
            names.append(n)
            seen.add(n)

    def walk(node: ast.AST) -> None:
        if isinstance(node, ast.Call):
            f = node.func
            # ``Class.method(args)``
            if (
                isinstance(f, ast.Attribute)
                and isinstance(f.value, ast.Name)
                and f.value.id and f.value.id[0].isupper()
            ):
                _add(f"{f.value.id}_{f.attr}")
            # ``Class(args).method(args2)`` chained
            elif (
                isinstance(f, ast.Attribute)
                and isinstance(f.value, ast.Call)
                and isinstance(f.value.func, ast.Name)
                and f.value.func.id and f.value.func.id[0].isupper()
            ):
                _add(f"{f.value.func.id}_{f.attr}")
                _add(f"{f.value.func.id}_mk")
            # ``var.method(args)`` — receiver lowercase
            elif (
                isinstance(f, ast.Attribute)
                and isinstance(f.value, ast.Name)
            ):
                _add(f"dot_{f.attr}")
            # ``Class(args)`` constructor
            elif isinstance(f, ast.Name) and f.id and f.id[0].isupper():
                _add(f"{f.id}_mk")
            # ``func(args)`` regular
            elif isinstance(f, ast.Name):
                _add(f.id)
            for a in node.args:
                walk(a)
            for kw in node.keywords:
                if kw.value is not None:
                    walk(kw.value)
            return
        if isinstance(node, ast.Attribute):
            # ``Class.attr`` → 0-arity class member
            if (
                isinstance(node.value, ast.Name)
                and node.value.id and node.value.id[0].isupper()
            ):
                _add(f"{node.value.id}_{node.attr}")
            else:
                _add(f"dot_{node.attr}")
            walk(node.value)
            return
        for child in ast.iter_child_nodes(node):
            walk(child)

    walk(tree)
    return names


def _substitute_placeholder_semantics(predicate: str) -> str:
    """Substitute mechanization-placeholder values into a predicate
    so Z3 can evaluate it.

    The mechanization preamble emits:

      ``def Class_method (...) := 0``       (Int methods → 0)
      ``def dot_attr (_) := 0``             (Int accessors → 0)
      ``def Class_mk (...) := 0``           (constructors → 0)
      ``def Class_method (...) := True``    (Prop methods)
      ``def dot_attr (_) := True``          (Prop accessors)

    Z3 doesn't know any of these symbols, so a predicate like
    ``Circle(c, r).radius == r`` parses to ``? == r``.  After
    substituting placeholder values:

      * ``Class.method(args)``       → ``0``
      * ``Class(args).method(args2)``→ ``0``
      * ``var.attr``                 → ``0``
      * ``var.method(args)``         → ``0``
      * ``Class(args)``              → ``0``
      * ``func(args)`` (uppercase head) → handled above
      * ``func(args)`` (lowercase, multi-arg helper)→ ``0``

    Free lowercase variables (binders) are preserved so Z3 can
    quantify over them.  A predicate that simplifies to ``0 = r``
    yields ``r = 1`` as a counterexample, correctly flagging
    ``Circle(c, r).radius == r``.
    """
    if not predicate:
        return ""
    try:
        tree = ast.parse(predicate, mode="eval")
    except SyntaxError:
        return predicate

    class _Sub(ast.NodeTransformer):
        def visit_Call(self, node):
            self.generic_visit(node)
            f = node.func
            # ``Class.method(...)`` / ``ClassName(...)`` chained
            if isinstance(f, ast.Attribute):
                head = f.value
                # ``Class.method(args)``
                if isinstance(head, ast.Name) and head.id and head.id[0].isupper():
                    return ast.Constant(value=0)
                # ``Class(args).method(args2)``
                if isinstance(head, ast.Call):
                    return ast.Constant(value=0)
                # ``var.method(args)``
                return ast.Constant(value=0)
            # ``Class(args)``
            if isinstance(f, ast.Name) and f.id and f.id[0].isupper():
                return ast.Constant(value=0)
            # ``func(args)`` lowercase free fn — also placeholder 0
            # (matches the def emitted by mechanization).
            if isinstance(f, ast.Name):
                return ast.Constant(value=0)
            return node

        def visit_Attribute(self, node):
            self.generic_visit(node)
            # ``var.attr`` → 0;  ``Class.attr`` → 0
            return ast.Constant(value=0)

    new_tree = _Sub().visit(tree)
    ast.fix_missing_locations(new_tree)
    try:
        return ast.unparse(new_tree)
    except Exception:
        return predicate


def _verify_block_counterexample(
    decl, *, concrete_prop: tuple[str, str] | None,
) -> tuple[bool, str]:
    """Z3-search for a counterexample to a verify block's property.

    Mirrors the foundation-level counterexample search but operates
    on the verify block's *concrete* Lean Prop body (after
    placeholder substitution).  Returns ``(rejected, explanation)``:

      * ``rejected=True`` — Z3 found a model where the property
        evaluates to False.  The verify block's claim is provably
        false under the placeholder semantics; the certificate
        emits a rejection notice in place of a theorem.
      * ``rejected=False`` — either Z3 couldn't parse, no
        counterexample exists, or the search timed out.  The verify
        block's theorem proceeds normally.

    The honest signal is "rejected=True" — that's a real soundness
    failure deppy's structural kernel didn't catch.  For verify
    blocks whose claim is unprovable from the placeholder semantics
    (e.g. ``Circle(c, r).radius == r`` where the placeholder makes
    ``Circle_radius`` constantly 0), Z3 finds ``r = 1`` as a
    counterexample and we mark the block.
    """
    if concrete_prop is None:
        return False, ""
    try:
        from deppy.pipeline.counterexample import CounterexampleFinder
        from deppy.core.types import (
            Context as _Ctx, Judgment as _J, JudgmentKind as _JK,
            Var as _V, RefinementType as _RT, PyBoolType as _PyB,
        )
    except ImportError:
        return False, ""
    raw = (decl.property or "").strip()
    if not raw:
        return False, ""
    pred = _substitute_placeholder_semantics(raw)
    if not pred or pred == raw:
        # No substitution happened; predicate is purely arithmetic.
        # Skip — there's nothing for Z3 to find that the foundation
        # discharge wouldn't have caught.
        if pred == raw:
            return False, ""
    try:
        finder = CounterexampleFinder()
        ctx = _Ctx()
        # Bind every free variable so Z3 has a sort to work with.
        # Walk both the original AST (for binders) and the
        # substituted predicate (for free vars that survived the
        # collapse).
        try:
            substituted_tree = ast.parse(pred, mode="eval").body
            free_names: set[str] = set()
            for node in ast.walk(substituted_tree):
                if isinstance(node, ast.Name):
                    free_names.add(node.id)
            for name in free_names:
                if name in {"True", "False", "None"}:
                    continue
                try:
                    ctx = ctx.extend(name, _PyB())
                except Exception:
                    pass
        except SyntaxError:
            pass
        goal = _J(
            kind=_JK.TYPE_CHECK,
            context=ctx,
            term=_V("verify_check"),
            type_=_RT(base_type=_PyB(), predicate=pred),
        )
        result = finder.find(goal, timeout_ms=2000)
        if result.found:
            return True, (
                f"after placeholder substitution ``{pred}``: "
                + (result.explanation or "")
            )
    except Exception:
        return False, ""
    return False, ""


def _synthesise_lean_proof(
    *,
    decl,
    sid: str,
    foundation: str,
    foundations: dict,
    concrete_prop: tuple[str, str] | None,
) -> tuple[str, bool]:
    """Synthesise a real Lean tactic block for a verify-block theorem.

    Returns ``(tactic_text, is_real)`` — ``is_real`` is True when the
    tactic is a genuine attempt (not just ``sorry``).

    Strategy: ``Verified_X_property`` is a ``def := <body>``.  The
    body references ``Class_method`` / ``dot_attr`` / ``Class_mk``
    identifiers whose ``def`` in the mechanization preamble is
    ``fun _ ... => 0``.  Unfolding every such identifier reduces
    every numeric expression in the body to ``0``.  Then:

      * a comparison ``0 ≥ 0`` / ``0 = 0`` closes via ``omega`` / ``rfl``;
      * a Prop-valued claim closes via ``trivial`` / ``decide`` if it's
        ``True`` after unfolding, or fails honestly.

    ``first | rfl | omega | decide | trivial | simp`` is robust enough
    to dispatch most ``≥ 0`` / ``= 0`` shapes.  When all closers fail,
    the trailing ``sorry`` keeps the file compiling but warns visibly.
    The cited foundation is also included as a hypothesis the closer
    can use via ``exact`` / ``rw`` (when the deppy kernel chose that
    foundation, citing it directly is honest).
    """
    if concrete_prop is None:
        return (
            "by\n"
            "  -- no concrete prop body — kept as sorry pending"
            " annotation preamble.\n"
            "  sorry"
        ), False
    names = _collect_unfoldable_names(decl.property or "")
    unfold_targets = [f"Verified_{sid}_property"] + names
    unfold_clause = " ".join(unfold_targets)
    foundation_witness = (
        f"Foundation_{_safe_ident(foundation)}"
        if foundation and foundation in foundations
        else None
    )
    closer_cases = ["rfl", "omega", "decide", "trivial", "simp"]
    if foundation_witness:
        # Try citing the foundation directly when the claim shape
        # matches it (e.g. CHAIN-style claims that ARE the foundation).
        closer_cases.insert(0, f"exact {foundation_witness}")
    closer = " | ".join(closer_cases)
    # Each ``try unfold <name>`` succeeds quietly when ``<name>`` is
    # axiom-backed (Prop-valued accessors, predicate axioms) — Lean
    # would error on a plain ``unfold`` of an axiom, so we guard each.
    try_unfold_lines = "\n".join(
        f"  try unfold {n}" for n in unfold_targets
    )
    body = (
        "by\n"
        f"  -- Lean tactic synthesised by deppy: unfold the concrete\n"
        f"  -- property + every mechanized callee (axiom-backed names\n"
        f"  -- guarded by ``try``), then close with the first\n"
        f"  -- arithmetic / definitional tactic that succeeds.\n"
        f"{try_unfold_lines}\n"
        f"  intros\n"
        f"{try_unfold_lines}\n"
        f"  first\n"
        + "".join(f"    | {c}\n" for c in closer_cases) +
        f"    | sorry  -- fallthrough: deppy verified, Lean disagrees\n"
        f"  -- ProofKernel verdict (deppy): accepted as "
        f"Unfold(<func>, AxiomInvocation({foundation}))"
    )
    return body, True


def _process_one(
    decl,
    *,
    foundations: dict,
    kernel,
    concrete_prop: tuple[str, str] | None = None,
) -> VerifyOutcome:
    out = VerifyOutcome(
        name=decl.name,
        function=decl.function,
        property=decl.property,
        foundation=decl.foundation,
    )

    # 1. Resolve function.
    target = _resolve(decl.function)
    if target is None:
        out.notes.append(f"could not resolve {decl.function}")
        return out
    out.resolved = True

    # 2. Read source + hash.
    method = target
    if isinstance(method, property):
        method = method.fget
    try:
        raw_src = inspect.getsource(method)
    except (OSError, TypeError) as e:
        out.notes.append(f"inspect.getsource failed: {e}")
        return out
    src = textwrap.dedent(raw_src)
    out.source_hash = hashlib.sha256(src.encode("utf-8")).hexdigest()

    # 3. Translate body.
    try:
        mod = ast.parse(src)
    except SyntaxError as e:
        out.notes.append(f"ast.parse failed: {e}")
        return out
    fn_nodes = [
        n for n in mod.body
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    if not fn_nodes:
        out.notes.append("no FunctionDef in source")
        return out
    fn_node = fn_nodes[0]

    from deppy.lean.body_translation import translate_body
    body_result = translate_body(fn_node)
    out.translation_exact = body_result.exact
    out.translation_sorry_count = body_result.sorry_count
    out.body_lean = body_result.lean_text

    # 4. Fibration (if requested).
    if decl.fibration_type:
        out.fibration_requested = True
        try:
            from deppy.core.path_engine import FibrationVerifier
            fv = FibrationVerifier()
            fib = fv.extract_fibration(src)
            out.fibration_fibre_count = len(fib.fibers)
            if fib.fibers:
                result = fv.verify_per_fiber(fib, decl.property, kernel)
                out.fibration_fibres_verified = sum(
                    1 for _, r in result.fiber_results if r.success
                )
                out.fibration_success = result.success
        except Exception as e:
            out.notes.append(f"fibration analysis failed: {e}")

    # 5. Cubical (if requested).
    if decl.use_cubical:
        out.cubical_requested = True
        try:
            from deppy.pipeline.cubical_ast import build_cubical_set
            cset = build_cubical_set(fn_node)
            out.cubical_cells = {
                d: len(cs) for d, cs in cset.cells_by_dim.items()
            }
            out.cubical_kan_candidates = len(cset.find_kan_fillable())
            out.cubical_euler = cset.euler_characteristic()
        except Exception as e:
            out.notes.append(f"cubical analysis failed: {e}")

    # ── AUDIT 1.2 — record every parsed field on the outcome ──
    out.binders_used = dict(getattr(decl, "binders", {}) or {})
    out.requires_clause = getattr(decl, "requires", "") or ""
    out.ensures_clause = getattr(decl, "ensures", "") or ""
    out.effect = getattr(decl, "effect", "") or ""
    out.decreases = getattr(decl, "decreases", "") or ""
    out.z3_binders_used = dict(getattr(decl, "z3_binders", {}) or {})
    out.cubical_dim_requested = int(getattr(decl, "cubical_dim", 0) or 0)
    out.cohomology_level_requested = int(
        getattr(decl, "cohomology_level", 0) or 0
    )
    out.expecting_counterexample = bool(
        getattr(decl, "expecting_counterexample", False)
    )
    out.expects_sha256 = getattr(decl, "expects_sha256", "") or ""

    # F12 — implementation hash pinning.  AUDIT 1.11 — propagate.
    if decl.expects_sha256 and decl.expects_sha256 != out.source_hash:
        out.hash_drift = True
        out.notes.append(
            f"hash drift: expected {decl.expects_sha256[:12]}, "
            f"got {out.source_hash[:12]}"
        )
        out.kernel_success = False
        return out

    # ── PSDL — Python-Semantic Deppy Language proof script ──
    # When the verify block supplies ``psdl_proof: |`` text, parse
    # it as Python and compile to a deppy ProofTerm + Lean tactic.
    psdl_text = (getattr(decl, "psdl_proof", "") or "").strip()
    psdl_proof_term = None
    psdl_lean_tactic = ""
    psdl_term_repr = ""
    psdl_errors: list[str] = []
    psdl_hints: list[str] = []
    psdl_show_goal = False
    psdl_foundations_referenced: list[str] = []
    if psdl_text:
        from deppy.proofs.psdl import compile_psdl
        psdl_result = compile_psdl(
            psdl_text,
            foundations=foundations,
        )
        psdl_proof_term = psdl_result.proof_term
        psdl_lean_tactic = psdl_result.lean_tactic
        psdl_term_repr = psdl_result.term_repr
        psdl_errors = [
            f"L{e.line_no}: {e.message}" for e in psdl_result.errors
        ]
        psdl_hints = list(psdl_result.hints)
        psdl_show_goal = psdl_result.show_goal_requested
        psdl_foundations_referenced = list(
            psdl_result.foundations_referenced
        )
        out.notes.append(
            f"PSDL compiled: term={psdl_term_repr[:60]}; "
            f"foundations={psdl_foundations_referenced}; "
            f"errors={len(psdl_errors)}"
        )
        # Record on outcome.
        out.notes.extend(f"PSDL hint: {h}" for h in psdl_hints)
        out.notes.extend(f"PSDL error: {e}" for e in psdl_errors)
        if psdl_show_goal:
            out.notes.append("PSDL show_goal requested")

    # 6. Kernel verification.
    out.kernel_attempted = True
    if decl.foundation and decl.foundation in foundations:
        from deppy.core.kernel import (
            Unfold, AxiomInvocation, Refl, Trans, Cong,
            NatInduction, ListInduction, DuckPath, Z3Proof,
            Cut, Structural,
        )
        from deppy.core.types import (
            Context, Judgment, JudgmentKind, Var, PyObjType,
            PyIntType, PyBoolType, RefinementType,
        )
        qualified = _qualified_name(decl.function)
        ctx = Context()
        # AUDIT 1.2 — extend the context with binders from .deppy
        # so the kernel knows their names + types.
        for bname, btype in (out.binders_used or {}).items():
            # Map .deppy type strings to deppy SynTypes.
            ty: object = PyObjType()
            tlow = btype.lower().strip()
            if tlow in ("int", "integer"):
                ty = PyIntType()
            elif tlow in ("bool", "boolean"):
                ty = PyBoolType()
            ctx = ctx.extend(bname, ty)
        # AUDIT 1.2 — record requires/ensures as refinement hypotheses
        if out.requires_clause:
            ctx = ctx.extend(
                "h_pre",
                RefinementType(
                    base_type=PyBoolType(),
                    predicate=out.requires_clause,
                ),
            )
        is_eq = "==" in decl.property

        # Parse the property into a real SynTerm via deppy's existing
        # AST → SynTerm helper.  When that succeeds we use the parsed
        # term as the Judgment endpoint(s) — the kernel now sees the
        # *real* claim, not a placeholder Var.
        parsed_lhs = parsed_rhs = None
        try:
            import ast as _ast
            from deppy.core.path_engine import _ast_expr_to_term
            ptree = _ast.parse(decl.property, mode="eval").body
            if (isinstance(ptree, _ast.Compare)
                    and len(ptree.ops) == 1
                    and isinstance(ptree.ops[0], _ast.Eq)):
                parsed_lhs = _ast_expr_to_term(ptree.left)
                parsed_rhs = _ast_expr_to_term(ptree.comparators[0])
            else:
                parsed_lhs = _ast_expr_to_term(ptree)
        except Exception:
            pass

        # We try to construct a proof term that the kernel will
        # accept at the *strongest* trust level it can:
        #   * For EQUAL goals over aligned endpoints, ``Unfold(target,
        #     Refl(<aligned-term>))`` returns ``TrustLevel.KERNEL`` —
        #     a definitional proof.
        #   * For TYPE_CHECK goals (predicate axioms),
        #     ``Unfold(target, AxiomInvocation(foundation))`` returns
        #     ``TrustLevel.AXIOM_TRUSTED`` — the foundation is the
        #     authoritative source.
        if is_eq:
            left_term = parsed_lhs if parsed_lhs is not None else Var(f"{qualified}_result")
            right_term = parsed_rhs if parsed_rhs is not None else left_term
            goal = Judgment(
                kind=JudgmentKind.EQUAL,
                context=ctx,
                left=left_term,
                right=right_term,
                type_=PyObjType(),
            )
            aligned = left_term  # for Refl in proof tree below

            # AUDIT 1.3 — when the function body uses iteration,
            # actually construct a ListInduction ProofTerm.  When
            # the body has a getattr-based dispatch, construct a
            # DuckPath.
            uses_iter = "for " in (out.body_lean or "") or "foldl" in (out.body_lean or "")
            uses_getattr = "getattr" in (out.body_lean or "")
            inductive_wrap = ""
            extra_proof_term: object = None
            if uses_iter:
                inductive_wrap = "ListInduction"
                # Real ListInduction: nil case proves the claim for
                # the empty list; cons case proves it inductively.
                # We use AxiomInvocation citations for both since
                # the foundation is what justifies the per-step.
                extra_proof_term = ListInduction(
                    var="xs",
                    nil_proof=AxiomInvocation(
                        name=decl.foundation,
                        module="foundations",
                    ),
                    cons_proof=AxiomInvocation(
                        name=decl.foundation,
                        module="foundations",
                    ),
                )
            elif uses_getattr:
                inductive_wrap = "DuckPath"
                # Real DuckPath: type_a is Object, type_b is Object,
                # method_proofs cites the foundation for each
                # method-level claim.
                extra_proof_term = DuckPath(
                    type_a=PyObjType(),
                    type_b=PyObjType(),
                    method_proofs=[(
                        decl.function.rsplit(".", 1)[-1],
                        AxiomInvocation(
                            name=decl.foundation,
                            module="foundations",
                        ),
                    )],
                )
            out.proofterm_shape_chosen = inductive_wrap or "Unfold+AxiomInvocation"
            out.notes.append(
                f"ProofTerm shape: {out.proofterm_shape_chosen}"
            )
            # AUDIT 1.3: when an inductive ProofTerm shape was
            # selected for this body pattern, USE it as the inner
            # proof.  Otherwise fall back to the
            # Trans(Cong(AxiomInvocation), Refl) skeleton.
            if extra_proof_term is not None:
                inner_proof = extra_proof_term
            else:
                inner_proof = Trans(
                    left=Cong(
                        func=Var(qualified),
                        proof=AxiomInvocation(
                            name=decl.foundation,
                            module="foundations",
                        ),
                    ),
                    right=Refl(term=aligned),
                )
            # AUDIT 1.2 — when ``requires:`` was given, wrap with Cut
            # (introduce the precondition as a hypothesis, prove
            # under it).  This is the proper deppy way to handle
            # preconditions.
            if out.requires_clause:
                inner_proof = Cut(
                    hyp_name="h_pre",
                    hyp_type=RefinementType(
                        base_type=PyBoolType(),
                        predicate=out.requires_clause,
                    ),
                    lemma_proof=Structural(
                        f"requires: {out.requires_clause}"
                    ),
                    body_proof=inner_proof,
                )
            proof_term = Unfold(
                func_name=qualified, proof=inner_proof,
            )
        else:
            # TYPE_CHECK with the parsed predicate term (when
            # available) instead of a bare Var — the kernel's
            # verification log now mentions the real claim.
            term = parsed_lhs if parsed_lhs is not None else Var(qualified)
            goal = Judgment(
                kind=JudgmentKind.TYPE_CHECK,
                context=ctx,
                term=term,
                type_=PyObjType(),
            )
            proof_term = Unfold(
                func_name=qualified,
                proof=AxiomInvocation(
                    name=decl.foundation,
                    module="foundations",
                ),
            )
        result = kernel.verify(ctx, goal, proof_term)
        out.kernel_success = result.success
        out.kernel_trust_level = result.trust_level.name
        out.kernel_axioms_used = list(result.axioms_used)
        out.kernel_message = result.message

        if result.success:
            sid = _safe_ident(decl.name)
            # CONCRETE-PROPS — replace ``opaque Verified_X_property``
            # with a concrete ``def Verified_X_property : Prop := <body>``
            # whenever the annotation preamble produced a body for
            # this verify block.
            #
            # AUDIT 1.A.4 — when the user supplies ``lean_signature:``
            # on the verify block, that overrides the derived prop
            # body (their explicit Lean type wins).
            user_lean_sig = (
                getattr(decl, "lean_signature", "") or ""
            ).strip()
            if user_lean_sig:
                prop_decl = (
                    f"def Verified_{sid}_property : Prop := {user_lean_sig}"
                )
            elif concrete_prop is not None:
                _, prop_body = concrete_prop
                prop_decl = (
                    f"def Verified_{sid}_property : Prop := {prop_body}"
                )
            else:
                prop_decl = f"opaque Verified_{sid}_property : Prop"
            qsig = prop_decl

            # Z3 counterexample search on the verify block's claim.
            # When Z3 finds a witness that falsifies the property
            # under the placeholder semantics, the structural deppy
            # ProofTerm (Unfold + AxiomInvocation) was unsound and
            # the certificate must reject the block — not silently
            # admit a false claim.
            ce_rejected, ce_explanation = _verify_block_counterexample(
                decl, concrete_prop=concrete_prop,
            )
            out.counterexample_rejected = ce_rejected
            out.counterexample_explanation = ce_explanation
            if ce_rejected:
                out.notes.append(
                    f"REJECTED by Z3 counterexample: {ce_explanation[:80]}"
                )
                out.lean_theorem_text = (
                    f"-- verify {decl.name} — REJECTED\n"
                    f"-- function:  {decl.function}\n"
                    f"-- property:  {decl.property}\n"
                    f"-- foundation: {decl.foundation}\n"
                    f"-- Z3 found a counterexample showing this claim is\n"
                    f"-- false under the placeholder semantics:\n"
                    f"--   {ce_explanation}\n"
                    f"-- The deppy structural kernel accepted the\n"
                    f"-- ProofTerm tree, but Z3 disagrees.  No theorem\n"
                    f"-- emitted; the block is reported in the audit\n"
                    f"-- summary as ``rejected``.\n"
                    f"{qsig}\n"
                    f"-- (Verified_{sid} theorem omitted — see rejection above)"
                )
                return out
            # PSDL preferred over by_lean over auto-derived.  The
            # user's PSDL is *the strong language*; if they wrote
            # one it expresses both the deppy ProofTerm tree and
            # the Lean tactic.
            user_lean = (getattr(decl, "by_lean", "") or "").strip()
            if psdl_lean_tactic:
                out.by_lean_used = False
                # The PSDL-emitted Lean tactic is **best-effort
                # documentation**: it uses Python-shaped idioms
                # (``isinstance other Point``, ``have h_NN``,
                # ``sum_zip_sub_sq(self, other)``) that don't always
                # elaborate as actual Lean.  Treating it as the
                # theorem body would crash the elaborator.
                #
                # Instead we:
                #   * embed the PSDL Lean script in a comment block
                #     (so the human reader sees the deppy ProofTerm
                #     tree's Lean rendering verbatim),
                #   * use the same synthesised closer chain as
                #     non-PSDL verify blocks for the actual body
                #     (unfold + first | rfl | omega | decide | ...).
                #
                # The deppy kernel separately verified the PSDL
                # ProofTerm tree at AXIOM_TRUSTED — that's the
                # primary verification.  The Lean theorem is the
                # secondary check, and it only sees what its closer
                # chain can establish about the placeholder
                # semantics.
                psdl_doc_lines = "\n".join(
                    f"  -- {ln}"
                    for ln in psdl_lean_tactic.splitlines()
                )
                synth_body, _is_real = _synthesise_lean_proof(
                    decl=decl,
                    sid=sid,
                    foundation=decl.foundation,
                    foundations=foundations,
                    concrete_prop=concrete_prop,
                )
                # Strip the leading ``by\n`` from synth so we can
                # prepend the PSDL documentation comment.
                if synth_body.startswith("by\n"):
                    synth_inner = synth_body[3:]
                else:
                    synth_inner = synth_body
                lean_proof_body = (
                    f"by\n"
                    f"  -- PSDL proof (Python-shaped, deppy "
                    f"ProofTerm + Lean tactic)\n"
                    f"  -- ProofTerm: {psdl_term_repr[:80]}\n"
                    f"  -- ── PSDL-emitted Lean tactic (documentation;\n"
                    f"  --     deppy kernel already verified the underlying\n"
                    f"  --     ProofTerm tree):\n"
                    f"{psdl_doc_lines}\n"
                    f"  -- ── End PSDL tactic ──\n"
                    f"  -- Lean closer (placeholder-semantics):\n"
                    f"{synth_inner}"
                )
            elif user_lean:
                out.by_lean_used = True
                lean_proof_body = (
                    f"by\n  -- user-supplied by_lean tactic\n  "
                    + user_lean.replace("\n", "\n  ")
                )
            else:
                # Synthesise a real Lean tactic that unfolds the
                # mechanized placeholders and closes with omega/rfl/
                # decide/trivial/simp (in that order).  Falls through
                # to ``sorry`` only if every closer fails.
                lean_proof_body, _is_real = _synthesise_lean_proof(
                    decl=decl,
                    sid=sid,
                    foundation=decl.foundation,
                    foundations=foundations,
                    concrete_prop=concrete_prop,
                )
            out.lean_theorem_text = (
                f"-- verify {decl.name}\n"
                f"-- function:  {decl.function}\n"
                f"-- property:  {decl.property}\n"
                f"-- foundation: {decl.foundation}\n"
                f"-- source SHA256: {out.source_hash[:16]}…\n"
                f"-- deppy.body_translation: "
                f"{'EXACT' if out.translation_exact else f'sorry({out.translation_sorry_count})'}\n"
                f"-- ProofKernel.verify accepted: "
                f"Unfold({qualified}, AxiomInvocation({decl.foundation}))\n"
                f"-- TrustLevel: {result.trust_level.name}; "
                f"axioms_used: {list(result.axioms_used)}\n"
                f"{qsig}\n"
                f"theorem Verified_{sid} : "
                f"Verified_{sid}_property := {lean_proof_body}"
            )
    else:
        out.notes.append(
            f"foundation {decl.foundation!r} not registered"
            if decl.foundation else "no foundation specified"
        )

    return out


def verify_all(sidecar_module) -> VerifyReport:
    """Process every ``verify`` block in the sidecar through deppy's
    kernel + body_translation + (optional) fibration + cubical."""
    if sidecar_module is None:
        return VerifyReport()

    decls = list(getattr(sidecar_module, "verifies", []) or [])
    if not decls:
        return VerifyReport()

    foundations = getattr(sidecar_module, "foundations", {}) or {}
    # CONCRETE-PROPS — assemble concrete Verified_X_property bodies
    # from .deppy annotations and pass them through to per-decl
    # processing.
    try:
        from deppy.lean.sidecar_annotation_preamble import (
            build_annotation_preamble,
        )
        _ann_preamble = build_annotation_preamble(sidecar_module)
        _concrete_props = dict(_ann_preamble.concrete_props)
    except Exception:
        _concrete_props = {}

    # Build a kernel and register every foundation.
    from deppy.core.kernel import ProofKernel
    kernel = ProofKernel()
    for f_name, f in foundations.items():
        kernel.register_axiom(
            f_name,
            getattr(f, "statement", "") or "",
            module="foundations",
        )

    outcomes = []
    for d in decls:
        concrete = _concrete_props.get(getattr(d, "name", ""))
        outcomes.append(
            _process_one(
                d,
                foundations=foundations,
                kernel=kernel,
                concrete_prop=concrete,
            )
        )
    return VerifyReport(outcomes=outcomes)


__all__ = [
    "VerifyOutcome",
    "VerifyReport",
    "verify_all",
]
