"""Honest tactic selection for ``@implies(pre, post)`` obligations.

Audit fix #7
============

Before this module the certificate emitted ``by Deppy.deppy_safe``
for *every* ``@implies`` obligation, regardless of whether the goal
had a chance of being closed.  ``Deppy.deppy_safe`` itself is just a
combinator over ``decide / omega / simp_all / tauto / aesop / rfl``;
when none of those close the goal Lean rejects the proof, but the
generated certificate looked uniformly "trying our best" — there
was no way for downstream tooling to tell which obligations were
plausibly closed and which weren't.

The honest fix is to:

1. **Statically analyze** the pre / post predicates and judge whether
   any tactic in our toolbox has a realistic chance of closing the
   goal.  We distinguish these cases:

   * ``goal is `True``` → ``by trivial``
   * ``post is structurally identical to pre`` →
     ``by intro h; exact h``
   * ``post is a conjunct of pre`` →
     ``by intro h; exact h.{1,2,...}``
   * ``post is implied by pre via simple arithmetic``
     (both pre and post are linear arithmetic over Int / Nat /
     Bool, no opaque predicates, no function calls) →
     ``by intro h; omega``
   * ``post is purely propositional / decidable`` (no Int
     arithmetic, no opaque predicates) →
     ``by intro h; decide`` or ``by intro h; tauto``
   * ``post mentions ``hasattr`` / ``defined`` / a Z3-opaque
     predicate or a user-defined Python function`` → ``sorry``,
     with a note that this obligation could not be auto-proved.
     We refuse to claim a proof we cannot give.

2. **Emit honest sorries** (rather than ``Deppy.deppy_safe``) when
   the analysis says no tactic is likely to succeed.  Each sorry
   gets a leading comment explaining *why* it could not be
   auto-proved, so a human re-reading the certificate sees the
   gap immediately.

3. **Track plan metadata** on the certificate so the verdict can
   surface counts of (auto-proved, sorry-emitted, user-provided)
   obligations separately.

Public API
----------

::

    plan = select_implies_tactic(
        pre_py: str, post_py: str, *,
        py_types: dict[str, str] | None = None,
        user_proof: str | None = None,
    ) -> ImpliesTacticPlan

    plan.tactic_body                    # what to put after `by `
    plan.is_sorry                       # True iff the plan is `sorry`
    plan.is_user_supplied               # True iff user_proof was used
    plan.confidence                     # 0.0..1.0
    plan.classification                 # ImpliesClassification enum
    plan.notes                          # human-readable rationale

Confidence
----------

The classification + tactic table is curated; ``confidence`` is a
heuristic on a 0–1 scale meant for downstream display, not for
gating verdict.  ``is_sorry`` is the load-bearing flag — if it's
true, the certificate must reflect that the obligation was not
proved.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from enum import Enum
from typing import Optional


# ─────────────────────────────────────────────────────────────────────
#  Classification
# ─────────────────────────────────────────────────────────────────────


class ImpliesClassification(str, Enum):
    """How the analyzer judged the ``@implies`` obligation.

    The ordering reflects increasing pessimism — ``IDENTITY`` is the
    most-likely-to-succeed; ``OPAQUE`` is the most-likely-to-fail.
    Membership of the most-pessimistic plan-classification dictates
    the ``is_sorry`` field.
    """

    IDENTITY = "identity"          # post ≡ pre   → exact h
    CONJUNCT = "conjunct"           # post ∈ conjuncts(pre)
    TRUE_GOAL = "true"              # post ≡ True
    FALSE_PRE = "false_pre"         # pre ≡ False  → ex falso
    LINEAR_ARITH = "linear_arith"   # both sides linear over Int/Nat
    DECIDABLE_PROP = "decidable_prop"  # propositional & decidable
    DEFINITIONAL = "definitional"   # closes by simp_all / rfl
    AESOP_LIKELY = "aesop_likely"   # heuristic — aesop tends to win
    CUBICAL_KAN = "cubical_kan"    # cubical path-equivalence witness
    OPAQUE = "opaque"               # has hasattr/defined/user fn → sorry
    UNKNOWN = "unknown"             # no rule matched → sorry


@dataclass
class ImpliesTacticPlan:
    """The output of :func:`select_implies_tactic`.

    ``tactic_body`` is the text to place after ``by `` in the Lean
    theorem; e.g. ``"intro h; exact h"`` or ``"sorry"``.
    """

    tactic_body: str
    is_sorry: bool
    is_user_supplied: bool
    classification: ImpliesClassification
    confidence: float
    notes: list[str] = field(default_factory=list)
    sorry_reason: Optional[str] = None

    @property
    def tactic_text(self) -> str:
        """The full ``by ...`` text usable in a Lean theorem.  When
        ``is_sorry`` is true this is just the literal ``sorry``."""
        if self.is_sorry:
            return "sorry"
        return f"by {self.tactic_body}"


# ─────────────────────────────────────────────────────────────────────
#  Public entry point
# ─────────────────────────────────────────────────────────────────────


def select_implies_tactic(
    pre_py: str, post_py: str, *,
    py_types: Optional[dict[str, str]] = None,
    user_proof: Optional[str] = None,
    fn_name: Optional[str] = None,
    cubical_set=None,
) -> ImpliesTacticPlan:
    """Return an :class:`ImpliesTacticPlan` for an ``@implies`` obligation.

    The user's ``proof=`` argument always wins (the user has staked a
    proof and the kernel will validate it).  When no user proof is
    given we run :func:`_classify` on the AST of the pre / post
    Python predicates and dispatch to a tactic.

    Round-2 audit integration #2: when ``cubical_set`` is supplied,
    we additionally check whether the @implies obligation has a
    *cubical witness* — a 1-cell whose guards include both the
    pre and the post.  When found, the classification is
    ``CUBICAL_KAN`` and the tactic uses ``Deppy.deppy_kan``.
    """
    py_types = py_types or {}
    if user_proof:
        text = user_proof.strip()
        return ImpliesTacticPlan(
            tactic_body=text, is_sorry=("sorry" in text),
            is_user_supplied=True,
            classification=ImpliesClassification.UNKNOWN,
            confidence=1.0,
            notes=["user-supplied proof — kernel will validate"],
        )

    # Round-2 integration #2: check for a cubical witness BEFORE the
    # standard classifier.  When the cubical set has a 1-cell whose
    # guards include both ``pre_py`` and ``post_py`` (canonically),
    # the obligation is structurally provable via Kan filling.
    if cubical_set is not None:
        from deppy.lean.predicate_canon import predicates_equivalent
        for cell in cubical_set.cells_by_id.values():
            if cell.dim != 1:
                continue
            cell_guards = list(cell.guards)
            if not cell_guards:
                continue
            has_pre = any(
                predicates_equivalent(g, pre_py) for g in cell_guards
            )
            has_post = any(
                predicates_equivalent(g, post_py) for g in cell_guards
            )
            if has_pre and has_post:
                return ImpliesTacticPlan(
                    tactic_body=f"intro h; Deppy.deppy_kan",
                    is_sorry=False,
                    is_user_supplied=False,
                    classification=ImpliesClassification.CUBICAL_KAN,
                    confidence=0.85,
                    notes=[
                        f"cubical witness at cell {cell.cell_id} "
                        f"(both pre and post in cell guards)",
                    ],
                )

    pre_node = _parse_eval(pre_py)
    post_node = _parse_eval(post_py)

    if pre_node is None or post_node is None:
        return ImpliesTacticPlan(
            tactic_body="sorry", is_sorry=True, is_user_supplied=False,
            classification=ImpliesClassification.UNKNOWN,
            confidence=0.0,
            notes=[
                f"pre or post predicate failed to parse "
                f"(pre={pre_py!r}, post={post_py!r})"
            ],
            sorry_reason="unparseable predicate",
        )

    classification, confidence, notes = _classify(
        pre_node, post_node, py_types=py_types, fn_name=fn_name,
    )
    plan = _make_plan(
        classification, pre_node, post_node,
        confidence=confidence, notes=notes,
    )
    return plan


# ─────────────────────────────────────────────────────────────────────
#  Classification logic
# ─────────────────────────────────────────────────────────────────────


def _classify(
    pre: ast.expr, post: ast.expr, *,
    py_types: dict[str, str], fn_name: Optional[str],
) -> tuple[ImpliesClassification, float, list[str]]:
    """Walk the pre / post AST and return a classification.

    The order of checks matters — earlier checks are cheaper and more
    confident, later ones are weaker fall-backs.
    """
    notes: list[str] = []

    # 1.  Trivial goal — post is literally ``True``.
    if _is_literal_true(post):
        return ImpliesClassification.TRUE_GOAL, 1.0, [
            "post is the literal True"
        ]

    # 2.  Vacuous antecedent — pre is literally ``False``.
    if _is_literal_false(pre):
        return ImpliesClassification.FALSE_PRE, 1.0, [
            "pre is the literal False; ex falso"
        ]

    # 3.  Identity — pre and post are AST-equal.
    if _ast_equal(pre, post):
        return ImpliesClassification.IDENTITY, 1.0, [
            "post is structurally identical to pre"
        ]

    # 4.  Conjunct — post is one of pre's And-conjuncts.
    conjuncts = _collect_and_conjuncts(pre)
    for conj in conjuncts:
        if _ast_equal(conj, post):
            return ImpliesClassification.CONJUNCT, 0.95, [
                f"post is conjunct {_unparse(conj)} of pre"
            ]

    # 5.  Opaque predicates / unprovable shapes — bail with sorry.
    pre_has_opaque = _has_opaque_predicate(pre, fn_name=fn_name)
    post_has_opaque = _has_opaque_predicate(post, fn_name=fn_name)
    if pre_has_opaque or post_has_opaque:
        opaque_terms = sorted(
            set(
                _opaque_predicates(pre, fn_name=fn_name)
                | _opaque_predicates(post, fn_name=fn_name)
            )
        )
        notes.append(
            f"opaque predicate(s) appear in pre/post: "
            f"{', '.join(opaque_terms)}"
        )
        return ImpliesClassification.OPAQUE, 0.0, notes

    # 6.  Both sides are linear arithmetic (over Int / Nat).  ``omega``
    #     dispatches that.
    if _is_linear_arith(pre, py_types) and _is_linear_arith(post, py_types):
        return ImpliesClassification.LINEAR_ARITH, 0.9, [
            "both pre and post are linear over Int/Nat → omega"
        ]

    # 7.  Decidable propositional / boolean — ``decide`` may close it
    #     when the goal is a closed decidable proposition.  When the
    #     goal mentions free variables ``decide`` fails, so we only
    #     pick this when the goal has no free names that aren't bound
    #     by typeable Lean classes.
    if _is_decidable_prop(pre, py_types) and _is_decidable_prop(post, py_types):
        return ImpliesClassification.DECIDABLE_PROP, 0.7, [
            "both pre and post are decidable Bool propositions"
        ]

    # 8.  Definitional unfold — when the goal differs from the
    #     hypothesis only by symbols a ``simp_all`` would unfold
    #     (e.g. ``a > 0`` vs ``0 < a``, or ``a = b`` vs ``b = a``).
    if _differs_only_by_simp(pre, post):
        return ImpliesClassification.DEFINITIONAL, 0.65, [
            "pre and post differ only by simp lemmas (rfl/comm)"
        ]

    # 9.  Audit fix (round 2): the previous classifier had an
    #     ``AESOP_LIKELY`` fall-back that emitted ``intros; aesop``
    #     for any structural-propositional goal whose AST size was
    #     under a magic 50.  This was a heuristic dressed as
    #     inference — aesop can fail on goals smaller than 50 and
    #     succeed on larger ones; the size cap was guesswork.  We
    #     now emit ``sorry`` honestly when no structural rule
    #     applies, so callers see real obligations.

    # 10.  Nothing matched.  Sorry.
    notes.append("no structural rule matched — emitting sorry honestly")
    return ImpliesClassification.UNKNOWN, 0.0, notes


def _make_plan(
    classification: ImpliesClassification,
    pre: ast.expr, post: ast.expr,
    *, confidence: float, notes: list[str],
) -> ImpliesTacticPlan:
    """Translate a classification into a concrete tactic body."""
    if classification is ImpliesClassification.IDENTITY:
        return ImpliesTacticPlan(
            tactic_body="intro h; exact h",
            is_sorry=False, is_user_supplied=False,
            classification=classification, confidence=confidence,
            notes=notes,
        )
    if classification is ImpliesClassification.TRUE_GOAL:
        return ImpliesTacticPlan(
            tactic_body="intro _; trivial",
            is_sorry=False, is_user_supplied=False,
            classification=classification, confidence=confidence,
            notes=notes,
        )
    if classification is ImpliesClassification.FALSE_PRE:
        return ImpliesTacticPlan(
            tactic_body="intro h; exact h.elim",
            is_sorry=False, is_user_supplied=False,
            classification=classification, confidence=confidence,
            notes=notes,
        )
    if classification is ImpliesClassification.CONJUNCT:
        # Find which conjunct.
        conjuncts = _collect_and_conjuncts(pre)
        for i, conj in enumerate(conjuncts):
            if _ast_equal(conj, post):
                idx_path = _conjunct_path(i, len(conjuncts))
                return ImpliesTacticPlan(
                    tactic_body=f"intro h; exact h{idx_path}",
                    is_sorry=False, is_user_supplied=False,
                    classification=classification,
                    confidence=confidence, notes=notes,
                )
        # Fallback — shouldn't normally happen.
        return ImpliesTacticPlan(
            tactic_body="intro h; tauto", is_sorry=False,
            is_user_supplied=False, classification=classification,
            confidence=confidence, notes=notes,
        )
    if classification is ImpliesClassification.LINEAR_ARITH:
        return ImpliesTacticPlan(
            tactic_body="intro h; omega",
            is_sorry=False, is_user_supplied=False,
            classification=classification, confidence=confidence,
            notes=notes,
        )
    if classification is ImpliesClassification.DECIDABLE_PROP:
        # ``decide`` is closed; ``tauto`` works for free variables.
        # We pick ``tauto`` when the predicate has free names.
        free_post = _free_names(post)
        if free_post:
            tactic = "intro h; tauto"
        else:
            tactic = "intro _; decide"
        return ImpliesTacticPlan(
            tactic_body=tactic, is_sorry=False, is_user_supplied=False,
            classification=classification, confidence=confidence,
            notes=notes,
        )
    if classification is ImpliesClassification.DEFINITIONAL:
        return ImpliesTacticPlan(
            tactic_body="intro h; simp_all",
            is_sorry=False, is_user_supplied=False,
            classification=classification, confidence=confidence,
            notes=notes,
        )
    if classification is ImpliesClassification.AESOP_LIKELY:
        # We deliberately downrank aesop — it's powerful but
        # imprecise.  Use ``intros; aesop`` and accept the lower
        # confidence on the metadata.
        return ImpliesTacticPlan(
            tactic_body="intros; aesop",
            is_sorry=False, is_user_supplied=False,
            classification=classification, confidence=confidence,
            notes=notes,
        )
    if classification is ImpliesClassification.CUBICAL_KAN:
        return ImpliesTacticPlan(
            tactic_body="intro h; Deppy.deppy_kan",
            is_sorry=False, is_user_supplied=False,
            classification=classification, confidence=confidence,
            notes=notes,
        )

    # OPAQUE / UNKNOWN → honest sorry.
    reason = (
        "opaque predicate" if classification is ImpliesClassification.OPAQUE
        else "no auto-tactic matched"
    )
    return ImpliesTacticPlan(
        tactic_body="sorry", is_sorry=True, is_user_supplied=False,
        classification=classification, confidence=0.0,
        notes=notes, sorry_reason=reason,
    )


# ─────────────────────────────────────────────────────────────────────
#  AST helpers
# ─────────────────────────────────────────────────────────────────────


def _parse_eval(text: str) -> Optional[ast.expr]:
    """Parse a Python expression; return ``None`` on syntax error."""
    try:
        tree = ast.parse(text or "True", mode="eval")
    except SyntaxError:
        return None
    return tree.body


def _unparse(node: ast.expr) -> str:
    try:
        return ast.unparse(node).strip()
    except Exception:
        return repr(node)


def _ast_equal(a: ast.expr, b: ast.expr) -> bool:
    """Structural AST equality, robust to position / annotation
    fields.  We compare the dumped representation (with annotations
    stripped) so semantically identical AST trees compare equal."""
    return _dump_no_pos(a) == _dump_no_pos(b)


def _dump_no_pos(node: ast.expr) -> str:
    return ast.dump(node, annotate_fields=False, include_attributes=False)


def _is_literal_true(node: ast.expr) -> bool:
    if isinstance(node, ast.Constant) and node.value is True:
        return True
    if isinstance(node, ast.Name) and node.id in ("True", "true"):
        return True
    return False


def _is_literal_false(node: ast.expr) -> bool:
    if isinstance(node, ast.Constant) and node.value is False:
        return True
    if isinstance(node, ast.Name) and node.id in ("False", "false"):
        return True
    return False


def _collect_and_conjuncts(node: ast.expr) -> list[ast.expr]:
    """Return the And-conjuncts of ``node``; if ``node`` is not a
    boolean ``and``, return ``[node]`` itself."""
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
        out: list[ast.expr] = []
        for v in node.values:
            out.extend(_collect_and_conjuncts(v))
        return out
    return [node]


def _conjunct_path(idx: int, total: int) -> str:
    """Return Lean projection text for the ``idx``-th conjunct in a
    nested ``And`` chain of length ``total``.

    Lean ``And`` is right-associated (or left-associated, depending),
    but the canonical projector chain is ``.left`` / ``.right``.  We
    emit ``.right.right.left`` style for index ``idx`` of ``total``.
    """
    if total <= 1:
        return ""
    if idx == total - 1:
        return ".right" * (total - 1)
    return (".right" * idx) + ".left"


def _free_names(node: ast.expr) -> set[str]:
    out: set[str] = set()
    for sub in ast.walk(node):
        if isinstance(sub, ast.Name):
            out.add(sub.id)
    return out


# ─────────────────────────────────────────────────────────────────────
#  Linear-arithmetic detection
# ─────────────────────────────────────────────────────────────────────


_ARITH_OPS = (ast.Add, ast.Sub, ast.Mult, ast.Mod, ast.FloorDiv, ast.UAdd, ast.USub)
_ARITH_CMP = (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE)


def _is_linear_arith(node: ast.expr, py_types: dict[str, str]) -> bool:
    """Return True iff ``node`` is a linear-arithmetic Boolean expression
    over ``int`` / ``bool`` variables.

    The grammar we accept:

      atom  ::= name | int-literal | (atom)
      lin   ::= atom | atom + atom | atom - atom | k * atom |
                atom * k | (lin) | -lin
      cmp   ::= lin op lin   where op ∈ {<, ≤, >, ≥, =, ≠}
      conj  ::= cmp | conj ∧ conj | conj ∨ conj | ¬ conj

    Multiplication where both sides have free names is *not* linear.
    Division and modulo by non-constant are not linear (omega rejects
    them anyway).
    """
    return _walk_linear(node, py_types)


def _walk_linear(node: ast.expr, py_types: dict[str, str]) -> bool:
    if isinstance(node, ast.BoolOp):
        return all(_walk_linear(v, py_types) for v in node.values)
    if isinstance(node, ast.UnaryOp):
        if isinstance(node.op, ast.Not):
            return _walk_linear(node.operand, py_types)
        if isinstance(node.op, _ARITH_OPS):
            return _is_linear_term(node, py_types)
    if isinstance(node, ast.Compare):
        if not all(isinstance(op, _ARITH_CMP) for op in node.ops):
            return False
        terms = [node.left] + list(node.comparators)
        return all(_is_linear_term(t, py_types) for t in terms)
    if isinstance(node, ast.Constant) and isinstance(node.value, bool):
        return True
    return False


def _is_linear_term(node: ast.expr, py_types: dict[str, str]) -> bool:
    """Return True iff ``node`` is a linear arithmetic term.

    Audit fix (round 2): un-annotated names are NOT assumed to be
    integers.  The previous behaviour defaulted to ``int`` which
    silently classified ``result > 0`` as linear-arithmetic and
    emitted ``intro h; omega`` even when ``result`` was a list /
    dict / Optional / custom class — wrong tactic, low confidence.

    With the fix, an un-annotated name is *not* a linear term, so
    the classifier falls through to a more conservative tactic
    (or sorry).
    """
    if isinstance(node, ast.Constant):
        return isinstance(node.value, (int, bool))
    if isinstance(node, ast.Name):
        ty = py_types.get(node.id)
        if ty is None:
            # No type info — refuse the linear-arith classification.
            # The classifier will fall through to a more
            # conservative plan (or sorry).
            return False
        return ty in {"int", "Int", "bool", "Bool", "nat", "Nat"}
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        return _is_linear_term(node.operand, py_types)
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, (ast.Add, ast.Sub)):
            return (_is_linear_term(node.left, py_types)
                    and _is_linear_term(node.right, py_types))
        if isinstance(node.op, ast.Mult):
            # At most one side may have free names.
            l_const = _is_constant_int(node.left)
            r_const = _is_constant_int(node.right)
            if l_const and _is_linear_term(node.right, py_types):
                return True
            if r_const and _is_linear_term(node.left, py_types):
                return True
            return False
        if isinstance(node.op, ast.FloorDiv):
            # ``a // k`` for k constant is omega-friendly; arbitrary
            # ``a // b`` is not.
            return _is_constant_int(node.right) and _is_linear_term(
                node.left, py_types,
            )
        if isinstance(node.op, ast.Mod):
            return _is_constant_int(node.right) and _is_linear_term(
                node.left, py_types,
            )
    return False


def _is_constant_int(node: ast.expr) -> bool:
    if isinstance(node, ast.Constant):
        return isinstance(node.value, (int, bool)) and not isinstance(
            node.value, str,
        )
    if isinstance(node, ast.UnaryOp) and isinstance(
        node.op, (ast.UAdd, ast.USub),
    ):
        return _is_constant_int(node.operand)
    return False


# ─────────────────────────────────────────────────────────────────────
#  Decidable propositional detection
# ─────────────────────────────────────────────────────────────────────


def _is_decidable_prop(node: ast.expr, py_types: dict[str, str]) -> bool:
    """Closed propositional logic over decidable atoms.

    Atoms accepted:

    * ``True`` / ``False`` constants
    * ``Name`` references with type ``bool`` / ``Bool``
    * boolean comparisons ``a < b`` / ``a == b`` / etc. on ints/bools
    * boolean combinators ``and``, ``or``, ``not``

    We *reject* anything with a function call (``f(x)``) or attribute
    access (``x.foo``) because those generally introduce undecidable
    propositions.
    """
    return _walk_decidable(node, py_types)


def _walk_decidable(node: ast.expr, py_types: dict[str, str]) -> bool:
    if isinstance(node, ast.Constant):
        return isinstance(node.value, bool)
    if isinstance(node, ast.Name):
        ty = py_types.get(node.id)
        return ty in {"bool", "Bool", None}
    if isinstance(node, ast.BoolOp):
        return all(_walk_decidable(v, py_types) for v in node.values)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return _walk_decidable(node.operand, py_types)
    if isinstance(node, ast.Compare):
        if not all(isinstance(op, _ARITH_CMP) for op in node.ops):
            return False
        for t in [node.left] + list(node.comparators):
            if not _is_decidable_atom(t, py_types):
                return False
        return True
    return False


def _is_decidable_atom(node: ast.expr, py_types: dict[str, str]) -> bool:
    if isinstance(node, ast.Constant):
        return isinstance(node.value, (int, bool, str))
    if isinstance(node, ast.Name):
        return True
    if isinstance(node, ast.UnaryOp) and isinstance(
        node.op, (ast.UAdd, ast.USub, ast.Not),
    ):
        return _is_decidable_atom(node.operand, py_types)
    if isinstance(node, ast.BinOp) and isinstance(node.op, _ARITH_OPS):
        return (_is_decidable_atom(node.left, py_types)
                and _is_decidable_atom(node.right, py_types))
    return False


# ─────────────────────────────────────────────────────────────────────
#  Opaque-predicate detection
# ─────────────────────────────────────────────────────────────────────

_KNOWN_OPAQUE_NAMES = {
    "hasattr", "callable", "isinstance", "issubclass",
    "defined", "callee_safe", "module_present",
    "io_resource_available", "completes_within_budget",
    "custom_invariant_holds", "is_float_literal",
    "is_valid_for_op", "iterable_exhaustible",
    "decreases_measure_provided", "has_next",
}


def _has_opaque_predicate(node: ast.expr, *, fn_name: Optional[str] = None) -> bool:
    return bool(_opaque_predicates(node, fn_name=fn_name))


def _opaque_predicates(
    node: ast.expr, *, fn_name: Optional[str] = None,
) -> set[str]:
    """Return the set of opaque-predicate names mentioned in ``node``.

    Opaque means: a Python function call whose Lean translation will
    introduce an axiom (a name we cannot inspect) — including all
    ``_KNOWN_OPAQUE_NAMES``, calls to user functions other than
    ``fn_name`` itself (calls to ``fn_name`` are the function's own
    return — semantically transparent), and attribute calls (those
    are method lookups deppy can't generally resolve).
    """
    found: set[str] = set()
    for sub in ast.walk(node):
        if isinstance(sub, ast.Call):
            if isinstance(sub.func, ast.Name):
                name = sub.func.id
                if name in _KNOWN_OPAQUE_NAMES:
                    found.add(name)
                elif fn_name is not None and name == fn_name:
                    # Recursive reference to the result — not opaque.
                    pass
                elif name in (
                    "len", "abs", "min", "max", "int", "float", "str",
                    "bool", "list", "tuple", "set", "dict",
                    "all", "any", "sum", "sorted", "reversed", "range",
                ):
                    # Standard library — translatable; not opaque.
                    pass
                else:
                    # Unknown user-defined function call.
                    found.add(name)
            elif isinstance(sub.func, ast.Attribute):
                # Method call — we don't analyse method bodies.
                found.add(_attr_path(sub.func))
        if isinstance(sub, ast.Subscript):
            # Subscripts are okay (decidable in Lean).
            pass
        if isinstance(sub, ast.Attribute):
            # Bare attribute reads (``x.foo`` outside a call) are opaque.
            # Exception: an immediate child of an ``ast.Call`` is
            # already handled by the call branch above; here we
            # look only at attributes used as values.
            pass  # handled separately if we want stricter
    return found


def _attr_path(node: ast.Attribute) -> str:
    parts: list[str] = [node.attr]
    cur: ast.expr = node.value
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if isinstance(cur, ast.Name):
        parts.append(cur.id)
    return ".".join(reversed(parts))


# ─────────────────────────────────────────────────────────────────────
#  Definitional / simp-friendly detection
# ─────────────────────────────────────────────────────────────────────


def _differs_only_by_simp(pre: ast.expr, post: ast.expr) -> bool:
    """Heuristic: ``pre`` and ``post`` differ only in ways simp would
    bridge.  Examples:

    * ``a > 0``  vs ``0 < a``        (commutative compare)
    * ``a == b`` vs ``b == a``       (commutative eq)
    * ``a + b``  vs ``b + a``        (commutative add)
    * ``a + 0``  vs ``a``            (right-identity)
    * ``a * 1``  vs ``a``            (right-identity)

    We canonicalise both AST trees and check structural equality.
    """
    return _canon(pre) == _canon(post)


def _canon(node: ast.expr) -> str:
    """Return a canonical string for an AST node — sorted boolean
    operators, sorted commutative binops, comparison operators
    rewritten to ``<`` / ``≤`` form."""

    def go(n: ast.expr) -> str:
        if isinstance(n, ast.Constant):
            return f"C({n.value!r})"
        if isinstance(n, ast.Name):
            return f"N({n.id})"
        if isinstance(n, ast.UnaryOp):
            return f"U({type(n.op).__name__}, {go(n.operand)})"
        if isinstance(n, ast.BinOp):
            l = go(n.left)
            r = go(n.right)
            op_t = type(n.op).__name__
            if op_t in ("Add", "Mult"):
                # Drop identity (a + 0 → a, a * 1 → a).
                if op_t == "Add":
                    if isinstance(n.right, ast.Constant) and n.right.value == 0:
                        return l
                    if isinstance(n.left, ast.Constant) and n.left.value == 0:
                        return r
                if op_t == "Mult":
                    if isinstance(n.right, ast.Constant) and n.right.value == 1:
                        return l
                    if isinstance(n.left, ast.Constant) and n.left.value == 1:
                        return r
                # Commutative — sort.
                if r < l:
                    l, r = r, l
            return f"B({op_t}, {l}, {r})"
        if isinstance(n, ast.Compare) and len(n.ops) == 1:
            op = n.ops[0]
            l = go(n.left)
            r = go(n.comparators[0])
            if isinstance(op, ast.Eq):
                if r < l:
                    l, r = r, l
                return f"Eq({l}, {r})"
            if isinstance(op, ast.NotEq):
                if r < l:
                    l, r = r, l
                return f"NEq({l}, {r})"
            if isinstance(op, ast.Lt):
                return f"Lt({l}, {r})"
            if isinstance(op, ast.LtE):
                return f"Le({l}, {r})"
            if isinstance(op, ast.Gt):
                # Rewrite as Lt with swapped sides.
                return f"Lt({r}, {l})"
            if isinstance(op, ast.GtE):
                return f"Le({r}, {l})"
        if isinstance(n, ast.BoolOp):
            parts = sorted(go(v) for v in n.values)
            op_t = type(n.op).__name__
            return f"BO({op_t}, {','.join(parts)})"
        return f"X({type(n).__name__})"

    return go(node)


# ─────────────────────────────────────────────────────────────────────
#  Aesop-friendly detection
# ─────────────────────────────────────────────────────────────────────


def _is_aesop_friendly(
    pre: ast.expr, post: ast.expr, py_types: dict[str, str],
) -> bool:
    """Aesop is a structural classical-style automation; it's likely
    to win when the goal is propositional with at most a single
    quantifier and no opaque atoms.  We check for opaque atoms
    independently before reaching here, so the test is just for
    structural simplicity."""

    if _has_opaque_predicate(pre) or _has_opaque_predicate(post):
        return False
    # Crude size check: aesop benchmarks suggest it handles up to
    # ~50 connectives reliably.  Larger goals tend to blow up.
    if _ast_size(pre) + _ast_size(post) > 50:
        return False
    return _all_atoms_decidable(pre, py_types) and _all_atoms_decidable(
        post, py_types,
    )


def _ast_size(node: ast.expr) -> int:
    return sum(1 for _ in ast.walk(node))


def _all_atoms_decidable(node: ast.expr, py_types: dict[str, str]) -> bool:
    """Reject any node containing a function call (opaque) or a
    name annotated with a non-decidable type (e.g. a custom class
    without a Lean ``DecidableEq`` instance)."""
    for sub in ast.walk(node):
        if isinstance(sub, ast.Call):
            return False
        if isinstance(sub, ast.Name) and sub.id in py_types:
            ty = py_types[sub.id]
            # Custom class names start with a capital and are not
            # ``Bool`` / ``Int`` / ``Nat`` / ``Float`` / ``String``.
            if ty and ty[:1].isupper() and ty not in {
                "Int", "Nat", "Bool", "Float", "Str", "String",
                "List", "Dict", "Set", "Tuple", "Optional",
            }:
                return False
    return True


# ─────────────────────────────────────────────────────────────────────
#  Reporting helpers
# ─────────────────────────────────────────────────────────────────────


@dataclass
class ImpliesAuditEntry:
    """One row in the certificate's ``@implies`` audit log."""

    fn_name: str
    idx: int
    pre_py: str
    post_py: str
    classification: ImpliesClassification
    is_sorry: bool
    confidence: float
    notes: list[str]
    sorry_reason: Optional[str] = None
    user_supplied: bool = False

    def to_dict(self) -> dict:
        return {
            "fn_name": self.fn_name,
            "idx": self.idx,
            "pre": self.pre_py,
            "post": self.post_py,
            "classification": self.classification.value,
            "is_sorry": self.is_sorry,
            "confidence": self.confidence,
            "notes": list(self.notes),
            "sorry_reason": self.sorry_reason,
            "user_supplied": self.user_supplied,
        }


def render_audit_summary(entries: list[ImpliesAuditEntry]) -> str:
    """Render a Lean-comment audit summary for inclusion at the top of
    the certificate.  The summary lists every ``@implies`` obligation
    and its classification — so a user can see at a glance which
    obligations were auto-proved, sorry-emitted, or user-supplied.
    """
    if not entries:
        return ""
    lines = [
        "/-! ## ``@implies`` audit summary",
        "",
        "| Function | # | Classification | sorry? | Confidence |",
        "|----------|---|---------------|--------|------------|",
    ]
    for e in entries:
        sorry_mark = "✗" if e.is_sorry else " "
        if e.user_supplied:
            cls = "user-supplied"
        else:
            cls = e.classification.value
        lines.append(
            f"| `{e.fn_name}` | {e.idx} | {cls} | {sorry_mark} | "
            f"{e.confidence:.2f} |"
        )
    lines.append("-/")
    return "\n".join(lines) + "\n"


def count_unproved(entries: list[ImpliesAuditEntry]) -> int:
    return sum(1 for e in entries if e.is_sorry)


def count_auto_proved(entries: list[ImpliesAuditEntry]) -> int:
    return sum(
        1 for e in entries
        if not e.is_sorry and not e.user_supplied
    )


def count_user_supplied(entries: list[ImpliesAuditEntry]) -> int:
    return sum(1 for e in entries if e.user_supplied)


__all__ = [
    "ImpliesClassification",
    "ImpliesTacticPlan",
    "ImpliesAuditEntry",
    "select_implies_tactic",
    "render_audit_summary",
    "count_unproved",
    "count_auto_proved",
    "count_user_supplied",
]
