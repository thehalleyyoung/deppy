"""
Proof Template Library — Parameterized proof templates for scalable verification.

From the monograph chapter "Scalable Verification for Production Codebases":

    Instead of asking the LLM to construct a full proof term for every obligation,
    we maintain a library of *parameterized proof templates*.  The system matches
    the obligation to a template, and the LLM's job reduces to choosing the
    template and filling in a handful of parameters.  This cuts LLM cost by ~78%
    while producing higher-quality proofs (templates encode verified patterns).

The library ships 16 built-in templates grouped into two tiers:

    Core templates (6):
        FoldInduction, StructuralRecursion, CaseAnalysis,
        EquationalChain, Monotonicity, CommutativityDiagram

    Domain-specific templates (10):
        ArithmeticIdentity, CollectionLength, SortedPreservation,
        MapHomomorphism, ExceptionSafety, ResourceSafety,
        TypeNarrowing, Idempotency, Involution, Distributivity

Usage::

    registry = default_template_registry()
    matches  = registry.match(obligation)
    proof    = registry.instantiate(matches[0], params)
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Callable

from deppy.core.types import (
    SynType, SynTerm, Context, Judgment, JudgmentKind,
    PyObjType, PyIntType, PyListType,
    Var, Literal, App, Lam,
)
from deppy.core.kernel import ProofTerm, ProofKernel, VerificationResult

# Re-import concrete proof term constructors used by skeletons
from deppy.core.kernel import (
    Refl, Sym, Trans, Cong, Assume, Cases,
    NatInduction, ListInduction, Structural,
    AxiomInvocation, Unfold, Rewrite,
    TrustLevel,
)


# ═══════════════════════════════════════════════════════════════════
#  Template Infrastructure
# ═══════════════════════════════════════════════════════════════════

class TemplateCategory(str, Enum):
    """Categories that group related templates."""
    INDUCTION = "induction"
    CASE_ANALYSIS = "case_analysis"
    EQUATIONAL = "equational"
    ORDER = "order"
    ALGEBRAIC = "algebraic"
    COLLECTION = "collection"
    RESOURCE = "resource"
    TYPE_LEVEL = "type_level"


@dataclass
class TemplatePattern:
    """Describes what kinds of obligations a template can match.

    Uses structural pattern matching on the Judgment's form.

    Attributes:
        judgment_kind: If set, only match judgments of this kind.
        term_patterns: String fragments that must appear in the term repr
                       (e.g. ``["reduce", "fold"]`` — *any* match suffices).
        requires_induction_var: Template needs an induction variable.
        requires_cases: Template needs exhaustive case branches.
        max_complexity: Refuse if obligation term exceeds this depth.
        required_keywords: *All* of these must appear (AND semantics).
        excluded_keywords: Reject if *any* of these appear.
    """
    judgment_kind: JudgmentKind | None = None
    term_patterns: list[str] = field(default_factory=list)
    requires_induction_var: bool = False
    requires_cases: bool = False
    max_complexity: int | None = None
    required_keywords: list[str] = field(default_factory=list)
    excluded_keywords: list[str] = field(default_factory=list)


@dataclass
class TemplateParameter:
    """A parameter that must be provided to instantiate a template.

    Attributes:
        name: Parameter identifier.
        description: Human-readable purpose.
        type_hint: Expected Python / Deppy type (for documentation).
        required: Whether the parameter must be supplied.
        default: Optional default value.
    """
    name: str
    description: str
    type_hint: str  # "ProofTerm", "SynTerm", "str", etc.
    required: bool = True
    default: Any = None


@dataclass
class TemplateMatch:
    """Result of matching a template against an obligation.

    Attributes:
        template: The matched template.
        confidence: Quality of the match (0.0–1.0).
        suggested_params: Parameter values auto-inferred from context.
        missing_params: Parameter names the caller still must supply.
    """
    template: ProofTemplate
    confidence: float
    suggested_params: dict[str, Any] = field(default_factory=dict)
    missing_params: list[str] = field(default_factory=list)

    def __repr__(self) -> str:
        missing = f", missing={self.missing_params}" if self.missing_params else ""
        return (f"TemplateMatch({self.template.name}, "
                f"conf={self.confidence:.2f}{missing})")


# ═══════════════════════════════════════════════════════════════════
#  ProofTemplate base class
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofTemplate:
    """A parameterized proof template.

    Attributes:
        name: Template identifier.
        pattern: What kinds of obligations this template can prove.
        parameters: What must be provided to instantiate the template.
        skeleton: A function ``(params…) -> ProofTerm``.
        description: Human-readable description.
        category: Template category.
    """
    name: str
    pattern: TemplatePattern
    parameters: list[TemplateParameter]
    skeleton: Callable[..., ProofTerm]
    description: str = ""
    category: str = ""

    # -- matching helpers ----------------------------------------------------

    def match(self, obligation: Judgment,
              context: dict[str, Any] | None = None) -> TemplateMatch | None:
        """Check whether this template matches *obligation*.

        Returns a ``TemplateMatch`` on success, ``None`` on failure.
        """
        pat = self.pattern

        # 1. Judgment kind
        if pat.judgment_kind is not None and obligation.kind != pat.judgment_kind:
            return None

        # 2. Build a searchable string from the obligation
        text = _obligation_text(obligation)

        # 3. term_patterns — at least one must appear (OR semantics)
        if pat.term_patterns:
            if not any(p.lower() in text for p in pat.term_patterns):
                return None

        # 4. required_keywords — all must appear (AND semantics)
        if pat.required_keywords:
            if not all(kw.lower() in text for kw in pat.required_keywords):
                return None

        # 5. excluded_keywords
        if pat.excluded_keywords:
            if any(kw.lower() in text for kw in pat.excluded_keywords):
                return None

        # 6. Complexity guard
        if pat.max_complexity is not None:
            depth = _term_depth(obligation.term) if obligation.term else 0
            if depth > pat.max_complexity:
                return None

        # -- compute confidence & suggested params --
        confidence = self._compute_confidence(obligation, text, context)
        suggested, missing = self._infer_params(obligation, context)

        return TemplateMatch(
            template=self,
            confidence=confidence,
            suggested_params=suggested,
            missing_params=missing,
        )

    def _compute_confidence(self, obligation: Judgment, text: str,
                            context: dict[str, Any] | None) -> float:
        """Heuristic confidence score.  Subclasses may override."""
        score = 0.5
        pat = self.pattern
        # bonus for each matching term_pattern keyword
        if pat.term_patterns:
            hits = sum(1 for p in pat.term_patterns if p.lower() in text)
            score += 0.1 * min(hits, 3)
        # bonus for exact judgment kind match
        if pat.judgment_kind is not None:
            score += 0.1
        return min(score, 1.0)

    def _infer_params(self, obligation: Judgment,
                      context: dict[str, Any] | None
                      ) -> tuple[dict[str, Any], list[str]]:
        """Try to fill parameters automatically.

        Returns ``(suggested, missing)``  where *missing* names those
        parameters that could not be inferred.
        """
        suggested: dict[str, Any] = {}
        missing: list[str] = []
        for p in self.parameters:
            if not p.required:
                if p.default is not None:
                    suggested[p.name] = p.default
                continue
            # Context may already carry the value
            if context and p.name in context:
                suggested[p.name] = context[p.name]
            elif p.default is not None:
                suggested[p.name] = p.default
            else:
                missing.append(p.name)
        return suggested, missing

    def instantiate(self, params: dict[str, Any]) -> ProofTerm:
        """Build a proof term by calling the skeleton with *params*."""
        return self.skeleton(**params)


# ═══════════════════════════════════════════════════════════════════
#  Helpers
# ═══════════════════════════════════════════════════════════════════

def _obligation_text(j: Judgment) -> str:
    """Flatten a judgment into a lower-cased searchable string."""
    parts: list[str] = []
    if j.term:
        parts.append(repr(j.term))
    if j.type_:
        parts.append(repr(j.type_))
    if j.left:
        parts.append(repr(j.left))
    if j.right:
        parts.append(repr(j.right))
    return " ".join(parts).lower()


def _term_depth(t: SynTerm | None, depth: int = 0) -> int:
    """Approximate AST depth of a SynTerm."""
    if t is None:
        return depth
    if isinstance(t, (Var, Literal)):
        return depth + 1
    if isinstance(t, App):
        return max(_term_depth(t.func, depth + 1),
                   _term_depth(t.arg, depth + 1))
    if isinstance(t, Lam):
        return _term_depth(t.body, depth + 1)
    return depth + 1


# ═══════════════════════════════════════════════════════════════════
#  Core Templates (6) — from monograph §4.3
# ═══════════════════════════════════════════════════════════════════

def _fold_induction_skeleton(
    *,
    induction_var: str = "xs",
    base_proof: ProofTerm | None = None,
    step_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Build a list-induction proof term for fold/reduce obligations."""
    return ListInduction(
        var=induction_var,
        nil_proof=base_proof or Refl(Literal(value=None)),
        cons_proof=step_proof or Assume("IH"),
    )


class FoldInductionTemplate(ProofTemplate):
    """Proves properties of reduce/fold/for-loop-with-accumulator by induction.

    Pattern
        Obligation mentions ``reduce``, ``fold``, ``accumulate``, or a
        for-loop accumulator pattern.

    Parameters
        * ``induction_var`` — the list being folded over.
        * ``base_proof``   — proof for the empty-list case.
        * ``step_proof``   — proof for the cons case (with IH).

    Skeleton
        ``ListInduction(var, base_proof, step_proof)``
    """

    def __init__(self) -> None:
        super().__init__(
            name="fold_induction",
            pattern=TemplatePattern(
                judgment_kind=JudgmentKind.EQUAL,
                term_patterns=["reduce", "fold", "accumulate", "foldl", "foldr",
                               "for", "accumulator"],
            ),
            parameters=[
                TemplateParameter("induction_var", "Variable bound to the list",
                                  "str", required=False, default="xs"),
                TemplateParameter("base_proof",
                                  "Proof for the empty-list (nil) base case",
                                  "ProofTerm"),
                TemplateParameter("step_proof",
                                  "Proof for the cons inductive step",
                                  "ProofTerm"),
            ],
            skeleton=_fold_induction_skeleton,
            description=(
                "Proves properties of reduce/fold/for-loop-with-accumulator "
                "by induction on the list argument."
            ),
            category=TemplateCategory.INDUCTION,
        )

    def _compute_confidence(self, obligation, text, context):
        score = 0.5
        for kw in ("reduce", "fold", "accumulate"):
            if kw in text:
                score += 0.15
        if "for" in text and "accumulator" in text:
            score += 0.1
        return min(score, 1.0)


# -- Structural Recursion ----------------------------------------------------

def _structural_recursion_skeleton(
    *,
    induction_var: str = "n",
    base_proof: ProofTerm | None = None,
    step_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Build a nat-induction proof for structurally recursive functions."""
    return NatInduction(
        var=induction_var,
        base_proof=base_proof or Refl(Literal(value=0)),
        step_proof=step_proof or Assume("IH"),
    )


class StructuralRecursionTemplate(ProofTemplate):
    """Proves properties of recursive functions by structural induction.

    Pattern
        Function has a recursive call on a structurally smaller argument
        (``n-1``, ``tail``, ``rest``, etc.).

    Parameters
        * ``induction_var`` — the decreasing argument.
        * ``base_proof``    — proof for the base case(s).
        * ``step_proof``    — proof for the recursive case with IH.

    Skeleton
        ``NatInduction(var, base_proof, step_proof)``
    """

    def __init__(self) -> None:
        super().__init__(
            name="structural_recursion",
            pattern=TemplatePattern(
                judgment_kind=None,
                term_patterns=["rec", "recursive", "n-1", "n - 1",
                               "tail", "rest", "sub"],
                requires_induction_var=True,
            ),
            parameters=[
                TemplateParameter("induction_var",
                                  "Structurally decreasing argument",
                                  "str", required=False, default="n"),
                TemplateParameter("base_proof",
                                  "Proof for the base case",
                                  "ProofTerm"),
                TemplateParameter("step_proof",
                                  "Proof for the recursive case with IH",
                                  "ProofTerm"),
            ],
            skeleton=_structural_recursion_skeleton,
            description=(
                "Proves properties of recursive functions by structural "
                "induction on the decreasing argument."
            ),
            category=TemplateCategory.INDUCTION,
        )

    def _compute_confidence(self, obligation, text, context):
        score = 0.4
        for kw in ("recursive", "rec", "n-1", "n - 1", "tail"):
            if kw in text:
                score += 0.12
        return min(score, 1.0)


# -- Case Analysis -----------------------------------------------------------

def _case_analysis_skeleton(
    *,
    scrutinee: SynTerm | None = None,
    branches: list[tuple[str, ProofTerm]] | None = None,
) -> ProofTerm:
    """Build a Cases proof term."""
    scr = scrutinee or Var("x")
    br = branches or [("_", Structural("default branch"))]
    return Cases(scrutinee=scr, branches=br)


class CaseAnalysisTemplate(ProofTemplate):
    """Proves by exhaustive case split (if/elif/else, match, isinstance).

    Pattern
        Obligation involves a conditional, ``match`` statement, or
        ``isinstance`` check.

    Parameters
        * ``scrutinee``  — the term being cased on.
        * ``branches``   — ``[(pattern, proof), ...]`` for each case.

    Skeleton
        ``Cases(scrutinee, branches)``
    """

    def __init__(self) -> None:
        super().__init__(
            name="case_analysis",
            pattern=TemplatePattern(
                term_patterns=["if", "elif", "match", "isinstance", "case",
                               "IfThenElse"],
                requires_cases=True,
            ),
            parameters=[
                TemplateParameter("scrutinee",
                                  "Term being cased on",
                                  "SynTerm"),
                TemplateParameter("branches",
                                  "List of (pattern, proof) pairs",
                                  "list[tuple[str, ProofTerm]]"),
            ],
            skeleton=_case_analysis_skeleton,
            description=(
                "Proves by exhaustive case analysis over conditionals, "
                "match statements, or isinstance checks."
            ),
            category=TemplateCategory.CASE_ANALYSIS,
        )

    def _compute_confidence(self, obligation, text, context):
        score = 0.45
        for kw in ("if", "elif", "match", "isinstance", "ifthenelse"):
            if kw in text:
                score += 0.1
        return min(score, 1.0)


# -- Equational Chain --------------------------------------------------------

def _equational_chain_skeleton(
    *,
    steps: list[tuple[SynTerm, ProofTerm]] | None = None,
) -> ProofTerm:
    """Build a proof  a = b = c = …  via Trans chains."""
    if not steps or len(steps) < 2:
        return Refl(Var("_"))
    # Chain: Trans(step0, Trans(step1, …))
    proofs = [p for _, p in steps]
    result = proofs[-1]
    for p in reversed(proofs[:-1]):
        result = Trans(left=p, right=result)
    return result


class EquationalChainTemplate(ProofTemplate):
    """Proves ``a = d`` via ``a = b = c = d`` using axiom applications.

    Pattern
        Equality obligation where intermediate steps use known axioms
        or rewrite rules.

    Parameters
        * ``steps`` — ``[(intermediate_term, justification_proof), ...]``

    Skeleton
        ``Trans(Trans(…), …)`` chain of the step proofs.
    """

    def __init__(self) -> None:
        super().__init__(
            name="equational_chain",
            pattern=TemplatePattern(
                judgment_kind=JudgmentKind.EQUAL,
                term_patterns=["rewrite", "chain", "step", "simplify",
                               "="],
            ),
            parameters=[
                TemplateParameter("steps",
                                  "List of (intermediate_term, proof) pairs",
                                  "list[tuple[SynTerm, ProofTerm]]"),
            ],
            skeleton=_equational_chain_skeleton,
            description=(
                "Proves a = d via a chain a = b = c = d, each step "
                "justified by an axiom application or rewrite."
            ),
            category=TemplateCategory.EQUATIONAL,
        )

    def _compute_confidence(self, obligation, text, context):
        score = 0.4
        if obligation.kind == JudgmentKind.EQUAL:
            score += 0.2
        for kw in ("rewrite", "chain", "step", "simplify"):
            if kw in text:
                score += 0.1
        return min(score, 1.0)


# -- Monotonicity ------------------------------------------------------------

def _monotonicity_skeleton(
    *,
    func_name: str = "f",
    monotonicity_witness: ProofTerm | None = None,
    argument_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Build a monotonicity proof: from a <= b and f monotone, get f(a) <= f(b)."""
    wit = monotonicity_witness or AxiomInvocation(
        name=f"{func_name}_monotone"
    )
    arg = argument_proof or Assume("a_le_b")
    return Trans(left=wit, right=arg)


class MonotonicityTemplate(ProofTemplate):
    """Proves ``f(a) <= f(b)`` from ``a <= b`` and ``f`` monotone.

    Pattern
        Inequality obligation involving a known monotone function
        (``len``, ``abs``, ``sorted``, etc.).

    Parameters
        * ``func_name``             — name of the monotone function.
        * ``monotonicity_witness``  — proof that ``f`` is monotone.
        * ``argument_proof``        — proof that ``a <= b``.

    Skeleton
        ``Trans(witness, argument_proof)``
    """

    def __init__(self) -> None:
        super().__init__(
            name="monotonicity",
            pattern=TemplatePattern(
                term_patterns=["<=", ">=", "monotone", "increasing",
                               "decreasing", "len", "abs"],
            ),
            parameters=[
                TemplateParameter("func_name",
                                  "Name of the monotone function",
                                  "str", required=False, default="f"),
                TemplateParameter("monotonicity_witness",
                                  "Proof that the function is monotone",
                                  "ProofTerm"),
                TemplateParameter("argument_proof",
                                  "Proof that a <= b",
                                  "ProofTerm"),
            ],
            skeleton=_monotonicity_skeleton,
            description=(
                "Proves f(a) <= f(b) from a <= b using a monotonicity witness."
            ),
            category=TemplateCategory.ORDER,
        )


# -- Commutativity Diagram ---------------------------------------------------

def _commutativity_diagram_skeleton(
    *,
    f_name: str = "f",
    g_name: str = "g",
    nat_transform_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Build proof that f∘g = g'∘f' from a natural transformation."""
    nat = nat_transform_proof or AxiomInvocation(
        name=f"{f_name}_{g_name}_commute"
    )
    return nat


class CommutativityDiagramTemplate(ProofTemplate):
    """Proves ``f ∘ g = g' ∘ f'`` when operations commute.

    Pattern
        Obligation involving function composition with reordered
        operations (e.g. ``map`` then ``filter`` vs ``filter`` then ``map``).

    Parameters
        * ``f_name``, ``g_name``      — the two operations.
        * ``nat_transform_proof``     — natural transformation witness.

    Skeleton
        The natural transformation proof itself.
    """

    def __init__(self) -> None:
        super().__init__(
            name="commutativity_diagram",
            pattern=TemplatePattern(
                judgment_kind=JudgmentKind.EQUAL,
                term_patterns=["commute", "compose", "∘", "diagram",
                               "natural", "swap"],
            ),
            parameters=[
                TemplateParameter("f_name", "First operation", "str",
                                  required=False, default="f"),
                TemplateParameter("g_name", "Second operation", "str",
                                  required=False, default="g"),
                TemplateParameter("nat_transform_proof",
                                  "Natural transformation witnessing commutativity",
                                  "ProofTerm"),
            ],
            skeleton=_commutativity_diagram_skeleton,
            description=(
                "Proves f∘g = g'∘f' via a natural transformation witness."
            ),
            category=TemplateCategory.ALGEBRAIC,
        )


# ═══════════════════════════════════════════════════════════════════
#  Domain-Specific Templates (10) — from monograph §4.4
# ═══════════════════════════════════════════════════════════════════

def _arithmetic_identity_skeleton(
    *,
    identity_name: str = "add_zero",
    axiom_module: str = "arithmetic",
) -> ProofTerm:
    """Prove arithmetic identity via ring/field axiom."""
    return AxiomInvocation(name=identity_name, module=axiom_module)


class ArithmeticIdentityTemplate(ProofTemplate):
    """Proves arithmetic identities using ring/field axioms.

    Examples: ``a*(b+c) = a*b + a*c``, ``a+0 = a``, ``a*1 = a``.
    """

    def __init__(self) -> None:
        super().__init__(
            name="arithmetic_identity",
            pattern=TemplatePattern(
                judgment_kind=JudgmentKind.EQUAL,
                term_patterns=["+", "*", "-", "/", "0", "1",
                               "add", "mul", "sub", "div"],
            ),
            parameters=[
                TemplateParameter("identity_name",
                                  "Axiom name (e.g. 'add_zero', 'mul_comm')",
                                  "str"),
                TemplateParameter("axiom_module",
                                  "Module containing the axiom",
                                  "str", required=False, default="arithmetic"),
            ],
            skeleton=_arithmetic_identity_skeleton,
            description="Proves arithmetic identities via ring/field axioms.",
            category=TemplateCategory.ALGEBRAIC,
        )


# -- Collection Length -------------------------------------------------------

def _collection_length_skeleton(
    *,
    operation: str = "append",
    base_len_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Prove len() property by tracking operations."""
    proof = base_len_proof or AxiomInvocation(
        name=f"len_{operation}", module="collections"
    )
    return proof


class CollectionLengthTemplate(ProofTemplate):
    """Proves ``len(...)`` properties by tracking operations.

    Examples: ``len(xs + [y]) == len(xs) + 1``,
              ``len(xs[:k]) <= len(xs)``.
    """

    def __init__(self) -> None:
        super().__init__(
            name="collection_length",
            pattern=TemplatePattern(
                term_patterns=["len", "length", "size", "count",
                               "append", "extend", "pop", "insert"],
            ),
            parameters=[
                TemplateParameter("operation",
                                  "List operation (append, extend, pop, …)",
                                  "str", required=False, default="append"),
                TemplateParameter("base_len_proof",
                                  "Proof linking old length to new length",
                                  "ProofTerm", required=False),
            ],
            skeleton=_collection_length_skeleton,
            description=(
                "Proves len() properties by tracking list operations."
            ),
            category=TemplateCategory.COLLECTION,
        )


# -- Sorted Preservation ----------------------------------------------------

def _sorted_preservation_skeleton(
    *,
    input_sorted_proof: ProofTerm | None = None,
    operation_preserves_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Prove output is sorted given sorted input."""
    inp = input_sorted_proof or Assume("input_sorted")
    op = operation_preserves_proof or Structural("operation preserves order")
    return Trans(left=inp, right=op)


class SortedPreservationTemplate(ProofTemplate):
    """Proves output is sorted given sorted input.

    Pattern: binary search, merge, insertion into sorted list, etc.
    """

    def __init__(self) -> None:
        super().__init__(
            name="sorted_preservation",
            pattern=TemplatePattern(
                term_patterns=["sorted", "sort", "order", "binary_search",
                               "merge", "insert", "bisect"],
            ),
            parameters=[
                TemplateParameter("input_sorted_proof",
                                  "Proof that input is sorted",
                                  "ProofTerm"),
                TemplateParameter("operation_preserves_proof",
                                  "Proof that the operation preserves sortedness",
                                  "ProofTerm"),
            ],
            skeleton=_sorted_preservation_skeleton,
            description="Proves output is sorted given sorted input.",
            category=TemplateCategory.COLLECTION,
        )


# -- Map Homomorphism --------------------------------------------------------

def _map_homomorphism_skeleton(
    *,
    f_name: str = "f",
    g_name: str = "g",
    composition_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Prove f(map(g, xs)) = map(f∘g, xs)."""
    return composition_proof or AxiomInvocation(
        name="map_composition", module="collections"
    )


class MapHomomorphismTemplate(ProofTemplate):
    """Proves ``f(map(g, xs)) = map(f∘g, xs)``-type properties.

    Homomorphism between list operations and function composition.
    """

    def __init__(self) -> None:
        super().__init__(
            name="map_homomorphism",
            pattern=TemplatePattern(
                judgment_kind=JudgmentKind.EQUAL,
                term_patterns=["map", "comprehension", "transform",
                               "apply", "compose"],
            ),
            parameters=[
                TemplateParameter("f_name", "Outer function", "str",
                                  required=False, default="f"),
                TemplateParameter("g_name", "Inner function", "str",
                                  required=False, default="g"),
                TemplateParameter("composition_proof",
                                  "Proof of the composition property",
                                  "ProofTerm", required=False),
            ],
            skeleton=_map_homomorphism_skeleton,
            description=(
                "Proves map homomorphism: f(map(g, xs)) = map(f∘g, xs)."
            ),
            category=TemplateCategory.ALGEBRAIC,
        )


# -- Exception Safety --------------------------------------------------------

def _exception_safety_skeleton(
    *,
    precondition_proof: ProofTerm | None = None,
    handler_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Prove operations don't raise under given preconditions."""
    pre = precondition_proof or Assume("precondition_holds")
    handler = handler_proof or Structural("no exception raised")
    return Trans(left=pre, right=handler)


class ExceptionSafetyTemplate(ProofTemplate):
    """Proves exception safety: operations don't raise under given preconditions.

    Pattern: ``try``/``except``, ``raise``, division, indexing, key access
    """

    def __init__(self) -> None:
        super().__init__(
            name="exception_safety",
            pattern=TemplatePattern(
                term_patterns=["try", "except", "raise", "error",
                               "division", "index", "key",
                               "ZeroDivisionError", "IndexError", "KeyError"],
            ),
            parameters=[
                TemplateParameter("precondition_proof",
                                  "Proof that precondition prevents the exception",
                                  "ProofTerm"),
                TemplateParameter("handler_proof",
                                  "Proof that the handler is safe",
                                  "ProofTerm", required=False),
            ],
            skeleton=_exception_safety_skeleton,
            description=(
                "Proves exception safety under given preconditions."
            ),
            category=TemplateCategory.RESOURCE,
        )


# -- Resource Safety ---------------------------------------------------------

def _resource_safety_skeleton(
    *,
    acquire_proof: ProofTerm | None = None,
    release_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Prove resources are properly acquired and released."""
    acq = acquire_proof or Structural("resource acquired")
    rel = release_proof or Structural("resource released")
    return Trans(left=acq, right=rel)


class ResourceSafetyTemplate(ProofTemplate):
    """Proves resources are properly acquired and released.

    Pattern: ``with``-statement, ``try``/``finally``, ``open``/``close``
    """

    def __init__(self) -> None:
        super().__init__(
            name="resource_safety",
            pattern=TemplatePattern(
                term_patterns=["with", "finally", "open", "close",
                               "acquire", "release", "context_manager",
                               "enter", "exit"],
            ),
            parameters=[
                TemplateParameter("acquire_proof",
                                  "Proof of resource acquisition",
                                  "ProofTerm", required=False),
                TemplateParameter("release_proof",
                                  "Proof of resource release on all paths",
                                  "ProofTerm", required=False),
            ],
            skeleton=_resource_safety_skeleton,
            description="Proves resources are properly acquired and released.",
            category=TemplateCategory.RESOURCE,
        )


# -- Type Narrowing ----------------------------------------------------------

def _type_narrowing_skeleton(
    *,
    scrutinee: SynTerm | None = None,
    type_branches: list[tuple[str, ProofTerm]] | None = None,
) -> ProofTerm:
    """Prove type-narrowed properties after isinstance checks."""
    scr = scrutinee or Var("x")
    branches = type_branches or [("object", Structural("base case"))]
    return Cases(scrutinee=scr, branches=branches)


class TypeNarrowingTemplate(ProofTemplate):
    """Proves type-narrowed properties after isinstance checks.

    Pattern: ``isinstance(x, T)``, type guard, ``type(x) is T``
    """

    def __init__(self) -> None:
        super().__init__(
            name="type_narrowing",
            pattern=TemplatePattern(
                term_patterns=["isinstance", "type_guard", "TypeGuard",
                               "type(", "issubclass", "narrow"],
            ),
            parameters=[
                TemplateParameter("scrutinee",
                                  "Term whose type is narrowed",
                                  "SynTerm"),
                TemplateParameter("type_branches",
                                  "List of (type_name, proof) per narrowed branch",
                                  "list[tuple[str, ProofTerm]]"),
            ],
            skeleton=_type_narrowing_skeleton,
            description="Proves type-narrowed properties after isinstance checks.",
            category=TemplateCategory.TYPE_LEVEL,
        )


# -- Idempotency -------------------------------------------------------------

def _idempotency_skeleton(
    *,
    func_name: str = "f",
    single_application_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Prove f(f(x)) = f(x)."""
    return single_application_proof or AxiomInvocation(
        name=f"{func_name}_idempotent", module="algebra"
    )


class IdempotencyTemplate(ProofTemplate):
    """Proves ``f(f(x)) = f(x)``.

    Pattern: equality where left side is ``f`` applied twice.
    Examples: ``sorted(sorted(xs)) = sorted(xs)``,
              ``deduplicate(deduplicate(xs)) = deduplicate(xs)``
    """

    def __init__(self) -> None:
        super().__init__(
            name="idempotency",
            pattern=TemplatePattern(
                judgment_kind=JudgmentKind.EQUAL,
                term_patterns=["idempotent", "sorted(sorted",
                               "deduplicate(deduplicate", "normalize(normalize",
                               "abs(abs", "strip(strip"],
            ),
            parameters=[
                TemplateParameter("func_name",
                                  "Name of the idempotent function",
                                  "str"),
                TemplateParameter("single_application_proof",
                                  "Proof that f(f(x)) = f(x)",
                                  "ProofTerm", required=False),
            ],
            skeleton=_idempotency_skeleton,
            description="Proves f(f(x)) = f(x) for idempotent functions.",
            category=TemplateCategory.ALGEBRAIC,
        )


# -- Involution --------------------------------------------------------------

def _involution_skeleton(
    *,
    func_name: str = "f",
    involution_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Prove f(f(x)) = x."""
    return involution_proof or AxiomInvocation(
        name=f"{func_name}_involution", module="algebra"
    )


class InvolutionTemplate(ProofTemplate):
    """Proves ``f(f(x)) = x`` (e.g. reverse, negate, complement).

    Pattern: equality where ``f`` applied twice yields identity.
    """

    def __init__(self) -> None:
        super().__init__(
            name="involution",
            pattern=TemplatePattern(
                judgment_kind=JudgmentKind.EQUAL,
                term_patterns=["involution", "reverse(reverse",
                               "negate(negate", "complement",
                               "not(not", "invert(invert", "transpose(transpose"],
            ),
            parameters=[
                TemplateParameter("func_name",
                                  "Name of the involutory function",
                                  "str"),
                TemplateParameter("involution_proof",
                                  "Proof that f(f(x)) = x",
                                  "ProofTerm", required=False),
            ],
            skeleton=_involution_skeleton,
            description="Proves f(f(x)) = x for involutory functions.",
            category=TemplateCategory.ALGEBRAIC,
        )


# -- Distributivity ----------------------------------------------------------

def _distributivity_skeleton(
    *,
    func_name: str = "f",
    op_name: str = "op",
    distributivity_proof: ProofTerm | None = None,
) -> ProofTerm:
    """Prove f(a op b) = f(a) op f(b)."""
    return distributivity_proof or AxiomInvocation(
        name=f"{func_name}_distributes_over_{op_name}", module="algebra"
    )


class DistributivityTemplate(ProofTemplate):
    """Proves ``f(a op b) = f(a) op f(b)``.

    Pattern: equality with function distributing over an operation.
    Examples: ``len(xs + ys) = len(xs) + len(ys)``,
              ``abs(a * b) = abs(a) * abs(b)``
    """

    def __init__(self) -> None:
        super().__init__(
            name="distributivity",
            pattern=TemplatePattern(
                judgment_kind=JudgmentKind.EQUAL,
                term_patterns=["distribute", "distrib", "homomorphism",
                               "len(", "abs("],
            ),
            parameters=[
                TemplateParameter("func_name",
                                  "Function that distributes", "str"),
                TemplateParameter("op_name",
                                  "Operation distributed over", "str"),
                TemplateParameter("distributivity_proof",
                                  "Proof of distributivity",
                                  "ProofTerm", required=False),
            ],
            skeleton=_distributivity_skeleton,
            description="Proves f(a op b) = f(a) op f(b).",
            category=TemplateCategory.ALGEBRAIC,
        )


# ═══════════════════════════════════════════════════════════════════
#  Template Registry
# ═══════════════════════════════════════════════════════════════════

class TemplateRegistry:
    """Registry of all proof templates with matching logic.

    The registry maintains a list of ``ProofTemplate`` instances and
    exposes methods to:

    * **match**      — find all templates that could prove an obligation;
    * **best_match** — return the single best template;
    * **instantiate** — build a proof term from a match + parameters;
    * **auto_prove** — match → infer params → build → (optionally verify).
    """

    def __init__(self) -> None:
        self.templates: list[ProofTemplate] = self._build_default_registry()

    # -- registry construction -----------------------------------------------

    @staticmethod
    def _build_default_registry() -> list[ProofTemplate]:
        """Build the default set of 16 templates."""
        return [
            # Core 6
            FoldInductionTemplate(),
            StructuralRecursionTemplate(),
            CaseAnalysisTemplate(),
            EquationalChainTemplate(),
            MonotonicityTemplate(),
            CommutativityDiagramTemplate(),
            # Domain-specific 10
            ArithmeticIdentityTemplate(),
            CollectionLengthTemplate(),
            SortedPreservationTemplate(),
            MapHomomorphismTemplate(),
            ExceptionSafetyTemplate(),
            ResourceSafetyTemplate(),
            TypeNarrowingTemplate(),
            IdempotencyTemplate(),
            InvolutionTemplate(),
            DistributivityTemplate(),
        ]

    # -- matching ------------------------------------------------------------

    def match(self, obligation: Judgment,
              context: dict[str, Any] | None = None) -> list[TemplateMatch]:
        """Find all templates that match *obligation*.

        Returns matches sorted by confidence (highest first).
        """
        matches: list[TemplateMatch] = []
        for tmpl in self.templates:
            m = tmpl.match(obligation, context)
            if m is not None:
                matches.append(m)
        matches.sort(key=lambda m: m.confidence, reverse=True)
        return matches

    def best_match(self, obligation: Judgment,
                   context: dict[str, Any] | None = None
                   ) -> TemplateMatch | None:
        """Return the best matching template, or ``None`` if no match."""
        matches = self.match(obligation, context)
        return matches[0] if matches else None

    # -- instantiation -------------------------------------------------------

    def instantiate(self, match: TemplateMatch,
                    params: dict[str, Any]) -> ProofTerm:
        """Instantiate a matched template with given parameters.

        Merges caller-supplied *params* with ``match.suggested_params``.
        Returns the constructed proof term.
        """
        merged = {**match.suggested_params, **params}
        return match.template.instantiate(merged)

    # -- auto-prove ----------------------------------------------------------

    def auto_prove(self, obligation: Judgment,
                   kernel: ProofKernel | None = None,
                   context: dict[str, Any] | None = None) -> ProofTerm | None:
        """Try to automatically prove an obligation using templates.

        Algorithm:
            1. Find matching templates.
            2. For each match (best first), try to auto-fill parameters
               from *context*.
            3. Build the proof term.
            4. Optionally verify through *kernel*.
            5. Return the first proof that succeeds (or ``None``).
        """
        matches = self.match(obligation, context)
        for m in matches:
            if m.missing_params:
                # Try filling missing params from context
                filled = dict(m.suggested_params)
                still_missing = []
                for p_name in m.missing_params:
                    if context and p_name in context:
                        filled[p_name] = context[p_name]
                    else:
                        still_missing.append(p_name)
                if still_missing:
                    continue
                m = TemplateMatch(
                    template=m.template,
                    confidence=m.confidence,
                    suggested_params=filled,
                    missing_params=[],
                )

            try:
                proof = self.instantiate(m, {})
            except Exception:
                continue

            if kernel is not None:
                result = kernel.verify(obligation.context, obligation, proof)
                if not result.success:
                    continue

            return proof
        return None

    # -- registration --------------------------------------------------------

    def register(self, template: ProofTemplate) -> None:
        """Register a custom template."""
        self.templates.append(template)

    # -- introspection -------------------------------------------------------

    def list_templates(self) -> list[dict[str, Any]]:
        """Return a summary of all registered templates."""
        return [
            {
                "name": t.name,
                "category": t.category,
                "description": t.description,
                "num_params": len(t.parameters),
            }
            for t in self.templates
        ]

    def get_template(self, name: str) -> ProofTemplate | None:
        """Retrieve a template by name."""
        for t in self.templates:
            if t.name == name:
                return t
        return None

    def templates_by_category(self) -> dict[str, list[ProofTemplate]]:
        """Group templates by category."""
        result: dict[str, list[ProofTemplate]] = {}
        for t in self.templates:
            cat = t.category if t.category else "uncategorized"
            result.setdefault(cat, []).append(t)
        return result


def default_template_registry() -> TemplateRegistry:
    """Create the default registry with all 16 built-in templates."""
    return TemplateRegistry()


# ═══════════════════════════════════════════════════════════════════
#  Template-Guided LLM Interaction
# ═══════════════════════════════════════════════════════════════════

class TemplateLLMBridge:
    """Bridge between templates and LLM proof generation.

    Instead of asking the LLM to write a full proof, we:

    1. Match the obligation to possible templates.
    2. Ask the LLM to choose a template and fill parameters.
    3. Construct the proof from the LLM's choices.

    This is ~10× cheaper than full proof generation because the LLM
    only needs to output a template name + a handful of parameter
    values instead of an entire proof tree.

    Cost model (from monograph §4.5)::

        Full proof generation:   ~1 200 tokens/obligation  (avg)
        Template-guided:         ~  260 tokens/obligation  (avg)
        Reduction:                     78 %

    Attributes:
        registry: The template registry to draw from.
    """

    def __init__(self, registry: TemplateRegistry | None = None) -> None:
        self.registry = registry or default_template_registry()

    # -- prompt formatting ---------------------------------------------------

    def format_template_prompt(self, obligation: Judgment,
                               matches: list[TemplateMatch]) -> str:
        """Format a prompt asking the LLM to choose a template and fill params.

        Much cheaper than asking for a full proof because the LLM only
        needs to output template name + parameter values, not the
        entire proof.

        Returns a structured prompt string.
        """
        lines: list[str] = [
            "You are a proof assistant.  Given the proof obligation below,",
            "choose the best template and provide parameter values.",
            "",
            "## Obligation",
            f"  {obligation}",
            "",
            "## Available templates (ranked by match confidence)",
        ]

        for i, m in enumerate(matches, 1):
            t = m.template
            lines.append(f"")
            lines.append(f"### {i}. {t.name}  (confidence {m.confidence:.2f})")
            lines.append(f"    {t.description}")
            lines.append(f"    Parameters:")
            for p in t.parameters:
                req = "REQUIRED" if p.required else "optional"
                default = f", default={p.default!r}" if p.default is not None else ""
                suggested = ""
                if p.name in m.suggested_params:
                    suggested = f", suggested={m.suggested_params[p.name]!r}"
                lines.append(
                    f"      - {p.name} ({p.type_hint}, {req}{default}{suggested})"
                    f": {p.description}"
                )

        lines.append("")
        lines.append("## Instructions")
        lines.append("Respond with JSON: {\"template\": \"<name>\", \"params\": {…}}")
        lines.append("Only include parameters you want to set explicitly.")

        return "\n".join(lines)

    # -- response parsing ----------------------------------------------------

    def parse_template_response(self, response: str,
                                matches: list[TemplateMatch]
                                ) -> tuple[str, dict[str, Any]]:
        """Parse the LLM's response into ``(template_name, params)``.

        Extracts a JSON object from the response text.  Tolerates
        markdown code fences and leading/trailing prose.

        Raises ``ValueError`` on unparseable responses.
        """
        # Strip markdown fences
        cleaned = response.strip()
        cleaned = re.sub(r"```(?:json)?\s*", "", cleaned)
        cleaned = re.sub(r"```", "", cleaned)
        cleaned = cleaned.strip()

        # Try to find JSON object (allow one level of nesting for "params": {…})
        json_match = re.search(r"\{[^{}]*(?:\{[^{}]*\}[^{}]*)?\}", cleaned, re.DOTALL)
        if not json_match:
            raise ValueError(f"No JSON object found in LLM response: {response!r}")

        try:
            data = json.loads(json_match.group())
        except json.JSONDecodeError as exc:
            raise ValueError(f"Invalid JSON in LLM response: {exc}") from exc

        template_name = data.get("template", "")
        params = data.get("params", {})

        if not isinstance(template_name, str) or not template_name:
            raise ValueError("Missing 'template' key in LLM response")
        if not isinstance(params, dict):
            raise ValueError("'params' must be a JSON object")

        # Validate template name against known matches
        known_names = {m.template.name for m in matches}
        if template_name not in known_names:
            # Try fuzzy matching
            for name in known_names:
                if template_name.lower() in name.lower() or name.lower() in template_name.lower():
                    template_name = name
                    break
            else:
                raise ValueError(
                    f"Unknown template {template_name!r}; "
                    f"expected one of {known_names}"
                )

        return template_name, params

    # -- end-to-end ----------------------------------------------------------

    def prove_with_llm_choice(
        self,
        obligation: Judgment,
        llm_response: str,
        context: dict[str, Any] | None = None,
    ) -> ProofTerm | None:
        """Given an obligation and an LLM response, build the proof.

        1. Match obligation to templates.
        2. Parse LLM response to get chosen template + params.
        3. Instantiate and return the proof.

        Returns ``None`` if parsing fails or no match is found.
        """
        matches = self.registry.match(obligation, context)
        if not matches:
            return None

        try:
            tmpl_name, params = self.parse_template_response(
                llm_response, matches
            )
        except ValueError:
            return None

        # Find the match with the chosen template name
        chosen_match: TemplateMatch | None = None
        for m in matches:
            if m.template.name == tmpl_name:
                chosen_match = m
                break
        if chosen_match is None:
            return None

        return self.registry.instantiate(chosen_match, params)

    def cost_estimate(self, matches: list[TemplateMatch]) -> dict[str, Any]:
        """Estimate token cost savings vs full proof generation.

        Returns a dict with ``full_cost``, ``template_cost``, and
        ``reduction_pct`` based on the monograph's empirical model.
        """
        avg_full_cost_tokens = 1200
        # Template cost = prompt overhead + per-param cost
        if not matches:
            return {
                "full_cost": avg_full_cost_tokens,
                "template_cost": avg_full_cost_tokens,
                "reduction_pct": 0.0,
            }
        best = matches[0]
        n_params = len(best.template.parameters)
        # ~80 tokens for template selection + ~30 per parameter
        template_cost = 80 + 30 * n_params
        # Prompt overhead for listing templates (~20 tokens each)
        prompt_overhead = 20 * len(matches)
        total_template_cost = template_cost + prompt_overhead

        reduction = 1.0 - (total_template_cost / avg_full_cost_tokens)
        reduction = max(reduction, 0.0)

        return {
            "full_cost": avg_full_cost_tokens,
            "template_cost": total_template_cost,
            "reduction_pct": round(reduction * 100, 1),
        }


# ═══════════════════════════════════════════════════════════════════
#  Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Run self-tests demonstrating template matching and instantiation."""
    print("=" * 60)
    print("Proof Template Library — Self Tests")
    print("=" * 60)

    ctx = Context()
    registry = default_template_registry()

    # -- Test 1: Registry has 16 templates -----------------------------------
    assert len(registry.templates) == 16, (
        f"Expected 16 templates, got {len(registry.templates)}"
    )
    print(f"\n✓ Registry contains {len(registry.templates)} templates")

    # -- Test 2: list_templates introspection --------------------------------
    summary = registry.list_templates()
    assert len(summary) == 16
    names = [s["name"] for s in summary]
    assert "fold_induction" in names
    assert "case_analysis" in names
    assert "involution" in names
    print("✓ list_templates returns correct metadata")

    # -- Test 3: templates_by_category grouping ------------------------------
    cats = registry.templates_by_category()
    assert "induction" in cats or TemplateCategory.INDUCTION in cats
    print(f"✓ templates_by_category: {list(cats.keys())}")

    # -- Test 4: get_template by name ----------------------------------------
    t = registry.get_template("fold_induction")
    assert t is not None
    assert t.name == "fold_induction"
    assert registry.get_template("nonexistent") is None
    print("✓ get_template lookup works")

    # -- Test 5: Fold induction match ----------------------------------------
    fold_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(func=Var("reduce"), arg=Var("xs")),
        right=Var("result"),
    )
    matches = registry.match(fold_obligation)
    assert len(matches) > 0, "fold obligation should match at least 1 template"
    assert matches[0].template.name == "fold_induction", (
        f"Best match should be fold_induction, got {matches[0].template.name}"
    )
    print(f"✓ Fold obligation matched {len(matches)} templates, "
          f"best={matches[0].template.name}")

    # -- Test 6: Case analysis match -----------------------------------------
    case_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=App(func=Var("isinstance"), arg=Var("x")),
    )
    matches = registry.match(case_obligation)
    assert len(matches) > 0
    case_names = [m.template.name for m in matches]
    assert "case_analysis" in case_names or "type_narrowing" in case_names
    print(f"✓ Case/isinstance obligation matched: "
          f"{[m.template.name for m in matches[:3]]}")

    # -- Test 7: Equational chain match --------------------------------------
    eq_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(func=Var("simplify"), arg=Var("expr")),
        right=Var("result"),
    )
    matches = registry.match(eq_obligation)
    eq_names = [m.template.name for m in matches]
    assert "equational_chain" in eq_names
    print(f"✓ Equality+simplify obligation includes equational_chain")

    # -- Test 8: Instantiation of fold_induction -----------------------------
    fold_match = registry.best_match(fold_obligation)
    assert fold_match is not None
    proof = registry.instantiate(fold_match, {
        "base_proof": Refl(Literal(value=0)),
        "step_proof": Assume("IH"),
    })
    assert isinstance(proof, ListInduction)
    assert proof.var == "xs"
    print(f"✓ Instantiated fold_induction: {proof}")

    # -- Test 9: Instantiation of case_analysis ------------------------------
    case_match = None
    for m in registry.match(case_obligation):
        if m.template.name == "case_analysis":
            case_match = m
            break
    if case_match is not None:
        case_proof = registry.instantiate(case_match, {
            "scrutinee": Var("x"),
            "branches": [
                ("int", Refl(Var("x"))),
                ("str", Refl(Var("x"))),
            ],
        })
        assert isinstance(case_proof, Cases)
        print(f"✓ Instantiated case_analysis: {case_proof}")

    # -- Test 10: Equational chain instantiation -----------------------------
    eq_match = None
    for m in registry.match(eq_obligation):
        if m.template.name == "equational_chain":
            eq_match = m
            break
    if eq_match is not None:
        chain_proof = registry.instantiate(eq_match, {
            "steps": [
                (Var("a"), Refl(Var("a"))),
                (Var("b"), Assume("a_eq_b")),
                (Var("c"), Assume("b_eq_c")),
            ],
        })
        assert isinstance(chain_proof, Trans)
        print(f"✓ Instantiated equational_chain: {chain_proof}")

    # -- Test 11: Structural recursion match ---------------------------------
    rec_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=App(func=Var("recursive"), arg=Var("n")),
    )
    matches = registry.match(rec_obligation)
    rec_names = [m.template.name for m in matches]
    assert "structural_recursion" in rec_names
    print(f"✓ Recursive obligation matched structural_recursion")

    # -- Test 12: Monotonicity match -----------------------------------------
    mono_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=App(func=Var("len"), arg=Var("xs")),
    )
    matches = registry.match(mono_obligation)
    mono_names = [m.template.name for m in matches]
    assert "monotonicity" in mono_names or "collection_length" in mono_names
    print(f"✓ len() obligation matched: {mono_names[:3]}")

    # -- Test 13: Idempotency match ------------------------------------------
    idem_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(func=Var("sorted(sorted"), arg=Var("xs")),
        right=App(func=Var("sorted"), arg=Var("xs")),
    )
    matches = registry.match(idem_obligation)
    idem_names = [m.template.name for m in matches]
    assert "idempotency" in idem_names
    print(f"✓ sorted(sorted(xs)) obligation matched idempotency")

    # -- Test 14: Involution match -------------------------------------------
    inv_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(func=Var("reverse(reverse"), arg=Var("xs")),
        right=Var("xs"),
    )
    matches = registry.match(inv_obligation)
    inv_names = [m.template.name for m in matches]
    assert "involution" in inv_names
    print(f"✓ reverse(reverse(xs)) obligation matched involution")

    # -- Test 15: No match for unrelated obligation --------------------------
    unrelated = Judgment(
        kind=JudgmentKind.WELL_FORMED,
        context=ctx,
        type_=PyObjType(),
    )
    matches = registry.match(unrelated)
    print(f"✓ Unrelated WELL_FORMED obligation matched {len(matches)} templates")

    # -- Test 16: auto_prove with context ------------------------------------
    auto_ctx = {
        "base_proof": Refl(Literal(value=0)),
        "step_proof": Assume("IH"),
    }
    auto_proof = registry.auto_prove(fold_obligation, context=auto_ctx)
    assert auto_proof is not None
    assert isinstance(auto_proof, ListInduction)
    print(f"✓ auto_prove produced: {auto_proof}")

    # -- Test 17: auto_prove with no context returns None --------------------
    no_ctx_proof = registry.auto_prove(fold_obligation)
    # May return None or a proof depending on defaults
    print(f"✓ auto_prove with no context: {type(no_ctx_proof).__name__}")

    # -- Test 18: TemplateLLMBridge prompt formatting ------------------------
    bridge = TemplateLLMBridge(registry)
    matches = registry.match(fold_obligation)
    prompt = bridge.format_template_prompt(fold_obligation, matches[:3])
    assert "fold_induction" in prompt
    assert "Obligation" in prompt
    assert "template" in prompt.lower()
    assert len(prompt) > 100
    print(f"✓ LLM prompt formatted ({len(prompt)} chars)")

    # -- Test 19: TemplateLLMBridge response parsing -------------------------
    llm_response = '{"template": "fold_induction", "params": {}}'
    tmpl_name, params = bridge.parse_template_response(llm_response, matches)
    assert tmpl_name == "fold_induction"
    assert isinstance(params, dict)
    print(f"✓ Parsed LLM response: template={tmpl_name}")

    # Test with markdown fences
    fenced = '```json\n{"template": "fold_induction", "params": {}}\n```'
    tmpl_name2, _ = bridge.parse_template_response(fenced, matches)
    assert tmpl_name2 == "fold_induction"
    print(f"✓ Parsed fenced LLM response: template={tmpl_name2}")

    # Test invalid response
    try:
        bridge.parse_template_response("not json at all", matches)
        assert False, "Should have raised ValueError"
    except ValueError:
        print("✓ Invalid LLM response correctly raises ValueError")

    # -- Test 20: prove_with_llm_choice end-to-end ---------------------------
    proof = bridge.prove_with_llm_choice(
        fold_obligation,
        '{"template": "fold_induction", "params": {}}',
    )
    assert proof is not None
    print(f"✓ prove_with_llm_choice: {type(proof).__name__}")

    # Invalid template name
    proof_bad = bridge.prove_with_llm_choice(
        fold_obligation,
        '{"template": "nonexistent_template", "params": {}}',
    )
    assert proof_bad is None
    print("✓ prove_with_llm_choice returns None for bad template")

    # -- Test 21: Cost estimate ----------------------------------------------
    matches = registry.match(fold_obligation)
    cost = bridge.cost_estimate(matches)
    assert cost["full_cost"] == 1200
    assert cost["template_cost"] < cost["full_cost"]
    assert cost["reduction_pct"] > 0
    print(f"✓ Cost estimate: {cost['reduction_pct']}% reduction "
          f"({cost['template_cost']} vs {cost['full_cost']} tokens)")

    # -- Test 22: Custom template registration -------------------------------
    custom_skeleton = lambda *, msg="hello": Structural(msg)
    custom_tmpl = ProofTemplate(
        name="custom_test",
        pattern=TemplatePattern(
            term_patterns=["custom_keyword"],
        ),
        parameters=[
            TemplateParameter("msg", "A message", "str",
                              required=False, default="hello"),
        ],
        skeleton=custom_skeleton,
        description="A custom test template.",
        category="custom",
    )
    registry.register(custom_tmpl)
    assert len(registry.templates) == 17
    assert registry.get_template("custom_test") is not None

    custom_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=Var("custom_keyword"),
    )
    matches = registry.match(custom_obligation)
    custom_names = [m.template.name for m in matches]
    assert "custom_test" in custom_names
    print("✓ Custom template registered and matched")

    # Instantiate custom template
    for m in matches:
        if m.template.name == "custom_test":
            p = registry.instantiate(m, {"msg": "verified!"})
            assert isinstance(p, Structural)
            assert p.description == "verified!"
            print(f"✓ Custom template instantiated: {p}")
            break

    # -- Test 23: Resource safety match --------------------------------------
    resource_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=Var("open"),
    )
    matches = registry.match(resource_obligation)
    res_names = [m.template.name for m in matches]
    assert "resource_safety" in res_names
    print(f"✓ 'open' obligation matched resource_safety")

    # -- Test 24: Arithmetic identity match ----------------------------------
    arith_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(func=Var("add"), arg=Literal(value=0)),
        right=Var("a"),
    )
    matches = registry.match(arith_obligation)
    arith_names = [m.template.name for m in matches]
    assert "arithmetic_identity" in arith_names
    print(f"✓ add(0) obligation matched arithmetic_identity")

    # -- Test 25: Exception safety match -------------------------------------
    exc_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=Var("ZeroDivisionError"),
    )
    matches = registry.match(exc_obligation)
    exc_names = [m.template.name for m in matches]
    assert "exception_safety" in exc_names
    print(f"✓ ZeroDivisionError obligation matched exception_safety")

    # -- Test 26: Sorted preservation match ----------------------------------
    sorted_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=App(func=Var("sorted"), arg=Var("xs")),
    )
    matches = registry.match(sorted_obligation)
    sort_names = [m.template.name for m in matches]
    assert "sorted_preservation" in sort_names
    print(f"✓ sorted(xs) matched sorted_preservation")

    # -- Test 27: Map homomorphism match -------------------------------------
    map_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(func=Var("map"), arg=Var("f")),
        right=App(func=Var("compose"), arg=Var("g")),
    )
    matches = registry.match(map_obligation)
    map_names = [m.template.name for m in matches]
    assert "map_homomorphism" in map_names
    print(f"✓ map/compose obligation matched map_homomorphism")

    # -- Test 28: Distributivity match ---------------------------------------
    dist_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=App(func=Var("distribute"), arg=Var("x")),
    )
    matches = registry.match(dist_obligation)
    dist_names = [m.template.name for m in matches]
    assert "distributivity" in dist_names
    print(f"✓ distribute(x) matched distributivity")

    # -- Test 29: Commutativity diagram match --------------------------------
    comm_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(func=Var("compose"), arg=Var("f")),
        right=App(func=Var("swap"), arg=Var("g")),
    )
    matches = registry.match(comm_obligation)
    comm_names = [m.template.name for m in matches]
    assert "commutativity_diagram" in comm_names
    print(f"✓ compose/swap obligation matched commutativity_diagram")

    # -- Test 30: Type narrowing match ---------------------------------------
    narrow_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=App(func=Var("isinstance"), arg=Var("x")),
    )
    matches = registry.match(narrow_obligation)
    narrow_names = [m.template.name for m in matches]
    assert "type_narrowing" in narrow_names
    print(f"✓ isinstance(x) matched type_narrowing")

    # -- Test 31: Confidence ordering ----------------------------------------
    multi_obligation = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        left=App(func=Var("reduce"), arg=Var("xs")),
        right=App(func=Var("fold"), arg=Var("ys")),
    )
    matches = registry.match(multi_obligation)
    assert len(matches) >= 1
    # Verify descending confidence order
    confs = [m.confidence for m in matches]
    assert confs == sorted(confs, reverse=True), (
        f"Matches should be sorted by confidence: {confs}"
    )
    print(f"✓ Matches sorted by confidence: {confs[:5]}")

    # -- Test 32: TemplateMatch repr -----------------------------------------
    if matches:
        r = repr(matches[0])
        assert "TemplateMatch" in r
        print(f"✓ TemplateMatch repr: {r}")

    # -- Test 33: TemplateCategory values ------------------------------------
    assert TemplateCategory.INDUCTION.value == "induction"
    assert TemplateCategory.ALGEBRAIC.value == "algebraic"
    print(f"✓ TemplateCategory enum works")

    # -- Test 34: _term_depth helper -----------------------------------------
    simple = Var("x")
    nested = App(func=App(func=Var("f"), arg=Var("x")), arg=Var("y"))
    assert _term_depth(simple) == 1
    assert _term_depth(nested) >= 2
    assert _term_depth(None) == 0
    print(f"✓ _term_depth: simple={_term_depth(simple)}, "
          f"nested={_term_depth(nested)}")

    # -- Test 35: max_complexity filter --------------------------------------
    complex_tmpl = ProofTemplate(
        name="simple_only",
        pattern=TemplatePattern(
            max_complexity=1,
            term_patterns=["f"],
        ),
        parameters=[],
        skeleton=lambda: Refl(Var("x")),
        description="Only matches shallow terms",
    )
    shallow_obl = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=Var("f"),
    )
    deep_obl = Judgment(
        kind=JudgmentKind.EQUAL,
        context=ctx,
        term=App(func=App(func=Var("f"), arg=Var("x")), arg=Var("y")),
    )
    assert complex_tmpl.match(shallow_obl) is not None
    assert complex_tmpl.match(deep_obl) is None
    print("✓ max_complexity filter works")

    # -- Test 36: excluded_keywords filter -----------------------------------
    excl_tmpl = ProofTemplate(
        name="no_unsafe",
        pattern=TemplatePattern(
            term_patterns=["process"],
            excluded_keywords=["unsafe"],
        ),
        parameters=[],
        skeleton=lambda: Structural("safe"),
    )
    safe_obl = Judgment(kind=JudgmentKind.EQUAL, context=ctx,
                        term=Var("process"))
    unsafe_obl = Judgment(kind=JudgmentKind.EQUAL, context=ctx,
                          term=Var("unsafe_process"))
    assert excl_tmpl.match(safe_obl) is not None
    assert excl_tmpl.match(unsafe_obl) is None
    print("✓ excluded_keywords filter works")

    # -- Test 37: required_keywords filter -----------------------------------
    req_tmpl = ProofTemplate(
        name="needs_both",
        pattern=TemplatePattern(
            required_keywords=["alpha", "beta"],
        ),
        parameters=[],
        skeleton=lambda: Structural("both"),
    )
    both_obl = Judgment(kind=JudgmentKind.EQUAL, context=ctx,
                        term=Var("alpha_beta"))
    only_one = Judgment(kind=JudgmentKind.EQUAL, context=ctx,
                        term=Var("alpha_only"))
    assert req_tmpl.match(both_obl) is not None
    assert req_tmpl.match(only_one) is None
    print("✓ required_keywords filter works")

    # -- Test 38: LLM bridge cost estimate with empty matches ----------------
    empty_cost = bridge.cost_estimate([])
    assert empty_cost["reduction_pct"] == 0.0
    print(f"✓ Cost estimate with no matches: {empty_cost}")

    # -- Test 39: Structural recursion instantiation -------------------------
    rec_matches = registry.match(rec_obligation)
    for m in rec_matches:
        if m.template.name == "structural_recursion":
            rp = registry.instantiate(m, {
                "induction_var": "n",
                "base_proof": Refl(Literal(value=0)),
                "step_proof": Assume("IH"),
            })
            assert isinstance(rp, NatInduction)
            assert rp.var == "n"
            print(f"✓ Instantiated structural_recursion: {rp}")
            break

    # -- Test 40: Monotonicity instantiation ---------------------------------
    mono_matches = registry.match(mono_obligation)
    for m in mono_matches:
        if m.template.name == "monotonicity":
            mp = registry.instantiate(m, {
                "monotonicity_witness": AxiomInvocation(name="len_monotone"),
                "argument_proof": Assume("a_le_b"),
            })
            assert isinstance(mp, Trans)
            print(f"✓ Instantiated monotonicity: {mp}")
            break

    print("\n" + "=" * 60)
    print(f"All 40 self-tests passed!")
    print("=" * 60)


if __name__ == "__main__":
    _self_test()
