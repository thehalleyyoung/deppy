"""
Lean proof analyzer for the CCTT soundness pipeline.

Analyzes Lean 4 proof terms (parsed ``LeanExpr`` AST) to extract:

* **Proof strategy** — rfl, simp, ring, omega, induction, cases, calc, …
* **Dependencies** — which lemmas / theorems a proof invokes.
* **Decidability** — whether the proposition is decidable (and which Z3
  fragment it falls into).
* **Soundness certificates** — self-contained records that attest to *why*
  a Lean theorem can be trusted when imported into CCTT as an axiom.

The main entry point is ``ProofAnalyzer.analyze(decl)``, which returns a
``ProofAnalysis`` (containing a ``SoundnessCertificate``).

For quick one-shot usage::

    from cctt.mathlib_bridge.proof_analyzer import analyze_proof
    cert = analyze_proof(decl)
    print(cert.proof_strategy, cert.confidence)
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple, Union

try:
    import z3 as _z3
    _HAS_Z3 = True
except ImportError:
    _z3 = None
    _HAS_Z3 = False

from cctt.mathlib_bridge.lean_parser import (
    LeanExpr,
    LeanVar,
    LeanApp,
    LeanLam,
    LeanPi,
    LeanMatch,
    LeanLet,
    LeanLit,
    LeanSort,
    LeanProj,
    LeanIf,
    LeanTactic,
    LeanTacticBlock,
    LeanParam,
    LeanDecl,
    LeanHole,
    LeanSorry,
    LeanAnonymousCtor,
)
from cctt.mathlib_bridge.prop_translator import LeanPropToCCTTPredicate, TranslatedPredicate


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class SoundnessCertificate:
    """Self-contained record attesting to why a Lean theorem is sound."""

    lean_theorem: str
    lean_proof_hash: str
    proof_strategy: str
    dependencies: list  # list[str]
    z3_fragment: Optional[str]
    decidable: bool
    soundness_narrative: str
    confidence: float
    proof_depth: int
    tactic_count: int
    is_constructive: bool
    uses_sorry: bool
    axioms_used: list  # list[str]


@dataclass
class TacticInfo:
    """Information about a single tactic usage."""

    name: str
    args: list  # list[LeanExpr]
    depth: int
    position: int


@dataclass
class ProofAnalysis:
    """Full analysis of a Lean proof."""

    declaration: LeanDecl
    certificate: SoundnessCertificate
    tactic_histogram: dict  # dict[str, int]
    lemma_applications: list  # list[str]
    induction_vars: list  # list[str]
    case_splits: list  # list[str]
    rewrite_targets: list  # list[str]
    key_steps: list  # list[str]
    structural_summary: str


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

_CLASSICAL_AXIOMS: frozenset[str] = frozenset({
    "Classical.choice",
    "Classical.em",
    "Classical.byContradiction",
    "Classical.propDecidable",
    "Classical.dec",
    "Classical.decEq",
    "Classical.arbitrary",
    "Decidable.decide",
})

_FOUNDATIONAL_AXIOMS: frozenset[str] = frozenset({
    "propext",
    "funext",
    "Quot.mk",
    "Quot.lift",
    "Quot.ind",
    "Quot.sound",
    "Classical.choice",
    "Classical.em",
    "Classical.byContradiction",
})

_DECISION_TACTICS: frozenset[str] = frozenset({
    "decide", "native_decide", "norm_num", "ring", "omega", "linarith",
    "simp", "rfl", "trivial",
})

_ARITH_TYPES: frozenset[str] = frozenset({
    "Nat", "Int", "Fin", "ZMod", "ℕ", "ℤ",
})

_ARITH_OPS: frozenset[str] = frozenset({
    "HAdd.hAdd", "HSub.hSub", "HMul.hMul", "HDiv.hDiv", "HMod.hMod",
    "Add.add", "Sub.sub", "Mul.mul", "Div.div", "Mod.mod",
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod",
    "Int.add", "Int.sub", "Int.mul", "Int.div", "Int.mod",
    "Nat.succ", "Nat.pred", "Nat.zero",
})

_COMPARISON_OPS: frozenset[str] = frozenset({
    "LT.lt", "LE.le", "GT.gt", "GE.ge", "Eq",
    "Nat.lt", "Nat.le", "Int.lt", "Int.le",
    "BEq.beq", "DecidableEq",
    "Ne",
})

_STRING_OPS: frozenset[str] = frozenset({
    "String.append", "String.length", "String.mk", "String.data",
    "String.push", "String.drop", "String.take", "String.isPrefixOf",
    "String.replace", "String.toNat?", "String.toNat!",
})

_BV_OPS: frozenset[str] = frozenset({
    "BitVec.add", "BitVec.sub", "BitVec.mul", "BitVec.and",
    "BitVec.or", "BitVec.xor", "BitVec.shiftLeft", "BitVec.shiftRight",
    "BitVec.zeroExtend", "BitVec.signExtend",
})

_ARRAY_OPS: frozenset[str] = frozenset({
    "Array.get!", "Array.set!", "Array.push", "Array.pop",
    "Array.size", "Array.mk", "Array.toList", "Array.data",
    "List.get!", "List.set", "List.length", "List.append",
})


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _expr_to_text(expr: LeanExpr) -> str:
    """Best-effort serialisation of a ``LeanExpr`` into a string."""
    if isinstance(expr, LeanVar):
        return expr.name
    if isinstance(expr, LeanLit):
        return repr(expr.value)
    if isinstance(expr, LeanApp):
        fn_text = _expr_to_text(expr.fn)
        arg_texts = " ".join(_expr_to_text(a) for a in expr.args)
        return f"({fn_text} {arg_texts})"
    if isinstance(expr, LeanLam):
        params = " ".join(p.name for p in expr.params)
        return f"(fun {params} => {_expr_to_text(expr.body)})"
    if isinstance(expr, LeanPi):
        params = " ".join(p.name for p in expr.params)
        return f"(∀ {params}, {_expr_to_text(expr.codomain)})"
    if isinstance(expr, LeanLet):
        return f"(let {expr.name} := {_expr_to_text(expr.value)}; {_expr_to_text(expr.body)})"
    if isinstance(expr, LeanMatch):
        scruts = ", ".join(_expr_to_text(s) for s in expr.scrutinees)
        return f"(match {scruts} with ...)"
    if isinstance(expr, LeanIf):
        return f"(if {_expr_to_text(expr.cond)} then {_expr_to_text(expr.then_)} else {_expr_to_text(expr.else_)})"
    if isinstance(expr, LeanSort):
        if expr.level == 0:
            return "Prop"
        return f"Type {expr.level - 1}" if expr.level > 1 else "Type"
    if isinstance(expr, LeanProj):
        return f"{_expr_to_text(expr.expr)}.{expr.field}"
    if isinstance(expr, LeanTactic):
        arg_texts = " ".join(_expr_to_text(a) for a in expr.args)
        return f"{expr.tactic_name} {arg_texts}".strip()
    if isinstance(expr, LeanTacticBlock):
        return "by " + "; ".join(_expr_to_text(t) for t in expr.tactics)
    if isinstance(expr, LeanHole):
        return "_"
    if isinstance(expr, LeanSorry):
        return "sorry"
    if isinstance(expr, LeanAnonymousCtor):
        return "⟨" + ", ".join(_expr_to_text(a) for a in expr.args) + "⟩"
    return "?"


def _collect_var_names(expr: LeanExpr) -> set[str]:
    """Collect all variable names referenced in *expr*."""
    names: set[str] = set()
    _collect_var_names_into(expr, names)
    return names


def _collect_var_names_into(expr: LeanExpr, acc: set[str]) -> None:
    if isinstance(expr, LeanVar):
        acc.add(expr.name)
    elif isinstance(expr, LeanApp):
        _collect_var_names_into(expr.fn, acc)
        for a in expr.args:
            _collect_var_names_into(a, acc)
    elif isinstance(expr, LeanLam):
        _collect_var_names_into(expr.body, acc)
    elif isinstance(expr, LeanPi):
        _collect_var_names_into(expr.codomain, acc)
    elif isinstance(expr, LeanLet):
        _collect_var_names_into(expr.value, acc)
        _collect_var_names_into(expr.body, acc)
    elif isinstance(expr, LeanMatch):
        for s in expr.scrutinees:
            _collect_var_names_into(s, acc)
        for arm in expr.arms:
            _collect_var_names_into(arm.rhs, acc)
    elif isinstance(expr, LeanIf):
        _collect_var_names_into(expr.cond, acc)
        _collect_var_names_into(expr.then_, acc)
        _collect_var_names_into(expr.else_, acc)
    elif isinstance(expr, LeanProj):
        _collect_var_names_into(expr.expr, acc)
    elif isinstance(expr, LeanTactic):
        for a in expr.args:
            _collect_var_names_into(a, acc)
    elif isinstance(expr, LeanTacticBlock):
        for t in expr.tactics:
            _collect_var_names_into(t, acc)
    elif isinstance(expr, LeanAnonymousCtor):
        for a in expr.args:
            _collect_var_names_into(a, acc)


def _head_name(expr: LeanExpr) -> Optional[str]:
    """Return the head symbol name of an expression (unwrap applications)."""
    if isinstance(expr, LeanVar):
        return expr.name
    if isinstance(expr, LeanApp):
        return _head_name(expr.fn)
    return None


def _flatten_tactics(block: LeanTacticBlock) -> list[LeanTactic]:
    """Recursively flatten nested tactic blocks into a single list."""
    result: list[LeanTactic] = []
    for t in block.tactics:
        result.append(t)
        for arg in t.args:
            if isinstance(arg, LeanTacticBlock):
                result.extend(_flatten_tactics(arg))
            elif isinstance(arg, LeanTactic):
                result.append(arg)
    return result


def _is_qualified_name(name: str) -> bool:
    """Return ``True`` if *name* looks like a qualified Lean name."""
    return "." in name and not name.startswith("@") and name[0].isupper()


def _count_nodes(expr: LeanExpr) -> int:
    """Count the total number of AST nodes in *expr*."""
    if isinstance(expr, (LeanVar, LeanLit, LeanSort, LeanHole, LeanSorry)):
        return 1
    if isinstance(expr, LeanApp):
        return 1 + _count_nodes(expr.fn) + sum(_count_nodes(a) for a in expr.args)
    if isinstance(expr, LeanLam):
        return 1 + _count_nodes(expr.body)
    if isinstance(expr, LeanPi):
        return 1 + _count_nodes(expr.codomain)
    if isinstance(expr, LeanLet):
        count = 1 + _count_nodes(expr.value) + _count_nodes(expr.body)
        if expr.type_ is not None:
            count += _count_nodes(expr.type_)
        return count
    if isinstance(expr, LeanMatch):
        count = 1 + sum(_count_nodes(s) for s in expr.scrutinees)
        for arm in expr.arms:
            count += _count_nodes(arm.rhs)
        return count
    if isinstance(expr, LeanIf):
        return 1 + _count_nodes(expr.cond) + _count_nodes(expr.then_) + _count_nodes(expr.else_)
    if isinstance(expr, LeanProj):
        return 1 + _count_nodes(expr.expr)
    if isinstance(expr, LeanTactic):
        return 1 + sum(_count_nodes(a) for a in expr.args)
    if isinstance(expr, LeanTacticBlock):
        return 1 + sum(_count_nodes(t) for t in expr.tactics)
    if isinstance(expr, LeanAnonymousCtor):
        return 1 + sum(_count_nodes(a) for a in expr.args)
    return 1


def _expr_contains_name(expr: LeanExpr, name: str) -> bool:
    """Check whether *expr* contains a ``LeanVar`` with the given *name*."""
    if isinstance(expr, LeanVar):
        return expr.name == name
    if isinstance(expr, LeanApp):
        return _expr_contains_name(expr.fn, name) or any(
            _expr_contains_name(a, name) for a in expr.args
        )
    if isinstance(expr, LeanLam):
        return _expr_contains_name(expr.body, name)
    if isinstance(expr, LeanPi):
        return _expr_contains_name(expr.codomain, name)
    if isinstance(expr, LeanLet):
        return (
            _expr_contains_name(expr.value, name)
            or _expr_contains_name(expr.body, name)
        )
    if isinstance(expr, LeanMatch):
        if any(_expr_contains_name(s, name) for s in expr.scrutinees):
            return True
        return any(_expr_contains_name(arm.rhs, name) for arm in expr.arms)
    if isinstance(expr, LeanIf):
        return (
            _expr_contains_name(expr.cond, name)
            or _expr_contains_name(expr.then_, name)
            or _expr_contains_name(expr.else_, name)
        )
    if isinstance(expr, LeanProj):
        return _expr_contains_name(expr.expr, name)
    if isinstance(expr, LeanTactic):
        return any(_expr_contains_name(a, name) for a in expr.args)
    if isinstance(expr, LeanTacticBlock):
        return any(_expr_contains_name(t, name) for t in expr.tactics)
    if isinstance(expr, LeanAnonymousCtor):
        return any(_expr_contains_name(a, name) for a in expr.args)
    return False


def _type_mentions_arith(expr: Optional[LeanExpr]) -> bool:
    """Return True if the type expression mentions arithmetic types."""
    if expr is None:
        return False
    names = _collect_var_names(expr)
    return bool(names & _ARITH_TYPES)


def _type_mentions_string(expr: Optional[LeanExpr]) -> bool:
    """Return True if the type expression mentions String operations."""
    if expr is None:
        return False
    names = _collect_var_names(expr)
    return bool(names & _STRING_OPS) or "String" in names


def _type_mentions_bv(expr: Optional[LeanExpr]) -> bool:
    """Return True if the type expression mentions bitvector operations."""
    if expr is None:
        return False
    names = _collect_var_names(expr)
    return bool(names & _BV_OPS) or "BitVec" in names


def _type_mentions_array(expr: Optional[LeanExpr]) -> bool:
    """Return True if the type expression mentions array/list operations."""
    if expr is None:
        return False
    names = _collect_var_names(expr)
    return bool(names & _ARRAY_OPS) or "Array" in names or "List" in names


def _type_mentions_mul(expr: Optional[LeanExpr]) -> bool:
    """Return True if the type expression uses multiplication."""
    if expr is None:
        return False
    names = _collect_var_names(expr)
    mul_names = {"HMul.hMul", "Mul.mul", "Nat.mul", "Int.mul"}
    return bool(names & mul_names)


def _has_higher_order_quantifier(expr: Optional[LeanExpr]) -> bool:
    """Return True if *expr* contains a higher-order quantifier (∀/∃ over functions)."""
    if expr is None:
        return False
    if isinstance(expr, LeanPi):
        for p in expr.params:
            if p.type_ is not None and isinstance(p.type_, LeanPi):
                return True
        return _has_higher_order_quantifier(expr.codomain)
    if isinstance(expr, LeanApp):
        return _has_higher_order_quantifier(expr.fn) or any(
            _has_higher_order_quantifier(a) for a in expr.args
        )
    if isinstance(expr, LeanLam):
        return _has_higher_order_quantifier(expr.body)
    return False


# ---------------------------------------------------------------------------
# ProofAnalyzer
# ---------------------------------------------------------------------------


class ProofAnalyzer:
    """Analyze Lean proof terms to produce soundness certificates for CCTT.

    The analyzer inspects a ``LeanDecl`` (a parsed Lean declaration) and
    produces a ``ProofAnalysis`` containing:

    * A ``SoundnessCertificate`` summarising trust-relevant properties.
    * A tactic histogram and list of lemma applications.
    * Induction variables, case splits, rewrite targets.
    * A structural summary and key proof steps.

    Usage::

        analyzer = ProofAnalyzer()
        analysis = analyzer.analyze(decl)
        cert = analysis.certificate
    """

    # ------------------------------------------------------------------ public

    def analyze(self, decl: LeanDecl) -> ProofAnalysis:
        """Main entry point: analyse *decl* and return a ``ProofAnalysis``."""
        body = decl.body
        if body is None:
            body = LeanHole()

        strategy = self._extract_strategy(body)
        dependencies = self._extract_dependencies(body)
        tactics = self._extract_tactics(body)
        histogram = self._build_tactic_histogram(tactics)
        induction_vars = self._detect_induction(body)
        case_splits = self._detect_case_splits(body)
        rewrite_targets = self._detect_rewrites(body)
        lemma_apps = self._extract_lemma_applications(body)
        key_steps = self._extract_key_steps(body)

        z3_frag = self._classify_z3_fragment(decl)
        decidable = self._is_decidable(decl)
        constructive = self._is_constructive(body)
        sorry = self._uses_sorry(body)
        axioms = self._extract_axioms_used(body)
        proof_hash = self._compute_proof_hash(decl)
        confidence = self._compute_confidence(decl, strategy)
        narrative = self._generate_soundness_narrative(decl, strategy, dependencies)
        depth = self._compute_proof_depth(body)

        if sorry:
            confidence = 0.0

        cert = SoundnessCertificate(
            lean_theorem=decl.name,
            lean_proof_hash=proof_hash,
            proof_strategy=strategy,
            dependencies=dependencies,
            z3_fragment=z3_frag,
            decidable=decidable,
            soundness_narrative=narrative,
            confidence=confidence,
            proof_depth=depth,
            tactic_count=len(tactics),
            is_constructive=constructive,
            uses_sorry=sorry,
            axioms_used=axioms,
        )

        analysis = ProofAnalysis(
            declaration=decl,
            certificate=cert,
            tactic_histogram=histogram,
            lemma_applications=lemma_apps,
            induction_vars=induction_vars,
            case_splits=case_splits,
            rewrite_targets=rewrite_targets,
            key_steps=key_steps,
            structural_summary="",
        )
        analysis.structural_summary = self._generate_structural_summary(analysis)
        return analysis

    def analyze_proof_body(self, body: LeanExpr) -> ProofAnalysis:
        """Analyse a bare proof body without a full ``LeanDecl`` wrapper.

        Constructs a synthetic declaration around *body* and delegates to
        :meth:`analyze`.
        """
        synthetic_decl = LeanDecl(
            kind="theorem",
            name="<anonymous>",
            universe_params=[],
            params=[],
            return_type=None,
            body=body,
            attributes=[],
            docstring=None,
            namespace="",
        )
        return self.analyze(synthetic_decl)

    # ----------------------------------------------------- strategy detection

    def _extract_strategy(self, body: LeanExpr) -> str:
        """Determine the dominant proof strategy used in *body*."""
        if isinstance(body, LeanSorry):
            return "sorry"

        if isinstance(body, LeanVar) and body.name == "rfl":
            return "rfl"

        if isinstance(body, LeanTactic) and body.tactic_name == "rfl":
            return "rfl"

        if isinstance(body, LeanTacticBlock):
            return self._classify_tactic_block(body)

        if isinstance(body, (LeanApp, LeanLam, LeanLet, LeanMatch)):
            return self._classify_term_mode(body)

        if isinstance(body, LeanHole):
            return "unknown"

        return "direct"

    def _classify_tactic_block(self, block: LeanTacticBlock) -> str:
        """Classify a ``by …`` tactic block by its dominant tactic."""
        tactics = block.tactics
        if not tactics:
            return "unknown"

        first = tactics[0]
        first_name = first.tactic_name.lower() if isinstance(first, LeanTactic) else ""

        # Single-tactic proofs
        if len(tactics) == 1:
            if first_name == "rfl":
                return "rfl"
            if first_name == "simp":
                return "simp"
            if first_name == "ring":
                return "ring"
            if first_name == "omega":
                return "omega"
            if first_name == "linarith":
                return "linarith"
            if first_name == "decide":
                return "decide"
            if first_name == "norm_num":
                return "norm_num"
            if first_name == "trivial":
                return "trivial"
            if first_name in ("ext", "funext"):
                return "ext"
            if first_name in ("exact", "apply"):
                return "apply_lemma"
            if first_name in ("by_contra", "by_contradiction"):
                return "contradiction"
            if first_name == "contradiction":
                return "contradiction"

        all_tactics = _flatten_tactics(block)
        tactic_names = [t.tactic_name.lower() for t in all_tactics if isinstance(t, LeanTactic)]

        if "induction" in tactic_names:
            return "induction"
        if "cases" in tactic_names or "rcases" in tactic_names:
            return "cases"
        if "by_contra" in tactic_names or "by_contradiction" in tactic_names:
            return "contradiction"
        if "calc" in tactic_names or first_name == "calc":
            return "calc"
        if "ext" in tactic_names or "funext" in tactic_names:
            return "ext"

        # Count tactic kinds for dominant-strategy heuristic
        apply_exact_count = sum(1 for n in tactic_names if n in ("apply", "exact"))
        rw_count = sum(1 for n in tactic_names if n in ("rw", "rewrite", "rwa"))
        simp_count = sum(1 for n in tactic_names if n in ("simp", "simp_all", "dsimp"))

        total = len(tactic_names)
        if total > 0:
            if apply_exact_count / total > 0.5:
                return "apply_lemma"
            if simp_count / total > 0.5:
                return "simp"

        # Single decision procedure only if it's the *dominant* tactic
        if total <= 2:
            if "linarith" in tactic_names:
                return "linarith"
            if "omega" in tactic_names:
                return "omega"
            if "ring" in tactic_names:
                return "ring"

        return "mixed"

    def _classify_term_mode(self, body: LeanExpr) -> str:
        """Classify a term-mode proof by its structure."""
        if isinstance(body, LeanApp):
            head = _head_name(body)
            if head is not None:
                low = head.lower()
                if low in ("absurd", "false.elim", "not.elim"):
                    return "contradiction"
                if "rec" in low or "rec_on" in low or "cases_on" in low:
                    return "induction"
                if low in ("eq.trans", "eq.symm", "trans", "symm"):
                    return "calc"
                if low == "congr" or low.startswith("congr"):
                    return "congr"
                if low == "funext":
                    return "funext"
            return "direct"

        if isinstance(body, LeanMatch):
            return "cases"

        if isinstance(body, LeanLam):
            return self._classify_term_mode(body.body)

        if isinstance(body, LeanLet):
            return self._classify_term_mode(body.body)

        return "direct"

    # -------------------------------------------------- dependency extraction

    def _extract_dependencies(self, body: LeanExpr) -> list[str]:
        """Find fully-qualified lemma/theorem references in *body*."""
        deps: set[str] = set()
        self._collect_dependencies(body, deps)
        return sorted(deps)

    def _collect_dependencies(self, expr: LeanExpr, acc: set[str]) -> None:
        """Recursively collect dependency names into *acc*."""
        if isinstance(expr, LeanVar):
            if _is_qualified_name(expr.name):
                acc.add(expr.name)
            return

        if isinstance(expr, LeanApp):
            self._collect_dependencies(expr.fn, acc)
            for a in expr.args:
                self._collect_dependencies(a, acc)
            return

        if isinstance(expr, LeanLam):
            self._collect_dependencies(expr.body, acc)
            return

        if isinstance(expr, LeanPi):
            self._collect_dependencies(expr.codomain, acc)
            return

        if isinstance(expr, LeanLet):
            self._collect_dependencies(expr.value, acc)
            self._collect_dependencies(expr.body, acc)
            return

        if isinstance(expr, LeanMatch):
            for s in expr.scrutinees:
                self._collect_dependencies(s, acc)
            for arm in expr.arms:
                self._collect_dependencies(arm.rhs, acc)
            return

        if isinstance(expr, LeanIf):
            self._collect_dependencies(expr.cond, acc)
            self._collect_dependencies(expr.then_, acc)
            self._collect_dependencies(expr.else_, acc)
            return

        if isinstance(expr, LeanProj):
            self._collect_dependencies(expr.expr, acc)
            return

        if isinstance(expr, LeanTactic):
            for a in expr.args:
                self._collect_dependencies(a, acc)
            return

        if isinstance(expr, LeanTacticBlock):
            for t in expr.tactics:
                self._collect_dependencies(t, acc)
            return

        if isinstance(expr, LeanAnonymousCtor):
            for a in expr.args:
                self._collect_dependencies(a, acc)
            return

    # ---------------------------------------------------- tactic extraction

    def _extract_tactics(self, body: LeanExpr) -> list[TacticInfo]:
        """Extract all tactic invocations from *body*."""
        result: list[TacticInfo] = []
        self._collect_tactics(body, result, depth=0, counter=[0])
        return result

    def _collect_tactics(
        self,
        expr: LeanExpr,
        acc: list[TacticInfo],
        depth: int,
        counter: list[int],
    ) -> None:
        """Recursively collect ``TacticInfo`` objects into *acc*."""
        if isinstance(expr, LeanTactic):
            acc.append(TacticInfo(
                name=expr.tactic_name,
                args=list(expr.args),
                depth=depth,
                position=counter[0],
            ))
            counter[0] += 1
            for a in expr.args:
                self._collect_tactics(a, acc, depth + 1, counter)
            return

        if isinstance(expr, LeanTacticBlock):
            for t in expr.tactics:
                self._collect_tactics(t, acc, depth, counter)
            return

        if isinstance(expr, LeanApp):
            self._collect_tactics(expr.fn, acc, depth, counter)
            for a in expr.args:
                self._collect_tactics(a, acc, depth + 1, counter)
            return

        if isinstance(expr, LeanLam):
            self._collect_tactics(expr.body, acc, depth + 1, counter)
            return

        if isinstance(expr, LeanPi):
            self._collect_tactics(expr.codomain, acc, depth + 1, counter)
            return

        if isinstance(expr, LeanLet):
            self._collect_tactics(expr.value, acc, depth + 1, counter)
            self._collect_tactics(expr.body, acc, depth + 1, counter)
            return

        if isinstance(expr, LeanMatch):
            for s in expr.scrutinees:
                self._collect_tactics(s, acc, depth + 1, counter)
            for arm in expr.arms:
                self._collect_tactics(arm.rhs, acc, depth + 1, counter)
            return

        if isinstance(expr, LeanIf):
            self._collect_tactics(expr.cond, acc, depth + 1, counter)
            self._collect_tactics(expr.then_, acc, depth + 1, counter)
            self._collect_tactics(expr.else_, acc, depth + 1, counter)
            return

        if isinstance(expr, LeanAnonymousCtor):
            for a in expr.args:
                self._collect_tactics(a, acc, depth + 1, counter)
            return

    def _build_tactic_histogram(self, tactics: list[TacticInfo]) -> dict[str, int]:
        """Build a histogram mapping tactic names to usage counts."""
        hist: dict[str, int] = {}
        for t in tactics:
            key = t.name.lower()
            hist[key] = hist.get(key, 0) + 1
        return hist

    # ------------------------------------------------- induction detection

    def _detect_induction(self, body: LeanExpr) -> list[str]:
        """Find variables that are inducted on."""
        result: list[str] = []
        self._collect_induction_vars(body, result)
        return result

    def _collect_induction_vars(self, expr: LeanExpr, acc: list[str]) -> None:
        if isinstance(expr, LeanTactic):
            if expr.tactic_name.lower() == "induction":
                for a in expr.args:
                    if isinstance(a, LeanVar):
                        acc.append(a.name)
            for a in expr.args:
                self._collect_induction_vars(a, acc)
            return

        if isinstance(expr, LeanTacticBlock):
            for t in expr.tactics:
                self._collect_induction_vars(t, acc)
            return

        if isinstance(expr, LeanApp):
            head = _head_name(expr)
            if head is not None and ("rec" in head.lower() or "rec_on" in head.lower()):
                for a in expr.args:
                    if isinstance(a, LeanVar):
                        acc.append(a.name)
                        break
            self._collect_induction_vars(expr.fn, acc)
            for a in expr.args:
                self._collect_induction_vars(a, acc)
            return

        if isinstance(expr, LeanLam):
            self._collect_induction_vars(expr.body, acc)
        elif isinstance(expr, LeanLet):
            self._collect_induction_vars(expr.value, acc)
            self._collect_induction_vars(expr.body, acc)
        elif isinstance(expr, LeanMatch):
            for s in expr.scrutinees:
                self._collect_induction_vars(s, acc)
            for arm in expr.arms:
                self._collect_induction_vars(arm.rhs, acc)
        elif isinstance(expr, LeanIf):
            self._collect_induction_vars(expr.cond, acc)
            self._collect_induction_vars(expr.then_, acc)
            self._collect_induction_vars(expr.else_, acc)
        elif isinstance(expr, LeanAnonymousCtor):
            for a in expr.args:
                self._collect_induction_vars(a, acc)

    # ------------------------------------------------ case split detection

    def _detect_case_splits(self, body: LeanExpr) -> list[str]:
        """Find case-split descriptions in the proof."""
        result: list[str] = []
        self._collect_case_splits(body, result)
        return result

    def _collect_case_splits(self, expr: LeanExpr, acc: list[str]) -> None:
        if isinstance(expr, LeanTactic):
            tname = expr.tactic_name.lower()
            if tname in ("cases", "rcases", "obtain"):
                desc_parts = [_expr_to_text(a) for a in expr.args]
                desc = f"{tname} on {' '.join(desc_parts)}" if desc_parts else tname
                acc.append(desc)
            for a in expr.args:
                self._collect_case_splits(a, acc)
            return

        if isinstance(expr, LeanTacticBlock):
            for t in expr.tactics:
                self._collect_case_splits(t, acc)
            return

        if isinstance(expr, LeanMatch):
            scrut_descs = [_expr_to_text(s) for s in expr.scrutinees]
            acc.append(f"match on {', '.join(scrut_descs)}")
            for arm in expr.arms:
                self._collect_case_splits(arm.rhs, acc)
            return

        if isinstance(expr, LeanIf):
            acc.append(f"if {_expr_to_text(expr.cond)}")
            self._collect_case_splits(expr.then_, acc)
            self._collect_case_splits(expr.else_, acc)
            return

        if isinstance(expr, LeanApp):
            self._collect_case_splits(expr.fn, acc)
            for a in expr.args:
                self._collect_case_splits(a, acc)
        elif isinstance(expr, LeanLam):
            self._collect_case_splits(expr.body, acc)
        elif isinstance(expr, LeanLet):
            self._collect_case_splits(expr.value, acc)
            self._collect_case_splits(expr.body, acc)
        elif isinstance(expr, LeanAnonymousCtor):
            for a in expr.args:
                self._collect_case_splits(a, acc)

    # --------------------------------------------------- rewrite detection

    def _detect_rewrites(self, body: LeanExpr) -> list[str]:
        """Find rewrite targets in the proof."""
        result: list[str] = []
        self._collect_rewrites(body, result)
        return result

    def _collect_rewrites(self, expr: LeanExpr, acc: list[str]) -> None:
        if isinstance(expr, LeanTactic):
            tname = expr.tactic_name.lower()
            if tname in ("rw", "rewrite", "rwa", "simp", "simp_all"):
                for a in expr.args:
                    text = _expr_to_text(a)
                    if text != "?" and text != "_":
                        acc.append(text)
            for a in expr.args:
                self._collect_rewrites(a, acc)
            return

        if isinstance(expr, LeanTacticBlock):
            for t in expr.tactics:
                self._collect_rewrites(t, acc)
            return

        if isinstance(expr, LeanApp):
            head = _head_name(expr)
            if head is not None and head.lower() in ("eq.subst", "eq.mpr", "eq.mp"):
                for a in expr.args:
                    text = _expr_to_text(a)
                    acc.append(text)
            self._collect_rewrites(expr.fn, acc)
            for a in expr.args:
                self._collect_rewrites(a, acc)
        elif isinstance(expr, LeanLam):
            self._collect_rewrites(expr.body, acc)
        elif isinstance(expr, LeanLet):
            self._collect_rewrites(expr.value, acc)
            self._collect_rewrites(expr.body, acc)
        elif isinstance(expr, LeanMatch):
            for s in expr.scrutinees:
                self._collect_rewrites(s, acc)
            for arm in expr.arms:
                self._collect_rewrites(arm.rhs, acc)
        elif isinstance(expr, LeanAnonymousCtor):
            for a in expr.args:
                self._collect_rewrites(a, acc)

    # ----------------------------------------------- Z3 fragment classification

    def _classify_z3_fragment(self, decl: LeanDecl) -> Optional[str]:
        """Classify which Z3 logic fragment the proposition falls into."""
        ret = decl.return_type
        if ret is None:
            return None

        names = _collect_var_names(ret)

        has_arith = bool(names & _ARITH_TYPES) or bool(names & _ARITH_OPS)
        has_comparison = bool(names & _COMPARISON_OPS)
        has_string = bool(names & _STRING_OPS) or "String" in names
        has_bv = bool(names & _BV_OPS) or "BitVec" in names
        has_array = bool(names & _ARRAY_OPS) or "Array" in names
        has_mul = _type_mentions_mul(ret)
        has_higher_order = _has_higher_order_quantifier(ret)

        if has_bv and not has_arith and not has_string:
            return "QF_BV"

        if has_string and not has_arith and not has_bv:
            return "QF_S"

        if has_array and has_arith:
            if has_mul:
                return "AUFNIRA"
            return "QF_AUFLIA"

        if has_arith or has_comparison:
            if has_mul:
                return "QF_NIA"
            return "QF_LIA"

        if has_higher_order:
            return None

        if has_comparison:
            return "QF_LIA"

        return None

    # -------------------------------------------------- decidability check

    def _is_decidable(self, decl: LeanDecl) -> bool:
        """Determine whether the proposition in *decl* is decidable."""
        body = decl.body
        if body is not None:
            tactics = self._extract_tactics(body)
            for t in tactics:
                if t.name.lower() in ("decide", "native_decide"):
                    return True

        ret = decl.return_type
        if ret is None:
            return False

        if _has_higher_order_quantifier(ret):
            return False

        names = _collect_var_names(ret)

        # Collect parameter type names too — the return type often just has
        # variable names whose types are declared in the params.
        param_type_names: set[str] = set()
        for p in decl.params:
            if p.type_ is not None:
                param_type_names |= _collect_var_names(p.type_)

        all_names = names | param_type_names

        if all_names <= (_ARITH_TYPES | _ARITH_OPS | _COMPARISON_OPS | {"Bool", "True", "False"}):
            return True

        if "Bool" in all_names and not (all_names & _ARITH_TYPES):
            return True

        if "List.length" in all_names or "Array.size" in all_names:
            return True

        if "Decidable" in all_names or "DecidableEq" in all_names:
            return True

        # Check if everything in the return type is a known decidable symbol
        # or a plain variable whose parameter type is arithmetic / Bool.
        known_decidable = (
            _ARITH_TYPES | _ARITH_OPS | _COMPARISON_OPS
            | {"Prop", "True", "False", "Bool", "And", "Or", "Not",
               "Iff", "Eq", "Ne", "List.length", "Array.size",
               "Decidable", "DecidableEq"}
        )
        # Variables whose declared type is Nat/Int/Bool etc. are okay
        param_arith_vars = {
            p.name for p in decl.params
            if p.type_ is not None and _collect_var_names(p.type_) & (_ARITH_TYPES | {"Bool"})
        }
        extended_known = known_decidable | param_arith_vars

        if names and names <= extended_known:
            return True

        return False

    # ------------------------------------------- constructiveness check

    def _is_constructive(self, body: LeanExpr) -> bool:
        """Return True if the proof does not use classical axioms."""
        names = _collect_var_names(body)
        return not bool(names & _CLASSICAL_AXIOMS)

    # ---------------------------------------------------- sorry detection

    def _uses_sorry(self, body: LeanExpr) -> bool:
        """Return True if *body* contains ``sorry``."""
        if isinstance(body, LeanSorry):
            return True
        if isinstance(body, LeanTactic) and body.tactic_name.lower() == "sorry":
            return True
        if isinstance(body, LeanVar) and body.name == "sorry":
            return True

        if isinstance(body, LeanApp):
            return self._uses_sorry(body.fn) or any(self._uses_sorry(a) for a in body.args)
        if isinstance(body, LeanLam):
            return self._uses_sorry(body.body)
        if isinstance(body, LeanPi):
            return self._uses_sorry(body.codomain)
        if isinstance(body, LeanLet):
            return self._uses_sorry(body.value) or self._uses_sorry(body.body)
        if isinstance(body, LeanMatch):
            if any(self._uses_sorry(s) for s in body.scrutinees):
                return True
            return any(self._uses_sorry(arm.rhs) for arm in body.arms)
        if isinstance(body, LeanIf):
            return (
                self._uses_sorry(body.cond)
                or self._uses_sorry(body.then_)
                or self._uses_sorry(body.else_)
            )
        if isinstance(body, LeanTacticBlock):
            return any(self._uses_sorry(t) for t in body.tactics)
        if isinstance(body, LeanTactic):
            return any(self._uses_sorry(a) for a in body.args)
        if isinstance(body, LeanAnonymousCtor):
            return any(self._uses_sorry(a) for a in body.args)
        return False

    # ------------------------------------------------- axiom extraction

    def _extract_axioms_used(self, body: LeanExpr) -> list[str]:
        """Return a sorted list of foundational axioms referenced in *body*."""
        names = _collect_var_names(body)
        used = sorted(names & _FOUNDATIONAL_AXIOMS)
        return used

    # --------------------------------------------------- proof hash

    def _compute_proof_hash(self, decl: LeanDecl) -> str:
        """Compute a SHA-256 hash of the proof term text."""
        if decl.body is None:
            text = f"<axiom:{decl.name}>"
        else:
            text = _expr_to_text(decl.body)
        return hashlib.sha256(text.encode("utf-8")).hexdigest()

    # ----------------------------------------- soundness narrative

    def _generate_soundness_narrative(
        self,
        decl: LeanDecl,
        strategy: str,
        deps: list[str],
    ) -> str:
        """Generate a human-readable explanation of why the theorem is sound."""
        name = decl.name
        kind = decl.kind

        narratives: dict[str, str] = {
            "rfl": (
                f"{kind.capitalize()} '{name}' is proved by definitional equality (rfl). "
                f"Both sides reduce to the same normal form in Lean's type theory, "
                f"providing the strongest possible guarantee."
            ),
            "ring": (
                f"{kind.capitalize()} '{name}' is proved by the 'ring' decision procedure, "
                f"which verifies polynomial identities over commutative (semi)rings. "
                f"This is a verified decision procedure."
            ),
            "omega": (
                f"{kind.capitalize()} '{name}' is proved by the 'omega' decision procedure "
                f"for linear arithmetic over natural numbers and integers. "
                f"The result is machine-checked."
            ),
            "linarith": (
                f"{kind.capitalize()} '{name}' is proved by 'linarith', which checks "
                f"linear arithmetic facts by finding a suitable linear combination of "
                f"hypotheses. The certificate is verified by the kernel."
            ),
            "simp": (
                f"{kind.capitalize()} '{name}' is proved by the simplifier, which "
                f"applies a confluent rewriting system. The proof term is checked "
                f"by Lean's kernel."
            ),
            "norm_num": (
                f"{kind.capitalize()} '{name}' is proved by norm_num, a verified "
                f"normalisation procedure for numeric expressions."
            ),
            "decide": (
                f"{kind.capitalize()} '{name}' is proved by 'decide', which evaluates "
                f"the proposition by brute-force computation. The proposition is "
                f"decidable and the result is definitional."
            ),
            "induction": (
                f"{kind.capitalize()} '{name}' is proved by induction. The proof "
                f"establishes a base case and an inductive step, verified by "
                f"Lean's dependent type checker."
            ),
            "cases": (
                f"{kind.capitalize()} '{name}' is proved by case analysis. "
                f"Each constructor or possibility is handled exhaustively."
            ),
            "contradiction": (
                f"{kind.capitalize()} '{name}' is proved by contradiction. "
                f"A contradictory hypothesis is derived, from which the conclusion follows."
            ),
            "calc": (
                f"{kind.capitalize()} '{name}' is proved by a calculational chain "
                f"of equalities/inequalities, each step verified individually."
            ),
            "ext": (
                f"{kind.capitalize()} '{name}' is proved by extensionality — "
                f"showing that two objects agree on all inputs/components."
            ),
            "funext": (
                f"{kind.capitalize()} '{name}' is proved by function extensionality — "
                f"two functions are equal if they agree on all arguments."
            ),
            "congr": (
                f"{kind.capitalize()} '{name}' is proved by congruence — "
                f"applying the same function to equal arguments yields equal results."
            ),
            "apply_lemma": (
                f"{kind.capitalize()} '{name}' is proved by applying existing lemmas."
            ),
            "direct": (
                f"{kind.capitalize()} '{name}' is a direct term-mode proof. "
                f"The proof term is type-checked by Lean's kernel."
            ),
            "sorry": (
                f"{kind.capitalize()} '{name}' contains 'sorry' — an axiomatically "
                f"assumed gap. This proof is NOT sound and MUST NOT be trusted."
            ),
        }

        base = narratives.get(strategy, (
            f"{kind.capitalize()} '{name}' is proved by a {strategy} strategy. "
            f"The proof is verified by Lean's type-theoretic kernel."
        ))

        if deps:
            dep_str = ", ".join(deps[:5])
            if len(deps) > 5:
                dep_str += f", … ({len(deps)} total)"
            base += f" Depends on: {dep_str}."

        return base

    # ------------------------------------------------- confidence scoring

    def _compute_confidence(self, decl: LeanDecl, strategy: str) -> float:
        """Compute a confidence score for the proof."""
        if decl.body is not None and self._uses_sorry(decl.body):
            return 0.0

        scores: dict[str, float] = {
            "rfl": 1.0,
            "ring": 0.98,
            "omega": 0.98,
            "decide": 0.98,
            "norm_num": 0.97,
            "linarith": 0.96,
            "simp": 0.95,
            "trivial": 0.95,
            "induction": 0.90,
            "cases": 0.90,
            "calc": 0.90,
            "ext": 0.90,
            "funext": 0.90,
            "congr": 0.90,
            "contradiction": 0.88,
            "apply_lemma": 0.87,
            "direct": 0.85,
            "mixed": 0.85,
            "sorry": 0.0,
            "unknown": 0.50,
        }

        base = scores.get(strategy, 0.80)

        if decl.body is not None:
            names = _collect_var_names(decl.body)
            if names & _CLASSICAL_AXIOMS:
                base = min(base, 0.80)

        return base

    # --------------------------------------------------- proof depth

    def _compute_proof_depth(self, body: LeanExpr) -> int:
        """Compute the nesting depth of the proof term."""
        if isinstance(body, (LeanVar, LeanLit, LeanSort, LeanHole, LeanSorry)):
            return 0

        if isinstance(body, LeanApp):
            fn_depth = self._compute_proof_depth(body.fn)
            arg_depths = [self._compute_proof_depth(a) for a in body.args] if body.args else [0]
            return 1 + max(fn_depth, max(arg_depths))

        if isinstance(body, LeanLam):
            return 1 + self._compute_proof_depth(body.body)

        if isinstance(body, LeanPi):
            return 1 + self._compute_proof_depth(body.codomain)

        if isinstance(body, LeanLet):
            return 1 + max(
                self._compute_proof_depth(body.value),
                self._compute_proof_depth(body.body),
            )

        if isinstance(body, LeanMatch):
            scrut_depths = [self._compute_proof_depth(s) for s in body.scrutinees] or [0]
            arm_depths = [self._compute_proof_depth(arm.rhs) for arm in body.arms] or [0]
            return 1 + max(max(scrut_depths), max(arm_depths))

        if isinstance(body, LeanIf):
            return 1 + max(
                self._compute_proof_depth(body.cond),
                self._compute_proof_depth(body.then_),
                self._compute_proof_depth(body.else_),
            )

        if isinstance(body, LeanProj):
            return 1 + self._compute_proof_depth(body.expr)

        if isinstance(body, LeanTactic):
            if not body.args:
                return 0
            return 1 + max(self._compute_proof_depth(a) for a in body.args)

        if isinstance(body, LeanTacticBlock):
            if not body.tactics:
                return 0
            return max(self._compute_proof_depth(t) for t in body.tactics)

        if isinstance(body, LeanAnonymousCtor):
            if not body.args:
                return 0
            return 1 + max(self._compute_proof_depth(a) for a in body.args)

        return 0

    # ----------------------------------------- structural summary

    def _generate_structural_summary(self, analysis: ProofAnalysis) -> str:
        """Generate a one-line human-readable summary of the proof structure."""
        cert = analysis.certificate
        parts: list[str] = []

        parts.append(f"strategy={cert.proof_strategy}")

        if cert.tactic_count > 0:
            parts.append(f"tactics={cert.tactic_count}")

        if cert.proof_depth > 0:
            parts.append(f"depth={cert.proof_depth}")

        if analysis.induction_vars:
            parts.append(f"induction({', '.join(analysis.induction_vars)})")

        if analysis.case_splits:
            parts.append(f"cases={len(analysis.case_splits)}")

        if cert.dependencies:
            parts.append(f"deps={len(cert.dependencies)}")

        if cert.uses_sorry:
            parts.append("SORRY!")

        if not cert.is_constructive:
            parts.append("classical")

        if cert.z3_fragment:
            parts.append(f"z3={cert.z3_fragment}")

        parts.append(f"conf={cert.confidence:.2f}")

        return "; ".join(parts)

    # ------------------------------------------------- key steps

    def _extract_key_steps(self, body: LeanExpr) -> list[str]:
        """Extract human-readable key proof steps from *body*."""
        steps: list[str] = []
        self._collect_key_steps(body, steps, depth=0)
        return steps

    def _collect_key_steps(self, expr: LeanExpr, acc: list[str], depth: int) -> None:
        if depth > 6:
            return

        if isinstance(expr, LeanTactic):
            tname = expr.tactic_name.lower()
            if tname in ("sorry",):
                acc.append("sorry (unproved)")
            elif tname in ("rfl", "ring", "omega", "linarith", "norm_num", "decide", "trivial"):
                acc.append(f"close by {tname}")
            elif tname in ("simp", "simp_all", "dsimp"):
                lemma_args = [_expr_to_text(a) for a in expr.args if isinstance(a, LeanVar)]
                if lemma_args:
                    acc.append(f"simplify with [{', '.join(lemma_args)}]")
                else:
                    acc.append("simplify")
            elif tname in ("rw", "rewrite", "rwa"):
                targets = [_expr_to_text(a) for a in expr.args]
                acc.append(f"rewrite with {', '.join(targets)}" if targets else "rewrite")
            elif tname == "induction":
                vars_ = [_expr_to_text(a) for a in expr.args if isinstance(a, LeanVar)]
                acc.append(f"induct on {', '.join(vars_)}" if vars_ else "induction")
            elif tname in ("cases", "rcases", "obtain"):
                vars_ = [_expr_to_text(a) for a in expr.args if isinstance(a, LeanVar)]
                acc.append(f"case split on {', '.join(vars_)}" if vars_ else "case split")
            elif tname in ("apply", "exact"):
                targets = [_expr_to_text(a) for a in expr.args]
                acc.append(f"{tname} {', '.join(targets)}" if targets else tname)
            elif tname in ("intro", "intros"):
                vars_ = [_expr_to_text(a) for a in expr.args]
                acc.append(f"introduce {', '.join(vars_)}" if vars_ else "introduce")
            elif tname in ("have", "let"):
                if expr.args:
                    acc.append(f"establish {_expr_to_text(expr.args[0])}")
                else:
                    acc.append("establish intermediate")
            elif tname in ("by_contra", "by_contradiction"):
                acc.append("assume negation for contradiction")
            elif tname in ("ext", "funext"):
                acc.append("apply extensionality")
            elif tname == "calc":
                acc.append("begin calculational proof")
            elif tname == "constructor":
                acc.append("split into components")
            elif tname in ("left", "right"):
                acc.append(f"choose {tname} disjunct")
            elif tname == "exfalso":
                acc.append("reduce to proving False")
            elif tname == "contradiction":
                acc.append("derive contradiction")
            else:
                acc.append(f"apply tactic '{tname}'")

            for a in expr.args:
                self._collect_key_steps(a, acc, depth + 1)
            return

        if isinstance(expr, LeanTacticBlock):
            for t in expr.tactics:
                self._collect_key_steps(t, acc, depth)
            return

        if isinstance(expr, LeanApp):
            head = _head_name(expr)
            if head and _is_qualified_name(head):
                acc.append(f"apply {head}")
            for a in expr.args:
                self._collect_key_steps(a, acc, depth + 1)
            return

        if isinstance(expr, LeanMatch):
            scruts = ", ".join(_expr_to_text(s) for s in expr.scrutinees)
            acc.append(f"match on {scruts}")
            for arm in expr.arms:
                self._collect_key_steps(arm.rhs, acc, depth + 1)
            return

        if isinstance(expr, LeanLam):
            self._collect_key_steps(expr.body, acc, depth + 1)
        elif isinstance(expr, LeanLet):
            acc.append(f"let {expr.name}")
            self._collect_key_steps(expr.value, acc, depth + 1)
            self._collect_key_steps(expr.body, acc, depth + 1)
        elif isinstance(expr, LeanIf):
            acc.append(f"branch on {_expr_to_text(expr.cond)}")
            self._collect_key_steps(expr.then_, acc, depth + 1)
            self._collect_key_steps(expr.else_, acc, depth + 1)
        elif isinstance(expr, LeanSorry):
            acc.append("sorry (unproved)")

    # ---------------------------------------- lemma applications

    def _extract_lemma_applications(self, body: LeanExpr) -> list[str]:
        """Extract the names of lemmas applied via ``exact``/``apply``."""
        result: list[str] = []
        self._collect_lemma_applications(body, result)
        return result

    def _collect_lemma_applications(self, expr: LeanExpr, acc: list[str]) -> None:
        if isinstance(expr, LeanTactic):
            tname = expr.tactic_name.lower()
            if tname in ("apply", "exact", "refine", "refine'"):
                for a in expr.args:
                    if isinstance(a, LeanVar) and a.name[0].isupper():
                        acc.append(a.name)
                    elif isinstance(a, LeanVar) and _is_qualified_name(a.name):
                        acc.append(a.name)
                    elif isinstance(a, LeanApp):
                        head = _head_name(a)
                        if head:
                            acc.append(head)
            for a in expr.args:
                self._collect_lemma_applications(a, acc)
            return

        if isinstance(expr, LeanTacticBlock):
            for t in expr.tactics:
                self._collect_lemma_applications(t, acc)
            return

        if isinstance(expr, LeanApp):
            head = _head_name(expr)
            if head and _is_qualified_name(head):
                acc.append(head)
            self._collect_lemma_applications(expr.fn, acc)
            for a in expr.args:
                self._collect_lemma_applications(a, acc)
        elif isinstance(expr, LeanLam):
            self._collect_lemma_applications(expr.body, acc)
        elif isinstance(expr, LeanLet):
            self._collect_lemma_applications(expr.value, acc)
            self._collect_lemma_applications(expr.body, acc)
        elif isinstance(expr, LeanMatch):
            for s in expr.scrutinees:
                self._collect_lemma_applications(s, acc)
            for arm in expr.arms:
                self._collect_lemma_applications(arm.rhs, acc)
        elif isinstance(expr, LeanIf):
            self._collect_lemma_applications(expr.cond, acc)
            self._collect_lemma_applications(expr.then_, acc)
            self._collect_lemma_applications(expr.else_, acc)
        elif isinstance(expr, LeanAnonymousCtor):
            for a in expr.args:
                self._collect_lemma_applications(a, acc)


# ---------------------------------------------------------------------------
# Convenience function
# ---------------------------------------------------------------------------

def analyze_proof(decl: LeanDecl) -> SoundnessCertificate:
    """One-shot convenience: analyse *decl* and return its ``SoundnessCertificate``."""
    analyzer = ProofAnalyzer()
    analysis = analyzer.analyze(decl)
    return analysis.certificate


# ---------------------------------------------------------------------------
# Self-tests
# ---------------------------------------------------------------------------

if __name__ == "__main__":

    def _make_decl(
        name: str,
        body: Optional[LeanExpr],
        return_type: Optional[LeanExpr] = None,
        kind: str = "theorem",
        params: Optional[list[LeanParam]] = None,
    ) -> LeanDecl:
        return LeanDecl(
            kind=kind,
            name=name,
            universe_params=[],
            params=params or [],
            return_type=return_type,
            body=body,
            attributes=[],
            docstring=None,
            namespace="",
        )

    analyzer = ProofAnalyzer()
    errors: list[str] = []

    def check(cond: bool, msg: str) -> None:
        if not cond:
            errors.append(msg)
            print(f"  FAIL: {msg}")
        else:
            print(f"  ok: {msg}")

    # ------------------------------------------------------------------
    # 1. rfl proof
    # ------------------------------------------------------------------
    print("Test 1: rfl proof")
    rfl_decl = _make_decl(
        "Nat.add_zero_rfl",
        body=LeanVar("rfl"),
        return_type=LeanApp(
            fn=LeanVar("Eq"),
            args=[
                LeanApp(fn=LeanVar("HAdd.hAdd"), args=[LeanVar("n"), LeanLit(0)]),
                LeanVar("n"),
            ],
        ),
        params=[LeanParam("n", LeanVar("Nat"), "explicit")],
    )
    a1 = analyzer.analyze(rfl_decl)
    check(a1.certificate.proof_strategy == "rfl", "strategy=rfl")
    check(a1.certificate.confidence == 1.0, "confidence=1.0 for rfl")
    check(a1.certificate.is_constructive, "rfl is constructive")
    check(not a1.certificate.uses_sorry, "rfl does not use sorry")
    check(a1.certificate.decidable, "Nat equality is decidable")
    check(a1.certificate.z3_fragment == "QF_LIA", "Nat arith → QF_LIA")
    check(len(a1.certificate.lean_proof_hash) == 64, "SHA-256 hash is 64 hex chars")

    # ------------------------------------------------------------------
    # 2. simp proof
    # ------------------------------------------------------------------
    print("\nTest 2: simp proof")
    simp_decl = _make_decl(
        "List.length_nil",
        body=LeanTacticBlock(tactics=[
            LeanTactic("simp", [LeanVar("List.length")]),
        ]),
        return_type=LeanApp(
            fn=LeanVar("Eq"),
            args=[
                LeanApp(fn=LeanVar("List.length"), args=[LeanVar("List.nil")]),
                LeanLit(0),
            ],
        ),
    )
    a2 = analyzer.analyze(simp_decl)
    check(a2.certificate.proof_strategy == "simp", "strategy=simp")
    check(a2.certificate.confidence == 0.95, "confidence=0.95 for simp")
    check(a2.certificate.tactic_count == 1, "tactic_count=1")

    # ------------------------------------------------------------------
    # 3. ring proof
    # ------------------------------------------------------------------
    print("\nTest 3: ring proof")
    ring_decl = _make_decl(
        "Nat.mul_comm_ring",
        body=LeanTacticBlock(tactics=[LeanTactic("ring", [])]),
        return_type=LeanApp(
            fn=LeanVar("Eq"),
            args=[
                LeanApp(fn=LeanVar("HMul.hMul"), args=[LeanVar("a"), LeanVar("b")]),
                LeanApp(fn=LeanVar("HMul.hMul"), args=[LeanVar("b"), LeanVar("a")]),
            ],
        ),
        params=[
            LeanParam("a", LeanVar("Nat"), "explicit"),
            LeanParam("b", LeanVar("Nat"), "explicit"),
        ],
    )
    a3 = analyzer.analyze(ring_decl)
    check(a3.certificate.proof_strategy == "ring", "strategy=ring")
    check(a3.certificate.confidence == 0.98, "confidence=0.98 for ring")
    check(a3.certificate.z3_fragment == "QF_NIA", "Nat with mul → QF_NIA")

    # ------------------------------------------------------------------
    # 4. omega proof
    # ------------------------------------------------------------------
    print("\nTest 4: omega proof")
    omega_decl = _make_decl(
        "Nat.lt_succ",
        body=LeanTacticBlock(tactics=[LeanTactic("omega", [])]),
        return_type=LeanApp(
            fn=LeanVar("LT.lt"),
            args=[LeanVar("n"), LeanApp(fn=LeanVar("Nat.succ"), args=[LeanVar("n")])],
        ),
        params=[LeanParam("n", LeanVar("Nat"), "explicit")],
    )
    a4 = analyzer.analyze(omega_decl)
    check(a4.certificate.proof_strategy == "omega", "strategy=omega")
    check(a4.certificate.confidence == 0.98, "confidence=0.98 for omega")

    # ------------------------------------------------------------------
    # 5. induction proof
    # ------------------------------------------------------------------
    print("\nTest 5: induction proof")
    induction_decl = _make_decl(
        "Nat.add_comm",
        body=LeanTacticBlock(tactics=[
            LeanTactic("induction", [LeanVar("n")]),
            LeanTactic("simp", []),
            LeanTactic("simp", [LeanVar("Nat.add_succ")]),
        ]),
        return_type=LeanApp(
            fn=LeanVar("Eq"),
            args=[
                LeanApp(fn=LeanVar("HAdd.hAdd"), args=[LeanVar("n"), LeanVar("m")]),
                LeanApp(fn=LeanVar("HAdd.hAdd"), args=[LeanVar("m"), LeanVar("n")]),
            ],
        ),
        params=[
            LeanParam("n", LeanVar("Nat"), "explicit"),
            LeanParam("m", LeanVar("Nat"), "explicit"),
        ],
    )
    a5 = analyzer.analyze(induction_decl)
    check(a5.certificate.proof_strategy == "induction", "strategy=induction")
    check(a5.certificate.confidence == 0.90, "confidence=0.90 for induction")
    check("n" in a5.induction_vars, "induction on n")
    check(a5.certificate.tactic_count == 3, "tactic_count=3")

    # ------------------------------------------------------------------
    # 6. sorry proof  (confidence = 0.0)
    # ------------------------------------------------------------------
    print("\nTest 6: sorry proof")
    sorry_decl = _make_decl(
        "Broken.theorem",
        body=LeanSorry(),
        return_type=LeanApp(fn=LeanVar("Eq"), args=[LeanLit(1), LeanLit(2)]),
    )
    a6 = analyzer.analyze(sorry_decl)
    check(a6.certificate.proof_strategy == "sorry", "strategy=sorry")
    check(a6.certificate.confidence == 0.0, "confidence=0.0 for sorry")
    check(a6.certificate.uses_sorry, "uses_sorry=True")

    # ------------------------------------------------------------------
    # 7. sorry in tactic block
    # ------------------------------------------------------------------
    print("\nTest 7: sorry inside tactic block")
    sorry_tactic_decl = _make_decl(
        "Broken.tactic_sorry",
        body=LeanTacticBlock(tactics=[
            LeanTactic("intro", [LeanVar("h")]),
            LeanTactic("sorry", []),
        ]),
    )
    a7 = analyzer.analyze(sorry_tactic_decl)
    check(a7.certificate.uses_sorry, "sorry detected in tactic block")
    check(a7.certificate.confidence == 0.0, "confidence=0.0 for tactic sorry")

    # ------------------------------------------------------------------
    # 8. contradiction / by_contra proof
    # ------------------------------------------------------------------
    print("\nTest 8: contradiction proof")
    contra_decl = _make_decl(
        "Not.intro_example",
        body=LeanTacticBlock(tactics=[
            LeanTactic("by_contra", [LeanVar("h")]),
            LeanTactic("exact", [LeanApp(fn=LeanVar("Absurd.mk"), args=[LeanVar("h")])]),
        ]),
    )
    a8 = analyzer.analyze(contra_decl)
    check(a8.certificate.proof_strategy == "contradiction", "strategy=contradiction")

    # ------------------------------------------------------------------
    # 9. cases proof
    # ------------------------------------------------------------------
    print("\nTest 9: cases proof")
    cases_decl = _make_decl(
        "Bool.not_not",
        body=LeanTacticBlock(tactics=[
            LeanTactic("cases", [LeanVar("b")]),
            LeanTactic("rfl", []),
            LeanTactic("rfl", []),
        ]),
        return_type=LeanApp(
            fn=LeanVar("Eq"),
            args=[
                LeanApp(fn=LeanVar("Bool.not"), args=[
                    LeanApp(fn=LeanVar("Bool.not"), args=[LeanVar("b")])
                ]),
                LeanVar("b"),
            ],
        ),
        params=[LeanParam("b", LeanVar("Bool"), "explicit")],
    )
    a9 = analyzer.analyze(cases_decl)
    check(a9.certificate.proof_strategy == "cases", "strategy=cases")
    check(len(a9.case_splits) > 0, "case splits detected")

    # ------------------------------------------------------------------
    # 10. term-mode direct proof
    # ------------------------------------------------------------------
    print("\nTest 10: term-mode direct proof")
    term_decl = _make_decl(
        "Id.mk",
        body=LeanLam(
            params=[LeanParam("x", LeanVar("α"), "explicit")],
            body=LeanVar("x"),
        ),
        return_type=LeanPi(
            params=[LeanParam("x", LeanVar("α"), "explicit")],
            codomain=LeanVar("α"),
        ),
    )
    a10 = analyzer.analyze(term_decl)
    check(a10.certificate.proof_strategy == "direct", "strategy=direct for lambda")
    check(a10.certificate.is_constructive, "term-mode is constructive")

    # ------------------------------------------------------------------
    # 11. apply_lemma proof
    # ------------------------------------------------------------------
    print("\nTest 11: apply_lemma proof")
    apply_decl = _make_decl(
        "Nat.le_of_lt",
        body=LeanTacticBlock(tactics=[
            LeanTactic("exact", [LeanVar("Nat.le_of_lt_succ")]),
        ]),
    )
    a11 = analyzer.analyze(apply_decl)
    check(a11.certificate.proof_strategy == "apply_lemma", "strategy=apply_lemma")
    check("Nat.le_of_lt_succ" in a11.lemma_applications, "lemma application extracted")

    # ------------------------------------------------------------------
    # 12. linarith proof
    # ------------------------------------------------------------------
    print("\nTest 12: linarith proof")
    linarith_decl = _make_decl(
        "Nat.add_pos",
        body=LeanTacticBlock(tactics=[LeanTactic("linarith", [])]),
        return_type=LeanApp(
            fn=LeanVar("LT.lt"),
            args=[LeanLit(0), LeanApp(fn=LeanVar("HAdd.hAdd"), args=[LeanVar("a"), LeanVar("b")])],
        ),
        params=[
            LeanParam("a", LeanVar("Nat"), "explicit"),
            LeanParam("b", LeanVar("Nat"), "explicit"),
        ],
    )
    a12 = analyzer.analyze(linarith_decl)
    check(a12.certificate.proof_strategy == "linarith", "strategy=linarith")
    check(a12.certificate.confidence == 0.96, "confidence=0.96 for linarith")

    # ------------------------------------------------------------------
    # 13. classical proof
    # ------------------------------------------------------------------
    print("\nTest 13: classical proof (non-constructive)")
    classical_decl = _make_decl(
        "Classical.em_example",
        body=LeanApp(fn=LeanVar("Classical.em"), args=[LeanVar("P")]),
        return_type=LeanApp(
            fn=LeanVar("Or"),
            args=[LeanVar("P"), LeanApp(fn=LeanVar("Not"), args=[LeanVar("P")])],
        ),
    )
    a13 = analyzer.analyze(classical_decl)
    check(not a13.certificate.is_constructive, "classical proof is not constructive")
    check("Classical.em" in a13.certificate.axioms_used, "Classical.em in axioms_used")
    check(a13.certificate.confidence <= 0.80, "classical confidence ≤ 0.80")

    # ------------------------------------------------------------------
    # 14. empty proof (hole body)
    # ------------------------------------------------------------------
    print("\nTest 14: empty proof (no body)")
    empty_decl = _make_decl("Axiom.empty", body=None, kind="axiom")
    a14 = analyzer.analyze(empty_decl)
    check(a14.certificate.proof_strategy == "unknown", "strategy=unknown for no body")
    check(a14.certificate.lean_proof_hash != "", "hash computed even for empty proof")

    # ------------------------------------------------------------------
    # 15. ext proof
    # ------------------------------------------------------------------
    print("\nTest 15: ext proof")
    ext_decl = _make_decl(
        "Set.eq_ext",
        body=LeanTacticBlock(tactics=[
            LeanTactic("ext", [LeanVar("x")]),
            LeanTactic("simp", []),
        ]),
    )
    a15 = analyzer.analyze(ext_decl)
    check(a15.certificate.proof_strategy == "ext", "strategy=ext")

    # ------------------------------------------------------------------
    # 16. dependency extraction
    # ------------------------------------------------------------------
    print("\nTest 16: dependency extraction")
    dep_decl = _make_decl(
        "MyLemma",
        body=LeanApp(
            fn=LeanVar("Nat.add_comm"),
            args=[
                LeanApp(fn=LeanVar("Nat.mul_comm"), args=[LeanVar("a"), LeanVar("b")]),
                LeanVar("c"),
            ],
        ),
    )
    a16 = analyzer.analyze(dep_decl)
    check("Nat.add_comm" in a16.certificate.dependencies, "Nat.add_comm is a dependency")
    check("Nat.mul_comm" in a16.certificate.dependencies, "Nat.mul_comm is a dependency")

    # ------------------------------------------------------------------
    # 17. bitvector Z3 fragment
    # ------------------------------------------------------------------
    print("\nTest 17: bitvector Z3 fragment")
    bv_decl = _make_decl(
        "BV.add_comm",
        body=LeanTacticBlock(tactics=[LeanTactic("decide", [])]),
        return_type=LeanApp(
            fn=LeanVar("Eq"),
            args=[
                LeanApp(fn=LeanVar("BitVec.add"), args=[LeanVar("a"), LeanVar("b")]),
                LeanApp(fn=LeanVar("BitVec.add"), args=[LeanVar("b"), LeanVar("a")]),
            ],
        ),
    )
    a17 = analyzer.analyze(bv_decl)
    check(a17.certificate.z3_fragment == "QF_BV", "BitVec → QF_BV")

    # ------------------------------------------------------------------
    # 18. string Z3 fragment
    # ------------------------------------------------------------------
    print("\nTest 18: string Z3 fragment")
    str_decl = _make_decl(
        "String.append_assoc",
        body=LeanTacticBlock(tactics=[LeanTactic("simp", [])]),
        return_type=LeanApp(
            fn=LeanVar("Eq"),
            args=[
                LeanApp(fn=LeanVar("String.append"), args=[
                    LeanApp(fn=LeanVar("String.append"), args=[LeanVar("a"), LeanVar("b")]),
                    LeanVar("c"),
                ]),
                LeanApp(fn=LeanVar("String.append"), args=[
                    LeanVar("a"),
                    LeanApp(fn=LeanVar("String.append"), args=[LeanVar("b"), LeanVar("c")]),
                ]),
            ],
        ),
    )
    a18 = analyzer.analyze(str_decl)
    check(a18.certificate.z3_fragment == "QF_S", "String → QF_S")

    # ------------------------------------------------------------------
    # 19. soundness narrative generation
    # ------------------------------------------------------------------
    print("\nTest 19: soundness narrative")
    check("rfl" in a1.certificate.soundness_narrative.lower()
          or "definitional" in a1.certificate.soundness_narrative.lower(),
          "rfl narrative mentions definitional equality")
    check("sorry" in a6.certificate.soundness_narrative.lower()
          or "not sound" in a6.certificate.soundness_narrative.lower(),
          "sorry narrative warns about unsoundness")

    # ------------------------------------------------------------------
    # 20. tactic histogram
    # ------------------------------------------------------------------
    print("\nTest 20: tactic histogram")
    check("simp" in a5.tactic_histogram, "simp in induction histogram")
    check(a5.tactic_histogram.get("simp", 0) == 2, "simp count = 2")
    check(a5.tactic_histogram.get("induction", 0) == 1, "induction count = 1")

    # ------------------------------------------------------------------
    # 21. match as cases proof (term-mode)
    # ------------------------------------------------------------------
    print("\nTest 21: match as term-mode cases")
    from cctt.mathlib_bridge.lean_parser import MatchArm
    match_decl = _make_decl(
        "Bool.decide_match",
        body=LeanMatch(
            scrutinees=[LeanVar("b")],
            arms=[
                MatchArm(patterns=[LeanVar("true")], rhs=LeanVar("rfl")),
                MatchArm(patterns=[LeanVar("false")], rhs=LeanVar("rfl")),
            ],
        ),
    )
    a21 = analyzer.analyze(match_decl)
    check(a21.certificate.proof_strategy == "cases", "match → strategy=cases")

    # ------------------------------------------------------------------
    # 22. mixed tactic proof
    # ------------------------------------------------------------------
    print("\nTest 22: mixed tactic proof")
    mixed_decl = _make_decl(
        "Complex.theorem",
        body=LeanTacticBlock(tactics=[
            LeanTactic("intro", [LeanVar("h")]),
            LeanTactic("rw", [LeanVar("Nat.add_zero")]),
            LeanTactic("apply", [LeanVar("Nat.le_refl")]),
            LeanTactic("simp", []),
            LeanTactic("ring", []),
        ]),
    )
    a22 = analyzer.analyze(mixed_decl)
    check(a22.certificate.proof_strategy == "mixed", "strategy=mixed for diverse tactics")
    check(a22.certificate.tactic_count == 5, "tactic_count=5")

    # ------------------------------------------------------------------
    # 23. rewrite detection
    # ------------------------------------------------------------------
    print("\nTest 23: rewrite detection")
    rw_decl = _make_decl(
        "Rw.example",
        body=LeanTacticBlock(tactics=[
            LeanTactic("rw", [LeanVar("Nat.add_comm")]),
            LeanTactic("rw", [LeanVar("Nat.add_assoc")]),
            LeanTactic("rfl", []),
        ]),
    )
    a23 = analyzer.analyze(rw_decl)
    check("Nat.add_comm" in a23.rewrite_targets, "rewrite target: Nat.add_comm")
    check("Nat.add_assoc" in a23.rewrite_targets, "rewrite target: Nat.add_assoc")

    # ------------------------------------------------------------------
    # 24. proof depth computation
    # ------------------------------------------------------------------
    print("\nTest 24: proof depth")
    deep_body = LeanApp(
        fn=LeanVar("f"),
        args=[LeanApp(
            fn=LeanVar("g"),
            args=[LeanApp(fn=LeanVar("h"), args=[LeanVar("x")])],
        )],
    )
    deep_decl = _make_decl("Deep.proof", body=deep_body)
    a24 = analyzer.analyze(deep_decl)
    check(a24.certificate.proof_depth >= 3, f"depth ≥ 3 (got {a24.certificate.proof_depth})")

    # ------------------------------------------------------------------
    # 25. structural summary
    # ------------------------------------------------------------------
    print("\nTest 25: structural summary")
    check(len(a1.structural_summary) > 0, "structural summary is non-empty")
    check("rfl" in a1.structural_summary, "summary mentions rfl")
    check("SORRY" in a6.structural_summary, "sorry summary contains SORRY")

    # ------------------------------------------------------------------
    # 26. convenience function
    # ------------------------------------------------------------------
    print("\nTest 26: convenience function analyze_proof")
    cert26 = analyze_proof(rfl_decl)
    check(isinstance(cert26, SoundnessCertificate), "analyze_proof returns SoundnessCertificate")
    check(cert26.proof_strategy == "rfl", "convenience function detects rfl")

    # ------------------------------------------------------------------
    # 27. decide tactic → decidable
    # ------------------------------------------------------------------
    print("\nTest 27: decide → decidable")
    decide_decl = _make_decl(
        "Decidable.example",
        body=LeanTacticBlock(tactics=[LeanTactic("decide", [])]),
        return_type=LeanApp(fn=LeanVar("Eq"), args=[LeanLit(2), LeanLit(2)]),
    )
    a27 = analyzer.analyze(decide_decl)
    check(a27.certificate.decidable, "decide implies decidable")
    check(a27.certificate.proof_strategy == "decide", "strategy=decide")

    # ------------------------------------------------------------------
    # 28. array Z3 fragment
    # ------------------------------------------------------------------
    print("\nTest 28: array Z3 fragment")
    array_decl = _make_decl(
        "Array.size_push",
        body=LeanTacticBlock(tactics=[LeanTactic("simp", [])]),
        return_type=LeanApp(
            fn=LeanVar("Eq"),
            args=[
                LeanApp(fn=LeanVar("Array.size"), args=[
                    LeanApp(fn=LeanVar("Array.push"), args=[LeanVar("a"), LeanVar("x")])
                ]),
                LeanApp(fn=LeanVar("HAdd.hAdd"), args=[
                    LeanApp(fn=LeanVar("Array.size"), args=[LeanVar("a")]),
                    LeanLit(1),
                ]),
            ],
        ),
    )
    a28 = analyzer.analyze(array_decl)
    check(a28.certificate.z3_fragment == "QF_AUFLIA", "Array + arith → QF_AUFLIA")

    # ------------------------------------------------------------------
    # 29. key steps extraction
    # ------------------------------------------------------------------
    print("\nTest 29: key steps extraction")
    check(len(a5.key_steps) > 0, "induction proof has key steps")
    has_induct_step = any("induct" in s for s in a5.key_steps)
    check(has_induct_step, "key steps mention induction")

    # ------------------------------------------------------------------
    # 30. analyze_proof_body (bare body, no declaration)
    # ------------------------------------------------------------------
    print("\nTest 30: analyze_proof_body")
    bare = analyzer.analyze_proof_body(LeanVar("rfl"))
    check(bare.certificate.proof_strategy == "rfl", "bare rfl body → strategy=rfl")
    check(bare.declaration.name == "<anonymous>", "synthetic decl is <anonymous>")

    # ------------------------------------------------------------------
    # 31. propext axiom detection
    # ------------------------------------------------------------------
    print("\nTest 31: foundational axiom detection")
    propext_decl = _make_decl(
        "Propext.example",
        body=LeanApp(fn=LeanVar("propext"), args=[LeanVar("h")]),
    )
    a31 = analyzer.analyze(propext_decl)
    check("propext" in a31.certificate.axioms_used, "propext detected in axioms_used")

    # ------------------------------------------------------------------
    # 32. norm_num strategy
    # ------------------------------------------------------------------
    print("\nTest 32: norm_num strategy")
    norm_num_decl = _make_decl(
        "Norm_num.example",
        body=LeanTacticBlock(tactics=[LeanTactic("norm_num", [])]),
    )
    a32 = analyzer.analyze(norm_num_decl)
    check(a32.certificate.proof_strategy == "norm_num", "strategy=norm_num")
    check(a32.certificate.confidence == 0.97, "confidence=0.97 for norm_num")

    # ------------------------------------------------------------------
    # 33. hash stability
    # ------------------------------------------------------------------
    print("\nTest 33: hash stability")
    h1 = analyzer.analyze(rfl_decl).certificate.lean_proof_hash
    h2 = analyzer.analyze(rfl_decl).certificate.lean_proof_hash
    check(h1 == h2, "same proof → same hash")
    h3 = analyzer.analyze(ring_decl).certificate.lean_proof_hash
    check(h1 != h3, "different proof → different hash")

    # ------------------------------------------------------------------
    # 34. higher-order quantifier → undecidable
    # ------------------------------------------------------------------
    print("\nTest 34: higher-order quantifier → undecidable")
    ho_decl = _make_decl(
        "HO.undecidable",
        body=LeanVar("rfl"),
        return_type=LeanPi(
            params=[LeanParam("f", LeanPi(
                params=[LeanParam("x", LeanVar("Nat"), "explicit")],
                codomain=LeanVar("Nat"),
            ), "explicit")],
            codomain=LeanApp(fn=LeanVar("Eq"), args=[
                LeanApp(fn=LeanVar("f"), args=[LeanLit(0)]),
                LeanLit(0),
            ]),
        ),
    )
    a34 = analyzer.analyze(ho_decl)
    check(not a34.certificate.decidable, "higher-order quantifier → undecidable")

    # ------------------------------------------------------------------
    # Summary
    # ------------------------------------------------------------------
    print(f"\n{'=' * 50}")
    if errors:
        print(f"FAILED: {len(errors)} test(s)")
        for e in errors:
            print(f"  - {e}")
        raise SystemExit(1)
    else:
        print("All proof_analyzer self-tests passed!")
