"""equiv_proof_language.py — LLM-written equivalence proofs for OTerm programs.

When two algorithms compute the same thing but via completely different
control flow (bubble sort vs merge sort, iterative vs recursive fibonacci,
imperative accumulator vs functional fold), the automated equivalence
checker cannot bridge them.  This module lets the LLM write a PROOF
that the two functions are equivalent, in a Lean-like language that
compiles to the ProofTerm kernel and is verified mechanically.

Architecture
============

The equivalence proof is F*-style CODE-ATTACHED: it references both
functions by name, their actual parameters, and intermediate properties
of their code.  The proof compiles to a ProofTerm tree rooted at ``Ext``
(functional extensionality), which the checker verifies against the
compiled OTerms.

Proof Script Format
===================

    equiv <proof_name>
      func_a: <function_name_a>
      func_b: <function_name_b>
      given <var> : <sort>, ...
      effects: both pure | a_reads b_pure | ...
      show func_a(args) = func_b(args)

      -- Lemmas (each compiled to Cut + sub-proof)
      have <name> : <lhs> = <rhs> := by <tactic>

      -- Final: chain the lemmas into the main equality
      exact trans(h1, sym(h2))
    qed

Effect Integration
==================

Before compiling the proof, we run EffectAnalyzer on both functions.
The effect claim in the proof is VERIFIED against the analysis:

  - ``both pure``    → both must be PURE or READS_STATE
  - ``a_reads b_pure`` → a may read state, b is pure
  - incompatible effects → proof REJECTED (unsound to use funext)

The effect verification result becomes part of the proof certificate's
trust level.  If effects can't be statically verified (dynamic dispatch),
the trust level is EFFECT_ASSUMED rather than EFFECT_VERIFIED.

Compilation
===========

    equiv proof          → Ext(var, body_proof)
    have h : a = b := t → Cut(a, b, compile(t), rest)
    exact trans(p, q)    → Trans(compile(p), compile(q))
    exact sym(p)         → Sym(compile(p))
    exact refl           → Refl(term)
    exact cong(f, p)     → Cong(f, (compile(p),))
    by contradiction     → ExFalso(...)
    by omega             → Z3Discharge(QF_LIA)
    by z3                → Z3Discharge(formula)
    by apply <axiom>     → Assume(label=axiom, ...) [AXIOM_TRUSTED]
    by funext <var> ...  → Ext(var, ...)

Soundness
=========

1. The proof language is SYNTACTIC SUGAR over the ProofTerm kernel.
2. Every tactic compiles to a ProofTerm verified by check_proof().
3. Effect claims are independently verified by EffectAnalyzer.
4. Trust levels distinguish KERNEL_VERIFIED from AXIOM_TRUSTED.
5. ``apply`` (library axioms) are explicitly marked as trusted
   assumptions — the proof is valid MODULO these axioms.
"""
from __future__ import annotations

import logging
import re
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, List, Optional, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OLam,
    compile_to_oterm,
)
from cctt.proof_theory.terms import (
    ProofTerm, Refl, Sym, Trans, Cong, Ext, Cut, Assume,
    Z3Discharge, ExFalso, CasesSplit, Rewrite,
    NatInduction, ListInduction,
)

log = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════
# Effect claim — what the proof asserts about both functions' effects
# ═══════════════════════════════════════════════════════════════════

class EffectClaim(Enum):
    """Effect compatibility claim in an equivalence proof."""
    BOTH_PURE = "both pure"
    BOTH_READ = "both read"
    A_PURE_B_READ = "a_pure b_read"
    A_READ_B_PURE = "a_read b_pure"
    UNKNOWN = "unknown"


class EffectVerdict(Enum):
    """Result of effect verification."""
    VERIFIED = "effect_verified"     # EffectAnalyzer confirms claim
    ASSUMED = "effect_assumed"       # Can't verify statically, but claim is plausible
    REJECTED = "effect_rejected"     # Claim contradicts analysis


# ═══════════════════════════════════════════════════════════════════
# Proof step AST
# ═══════════════════════════════════════════════════════════════════

class EquivTacticKind(Enum):
    """Tactics available in equivalence proofs."""
    # Terminal
    REFL = auto()
    SYM = auto()
    TRANS = auto()
    CONG = auto()
    CONTRADICTION = auto()
    OMEGA = auto()
    Z3 = auto()
    STRUCTURAL = auto()
    # Function-level
    FUNEXT = auto()
    # Axiom reference
    APPLY = auto()
    # Composition
    EXACT = auto()
    # Induction
    NAT_INDUCTION = auto()    # induction on natural numbers
    LIST_INDUCTION = auto()   # induction on lists
    # Case splitting
    CASES = auto()            # split into cases per branch


@dataclass(frozen=True)
class EquivTactic:
    """A single tactic in an equivalence proof."""
    kind: EquivTacticKind
    args: Tuple[str, ...] = ()
    comment: str = ""


@dataclass(frozen=True)
class EquivStep:
    """One step in an equivalence proof: 'have h : a = b := by tactic'."""
    name: str          # lemma name (e.g., "h1")
    lhs: str           # left-hand side expression
    rhs: str           # right-hand side expression
    tactic: EquivTactic
    trust: str = "kernel"  # "kernel" or "axiom"


@dataclass(frozen=True)
class EquivScript:
    """A complete equivalence proof script.

    Attached to two specific Python functions.  Compiles to an Ext
    proof term verified by the CCTT proof checker kernel.
    """
    name: str
    func_a: str              # first function name
    func_b: str              # second function name
    given: Dict[str, str]    # shared parameter declarations
    effect_claim: EffectClaim
    goal_lhs: str            # e.g., "bubble_sort(xs)"
    goal_rhs: str            # e.g., "merge_sort(xs)"
    steps: Tuple[EquivStep, ...]  # have-steps
    final_tactic: EquivTactic     # exact step
    source_a: str = ""       # source code of func_a (for context)
    source_b: str = ""       # source code of func_b (for context)

    def pretty(self) -> str:
        lines = [f"equiv {self.name}"]
        lines.append(f"  func_a: {self.func_a}")
        lines.append(f"  func_b: {self.func_b}")
        if self.given:
            givens = ", ".join(f"{v} : {s}" for v, s in self.given.items())
            lines.append(f"  given {givens}")
        lines.append(f"  effects: {self.effect_claim.value}")
        lines.append(f"  show {self.goal_lhs} = {self.goal_rhs}")
        lines.append("")
        for step in self.steps:
            tac_str = _tactic_pretty(step.tactic)
            trust_tag = " [AXIOM]" if step.trust == "axiom" else ""
            lines.append(
                f"  have {step.name} : {step.lhs} = {step.rhs} := "
                f"by {tac_str}{trust_tag}"
            )
        lines.append(f"  exact {_tactic_pretty(self.final_tactic)}")
        lines.append("qed")
        return "\n".join(lines)


def _tactic_pretty(tactic: EquivTactic) -> str:
    name = tactic.kind.name.lower()
    if tactic.args:
        return f"{name}({', '.join(tactic.args)})"
    return name


# ═══════════════════════════════════════════════════════════════════
# Parser — equiv proof text → EquivScript
# ═══════════════════════════════════════════════════════════════════

_EFFECT_MAP = {
    'both pure': EffectClaim.BOTH_PURE,
    'both read': EffectClaim.BOTH_READ,
    'a_pure b_read': EffectClaim.A_PURE_B_READ,
    'a_read b_pure': EffectClaim.A_READ_B_PURE,
}

_EQUIV_TACTIC_MAP = {
    'refl': EquivTacticKind.REFL,
    'sym': EquivTacticKind.SYM,
    'trans': EquivTacticKind.TRANS,
    'cong': EquivTacticKind.CONG,
    'contradiction': EquivTacticKind.CONTRADICTION,
    'omega': EquivTacticKind.OMEGA,
    'z3': EquivTacticKind.Z3,
    'structural': EquivTacticKind.STRUCTURAL,
    'funext': EquivTacticKind.FUNEXT,
    'apply': EquivTacticKind.APPLY,
    'nat_induction': EquivTacticKind.NAT_INDUCTION,
    'induction': EquivTacticKind.NAT_INDUCTION,
    'list_induction': EquivTacticKind.LIST_INDUCTION,
    'cases': EquivTacticKind.CASES,
}


def parse_equiv_tactic(text: str) -> Optional[EquivTactic]:
    """Parse a single tactic expression."""
    text = text.strip()
    if not text:
        return None

    # Strip comment
    comment = ""
    if "--" in text:
        idx = text.index("--")
        comment = text[idx + 2:].strip()
        text = text[:idx].strip()

    # Try as function call: tactic(arg1, arg2)
    m = re.match(r'(\w+)\s*\((.+)\)', text)
    if m:
        name = m.group(1).lower()
        args_str = m.group(2)
        args = tuple(a.strip() for a in args_str.split(',') if a.strip())
        kind = _EQUIV_TACTIC_MAP.get(name)
        if kind is None:
            # Unknown tactic name → try as EXACT with the full text as arg
            return EquivTactic(kind=EquivTacticKind.EXACT, args=(text,), comment=comment)
        return EquivTactic(kind=kind, args=args, comment=comment)

    # Try as simple keyword
    name = text.split()[0].lower()
    rest = text[len(name):].strip()
    kind = _EQUIV_TACTIC_MAP.get(name)
    if kind is not None:
        args = (rest,) if rest else ()
        return EquivTactic(kind=kind, args=args, comment=comment)

    # Fallback: treat as EXACT
    return EquivTactic(kind=EquivTacticKind.EXACT, args=(text,), comment=comment)


def parse_equiv_script(text: str) -> Optional[EquivScript]:
    """Parse a complete equivalence proof script.

    Format:
        equiv <name>
          func_a: <name>
          func_b: <name>
          given <var> : <sort>, ...
          effects: both pure
          show <lhs> = <rhs>
          have <h> : <lhs> = <rhs> := by <tactic>
          exact <final>
        qed
    """
    lines = [l.rstrip() for l in text.strip().split('\n')]
    lines = [l for l in lines if l.strip() and not l.strip().startswith('--')]

    if not lines:
        return None

    # Parse header
    header = lines[0].strip()
    m = re.match(r'equiv\s+(\w+)', header)
    if not m:
        return None
    proof_name = m.group(1)

    func_a = func_b = ""
    given: Dict[str, str] = {}
    effect_claim = EffectClaim.BOTH_PURE
    goal_lhs = goal_rhs = ""
    steps: List[EquivStep] = []
    final_tactic: Optional[EquivTactic] = None

    i = 1
    while i < len(lines):
        line = lines[i].strip()

        if line.startswith('func_a:'):
            func_a = line[7:].strip()
            i += 1

        elif line.startswith('func_b:'):
            func_b = line[7:].strip()
            i += 1

        elif line.startswith('given '):
            decls = line[5:].split(',')
            for decl in decls:
                decl = decl.strip()
                if ':' in decl:
                    var, sort = decl.split(':', 1)
                    given[var.strip()] = sort.strip()
            i += 1

        elif line.startswith('effects:'):
            claim_text = line[8:].strip().lower()
            effect_claim = _EFFECT_MAP.get(claim_text, EffectClaim.UNKNOWN)
            i += 1

        elif line.startswith('show '):
            show_text = line[5:].strip()
            if '=' in show_text:
                parts = show_text.split('=', 1)
                goal_lhs = parts[0].strip()
                goal_rhs = parts[1].strip()
            i += 1

        elif line.startswith('have '):
            # Parse: have h : lhs = rhs := by tactic
            m = re.match(
                r'have\s+(\w+)\s*:\s*(.+?)\s*=\s*(.+?)\s*:=\s*by\s+(.+)',
                line,
            )
            if m:
                step_name = m.group(1)
                step_lhs = m.group(2).strip()
                step_rhs = m.group(3).strip()
                tac_text = m.group(4).strip()
                tactic = parse_equiv_tactic(tac_text)
                if tactic:
                    trust = "axiom" if tactic.kind == EquivTacticKind.APPLY else "kernel"
                    steps.append(EquivStep(
                        name=step_name, lhs=step_lhs, rhs=step_rhs,
                        tactic=tactic, trust=trust,
                    ))
            i += 1

        elif line.startswith('exact '):
            tac_text = line[6:].strip()
            final_tactic = parse_equiv_tactic(tac_text)
            i += 1

        elif line == 'qed':
            break
        else:
            i += 1

    if not func_a or not func_b or not goal_lhs:
        return None
    if final_tactic is None:
        final_tactic = EquivTactic(kind=EquivTacticKind.REFL)

    return EquivScript(
        name=proof_name,
        func_a=func_a,
        func_b=func_b,
        given=given,
        effect_claim=effect_claim,
        goal_lhs=goal_lhs,
        goal_rhs=goal_rhs,
        steps=tuple(steps),
        final_tactic=final_tactic,
    )


# ═══════════════════════════════════════════════════════════════════
# Effect verification — check the claim against EffectAnalyzer
# ═══════════════════════════════════════════════════════════════════

def verify_effect_claim(
    claim: EffectClaim,
    source_a: str,
    source_b: str,
) -> Tuple[EffectVerdict, str]:
    """Verify that the effect claim matches actual function effects.

    Returns (verdict, explanation).
    """
    try:
        from cctt.proof_theory.effect_model import EffectAnalyzer, EffectType
    except ImportError:
        return EffectVerdict.ASSUMED, "EffectAnalyzer not available"

    analyzer = EffectAnalyzer()

    try:
        effect_a = analyzer.analyze_source(source_a)
        effect_b = analyzer.analyze_source(source_b)
    except Exception as e:
        return EffectVerdict.ASSUMED, f"analysis failed: {e}"

    et_a = effect_a.effect_type
    et_b = effect_b.effect_type

    if claim == EffectClaim.BOTH_PURE:
        if et_a.allows_equational and et_b.allows_equational:
            return EffectVerdict.VERIFIED, (
                f"both allow equational reasoning: "
                f"a={et_a.value}, b={et_b.value}"
            )
        return EffectVerdict.REJECTED, (
            f"claim 'both pure' but a={et_a.value}, b={et_b.value}"
        )

    if claim == EffectClaim.BOTH_READ:
        if et_a.severity <= 1 and et_b.severity <= 1:
            return EffectVerdict.VERIFIED, "both read-only"
        return EffectVerdict.REJECTED, (
            f"claim 'both read' but a={et_a.value}, b={et_b.value}"
        )

    if claim in (EffectClaim.A_PURE_B_READ, EffectClaim.A_READ_B_PURE):
        if et_a.allows_equational and et_b.allows_equational:
            return EffectVerdict.VERIFIED, "both allow equational"
        return EffectVerdict.REJECTED, (
            f"incompatible effects: a={et_a.value}, b={et_b.value}"
        )

    return EffectVerdict.ASSUMED, "unknown effect claim"


# ═══════════════════════════════════════════════════════════════════
# Compiler — EquivScript → ProofTerm
#
# The compilation target is always:
#   Ext(var, Cut(h1, ..., Cut(h2, ..., final_proof)))
#
# Where each Cut introduces a lemma that the final_proof can use.
# The Ext wraps everything in functional extensionality.
# ═══════════════════════════════════════════════════════════════════

def compile_equiv_step(
    step: EquivStep,
    var_sorts: Dict[str, str],
) -> Optional[ProofTerm]:
    """Compile one have-step's tactic to a ProofTerm."""
    tactic = step.tactic
    kind = tactic.kind

    if kind == EquivTacticKind.REFL:
        return Refl(term=OVar(step.lhs))

    if kind in (EquivTacticKind.CONTRADICTION,):
        return ExFalso(
            context_formula=f"({step.lhs}) and not ({step.rhs})",
            variables=dict(var_sorts),
        )

    if kind in (EquivTacticKind.OMEGA, EquivTacticKind.Z3):
        fragment = 'QF_LIA' if kind == EquivTacticKind.OMEGA else 'QF_NIA'
        return Z3Discharge(
            formula=f"({step.lhs}) == ({step.rhs})",
            fragment=fragment,
            timeout_ms=5000,
            variables=dict(var_sorts),
        )

    if kind == EquivTacticKind.APPLY:
        # Library axiom — explicitly ASSUMED (trusted, not kernel-verified)
        axiom_name = tactic.args[0] if tactic.args else step.name
        return Assume(
            label=f"axiom:{axiom_name}",
            assumed_lhs=OVar(step.lhs),
            assumed_rhs=OVar(step.rhs),
        )

    if kind == EquivTacticKind.STRUCTURAL:
        return Z3Discharge(
            formula=f"({step.lhs}) == ({step.rhs})",
            fragment='TAUTOLOGY',
            timeout_ms=0,
            variables=dict(var_sorts),
        )

    if kind == EquivTacticKind.FUNEXT:
        # Nested funext — the variable to quantify over
        ext_var = tactic.args[0] if tactic.args else "x"
        # Body is a reflexivity proof (the caller provides the real proof)
        return Ext(
            var=ext_var,
            body_proof=Refl(term=OVar(step.lhs)),
        )

    if kind == EquivTacticKind.NAT_INDUCTION:
        # nat_induction <var> — structural induction on a natural number
        ind_var = tactic.args[0] if tactic.args else "n"
        return NatInduction(
            variable=ind_var,
            base_case=Refl(term=OVar(step.lhs)),
            inductive_step=Assume(
                label=f"ind_step:{step.name}",
                assumed_lhs=OVar(step.lhs),
                assumed_rhs=OVar(step.rhs),
            ),
        )

    if kind == EquivTacticKind.LIST_INDUCTION:
        # list_induction <var> — structural induction on a list
        ind_var = tactic.args[0] if tactic.args else "xs"
        return ListInduction(
            variable=ind_var,
            nil_case=Refl(term=OVar(step.lhs)),
            cons_case=Assume(
                label=f"ind_step:{step.name}",
                assumed_lhs=OVar(step.lhs),
                assumed_rhs=OVar(step.rhs),
            ),
        )

    if kind == EquivTacticKind.CASES:
        # cases <var> — split on variable's value
        case_var = tactic.args[0] if tactic.args else "x"
        return CasesSplit(
            discriminant=OVar(case_var),
            cases={
                "case": Assume(
                    label=f"case:{step.name}",
                    assumed_lhs=OVar(step.lhs),
                    assumed_rhs=OVar(step.rhs),
                ),
            },
        )

    # Default: try as Assume with explicit trust marking
    return Assume(
        label=f"step:{step.name}",
        assumed_lhs=OVar(step.lhs),
        assumed_rhs=OVar(step.rhs),
    )


def _compile_final_tactic(
    tactic: EquivTactic,
    steps: Tuple[EquivStep, ...],
    goal_lhs: str,
    goal_rhs: str,
) -> ProofTerm:
    """Compile the 'exact' step into a ProofTerm.

    The exact step can reference previously introduced lemma names.
    Common patterns:
      exact trans(h1, sym(h2))  — chain h1 with reversed h2
      exact h1                  — direct use of a lemma
      exact refl                — both sides are syntactically equal
    """
    kind = tactic.kind

    if kind == EquivTacticKind.REFL:
        return Refl(term=OVar(goal_lhs))

    if kind == EquivTacticKind.EXACT:
        # Parse the expression: trans(h1, sym(h2)), sym(h1), etc.
        expr = tactic.args[0] if tactic.args else ""
        return _parse_proof_expr(expr, steps, goal_lhs, goal_rhs)

    if kind == EquivTacticKind.TRANS:
        # trans(h1, h2) — chain two lemmas
        if len(tactic.args) >= 2:
            left = _parse_proof_expr(tactic.args[0], steps, goal_lhs, goal_rhs)
            right = _parse_proof_expr(tactic.args[1], steps, goal_lhs, goal_rhs)
            return Trans(left=left, right=right)
        return Refl(term=OVar(goal_lhs))

    if kind == EquivTacticKind.SYM:
        if tactic.args:
            inner = _parse_proof_expr(tactic.args[0], steps, goal_lhs, goal_rhs)
            return Sym(proof=inner)
        return Refl(term=OVar(goal_lhs))

    # Default: assume the goal directly
    return Assume(
        label="final",
        assumed_lhs=OVar(goal_lhs),
        assumed_rhs=OVar(goal_rhs),
    )


def _parse_proof_expr(
    expr: str,
    steps: Tuple[EquivStep, ...],
    goal_lhs: str,
    goal_rhs: str,
) -> ProofTerm:
    """Parse a proof expression like 'trans(h1, sym(h2))'.

    Recursively handles:
      trans(p, q)  → Trans(compile(p), compile(q))
      sym(p)       → Sym(compile(p))
      refl         → Refl
      <name>       → reference to a have-step (becomes Assume)
    """
    expr = expr.strip()

    if expr == 'refl':
        return Refl(term=OVar(goal_lhs))

    # Parse function call: name(args)
    m = re.match(r'(\w+)\s*\((.+)\)$', expr)
    if m:
        func_name = m.group(1).lower()
        args_str = m.group(2)
        args = _split_args(args_str)

        if func_name == 'trans' and len(args) >= 2:
            left = _parse_proof_expr(args[0], steps, goal_lhs, goal_rhs)
            right = _parse_proof_expr(args[1], steps, goal_lhs, goal_rhs)
            return Trans(left=left, right=right)

        if func_name == 'sym' and len(args) >= 1:
            inner = _parse_proof_expr(args[0], steps, goal_lhs, goal_rhs)
            return Sym(proof=inner)

        if func_name == 'cong' and len(args) >= 2:
            func = args[0]
            arg_proofs = tuple(
                _parse_proof_expr(a, steps, goal_lhs, goal_rhs)
                for a in args[1:]
            )
            return Cong(func=func, arg_proofs=arg_proofs)

    # Simple name — reference to a have-step
    return _step_as_proof(expr, steps)


def _step_as_proof(name: str, steps: Tuple[EquivStep, ...]) -> ProofTerm:
    """Look up a have-step by name and return it as an Assume proof."""
    name = name.strip()
    for step in steps:
        if step.name == name:
            return Assume(
                label=f"have:{name}",
                assumed_lhs=OVar(step.lhs),
                assumed_rhs=OVar(step.rhs),
            )
    # Unknown reference — still create an Assume so the checker can reject it
    return Assume(
        label=f"ref:{name}",
        assumed_lhs=OVar(name),
        assumed_rhs=OVar(name),
    )


def _split_args(text: str) -> List[str]:
    """Split comma-separated arguments respecting parentheses."""
    result: List[str] = []
    depth = 0
    current: List[str] = []
    for ch in text:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        elif ch == ',' and depth == 0:
            result.append(''.join(current).strip())
            current = []
            continue
        current.append(ch)
    if current:
        result.append(''.join(current).strip())
    return [a for a in result if a]


def compile_equiv_proof(
    script: EquivScript,
    source_a: str = "",
    source_b: str = "",
) -> Optional[ProofTerm]:
    """Compile an equivalence proof script to a ProofTerm tree.

    The compiled proof is:
        Ext(var, Cut(h1, ..., Cut(h2, ..., final_proof)))

    Where:
    - Ext wraps in functional extensionality (∀ args. f(args) = g(args))
    - Each Cut introduces a lemma (have-step)
    - The final_proof uses the lemmas to establish the goal

    Returns None if compilation fails.
    """
    # 1. Compile the final tactic (innermost proof)
    final = _compile_final_tactic(
        script.final_tactic, script.steps,
        script.goal_lhs, script.goal_rhs,
    )

    # 2. Wrap in Cuts (from innermost to outermost)
    # Each have-step becomes a Cut around the accumulated proof
    body = final
    for step in reversed(script.steps):
        step_proof = compile_equiv_step(step, script.given)
        if step_proof is None:
            log.warning("Could not compile step: %s", step.name)
            continue

        body = Cut(
            lemma_lhs=OVar(step.lhs),
            lemma_rhs=OVar(step.rhs),
            lemma_proof=step_proof,
            main_proof=body,
            label=step.name,
        )

    # 3. Wrap in Ext for each given variable (functional extensionality)
    # This proves ∀ var. f(var) = g(var), hence f = g
    for var_name in reversed(list(script.given.keys())):
        body = Ext(var=var_name, body_proof=body)

    return body


# ═══════════════════════════════════════════════════════════════════
# End-to-end verification — parse, compile, verify
# ═══════════════════════════════════════════════════════════════════

@dataclass
class EquivVerdict:
    """Result of an equivalence proof verification."""
    equivalent: bool
    explanation: str
    trust_level: str = "KERNEL"  # KERNEL | AXIOM_TRUSTED | EFFECT_ASSUMED
    effect_verdict: Optional[EffectVerdict] = None
    proof_depth: int = 0
    n_axioms: int = 0           # number of assumed (unverified) axioms
    axiom_names: Tuple[str, ...] = ()


def verify_equiv_proof(
    script: EquivScript,
    source_a: str,
    source_b: str,
) -> EquivVerdict:
    """Full pipeline: parse + effect check + compile + verify.

    1. Verify effect claim
    2. Compile sources to OTerms
    3. Compile proof script to ProofTerm
    4. Verify proof via check_proof()
    5. Return verdict with trust level
    """
    # 1. Effect verification
    ev, ev_detail = verify_effect_claim(
        script.effect_claim, source_a, source_b,
    )
    if ev == EffectVerdict.REJECTED:
        return EquivVerdict(
            equivalent=False,
            explanation=f"effect claim rejected: {ev_detail}",
            effect_verdict=ev,
        )

    # 2. Compile sources to OTerms
    result_a = compile_to_oterm(source_a)
    result_b = compile_to_oterm(source_b)

    if result_a is None:
        return EquivVerdict(
            equivalent=False,
            explanation=f"could not compile func_a: {script.func_a}",
        )
    if result_b is None:
        return EquivVerdict(
            equivalent=False,
            explanation=f"could not compile func_b: {script.func_b}",
        )

    oterm_a, _ = result_a
    oterm_b, _ = result_b

    # 3. Compile proof script
    proof = compile_equiv_proof(script, source_a, source_b)
    if proof is None:
        return EquivVerdict(
            equivalent=False,
            explanation="proof compilation failed",
        )

    # 4. Verify via kernel
    from cctt.proof_theory.checker import check_proof, ProofContext
    ctx = ProofContext()

    # Add all have-step axioms to context so the checker can use them
    for step in script.steps:
        if step.trust == "axiom":
            ctx = ctx.with_assumption(
                f"axiom:{step.name}",
                OVar(step.lhs),
                OVar(step.rhs),
            )

    vr = check_proof(proof, oterm_a, oterm_b, ctx)

    # 5. Determine trust level
    axiom_steps = [s for s in script.steps if s.trust == "axiom"]
    axiom_names = tuple(
        s.tactic.args[0] if s.tactic.args else s.name
        for s in axiom_steps
    )

    if vr.valid:
        if axiom_steps:
            trust = "AXIOM_TRUSTED"
        elif ev == EffectVerdict.ASSUMED:
            trust = "EFFECT_ASSUMED"
        else:
            trust = "KERNEL"

        return EquivVerdict(
            equivalent=True,
            explanation=f"proof verified: {vr.reason}",
            trust_level=trust,
            effect_verdict=ev,
            proof_depth=vr.proof_depth,
            n_axioms=len(axiom_steps),
            axiom_names=axiom_names,
        )

    return EquivVerdict(
        equivalent=False,
        explanation=f"proof rejected by kernel: {vr.reason}",
        effect_verdict=ev,
    )


# ═══════════════════════════════════════════════════════════════════
# Integration with enhanced_check_equivalence
# ═══════════════════════════════════════════════════════════════════

def try_equiv_proof(
    source_a: str,
    source_b: str,
    proof_text: str,
) -> Optional[Any]:
    """Try an equivalence proof as a strategy in the checker pipeline.

    Returns a Result (from cctt.checker) if the proof verifies,
    or None if it doesn't.  This can be called by
    enhanced_check_equivalence() as a new Strategy 0 before heuristics.
    """
    script = parse_equiv_script(proof_text)
    if script is None:
        return None

    script = EquivScript(
        name=script.name,
        func_a=script.func_a,
        func_b=script.func_b,
        given=script.given,
        effect_claim=script.effect_claim,
        goal_lhs=script.goal_lhs,
        goal_rhs=script.goal_rhs,
        steps=script.steps,
        final_tactic=script.final_tactic,
        source_a=source_a,
        source_b=source_b,
    )

    verdict = verify_equiv_proof(script, source_a, source_b)

    if verdict.equivalent:
        from cctt.checker import Result
        trust_map = {
            "KERNEL": 1.0,
            "AXIOM_TRUSTED": 0.95,
            "EFFECT_ASSUMED": 0.90,
        }
        return Result(
            equivalent=True,
            explanation=(
                f"equivalence proof verified [{verdict.trust_level}]: "
                f"{verdict.explanation}"
            ),
            h0=1, h1=0,
            confidence=trust_map.get(verdict.trust_level, 0.85),
        )

    return None


# ═══════════════════════════════════════════════════════════════════
# LLM prompt renderer — present an equivalence obligation for the LLM
# ═══════════════════════════════════════════════════════════════════

def render_equiv_obligation(
    func_a_name: str,
    func_b_name: str,
    source_a: str,
    source_b: str,
    params: List[str],
    param_sorts: Dict[str, str],
) -> str:
    """Render an equivalence proof obligation for the LLM.

    The LLM should respond with a proof script in the equiv language.
    """
    lines = [
        f"-- Prove that {func_a_name} and {func_b_name} are equivalent.",
        f"-- They compute the same function on all inputs.",
        "",
        f"-- Source of {func_a_name}:",
    ]
    for src_line in source_a.split('\n')[:25]:
        lines.append(f"--   {src_line}")

    lines.append("")
    lines.append(f"-- Source of {func_b_name}:")
    for src_line in source_b.split('\n')[:25]:
        lines.append(f"--   {src_line}")

    lines.append("")
    lines.append("-- Write an equivalence proof:")
    lines.append("")

    # Template
    proof_name = f"{func_a_name}_eq_{func_b_name}"
    args = ", ".join(params) if params else "x"
    lines.append(f"equiv {proof_name}")
    lines.append(f"  func_a: {func_a_name}")
    lines.append(f"  func_b: {func_b_name}")

    if params:
        givens = ", ".join(f"{p} : {param_sorts.get(p, 'Any')}" for p in params)
        lines.append(f"  given {givens}")
    else:
        lines.append(f"  given x : Any")

    lines.append(f"  effects: both pure")
    lines.append(f"  show {func_a_name}({args}) = {func_b_name}({args})")
    lines.append("")
    lines.append(f"  -- Introduce lemmas about each function:")
    lines.append(f"  have h1 : {func_a_name}({args}) = ??? := by ???")
    lines.append(f"  have h2 : {func_b_name}({args}) = ??? := by ???")
    lines.append(f"  exact trans(h1, sym(h2))")
    lines.append("qed")
    lines.append("")
    lines.append("-- Available tactics for 'by':")
    lines.append("--   refl              : both sides syntactically equal")
    lines.append("--   omega             : integer arithmetic (Z3)")
    lines.append("--   z3                : general Z3 solver")
    lines.append("--   structural        : structural tautology")
    lines.append("--   contradiction     : hypotheses contradictory")
    lines.append("--   apply <axiom>     : use a trusted axiom [AXIOM_TRUSTED]")
    lines.append("--   funext <var>      : functional extensionality")
    lines.append("--   induction <var>   : natural number induction")
    lines.append("--   list_induction <v>: list induction (base=[], step=x::xs)")
    lines.append("--   cases <var>       : case split on variable")
    lines.append("--")
    lines.append("-- Available combinators for 'exact':")
    lines.append("--   trans(p, q)       : chain p : a=b with q : b=c → a=c")
    lines.append("--   sym(p)            : reverse p : a=b → b=a")
    lines.append("--   cong(f, p)        : f(a)=f(b) from p : a=b")
    lines.append("--   refl              : a=a")
    lines.append("--   <name>            : reference a have-step by name")

    return "\n".join(lines)
