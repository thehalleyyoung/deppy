"""proof_language.py — Lean-like proof language for C4, attached to Python code.

In F*, proofs are not independent theorems — they are refinement type
annotations that the type checker pushes through the code's control flow.
Each branch, return, and assignment generates a proof obligation that is
discharged by the code itself (via Curry-Howard) or by explicit tactics.

This module provides a Lean-like proof language for C4 that follows the
same principle: every proof is ATTACHED to a specific Python function and
its spec.  The proof is structured around the function's code paths —
each path gets its own tactic that explains why the spec holds there.

Proof Script Format
===================

    proof <name> for <func_name>
      given <var> : <sort>, ...
      assuming <hypothesis>, ...
      show <goal>
      on path (<guard>) returning <expr>:
        by <tactic>
      on path (<guard>) returning <expr>:
        by <tactic>
    qed

Where <tactic> is one of:

  TERMINAL TACTICS (close the goal directly):
    contradiction     -- hypotheses are contradictory (maps to ExFalso)
    exfalso           -- same as contradiction
    structural        -- structural tautology from return expression
    omega             -- integer arithmetic (maps to Z3Discharge)
    linarith          -- linear arithmetic (maps to Z3Discharge)
    norm_num          -- numeric normalization (maps to Z3Discharge)
    simp [rules]      -- simplification (ArithmeticSimp / ListSimp)
    list_length       -- list literal length (maps to ListSimp)
    refl              -- reflexivity (maps to Refl)
    assumption        -- goal is one of the hypotheses
    trivial           -- try refl, then simp, then omega
    exact <term>      -- provide direct proof term

  COMPOSITIONAL TACTICS:
    have <name> : <prop> := by <tactic>   -- introduce lemma (Cut)
    apply <theorem>                        -- apply a theorem (LemmaApp)
    unfold <name>                          -- unfold definition (Unfold)
    rw [<rule>, ...]                       -- rewrite (Rewrite)
    cases <var> with | <pat> => <tac> ...  -- case analysis (CasesSplit)

Compilation
===========

Each tactic compiles to a C4 ProofTerm that the C4 compiler verifies
independently.  The proof language is syntactic sugar over C4's proof
term calculus — soundness comes from the compiler, not the parser.

    contradiction  →  ExFalso(context_formula=..., variables=...)
    omega          →  Z3Discharge(formula=..., fragment='QF_LIA')
    structural     →  Z3Discharge(formula=..., fragment='TAUTOLOGY')
    simp           →  ArithmeticSimp / ListSimp
    have ... := by →  Cut(lemma_proof=..., main_proof=...)
    cases ... with →  CasesSplit(cases={...})
"""
from __future__ import annotations

import logging
import re
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any, Dict, List, Optional, Tuple

from cctt.proof_theory.terms import (
    ProofTerm, ExFalso, Z3Discharge, ListSimp,
    ArithmeticSimp, CasesSplit, Rewrite, Cut,
    ProofObligation,
)

log = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════
# Tactic AST — parsed tactics before compilation to C4 ProofTerms
# ═══════════════════════════════════════════════════════════════════

class TacticKind(Enum):
    """The kind of tactic in a proof script."""
    # Terminal tactics
    CONTRADICTION = auto()
    EXFALSO = auto()
    STRUCTURAL = auto()
    OMEGA = auto()
    LINARITH = auto()
    NORM_NUM = auto()
    SIMP = auto()
    LIST_LENGTH = auto()
    REFL = auto()
    ASSUMPTION = auto()
    TRIVIAL = auto()
    EXACT = auto()
    # Compositional
    HAVE = auto()
    APPLY = auto()
    UNFOLD = auto()
    RW = auto()
    CASES = auto()


@dataclass(frozen=True)
class Tactic:
    """A single tactic in a proof script."""
    kind: TacticKind
    args: Tuple[str, ...] = ()  # tactic arguments
    comment: str = ""           # inline comment (-- ...)

    def pretty(self) -> str:
        name = self.kind.name.lower()
        if self.args:
            return f"{name} {' '.join(self.args)}"
        return name


@dataclass(frozen=True)
class PathProof:
    """Proof for a specific code path, attached to the function."""
    guard: str          # the path condition (from code's control flow)
    return_expr: str    # what the function returns on this path
    tactic: Tactic      # the tactic that proves the spec on this path
    comment: str = ""   # optional explanation


@dataclass(frozen=True)
class ProofScript:
    """A complete proof script attached to a Python function.

    This is the F*-style connection: the proof is about a specific
    function, references its actual variables and code paths, and
    proves its spec at each return point.
    """
    name: str                      # proof name
    func_name: str                 # function being proved
    given: Dict[str, str]          # variable declarations (name → sort)
    assuming: Tuple[str, ...]      # hypotheses (from spec requires + fiber guard)
    goal: str                      # what we're proving (the spec clause)
    path_proofs: Tuple[PathProof, ...]  # per-path proofs
    source: str = ""               # source code of the function

    def pretty(self) -> str:
        """Render the proof script in Lean-like syntax."""
        lines = [f"proof {self.name} for {self.func_name}"]
        if self.given:
            givens = ", ".join(f"{v} : {s}" for v, s in self.given.items())
            lines.append(f"  given {givens}")
        if self.assuming:
            lines.append(f"  assuming {', '.join(self.assuming)}")
        lines.append(f"  show {self.goal}")
        for pp in self.path_proofs:
            lines.append(f"  on path ({pp.guard}) returning {pp.return_expr}:")
            comment = f"  -- {pp.comment}" if pp.comment else ""
            lines.append(f"    by {pp.tactic.pretty()}{comment}")
        lines.append("qed")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Parser — proof script text → ProofScript
# ═══════════════════════════════════════════════════════════════════

# Tactic name → TacticKind mapping
_TACTIC_NAMES: Dict[str, TacticKind] = {
    'contradiction': TacticKind.CONTRADICTION,
    'exfalso': TacticKind.EXFALSO,
    'structural': TacticKind.STRUCTURAL,
    'omega': TacticKind.OMEGA,
    'linarith': TacticKind.LINARITH,
    'norm_num': TacticKind.NORM_NUM,
    'simp': TacticKind.SIMP,
    'list_length': TacticKind.LIST_LENGTH,
    'refl': TacticKind.REFL,
    'assumption': TacticKind.ASSUMPTION,
    'trivial': TacticKind.TRIVIAL,
    'exact': TacticKind.EXACT,
    'have': TacticKind.HAVE,
    'apply': TacticKind.APPLY,
    'unfold': TacticKind.UNFOLD,
    'rw': TacticKind.RW,
    'cases': TacticKind.CASES,
}


def parse_tactic(text: str) -> Optional[Tactic]:
    """Parse a single tactic from text.

    Examples:
        "contradiction"          → Tactic(CONTRADICTION)
        "omega"                  → Tactic(OMEGA)
        "simp [list_length]"     → Tactic(SIMP, args=("list_length",))
        "apply sorted_preserves" → Tactic(APPLY, args=("sorted_preserves",))
    """
    text = text.strip()
    if not text:
        return None

    # Strip inline comment
    comment = ""
    if "--" in text:
        idx = text.index("--")
        comment = text[idx + 2:].strip()
        text = text[:idx].strip()

    # Split into tactic name and arguments
    parts = text.split(None, 1)
    tactic_name = parts[0].lower()
    rest = parts[1] if len(parts) > 1 else ""

    kind = _TACTIC_NAMES.get(tactic_name)
    if kind is None:
        return None

    # Parse arguments based on tactic kind
    args: Tuple[str, ...] = ()
    if kind in (TacticKind.SIMP, TacticKind.RW):
        # Parse bracketed rule list: simp [rule1, rule2]
        m = re.match(r'\[(.*)\]', rest.strip())
        if m:
            rules = [r.strip() for r in m.group(1).split(',') if r.strip()]
            args = tuple(rules)
    elif kind in (TacticKind.APPLY, TacticKind.UNFOLD, TacticKind.EXACT):
        if rest.strip():
            args = (rest.strip(),)

    return Tactic(kind=kind, args=args, comment=comment)


def parse_proof_script(text: str) -> Optional[ProofScript]:
    """Parse a complete proof script from text.

    Expects the format:
        proof <name> for <func_name>
          given <var> : <sort>, ...
          assuming <hyp>, ...
          show <goal>
          on path (<guard>) returning <expr>:
            by <tactic>
        qed
    """
    lines = [l.rstrip() for l in text.strip().split('\n')]
    # Strip comment-only lines and blank lines
    lines = [l for l in lines if l.strip() and not l.strip().startswith('--')]

    if not lines:
        return None

    # Parse header: proof <name> for <func_name>
    header = lines[0].strip()
    m = re.match(r'proof\s+(\w+)\s+for\s+(\w+)', header)
    if not m:
        return None
    proof_name, func_name = m.group(1), m.group(2)

    given: Dict[str, str] = {}
    assuming: List[str] = []
    goal = ""
    path_proofs: List[PathProof] = []

    i = 1
    while i < len(lines):
        line = lines[i].strip()

        if line.startswith('given '):
            # Parse: given x : Int, y : Int
            decls = line[5:].split(',')
            for decl in decls:
                decl = decl.strip()
                if ':' in decl:
                    var, sort = decl.split(':', 1)
                    given[var.strip()] = sort.strip()
            i += 1

        elif line.startswith('assuming '):
            # Parse: assuming x == 3, y % 2 == 0
            hyps_text = line[9:]
            # Split on commas, but respect parenthesized expressions
            assuming = _split_hypotheses(hyps_text)
            i += 1

        elif line.startswith('show '):
            goal = line[5:].strip()
            i += 1

        elif line.startswith('on path'):
            # Parse: on path (<guard>) returning <expr>:
            m = re.match(
                r'on\s+path\s+\((.+?)\)\s+returning\s+(.+?)\s*:',
                line,
            )
            if not m:
                # Try without "returning" for conciseness
                m = re.match(r'on\s+path\s+\((.+?)\)\s*:', line)
                if m:
                    guard = m.group(1).strip()
                    return_expr = ""
                else:
                    i += 1
                    continue
            else:
                guard = m.group(1).strip()
                return_expr = m.group(2).strip()

            # Next line should be "by <tactic>"
            i += 1
            if i < len(lines):
                tactic_line = lines[i].strip()
                if tactic_line.startswith('by '):
                    tactic = parse_tactic(tactic_line[3:])
                    if tactic:
                        comment = tactic.comment
                        path_proofs.append(PathProof(
                            guard=guard,
                            return_expr=return_expr,
                            tactic=tactic,
                            comment=comment,
                        ))
            i += 1

        elif line == 'qed':
            break
        else:
            i += 1

    if not goal:
        return None

    return ProofScript(
        name=proof_name,
        func_name=func_name,
        given=given,
        assuming=tuple(assuming),
        goal=goal,
        path_proofs=tuple(path_proofs),
    )


def _split_hypotheses(text: str) -> List[str]:
    """Split comma-separated hypotheses, respecting parentheses."""
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
    return [h for h in result if h]


# ═══════════════════════════════════════════════════════════════════
# Compiler — Tactic → C4 ProofTerm
#
# Each tactic compiles to a ProofTerm that the C4 compiler verifies
# independently.  Soundness comes from the compiler, not the parser.
# ═══════════════════════════════════════════════════════════════════

def compile_tactic(
    tactic: Tactic,
    hypotheses: Tuple[str, ...],
    goal: str,
    return_expr: str,
    var_sorts: Dict[str, str],
    func_name: str = "",
) -> Optional[ProofTerm]:
    """Compile a single tactic to a C4 ProofTerm.

    The compiled proof term is then verified by the C4 compiler.
    The tactic is syntactic sugar — the proof term is the real proof.
    """
    kind = tactic.kind

    # ── contradiction / exfalso ─────────────────────────────────
    if kind in (TacticKind.CONTRADICTION, TacticKind.EXFALSO):
        context = " and ".join(f"({h})" for h in hypotheses)
        return ExFalso(
            context_formula=context,
            variables=dict(var_sorts),
            absurdity=tactic.comment or f"contradiction in {func_name}",
        )

    # ── omega / linarith / norm_num → Z3Discharge ──────────────
    if kind in (TacticKind.OMEGA, TacticKind.LINARITH, TacticKind.NORM_NUM):
        fragment_map = {
            TacticKind.OMEGA: 'QF_LIA',
            TacticKind.LINARITH: 'QF_LRA',
            TacticKind.NORM_NUM: 'QF_NIA',
        }
        if hypotheses:
            hyps_conj = " and ".join(f"({h})" for h in hypotheses)
            formula = f"not ({hyps_conj}) or ({goal})"
        else:
            formula = goal
        return Z3Discharge(
            formula=formula,
            fragment=fragment_map[kind],
            timeout_ms=5000,
            variables=dict(var_sorts),
        )

    # ── structural → Z3Discharge(TAUTOLOGY) ────────────────────
    if kind == TacticKind.STRUCTURAL:
        return Z3Discharge(
            formula=goal,
            fragment='TAUTOLOGY',
            timeout_ms=0,
            variables=dict(var_sorts),
        )

    # ── list_length → ListSimp ─────────────────────────────────
    if kind == TacticKind.LIST_LENGTH:
        return ListSimp(
            rule='list_literal_length',
            target=goal,
        )

    # ── simp → ArithmeticSimp or ListSimp ──────────────────────
    if kind == TacticKind.SIMP:
        rules = tactic.args
        if any('list' in r for r in rules):
            return ListSimp(
                rule=','.join(rules) if rules else 'simp',
                target=goal,
            )
        return ArithmeticSimp(
            rule=','.join(rules) if rules else 'simp',
            target=goal,
        )

    # ── refl → Z3Discharge with reflexivity ────────────────────
    if kind == TacticKind.REFL:
        return Z3Discharge(
            formula=goal,
            fragment='REFL',
            timeout_ms=0,
            variables=dict(var_sorts),
        )

    # ── assumption → Z3Discharge (goal is a hypothesis) ────────
    if kind == TacticKind.ASSUMPTION:
        if hypotheses:
            hyps_conj = " and ".join(f"({h})" for h in hypotheses)
            formula = f"not ({hyps_conj}) or ({goal})"
        else:
            formula = goal
        return Z3Discharge(
            formula=formula,
            fragment='QF_LIA',
            timeout_ms=5000,
            variables=dict(var_sorts),
        )

    # ── trivial → try refl then omega ──────────────────────────
    if kind == TacticKind.TRIVIAL:
        # Try as Z3Discharge — covers refl, simp, omega
        if hypotheses:
            hyps_conj = " and ".join(f"({h})" for h in hypotheses)
            formula = f"not ({hyps_conj}) or ({goal})"
        else:
            formula = goal
        return Z3Discharge(
            formula=formula,
            fragment='QF_LIA',
            timeout_ms=5000,
            variables=dict(var_sorts),
        )

    # ── apply → library axiom lookup ───────────────────────────
    if kind == TacticKind.APPLY:
        theorem_name = tactic.args[0] if tactic.args else ""
        from cctt.proof_theory.library_axioms import LibraryAxiom
        return LibraryAxiom(
            library=func_name,
            axiom_name=theorem_name,
            statement=goal,
        )

    # ── rw → Rewrite ──────────────────────────────────────────
    if kind == TacticKind.RW:
        from cctt.denotation import OVar
        rules = tactic.args
        return Rewrite(
            rule_name=rules[0] if rules else 'rw',
            lhs=OVar(goal),
            rhs=OVar(goal),
        )

    log.debug("Cannot compile tactic: %s", tactic.kind)
    return None


def compile_proof_script(
    script: ProofScript,
) -> Dict[str, ProofTerm]:
    """Compile a full proof script to per-path C4 ProofTerms.

    Returns a dict: path_guard → ProofTerm.
    Each ProofTerm is independently verifiable by the C4 compiler.
    """
    result: Dict[str, ProofTerm] = {}

    for pp in script.path_proofs:
        # Build hypotheses for this path: assuming + path guard
        hyps = list(script.assuming)
        if pp.guard != "True":
            hyps.append(pp.guard)

        proof = compile_tactic(
            tactic=pp.tactic,
            hypotheses=tuple(hyps),
            goal=script.goal,
            return_expr=pp.return_expr,
            var_sorts=script.given,
            func_name=script.func_name,
        )
        if proof is not None:
            result[pp.guard] = proof

    return result


# ═══════════════════════════════════════════════════════════════════
# Proof obligation renderer — presents obligations for the LLM
#
# The LLM writes proof scripts in the language above.  This function
# renders the obligation in a format the LLM can understand and
# respond to with a valid proof script.
# ═══════════════════════════════════════════════════════════════════

def render_proof_obligation(
    func_name: str,
    params: List[str],
    param_sorts: Dict[str, str],
    clause: str,
    requires: List[str],
    paths: List[Any],  # List[ReturnPath]
    source: str = "",
) -> str:
    """Render a proof obligation for the LLM to prove.

    The LLM should respond with a proof script in the language above.
    The proof is ATTACHED to the function — it references actual
    variables, code paths, and return expressions.
    """
    lines = [
        f"-- Prove that {func_name} satisfies: {clause}",
        f"-- Source code:",
    ]
    for src_line in (source or "").split('\n')[:30]:
        lines.append(f"--   {src_line}")

    lines.append("")
    lines.append("-- Write a proof in C4 proof language:")
    lines.append("")

    # Start the proof template
    proof_name = f"{func_name}_{_sanitize(clause)}"
    lines.append(f"proof {proof_name} for {func_name}")

    # Given
    if params:
        givens = ", ".join(f"{p} : {param_sorts.get(p, 'Int')}" for p in params)
        lines.append(f"  given {givens}")

    # Assuming
    if requires:
        lines.append(f"  assuming {', '.join(requires)}")

    # Show
    lines.append(f"  show {clause}")

    # List the paths that need proofs
    for path in paths:
        if hasattr(path, 'is_exception') and path.is_exception:
            continue
        guard = getattr(path, 'guard', 'True')
        ret = getattr(path, 'return_expr', '?')
        lines.append(f"  on path ({guard}) returning {ret}:")
        lines.append(f"    by ???  -- fill in: contradiction | structural | omega | simp | ...")

    lines.append("qed")
    lines.append("")
    lines.append("-- Available tactics:")
    lines.append("--   contradiction  : hypotheses are contradictory")
    lines.append("--   structural     : return expression structurally satisfies goal")
    lines.append("--   omega          : integer arithmetic proof")
    lines.append("--   linarith       : linear arithmetic proof")
    lines.append("--   simp [rules]   : simplification with rules")
    lines.append("--   list_length    : list literal has known length")
    lines.append("--   refl           : goal is reflexively true")
    lines.append("--   assumption     : goal is one of the hypotheses")
    lines.append("--   apply <thm>    : apply a known theorem")

    return "\n".join(lines)


def _sanitize(s: str) -> str:
    """Sanitize a string for use as an identifier."""
    return re.sub(r'[^a-zA-Z0-9_]', '_', s)[:30]


# ═══════════════════════════════════════════════════════════════════
# Verification — compile + verify a proof script through C4
# ═══════════════════════════════════════════════════════════════════

def verify_proof_script(
    script: ProofScript,
) -> Dict[str, Tuple[bool, str]]:
    """Compile and verify a proof script through the C4 compiler.

    Returns a dict: path_guard → (valid, detail).
    Each path proof is compiled to a ProofTerm and verified independently.
    """
    compiled = compile_proof_script(script)
    results: Dict[str, Tuple[bool, str]] = {}

    for guard, proof_term in compiled.items():
        try:
            from cctt.proof_theory.c4_compiler import compile_proof, Z3Env
            from cctt.denotation import OVar

            env = Z3Env()
            for var_name, var_sort in script.given.items():
                env.declare_var(var_name, var_sort)

            verdict = compile_proof(
                proof_term, OVar('_lhs'), OVar('_rhs'), env, depth=0,
            )
            results[guard] = (
                verdict.valid,
                f"C4 verified: {type(proof_term).__name__}" if verdict.valid
                else f"C4 rejected: {verdict.errors}",
            )
        except Exception as e:
            results[guard] = (False, f"compilation error: {e}")

    return results

