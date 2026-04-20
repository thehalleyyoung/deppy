"""
SynHoPy ProofTerm → Lean 4 proof translator.

Translates the proof term hierarchy from ``synhopy.core.kernel`` into
Lean 4 proof expressions or tactic scripts.  Uses duck-typing (dispatching
on ``type(pt).__name__``) so the kernel module need not be imported directly.

Public API
----------
    translate_proof(pt)           → str
    full_translate(pt)            → ProofTranslationResult
    classify_z3_formula(formula)  → str
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any


# ═══════════════════════════════════════════════════════════════════
# Result container
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ProofTranslationResult:
    """Result of translating a SynHoPy ProofTerm to Lean 4."""
    lean_proof: str                         # The Lean proof term/tactic
    trust_level: str = "LEAN_PROVABLE"      # LEAN_PROVABLE | LEAN_SORRY | LEAN_AXIOM
    untranslatable: list[str] = field(default_factory=list)
    comments: list[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════
# Z3 formula classifier
# ═══════════════════════════════════════════════════════════════════

_LINEAR_ARITH_RE = re.compile(
    r"^[\s\d\w+\-*/<>=!(),.]+$"
)

_BOOLEAN_OPS = {"and", "or", "not", "implies", "=>", "&&", "||", "!"}
_QUANTIFIER_OPS = {"forall", "exists", "∀", "∃"}


def classify_z3_formula(formula: str) -> str:
    """Pick the best Lean tactic for a Z3-verified formula.

    Returns one of: ``"omega"``, ``"decide"``, ``"rfl"``,
    ``"tauto"``, ``"simp"``, or ``"sorry"``.
    """
    stripped = formula.strip()
    if not stripped:
        return "sorry"

    tokens = set(re.findall(r"[a-zA-Z_]\w*|[+\-*/<>=!&|]+", stripped))

    # Simple reflexive equality  (e.g. "x == x", "0 == 0")
    if "==" in stripped or "= " in stripped:
        parts = re.split(r"==|(?<!=)=(?!=)", stripped)
        if len(parts) == 2 and parts[0].strip() == parts[1].strip():
            return "rfl"

    # Quantifiers → simp
    if tokens & _QUANTIFIER_OPS:
        return "simp"

    # Boolean / propositional connectives → tauto
    if tokens & _BOOLEAN_OPS:
        return "tauto"

    # Linear arithmetic: only integers, variables, +, -, *, comparisons
    # Reject if there are function calls (identifier followed by '(') or
    # dotted names (identifier.identifier) — those are too complex for omega.
    if re.search(r"[a-zA-Z_]\w*\s*\(", stripped):
        return "sorry"
    if re.search(r"[a-zA-Z_]\w*\.[a-zA-Z_]", stripped):
        return "sorry"
    ops_only = re.sub(r"[a-zA-Z_]\w*", "", stripped)
    if re.match(r"^[\s\d+\-*/<>=!(),.%]+$", ops_only):
        return "omega"

    # Fallback
    return "sorry"


# ═══════════════════════════════════════════════════════════════════
# Term / type rendering helpers
# ═══════════════════════════════════════════════════════════════════

def _render_term(t: Any) -> str:
    """Best-effort render of a SynTerm / SynType to a Lean-ish string."""
    if t is None:
        return "_"
    if isinstance(t, str):
        return t
    name = type(t).__name__
    if name == "Var":
        return getattr(t, "name", repr(t))
    if name == "Literal":
        v = getattr(t, "value", None)
        return repr(v) if v is not None else "_"
    return repr(t)


def _render_type(t: Any) -> str:
    """Best-effort render of a SynType to a Lean type string."""
    if t is None:
        return "_"
    if isinstance(t, str):
        return t
    return repr(t)


# ═══════════════════════════════════════════════════════════════════
# Core translator
# ═══════════════════════════════════════════════════════════════════

class _TranslationState:
    """Accumulates metadata during recursive translation."""

    def __init__(self) -> None:
        self.sorry_count: int = 0
        self.untranslatable: list[str] = []
        self.comments: list[str] = []
        self.uses_axiom: bool = False


def _translate(pt: Any, state: _TranslationState) -> str:
    """Recursive workhorse — dispatches on ``type(pt).__name__``."""
    name = type(pt).__name__

    # ── Refl ────────────────────────────────────────────────────
    if name == "Refl":
        return "rfl"

    # ── Sym ─────────────────────────────────────────────────────
    if name == "Sym":
        inner = _translate(getattr(pt, "proof"), state)
        return f"Eq.symm ({inner})"

    # ── Trans ───────────────────────────────────────────────────
    if name == "Trans":
        left = _translate(getattr(pt, "left"), state)
        right = _translate(getattr(pt, "right"), state)
        return f"Eq.trans ({left}) ({right})"

    # ── Cong ────────────────────────────────────────────────────
    if name == "Cong":
        func = _render_term(getattr(pt, "func"))
        inner = _translate(getattr(pt, "proof"), state)
        return f"congrArg {func} ({inner})"

    # ── TransportProof ──────────────────────────────────────────
    if name == "TransportProof":
        path = _translate(getattr(pt, "path_proof"), state)
        base = _translate(getattr(pt, "base_proof"), state)
        return f"{path} ▸ {base}"

    # ── Ext (legacy funext) ─────────────────────────────────────
    if name == "Ext":
        var = getattr(pt, "var", "x")
        body = _translate(getattr(pt, "body_proof"), state)
        return f"funext fun {var} => {body}"

    # ── FunExt ──────────────────────────────────────────────────
    if name == "FunExt":
        var = getattr(pt, "var", "x")
        body = _translate(getattr(pt, "pointwise_proof"), state)
        return f"funext fun {var} => {body}"

    # ── Cut (have) ──────────────────────────────────────────────
    if name == "Cut":
        hyp_name = getattr(pt, "hyp_name", "h")
        hyp_type = _render_type(getattr(pt, "hyp_type", None))
        lemma = _translate(getattr(pt, "lemma_proof"), state)
        body = _translate(getattr(pt, "body_proof"), state)
        return f"have {hyp_name} : {hyp_type} := {lemma}\n{body}"

    # ── Assume ──────────────────────────────────────────────────
    if name == "Assume":
        return getattr(pt, "name", "h")

    # ── Z3Proof ─────────────────────────────────────────────────
    if name == "Z3Proof":
        formula = getattr(pt, "formula", "")
        tactic = classify_z3_formula(formula)
        if tactic == "sorry":
            state.sorry_count += 1
            state.comments.append(f"Z3-verified but no Lean analog: {formula}")
            return f"by sorry /- Z3 verified: {formula} -/"
        return f"by {tactic}"

    # ── NatInduction ────────────────────────────────────────────
    if name == "NatInduction":
        var = getattr(pt, "var", "n")
        base = _translate(getattr(pt, "base_proof"), state)
        step = _translate(getattr(pt, "step_proof"), state)
        return (
            f"by induction {var} with\n"
            f"  | zero => exact {base}\n"
            f"  | succ n ih => exact {step}"
        )

    # ── ListInduction ───────────────────────────────────────────
    if name == "ListInduction":
        var = getattr(pt, "var", "xs")
        nil = _translate(getattr(pt, "nil_proof"), state)
        cons = _translate(getattr(pt, "cons_proof"), state)
        return (
            f"by induction {var} with\n"
            f"  | nil => exact {nil}\n"
            f"  | cons x xs ih => exact {cons}"
        )

    # ── Cases ───────────────────────────────────────────────────
    if name == "Cases":
        scrutinee = _render_term(getattr(pt, "scrutinee"))
        branches = getattr(pt, "branches", [])
        lines = [f"by cases {scrutinee} with"]
        for pattern, proof in branches:
            p = _translate(proof, state)
            lines.append(f"  | {pattern} => exact {p}")
        return "\n".join(lines)

    # ── PathComp ────────────────────────────────────────────────
    if name == "PathComp":
        left = _translate(getattr(pt, "left_path"), state)
        right = _translate(getattr(pt, "right_path"), state)
        return f"Eq.trans ({left}) ({right})"

    # ── Ap ──────────────────────────────────────────────────────
    if name == "Ap":
        func = _render_term(getattr(pt, "function"))
        inner = _translate(getattr(pt, "path_proof"), state)
        return f"congrArg {func} ({inner})"

    # ── Rewrite ─────────────────────────────────────────────────
    if name == "Rewrite":
        lemma_pt = getattr(pt, "lemma")
        lemma_str = _translate(lemma_pt, state)
        proof_pt = getattr(pt, "proof", None)
        if proof_pt is not None:
            inner = _translate(proof_pt, state)
            return f"by rw [{lemma_str}]; exact {inner}"
        return f"by rw [{lemma_str}]"

    # ── Unfold ──────────────────────────────────────────────────
    if name == "Unfold":
        fname = getattr(pt, "func_name", "f")
        proof_pt = getattr(pt, "proof", None)
        if proof_pt is not None:
            inner = _translate(proof_pt, state)
            return f"by unfold {fname}; exact {inner}"
        return f"by unfold {fname}"

    # ── Structural ──────────────────────────────────────────────
    if name == "Structural":
        desc = getattr(pt, "description", "")
        if desc:
            return f"by trivial /- {desc} -/"
        return "by trivial"

    # ── AxiomInvocation ─────────────────────────────────────────
    if name == "AxiomInvocation":
        ax_name = getattr(pt, "name", "axiom")
        module = getattr(pt, "module", "")
        state.uses_axiom = True
        state.comments.append(f"Axiom: {ax_name} from {module}")
        if module:
            return f"{ax_name} /- from {module} -/"
        return ax_name

    # ── DuckPath — sorry with explanation ───────────────────────
    if name == "DuckPath":
        type_a = _render_term(getattr(pt, "type_a", None))
        type_b = _render_term(getattr(pt, "type_b", None))
        msg = f"Duck-typing path: {type_a} ≈ {type_b} via method-wise equivalence"
        state.sorry_count += 1
        state.untranslatable.append(f"DuckPath({type_a}, {type_b})")
        state.comments.append(msg)
        return f"sorry /- {msg} -/"

    # ── CechGlue — sorry with explanation ───────────────────────
    if name == "CechGlue":
        patches = getattr(pt, "patches", [])
        n = len(patches)
        msg = f"Čech gluing of {n} patches (homotopy-specific, no direct Lean analog)"
        state.sorry_count += 1
        state.untranslatable.append(f"CechGlue({n} patches)")
        state.comments.append(msg)
        return f"sorry /- {msg} -/"

    # ── Univalence — sorry with explanation ─────────────────────
    if name == "Univalence":
        ft = _render_type(getattr(pt, "from_type", None))
        tt = _render_type(getattr(pt, "to_type", None))
        msg = f"Univalence: {ft} ≃ {tt} (requires cubical/HoTT library)"
        state.sorry_count += 1
        state.untranslatable.append(f"Univalence({ft}, {tt})")
        state.comments.append(msg)
        return f"sorry /- {msg} -/"

    # ── EffectWitness — sorry with explanation ──────────────────
    if name == "EffectWitness":
        effect = getattr(pt, "effect", "")
        msg = f"Effect witness for '{effect}' (no direct Lean analog)"
        state.sorry_count += 1
        state.untranslatable.append(f"EffectWitness({effect})")
        state.comments.append(msg)
        return f"sorry /- {msg} -/"

    # ── Patch — sorry with explanation ──────────────────────────
    if name == "Patch":
        cls_t = _render_term(getattr(pt, "cls", None))
        method = getattr(pt, "method_name", "")
        msg = f"Monkey-patch proof: {cls_t}.{method} (no direct Lean analog)"
        state.sorry_count += 1
        state.untranslatable.append(f"Patch({cls_t}.{method})")
        state.comments.append(msg)
        return f"sorry /- {msg} -/"

    # ── Fiber — sorry with explanation ──────────────────────────
    if name == "Fiber":
        scrutinee = _render_term(getattr(pt, "scrutinee", None))
        branches = getattr(pt, "type_branches", [])
        n = len(branches)
        msg = f"Fiber analysis on {scrutinee} with {n} branches (no direct Lean analog)"
        state.sorry_count += 1
        state.untranslatable.append(f"Fiber({scrutinee})")
        state.comments.append(msg)
        return f"sorry /- {msg} -/"

    # ── Fallback ────────────────────────────────────────────────
    state.sorry_count += 1
    state.untranslatable.append(f"Unknown proof term: {name}")
    state.comments.append(f"No translation for proof term type: {name}")
    return f"sorry /- untranslated: {name} -/"


# ═══════════════════════════════════════════════════════════════════
# Public API
# ═══════════════════════════════════════════════════════════════════

def translate_proof(pt: Any) -> str:
    """Translate a SynHoPy ProofTerm to a Lean 4 proof string."""
    state = _TranslationState()
    return _translate(pt, state)


def full_translate(pt: Any) -> ProofTranslationResult:
    """Translate a ProofTerm and return full metadata."""
    state = _TranslationState()
    lean_proof = _translate(pt, state)

    if state.uses_axiom and state.sorry_count == 0:
        trust = "LEAN_AXIOM"
    elif state.sorry_count > 0:
        trust = "LEAN_SORRY"
    else:
        trust = "LEAN_PROVABLE"

    return ProofTranslationResult(
        lean_proof=lean_proof,
        trust_level=trust,
        untranslatable=state.untranslatable,
        comments=state.comments,
    )
