"""Canonicalisation of Lean-syntax predicate strings.

Used by the cohomology computation to compare cochain values for
*propositional* equality without depending on textual whitespace,
redundant parentheses, or operator-associativity differences.

The audit revealed two cheats in
``deppy/lean/cohomology_compute.py``:

  * ``compute_cohomology`` used Python's ``in`` set-membership on the
    cochain key set rather than comparing the actual predicates;
    the fix needs predicate-equality.
  * ``verify_chain_complex`` returned ``d2_squared_zero=True``
    unconditionally; the fix needs a structural verifier that
    consumes both predicates and checks they encode the same
    proposition.

Public API
----------

::

    canon = canonicalize_predicate(text)
    same  = predicates_equivalent(text1, text2)
    iso   = matches_pattern(text, pattern_template, bindings_out)

``canonicalize_predicate`` returns a deterministic string form;
``predicates_equivalent`` compares two predicates after
canonicalisation; ``matches_pattern`` accepts a template with
``{NAME}`` placeholders and reports the captured bindings.

The canonical form
------------------

The function performs *purely textual* normalisations — it does
not parse the predicate as a Boolean expression because Lean
syntax is not a proper subset of Python:

  1. Whitespace is collapsed to single spaces.
  2. Redundant outer parentheses are removed (``((P))`` → ``P``).
  3. Spacing around binary operators is standardised
     (``→``, ``∧``, ``∨``, ``↔``, ``↑``, ``↓``).
  4. Implication operator variants are normalised (``->`` → ``→``).
  5. Conjunction operator variants are normalised
     (``and`` → ``∧``, ``&&`` → ``∧``).
  6. Disjunction operator variants are normalised
     (``or`` → ``∨``, ``||`` → ``∨``).

Operator-associativity normalisation
------------------------------------

For commutative-and-associative operators (``∧``, ``∨``) we
canonicalise the operand order *only when the operands are simple
atoms* — full normalisation would require parsing.  This is a
documented limitation: ``A ∧ B`` and ``B ∧ A`` will canonicalise
to the same form (the operands are sorted), but
``(A ∧ B) ∧ C`` and ``A ∧ (B ∧ C)`` may not.
"""
from __future__ import annotations

import re


# ─────────────────────────────────────────────────────────────────────
#  Token-level normalisations
# ─────────────────────────────────────────────────────────────────────

# Implication: '->' → '→'
_IMPL_VARIANTS = (
    (r"\s*->\s*", " → "),
    (r"\s*=>\s*", " → "),
    (r"\s*⟹\s*", " → "),
    (r"\s*→\s*", " → "),
)

# Conjunction: 'and', '&&', '/\\' → '∧'
_AND_VARIANTS = (
    (r"\s+and\s+", " ∧ "),
    (r"\s*&&\s*", " ∧ "),
    (r"\s*∧\s*", " ∧ "),
)

# Disjunction: 'or', '||', '\\/' → '∨'
_OR_VARIANTS = (
    (r"\s+or\s+", " ∨ "),
    (r"\s*\|\|\s*", " ∨ "),
    (r"\s*∨\s*", " ∨ "),
)

# Biconditional / iff
_IFF_VARIANTS = (
    (r"\s*<->\s*", " ↔ "),
    (r"\s*<=>\s*", " ↔ "),
    (r"\s*↔\s*", " ↔ "),
)

# Negation
_NOT_VARIANTS = (
    (r"\bnot\s+", "¬ "),
    (r"!\s*(?=\w|\()", "¬ "),
    (r"¬\s*", "¬ "),
)

# Equality / inequality (Python → Lean)
_EQ_VARIANTS = (
    (r"\s*==\s*", " = "),
    (r"\s*!=\s*", " ≠ "),
    (r"\s*<=\s*", " ≤ "),
    (r"\s*>=\s*", " ≥ "),
    (r"\s*≤\s*", " ≤ "),
    (r"\s*≥\s*", " ≥ "),
    (r"\s*≠\s*", " ≠ "),
)

# Operator stripping: remove spaces inside multi-character operators
# is handled by spacing-standardisation below.


# ─────────────────────────────────────────────────────────────────────
#  Public API
# ─────────────────────────────────────────────────────────────────────


def canonicalize_predicate(text: str) -> str:
    """Return a canonical form of ``text`` suitable for equality
    comparison with another canonicalised predicate."""
    if not text:
        return ""
    out = text.strip()
    # 1. Collapse whitespace.
    out = re.sub(r"\s+", " ", out)
    # 2. Normalise operators.
    for pat, repl in _IMPL_VARIANTS:
        out = re.sub(pat, repl, out)
    for pat, repl in _AND_VARIANTS:
        out = re.sub(pat, repl, out)
    for pat, repl in _OR_VARIANTS:
        out = re.sub(pat, repl, out)
    for pat, repl in _IFF_VARIANTS:
        out = re.sub(pat, repl, out)
    for pat, repl in _NOT_VARIANTS:
        out = re.sub(pat, repl, out)
    for pat, repl in _EQ_VARIANTS:
        out = re.sub(pat, repl, out)
    # 3. Strip redundant outer parentheses (only when they wrap the
    #    entire expression).
    out = _strip_outer_parens(out)
    # 4. Normalise commutative-and-associative operators by sorting
    #    operands at the top level.
    out = _normalise_commutative_top_level(out)
    return out.strip()


def predicates_equivalent(p: str, q: str) -> bool:
    """Return True iff ``p`` and ``q`` canonicalise to the same form."""
    return canonicalize_predicate(p) == canonicalize_predicate(q)


def matches_pattern(
    text: str, pattern: str,
    bindings_out: dict[str, str] | None = None,
) -> bool:
    """Match ``text`` against a template ``pattern`` with ``{NAME}``
    placeholders.  When ``bindings_out`` is supplied, captured
    bindings are written to it.

    Example::

        matches_pattern(
            "(safe(f)) → (safe(g))",
            "({P}) → ({Q})",
        )  # → True, bindings={"P": "safe(f)", "Q": "safe(g)"}
    """
    if bindings_out is None:
        bindings_out = {}
    canon_text = canonicalize_predicate(text)
    canon_pat = canonicalize_predicate(pattern)
    # Convert the pattern to a regex by replacing ``{NAME}`` tokens
    # with named groups.
    regex_text = re.escape(canon_pat)
    # Re-introduce regex-special tokens for our placeholders.
    regex_text = re.sub(
        r"\\\{(\w+)\\\}",
        lambda m: r"(?P<" + m.group(1) + r">.+?)",
        regex_text,
    )
    regex = re.compile(r"\A" + regex_text + r"\Z")
    m = regex.match(canon_text)
    if m is None:
        return False
    bindings_out.update(m.groupdict())
    return True


# ─────────────────────────────────────────────────────────────────────
#  Helpers
# ─────────────────────────────────────────────────────────────────────


def _strip_outer_parens(text: str) -> str:
    """Strip redundant outer parens that wrap the whole expression.

    ``"(P → Q)"`` → ``"P → Q"``.
    ``"(P) → (Q)"`` → unchanged (the outer parens don't wrap the
    whole expression — the ``→`` is at depth 0 between them).
    """
    text = text.strip()
    while len(text) >= 2 and text[0] == "(" and text[-1] == ")":
        depth = 0
        wraps_whole = True
        for i, ch in enumerate(text):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i < len(text) - 1:
                    wraps_whole = False
                    break
        if not wraps_whole:
            return text
        text = text[1:-1].strip()
    return text


def _normalise_commutative_top_level(text: str) -> str:
    """Sort top-level operands of commutative-and-associative
    operators (``∧``, ``∨``).  Limitation: only operates on the
    *top-level* split — does not recurse into operands.

    ``"B ∧ A"`` → ``"A ∧ B"``.
    ``"(B) ∧ A"`` → ``"A ∧ (B)"``.
    ``"A ∧ B ∧ C"`` → ``"A ∧ B ∧ C"`` (sorted lexicographically).
    """
    for op in ("∨", "∧"):
        parts = _split_top_level(text, op)
        if len(parts) > 1:
            sorted_parts = sorted(p.strip() for p in parts)
            text = f" {op} ".join(sorted_parts)
    return text


def _split_top_level(text: str, sep: str) -> list[str]:
    """Split ``text`` on ``sep`` at top level (paren-balanced)."""
    parts: list[str] = []
    depth = 0
    i = 0
    start = 0
    sep_len = len(sep)
    while i < len(text):
        ch = text[i]
        if ch == "(":
            depth += 1
            i += 1
        elif ch == ")":
            depth -= 1
            i += 1
        elif depth == 0 and text[i:i + sep_len] == sep:
            parts.append(text[start:i].strip())
            i += sep_len
            start = i
        else:
            i += 1
    parts.append(text[start:].strip())
    return parts


__all__ = [
    "canonicalize_predicate",
    "predicates_equivalent",
    "matches_pattern",
]
