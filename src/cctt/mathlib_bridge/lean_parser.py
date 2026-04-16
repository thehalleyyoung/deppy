"""
Lean 4 recursive-descent parser for the Mathlib → CCTT axiom conversion pipeline.

This module provides a comprehensive parser for Lean 4 surface syntax, producing
a typed AST that downstream stages (``mathlib_bridge``) convert into CCTT axioms.

Key design decisions:
  * Hand-written recursive descent — no parser generator dependency.
  * Unicode-aware tokeniser that handles Lean's mathematical operators.
  * Nested ``/- … -/`` block comments and ``/-- … -/`` doc-comments.
  * Tactic blocks parsed shallowly (the CCTT bridge only needs structure,
    not full tactic semantics).
  * Robust error messages with source positions.

Public API
----------
    parse_lean_file(source)  → LeanFile
    parse_lean_decl(source)  → LeanDecl
    parse_lean_expr(source)  → LeanExpr
    LeanParser               — stateful parser class

Typical usage::

    from new_src.cctt.mathlib_bridge.lean_parser import parse_lean_file
    lf = parse_lean_file(open("Mathlib/Data/List/Basic.lean").read())
    for d in lf.declarations:
        print(d.kind, d.name)
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field
from typing import Optional, Union, List


# ---------------------------------------------------------------------------
# AST nodes
# ---------------------------------------------------------------------------

@dataclass
class LeanExpr:
    """Base for all Lean expressions."""
    pass


@dataclass
class LeanVar(LeanExpr):
    name: str


@dataclass
class LeanApp(LeanExpr):
    fn: LeanExpr
    args: list  # list[LeanExpr]


@dataclass
class LeanLam(LeanExpr):
    params: list  # list[LeanParam]
    body: LeanExpr


@dataclass
class LeanPi(LeanExpr):
    params: list  # list[LeanParam]
    codomain: LeanExpr


@dataclass
class LeanMatch(LeanExpr):
    scrutinees: list  # list[LeanExpr]
    arms: list  # list[MatchArm]


@dataclass
class LeanLet(LeanExpr):
    name: str
    type_: Optional[LeanExpr]
    value: LeanExpr
    body: LeanExpr


@dataclass
class LeanLit(LeanExpr):
    value: Union[int, float, str, bool]


@dataclass
class LeanSort(LeanExpr):
    level: int  # 0=Prop, 1=Type, 2=Type 1, ...


@dataclass
class LeanProj(LeanExpr):
    expr: LeanExpr
    field: str


@dataclass
class LeanIf(LeanExpr):
    cond: LeanExpr
    then_: LeanExpr
    else_: LeanExpr


@dataclass
class LeanTactic(LeanExpr):
    tactic_name: str
    args: list  # list[LeanExpr]


@dataclass
class LeanTacticBlock(LeanExpr):
    tactics: list  # list[LeanTactic]


@dataclass
class LeanAnonymousCtor(LeanExpr):
    args: list  # list[LeanExpr]


@dataclass
class LeanDo(LeanExpr):
    stmts: list  # list[LeanExpr]


@dataclass
class LeanHole(LeanExpr):
    pass


@dataclass
class LeanSorry(LeanExpr):
    pass


@dataclass
class MatchArm:
    patterns: list  # list[LeanExpr]
    rhs: LeanExpr


@dataclass
class LeanParam:
    name: str
    type_: Optional[LeanExpr]
    binder: str  # "explicit", "implicit", "instance", "strict_implicit"
    default: Optional[LeanExpr] = None


@dataclass
class LeanDecl:
    kind: str  # "theorem", "def", "lemma", "instance", "class", "structure",
    #             "inductive", "abbrev", "axiom", "example"
    name: str
    universe_params: list  # list[str]
    params: list  # list[LeanParam]
    return_type: Optional[LeanExpr]
    body: Optional[LeanExpr]
    attributes: list  # list[str]
    docstring: Optional[str]
    namespace: str


@dataclass
class LeanInductiveCtor:
    name: str
    type_: Optional[LeanExpr]


@dataclass
class LeanFile:
    imports: list  # list[str]
    opens: list  # list[str]
    namespace: Optional[str]
    declarations: list  # list[LeanDecl]
    variables: list  # list[LeanParam]
    sections: list  # list[str]


# ---------------------------------------------------------------------------
# Token
# ---------------------------------------------------------------------------

@dataclass
class Token:
    kind: str
    value: str
    pos: int  # byte offset into original source


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

KEYWORDS: set[str] = {
    "theorem", "lemma", "def", "noncomputable", "instance", "class",
    "structure", "inductive", "abbrev", "axiom", "where", "let", "in",
    "fun", "λ", "match", "with", "if", "then", "else", "do", "return",
    "for", "while", "by", "have", "show", "suffices", "calc", "example",
    "namespace", "open", "section", "end", "variable", "import",
    "set_option", "universe", "#check", "#eval", "sorry", "Prop", "Type",
    "Sort", "True", "False", "private", "protected", "partial", "unsafe",
    "mutual", "extends", "deriving", "macro", "syntax", "attribute",
    "nonrec",
}

TACTIC_NAMES: set[str] = {
    "simp", "ring", "omega", "linarith", "norm_num", "exact", "apply",
    "intro", "constructor", "cases", "induction", "rfl", "congr", "ext",
    "funext", "calc", "have", "show", "suffices", "obtain", "rcases",
    "refine", "rw", "rewrite", "conv", "contradiction", "exfalso",
    "by_contra", "push_neg", "field_simp", "positivity", "gcongr",
    "aesop", "decide", "trivial", "assumption", "left", "right", "use",
    "intros", "specialize", "rename_i", "next", "all_goals", "any_goals",
    "first", "try", "repeat", "skip", "done", "sorry",
}

DECL_KEYWORDS: set[str] = {
    "theorem", "lemma", "def", "instance", "class", "structure",
    "inductive", "abbrev", "axiom", "example",
}

# Multi-character operators / symbols, ordered longest-first so the
# tokeniser matches greedily.
MULTI_CHAR_OPS: list[str] = sorted(
    [
        ":=", "->", "→", "×", "∀", "∃", "∧", "∨", "¬", "↔", "≠",
        "≤", "≥", "∘", "⟨", "⟩", "⦃", "⦄", "⊆", "⊇", "∈", "∉",
        "⊔", "⊓", "⊥", "⊤", "∑", "∏", "⋃", "⋂", "++", ">>", ">>=",
        "<<", "<|>", "<|", "|>", "||", "&&", "=>", "=>", "<=>",
        "..", "#check", "#eval",
    ],
    key=len,
    reverse=True,
)

SINGLE_CHAR_OPS: set[str] = set("=<>+-*/%^|.,;:(){}[]@#_!?&~'\\")


# ---------------------------------------------------------------------------
# Tokeniser
# ---------------------------------------------------------------------------

class LeanTokeniser:
    """
    Produces a flat list of ``Token`` objects from Lean 4 source text.

    Handles:
      * ``--`` line comments
      * ``/- … -/`` (nested) block comments
      * ``/-- … -/`` doc-comments (returned as ``DOC_COMMENT`` tokens)
      * Unicode mathematical operators
      * String literals (``"…"``)
      * Char literals (``'…'``)
      * Numeric literals (decimal, hex ``0x…``, binary ``0b…``)
      * Identifiers (including dotted names like ``List.map``)
    """

    def __init__(self, source: str) -> None:
        self.source = source
        self.pos = 0
        self.tokens: list[Token] = []

    # -- helpers ----------------------------------------------------------

    def _ch(self) -> str:
        """Return current character or empty string at EOF."""
        if self.pos < len(self.source):
            return self.source[self.pos]
        return ""

    def _peek(self, n: int = 1) -> str:
        return self.source[self.pos: self.pos + n]

    def _advance(self, n: int = 1) -> str:
        s = self.source[self.pos: self.pos + n]
        self.pos += n
        return s

    def _at_end(self) -> bool:
        return self.pos >= len(self.source)

    # -- skip whitespace & comments ---------------------------------------

    def _skip_ws_and_comments(self) -> Optional[str]:
        """Skip whitespace and comments.  Returns a doc-comment string if
        a ``/-- … -/`` comment is encountered, otherwise ``None``."""
        doc: Optional[str] = None
        while not self._at_end():
            c = self._ch()
            # whitespace
            if c in " \t\r\n":
                self.pos += 1
                continue
            # line comment
            if self._peek(2) == "--":
                # but not /-- (doc comment start handled below after /--)
                while not self._at_end() and self._ch() != "\n":
                    self.pos += 1
                continue
            # block or doc comment
            if self._peek(2) == "/-":
                is_doc = self._peek(3) == "/--"
                doc = self._skip_block_comment(is_doc)
                continue
            break
        return doc

    def _skip_block_comment(self, is_doc: bool = False) -> Optional[str]:
        """Skip a ``/- … -/`` block comment, handling nesting.
        If *is_doc*, returns the text inside."""
        start = self.pos
        depth = 0
        while not self._at_end():
            if self._peek(2) == "/-":
                depth += 1
                self.pos += 2
            elif self._peek(2) == "-/":
                depth -= 1
                self.pos += 2
                if depth == 0:
                    if is_doc:
                        inner = self.source[start + 3: self.pos - 2].strip()
                        return inner
                    return None
            else:
                self.pos += 1
        # unterminated block comment – just return
        return None

    # -- number -----------------------------------------------------------

    def _read_number(self) -> Token:
        start = self.pos
        if self._peek(2) in ("0x", "0X"):
            self.pos += 2
            while not self._at_end() and (self._ch() in "0123456789abcdefABCDEF_"):
                self.pos += 1
        elif self._peek(2) in ("0b", "0B"):
            self.pos += 2
            while not self._at_end() and self._ch() in "01_":
                self.pos += 1
        else:
            while not self._at_end() and (self._ch().isdigit() or self._ch() == "_"):
                self.pos += 1
            if not self._at_end() and self._ch() == ".":
                next_pos = self.pos + 1
                if next_pos < len(self.source) and self.source[next_pos].isdigit():
                    self.pos += 1  # skip '.'
                    while not self._at_end() and (self._ch().isdigit() or self._ch() == "_"):
                        self.pos += 1
        return Token("NUM", self.source[start: self.pos], start)

    # -- string / char ----------------------------------------------------

    def _read_string(self) -> Token:
        start = self.pos
        self.pos += 1  # opening "
        while not self._at_end():
            c = self._ch()
            if c == "\\":
                self.pos += 2
            elif c == '"':
                self.pos += 1
                break
            else:
                self.pos += 1
        return Token("STRING", self.source[start: self.pos], start)

    def _read_char(self) -> Token:
        start = self.pos
        self.pos += 1  # opening '
        if not self._at_end() and self._ch() == "\\":
            self.pos += 2
        elif not self._at_end():
            self.pos += 1
        if not self._at_end() and self._ch() == "'":
            self.pos += 1
        return Token("CHAR", self.source[start: self.pos], start)

    # -- identifier -------------------------------------------------------

    _IDENT_START = re.compile(
        r"[A-Za-z_\u03b1-\u03c9\u0391-\u03a9\u2070-\u209f\u1d62-\u1d6a]"
    )
    _IDENT_CONT = re.compile(
        r"[A-Za-z0-9_'\u03b1-\u03c9\u0391-\u03a9\u2070-\u209f\u2080-\u208e"
        r"\u1d62-\u1d6a\u2032!?\u207f]"
    )

    def _is_ident_start(self, c: str) -> bool:
        if not c:
            return False
        return bool(self._IDENT_START.match(c)) or c == "_"

    def _is_ident_cont(self, c: str) -> bool:
        if not c:
            return False
        # Lean identifiers can contain subscript digits, primes, etc.
        return bool(self._IDENT_CONT.match(c)) or c.isalnum() or c in ("_", "'", "!", "?")

    def _read_ident(self) -> Token:
        """Read a (possibly dotted) identifier such as ``List.map``."""
        start = self.pos
        while True:
            # read one segment
            while not self._at_end() and self._is_ident_cont(self._ch()):
                self.pos += 1
            # if followed by '.' and then an ident-start char, keep going
            if (
                not self._at_end()
                and self._ch() == "."
                and self.pos + 1 < len(self.source)
                and self._is_ident_start(self.source[self.pos + 1])
            ):
                self.pos += 1  # skip '.'
                continue
            break
        text = self.source[start: self.pos]
        kind = "KW" if text in KEYWORDS else "IDENT"
        return Token(kind, text, start)

    # -- main tokenise ----------------------------------------------------

    def tokenise(self) -> list[Token]:
        """Tokenise the full source and return a list of tokens."""
        while True:
            doc = self._skip_ws_and_comments()
            if doc is not None:
                self.tokens.append(Token("DOC_COMMENT", doc, self.pos))
            if self._at_end():
                break
            c = self._ch()

            # numbers
            if c.isdigit():
                self.tokens.append(self._read_number())
                continue

            # string literals
            if c == '"':
                self.tokens.append(self._read_string())
                continue

            # char literals — but only if followed by a single char + '
            if c == "'" and self.pos + 2 < len(self.source):
                # Lean char literal: 'a' or '\n'
                if self.source[self.pos + 1] == "\\":
                    self.tokens.append(self._read_char())
                    continue
                elif (
                    self.pos + 2 < len(self.source)
                    and self.source[self.pos + 2] == "'"
                ):
                    self.tokens.append(self._read_char())
                    continue

            # multi-char operators
            matched_op = False
            for op in MULTI_CHAR_OPS:
                if self.source[self.pos: self.pos + len(op)] == op:
                    self.tokens.append(Token("OP", op, self.pos))
                    self.pos += len(op)
                    matched_op = True
                    break
            if matched_op:
                continue

            # identifiers / keywords
            if self._is_ident_start(c):
                self.tokens.append(self._read_ident())
                continue

            # single-char operators
            if c in SINGLE_CHAR_OPS:
                self.tokens.append(Token("OP", c, self.pos))
                self.pos += 1
                continue

            # Skip anything we don't recognise (e.g. unusual Unicode)
            self.pos += 1

        self.tokens.append(Token("EOF", "", self.pos))
        return self.tokens


def _tokenize(source: str) -> list[Token]:
    """Module-level convenience wrapper."""
    return LeanTokeniser(source).tokenise()


# ---------------------------------------------------------------------------
# Parse error
# ---------------------------------------------------------------------------

class LeanParseError(Exception):
    """Raised when the parser encounters unexpected syntax."""

    def __init__(self, msg: str, pos: int, source: str = "") -> None:
        self.pos = pos
        if source:
            line_no = source[:pos].count("\n") + 1
            col = pos - source[:pos].rfind("\n") - 1
            super().__init__(f"Lean parse error at line {line_no} col {col}: {msg}")
        else:
            super().__init__(f"Lean parse error at pos {pos}: {msg}")


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

class LeanParser:
    """
    Recursive-descent parser for Lean 4 surface syntax.

    Usage::

        parser = LeanParser()
        file_ast = parser.parse_file(lean_source)
        decl_ast = parser.parse_decl(lean_source)
        expr_ast = parser.parse_expr(lean_source)

    The parser is re-entrant: each ``parse_*`` call resets internal state.
    """

    def __init__(self) -> None:
        self._tokens: list[Token] = []
        self._cursor: int = 0
        self._source: str = ""
        self._namespace_stack: list[str] = []

    # -- token helpers ----------------------------------------------------

    def _cur(self) -> Token:
        """Return the current token (never past EOF)."""
        if self._cursor < len(self._tokens):
            return self._tokens[self._cursor]
        return self._tokens[-1]  # EOF sentinel

    def _peek_token(self, offset: int = 0) -> Token:
        idx = self._cursor + offset
        if idx < len(self._tokens):
            return self._tokens[idx]
        return self._tokens[-1]

    def _at_eof(self) -> bool:
        return self._cur().kind == "EOF"

    def _advance_token(self) -> Token:
        tok = self._cur()
        if self._cursor < len(self._tokens) - 1:
            self._cursor += 1
        return tok

    def _expect(self, kind: str, value: Optional[str] = None) -> Token:
        tok = self._cur()
        if tok.kind != kind or (value is not None and tok.value != value):
            expected = f"{kind}" + (f" '{value}'" if value else "")
            raise LeanParseError(
                f"expected {expected}, got {tok.kind} '{tok.value}'",
                tok.pos,
                self._source,
            )
        return self._advance_token()

    def _match(self, kind: str, value: Optional[str] = None) -> Optional[Token]:
        """Consume the current token if it matches, else return ``None``."""
        tok = self._cur()
        if tok.kind == kind and (value is None or tok.value == value):
            return self._advance_token()
        return None

    def _match_kw(self, kw: str) -> Optional[Token]:
        return self._match("KW", kw)

    def _match_op(self, op: str) -> Optional[Token]:
        return self._match("OP", op)

    def _check(self, kind: str, value: Optional[str] = None) -> bool:
        tok = self._cur()
        return tok.kind == kind and (value is None or tok.value == value)

    def _check_kw(self, kw: str) -> bool:
        return self._check("KW", kw)

    def _check_op(self, op: str) -> bool:
        return self._check("OP", op)

    def _error(self, msg: str) -> LeanParseError:
        return LeanParseError(msg, self._cur().pos, self._source)

    # -- init helpers -----------------------------------------------------

    def _init(self, source: str) -> None:
        self._source = source
        self._tokens = _tokenize(source)
        self._cursor = 0
        self._namespace_stack = []

    def _current_namespace(self) -> str:
        return ".".join(self._namespace_stack)

    # =====================================================================
    # Public entry points
    # =====================================================================

    def parse_file(self, source: str) -> LeanFile:
        """Parse a complete Lean 4 source file."""
        self._init(source)
        imports: list[str] = []
        opens: list[str] = []
        declarations: list[LeanDecl] = []
        variables: list[LeanParam] = []
        sections: list[str] = []
        file_ns: Optional[str] = None

        while not self._at_eof():
            # doc-comments attach to the next declaration
            doc: Optional[str] = None
            if self._check("DOC_COMMENT", None):
                doc = self._advance_token().value

            # attributes
            attrs: list[str] = []
            if self._check_op("@") and self._peek_token(1).value == "[":
                attrs = self._parse_attributes()

            # modifiers (noncomputable, private, protected, partial, …)
            modifiers: list[str] = []
            while self._cur().value in (
                "noncomputable", "private", "protected", "partial",
                "unsafe", "nonrec",
            ):
                modifiers.append(self._advance_token().value)

            tok = self._cur()

            if tok.kind == "KW" and tok.value == "import":
                imports.append(self._parse_import())
            elif tok.kind == "KW" and tok.value == "open":
                opens.extend(self._parse_open())
            elif tok.kind == "KW" and tok.value == "namespace":
                ns = self._parse_namespace_start()
                self._namespace_stack.append(ns)
                if file_ns is None:
                    file_ns = ns
            elif tok.kind == "KW" and tok.value == "section":
                sec = self._parse_section_start()
                sections.append(sec)
                self._namespace_stack.append(sec)
            elif tok.kind == "KW" and tok.value == "end":
                self._advance_token()
                # consume optional name after 'end'
                if not self._at_eof() and self._cur().kind == "IDENT":
                    self._advance_token()
                if self._namespace_stack:
                    self._namespace_stack.pop()
            elif tok.kind == "KW" and tok.value == "variable":
                variables.extend(self._parse_variable())
            elif tok.kind == "KW" and tok.value == "set_option":
                self._skip_command()
            elif tok.kind == "KW" and tok.value == "universe":
                self._skip_command()
            elif tok.kind == "KW" and tok.value in ("#check", "#eval"):
                self._skip_command()
            elif tok.kind == "KW" and tok.value in DECL_KEYWORDS:
                decl = self._parse_decl(doc=doc, attrs=attrs, modifiers=modifiers)
                declarations.append(decl)
            elif tok.kind == "KW" and tok.value == "mutual":
                # mutual block: skip 'mutual', parse inner decls, expect 'end'
                self._advance_token()
                while not self._at_eof() and not self._check_kw("end"):
                    inner_doc: Optional[str] = None
                    if self._check("DOC_COMMENT", None):
                        inner_doc = self._advance_token().value
                    inner_attrs: list[str] = []
                    if self._check_op("@") and self._peek_token(1).value == "[":
                        inner_attrs = self._parse_attributes()
                    inner_mods: list[str] = []
                    while self._cur().value in (
                        "noncomputable", "private", "protected",
                        "partial", "unsafe", "nonrec",
                    ):
                        inner_mods.append(self._advance_token().value)
                    if self._cur().value in DECL_KEYWORDS:
                        d = self._parse_decl(
                            doc=inner_doc, attrs=inner_attrs,
                            modifiers=inner_mods,
                        )
                        declarations.append(d)
                    else:
                        self._advance_token()
                self._match_kw("end")
            else:
                # skip unrecognised token
                self._advance_token()

        return LeanFile(
            imports=imports,
            opens=opens,
            namespace=file_ns,
            declarations=declarations,
            variables=variables,
            sections=sections,
        )

    def parse_decl(self, source: str) -> LeanDecl:
        """Parse a single Lean 4 declaration from *source*."""
        self._init(source)
        doc: Optional[str] = None
        if self._check("DOC_COMMENT", None):
            doc = self._advance_token().value
        attrs: list[str] = []
        if self._check_op("@") and self._peek_token(1).value == "[":
            attrs = self._parse_attributes()
        modifiers: list[str] = []
        while self._cur().value in (
            "noncomputable", "private", "protected", "partial",
            "unsafe", "nonrec",
        ):
            modifiers.append(self._advance_token().value)
        return self._parse_decl(doc=doc, attrs=attrs, modifiers=modifiers)

    def parse_expr(self, source: str) -> LeanExpr:
        """Parse a single Lean 4 expression from *source*."""
        self._init(source)
        return self._parse_expr()

    # =====================================================================
    # Top-level helpers
    # =====================================================================

    def _parse_import(self) -> str:
        """``import Mathlib.Data.List.Basic``"""
        self._expect("KW", "import")
        parts: list[str] = []
        tok = self._cur()
        if tok.kind == "IDENT":
            parts.append(self._advance_token().value)
        # Allow dotted imports already captured as single IDENT token
        return ".".join(parts) if parts else ""

    def _parse_open(self) -> list[str]:
        """``open Nat List in …`` — returns list of opened namespaces."""
        self._expect("KW", "open")
        names: list[str] = []
        while not self._at_eof():
            tok = self._cur()
            if tok.kind == "IDENT":
                names.append(self._advance_token().value)
            elif tok.kind == "KW" and tok.value == "in":
                self._advance_token()
                break
            else:
                break
        return names

    def _parse_namespace_start(self) -> str:
        self._expect("KW", "namespace")
        if self._cur().kind == "IDENT":
            return self._advance_token().value
        return ""

    def _parse_section_start(self) -> str:
        self._expect("KW", "section")
        if self._cur().kind == "IDENT":
            return self._advance_token().value
        return ""

    def _parse_variable(self) -> list[LeanParam]:
        """``variable (x : A) [inst : B]``"""
        self._expect("KW", "variable")
        params: list[LeanParam] = []
        while not self._at_eof() and self._cur().value in ("(", "{", "[", "⦃"):
            params.extend(self._parse_params())
        return params

    def _skip_command(self) -> None:
        """Skip tokens until the next line break or declaration keyword."""
        self._advance_token()
        while not self._at_eof():
            tok = self._cur()
            # Stop at something that looks like a new top-level form
            if tok.kind == "KW" and tok.value in (
                *DECL_KEYWORDS, "import", "open", "namespace",
                "section", "end", "variable", "mutual",
                "#check", "#eval", "set_option", "universe",
            ):
                break
            if tok.kind == "DOC_COMMENT":
                break
            self._advance_token()

    # =====================================================================
    # Attributes: @[simp, ext, ...]
    # =====================================================================

    def _parse_attributes(self) -> list[str]:
        """Parse ``@[attr1, attr2, ...]`` and return list of attribute names."""
        attrs: list[str] = []
        self._expect("OP", "@")
        self._expect("OP", "[")
        while not self._at_eof() and not self._check_op("]"):
            tok = self._cur()
            if tok.kind in ("IDENT", "KW"):
                attrs.append(self._advance_token().value)
            elif self._check_op(","):
                self._advance_token()
            else:
                # skip unknown attribute arguments
                self._advance_token()
        self._match_op("]")
        return attrs

    # =====================================================================
    # Declaration parsing
    # =====================================================================

    def _parse_decl(
        self,
        doc: Optional[str] = None,
        attrs: Optional[list[str]] = None,
        modifiers: Optional[list[str]] = None,
    ) -> LeanDecl:
        """
        Parse a declaration starting at the current cursor.

        Handles ``theorem``, ``def``, ``lemma``, ``instance``, ``class``,
        ``structure``, ``inductive``, ``abbrev``, ``axiom``, ``example``.
        """
        if attrs is None:
            attrs = []
        if modifiers is None:
            modifiers = []

        kind_tok = self._advance_token()
        kind = kind_tok.value

        # Universe params: ``theorem foo.{u, v} …``
        universe_params: list[str] = []
        name = ""
        if kind != "example":
            if self._cur().kind == "IDENT":
                name = self._advance_token().value
            # parse optional universe parameters .{u, v}
            if self._check_op(".") and self._peek_token(1).value == "{":
                self._advance_token()  # skip '.'
                self._advance_token()  # skip '{'
                while not self._at_eof() and not self._check_op("}"):
                    if self._cur().kind == "IDENT":
                        universe_params.append(self._advance_token().value)
                    elif self._check_op(","):
                        self._advance_token()
                    else:
                        break
                self._match_op("}")

        # Parameters
        params: list[LeanParam] = []
        while not self._at_eof() and self._cur().value in ("(", "{", "[", "⦃"):
            params.extend(self._parse_params())

        # Return type
        return_type: Optional[LeanExpr] = None
        if self._match_op(":"):
            return_type = self._parse_expr()

        # Body
        body: Optional[LeanExpr] = None

        if kind in ("class", "structure"):
            body = self._parse_structure_body()
        elif kind == "inductive":
            body = self._parse_inductive_body()
        elif kind == "axiom":
            # axioms have no body
            pass
        elif self._match_op(":="):
            body = self._parse_expr()
        elif self._check_kw("where"):
            # ``where`` is used for structure fields, instance defs, etc.
            body = self._parse_where_body()
        elif self._check_kw("by"):
            body = self._parse_tactic_block()

        return LeanDecl(
            kind=kind,
            name=name,
            universe_params=universe_params,
            params=params,
            return_type=return_type,
            body=body,
            attributes=attrs,
            docstring=doc,
            namespace=self._current_namespace(),
        )

    # -- structure / class body -------------------------------------------

    def _parse_structure_body(self) -> Optional[LeanExpr]:
        """Parse ``where`` or ``extends`` clauses for structures/classes."""
        # optional 'extends'
        if self._check_kw("extends"):
            self._advance_token()
            # parse parent types separated by commas
            while not self._at_eof():
                if self._cur().kind == "IDENT":
                    self._advance_token()
                    # skip type arguments
                    while self._cur().kind == "IDENT" or self._cur().value in ("(", "{", "["):
                        if self._cur().value in ("(", "{", "["):
                            self._skip_balanced()
                        else:
                            self._advance_token()
                if self._match_op(","):
                    continue
                break

        if self._check_kw("where"):
            return self._parse_where_body()
        return None

    def _parse_where_body(self) -> LeanExpr:
        """Parse a ``where`` block — used for structures, instances, etc."""
        self._expect("KW", "where")
        stmts: list[LeanExpr] = []
        while not self._at_eof():
            tok = self._cur()
            # stop at things that mark the end of a where block
            if tok.kind == "KW" and tok.value in (
                "end", "namespace", "section", "theorem", "def", "lemma",
                "instance", "class", "structure", "inductive", "abbrev",
                "axiom", "example", "mutual", "variable", "open", "import",
            ):
                break
            if tok.kind == "DOC_COMMENT":
                break
            if self._check_op("@") and self._peek_token(1).value == "[":
                break
            # try to parse a field definition: name ':' type ':=' value
            if tok.kind == "IDENT":
                field_name = self._advance_token().value
                field_type: Optional[LeanExpr] = None
                field_val: Optional[LeanExpr] = None
                if self._match_op(":"):
                    field_type = self._parse_expr_until_field_end()
                if self._match_op(":="):
                    field_val = self._parse_expr_until_field_end()
                # represent as a let binding
                stmts.append(LeanLet(
                    name=field_name,
                    type_=field_type,
                    value=field_val if field_val else LeanHole(),
                    body=LeanHole(),
                ))
            else:
                self._advance_token()
        if len(stmts) == 1:
            return stmts[0]
        return LeanDo(stmts=stmts) if stmts else LeanHole()

    def _parse_expr_until_field_end(self) -> LeanExpr:
        """Parse an expression stopping at the next field boundary."""
        # We parse a full expression but watch for unbalanced tokens that
        # indicate a new field.
        return self._parse_expr()

    # -- inductive body ---------------------------------------------------

    def _parse_inductive_body(self) -> Optional[LeanExpr]:
        """Parse the body of an ``inductive`` declaration (constructors)."""
        # optional 'where'
        self._match_kw("where")

        ctors: list[LeanExpr] = []
        while not self._at_eof():
            tok = self._cur()
            if tok.kind == "KW" and tok.value in DECL_KEYWORDS:
                break
            if tok.kind == "KW" and tok.value in ("end", "namespace", "section"):
                break
            if tok.kind == "DOC_COMMENT":
                # doc comment for next ctor — skip for now
                self._advance_token()
                continue
            if self._match_op("|"):
                ctor_name = ""
                if self._cur().kind == "IDENT":
                    ctor_name = self._advance_token().value
                ctor_type: Optional[LeanExpr] = None
                if self._match_op(":"):
                    ctor_type = self._parse_expr()
                ctors.append(LeanLet(
                    name=ctor_name,
                    type_=ctor_type,
                    value=LeanHole(),
                    body=LeanHole(),
                ))
            elif self._check_kw("deriving"):
                self._skip_command()
                break
            else:
                break
        if ctors:
            return LeanDo(stmts=ctors)
        return None

    # =====================================================================
    # Parameter parsing
    # =====================================================================

    def _parse_params(self) -> list[LeanParam]:
        """
        Parse one binder group, dispatching on the opening bracket:

        * ``(x : A)`` — explicit
        * ``{x : A}`` — implicit
        * ``[x : A]`` — instance
        * ``⦃x : A⦄`` — strict implicit
        """
        tok = self._cur()
        if tok.value == "(":
            return self._parse_binder_group("(", ")", "explicit")
        elif tok.value == "{":
            return self._parse_binder_group("{", "}", "implicit")
        elif tok.value == "[":
            return self._parse_binder_group("[", "]", "instance")
        elif tok.value == "⦃":
            return self._parse_binder_group("⦃", "⦄", "strict_implicit")
        else:
            raise self._error(f"expected binder opener, got '{tok.value}'")

    def _parse_binder_group(
        self, open_: str, close: str, binder: str,
    ) -> list[LeanParam]:
        """Parse ``open names : type close``."""
        self._expect("OP", open_)
        names: list[str] = []
        type_expr: Optional[LeanExpr] = None
        default_expr: Optional[LeanExpr] = None

        # Collect names until ':' or closing bracket
        while not self._at_eof() and not self._check_op(close):
            if self._check_op(":"):
                break
            if self._cur().kind in ("IDENT", "KW"):
                names.append(self._advance_token().value)
            elif self._check_op("_"):
                names.append("_")
                self._advance_token()
            else:
                # might be a complex expression used as a name pattern
                names.append(self._cur().value)
                self._advance_token()

        if self._match_op(":"):
            type_expr = self._parse_expr_in_binder(close)

        # optional default value
        if self._match_op(":="):
            default_expr = self._parse_expr_in_binder(close)

        self._match_op(close)

        if not names:
            names = ["_"]

        return [
            LeanParam(
                name=n, type_=type_expr, binder=binder,
                default=default_expr,
            )
            for n in names
        ]

    def _parse_expr_in_binder(self, close: str) -> LeanExpr:
        """Parse an expression inside a binder, stopping at the closing
        bracket or ``:=``."""
        return self._parse_expr(stop_at={close, ":="})

    # =====================================================================
    # Expression parsing — recursive descent
    # =====================================================================

    def _parse_expr(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        """
        Top-level expression parser.

        *stop_at*: optional set of token values at which to stop early
        (used when parsing sub-expressions inside binders).
        """
        return self._parse_pi_or_arrow(stop_at)

    def _parse_pi_or_arrow(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        """
        Parse dependent / non-dependent function types::

            ∀ (x : A), B x
            A → B
            (x : A) → B x
        """
        # ∀ or forall
        if self._check_op("∀") or self._check_kw("∀"):
            self._advance_token()
            params = self._parse_pi_binders()
            if self._match_op(","):
                pass
            codomain = self._parse_expr(stop_at)
            return LeanPi(params=params, codomain=codomain)

        # ∃
        if self._check_op("∃") or self._check_kw("∃"):
            self._advance_token()
            params = self._parse_pi_binders()
            if self._match_op(","):
                pass
            body = self._parse_expr(stop_at)
            # Represent ∃ as application of Exists with a lambda
            return LeanApp(
                fn=LeanVar("Exists"),
                args=[LeanLam(params=params, body=body)],
            )

        left = self._parse_or(stop_at)

        # non-dependent arrow
        if self._match_op("→") or self._match_op("->"):
            right = self._parse_expr(stop_at)
            return LeanPi(
                params=[LeanParam("_", left, "explicit")],
                codomain=right,
            )

        # iff
        if self._match_op("↔"):
            right = self._parse_expr(stop_at)
            return LeanApp(fn=LeanVar("Iff"), args=[left, right])

        # product type
        if self._match_op("×"):
            right = self._parse_expr(stop_at)
            return LeanApp(fn=LeanVar("Prod"), args=[left, right])

        return left

    def _parse_pi_binders(self) -> list[LeanParam]:
        """Parse the binder list after ∀ / ∃, before the comma."""
        params: list[LeanParam] = []
        while not self._at_eof():
            if self._cur().value in ("(", "{", "[", "⦃"):
                params.extend(self._parse_params())
            elif self._cur().kind == "IDENT":
                # bare name without type
                name = self._advance_token().value
                type_expr: Optional[LeanExpr] = None
                if self._match_op(":"):
                    type_expr = self._parse_app()
                params.append(LeanParam(name=name, type_=type_expr, binder="explicit"))
            else:
                break
        return params

    # -- binary operators (precedence climbing) ---------------------------

    def _parse_or(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        left = self._parse_and(stop_at)
        while self._match_op("∨") or self._match_op("||"):
            right = self._parse_and(stop_at)
            left = LeanApp(fn=LeanVar("Or"), args=[left, right])
        return left

    def _parse_and(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        left = self._parse_not(stop_at)
        while self._match_op("∧") or self._match_op("&&"):
            right = self._parse_not(stop_at)
            left = LeanApp(fn=LeanVar("And"), args=[left, right])
        return left

    def _parse_not(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        if self._match_op("¬") or self._match_op("!"):
            operand = self._parse_not(stop_at)
            return LeanApp(fn=LeanVar("Not"), args=[operand])
        return self._parse_comparison(stop_at)

    def _parse_comparison(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        left = self._parse_set_ops(stop_at)
        cmp_ops = {"=", "≠", "<", "≤", ">", "≥", "∈", "∉", "⊆", "⊇"}
        tok = self._cur()
        if tok.kind == "OP" and tok.value in cmp_ops:
            op_val = self._advance_token().value
            right = self._parse_set_ops(stop_at)
            op_map = {
                "=": "Eq", "≠": "Ne", "<": "LT.lt", "≤": "LE.le",
                ">": "GT.gt", "≥": "GE.ge", "∈": "Membership.mem",
                "∉": "Not_mem", "⊆": "HasSubset.Subset",
                "⊇": "HasSuperset.Superset",
            }
            fn_name = op_map.get(op_val, op_val)
            return LeanApp(fn=LeanVar(fn_name), args=[left, right])
        return left

    def _parse_set_ops(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        left = self._parse_add(stop_at)
        set_ops = {"⊔", "⊓", "⋃", "⋂"}
        while self._cur().kind == "OP" and self._cur().value in set_ops:
            op_val = self._advance_token().value
            right = self._parse_add(stop_at)
            op_map = {
                "⊔": "Sup.sup", "⊓": "Inf.inf",
                "⋃": "Set.iUnion", "⋂": "Set.iInter",
            }
            left = LeanApp(fn=LeanVar(op_map.get(op_val, op_val)), args=[left, right])
        return left

    def _parse_add(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        left = self._parse_mul(stop_at)
        while self._cur().kind == "OP" and self._cur().value in ("+", "-", "++"):
            op_val = self._advance_token().value
            right = self._parse_mul(stop_at)
            op_map = {
                "+": "HAdd.hAdd", "-": "HSub.hSub", "++": "HAppend.hAppend",
            }
            left = LeanApp(fn=LeanVar(op_map.get(op_val, op_val)), args=[left, right])
        return left

    def _parse_mul(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        left = self._parse_pow(stop_at)
        while self._cur().kind == "OP" and self._cur().value in ("*", "/", "%", "∘"):
            op_val = self._advance_token().value
            right = self._parse_pow(stop_at)
            op_map = {
                "*": "HMul.hMul", "/": "HDiv.hDiv", "%": "HMod.hMod",
                "∘": "Function.comp",
            }
            left = LeanApp(fn=LeanVar(op_map.get(op_val, op_val)), args=[left, right])
        return left

    def _parse_pow(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        base = self._parse_app(stop_at)
        if self._match_op("^"):
            exp = self._parse_pow(stop_at)  # right-assoc
            return LeanApp(fn=LeanVar("HPow.hPow"), args=[base, exp])
        return base

    # -- application ------------------------------------------------------

    def _parse_app(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        """
        Parse function application: ``f a b c``.

        Application in Lean is juxtaposition.  We collect atoms until we
        hit something that cannot be an argument.
        """
        fn = self._parse_projection(stop_at)
        args: list[LeanExpr] = []
        while not self._at_eof():
            if stop_at and self._cur().value in stop_at:
                break
            if self._is_app_arg_start():
                args.append(self._parse_projection(stop_at))
            else:
                break
        if args:
            return LeanApp(fn=fn, args=args)
        return fn

    def _is_app_arg_start(self) -> bool:
        """Return ``True`` if the current token can start an application
        argument (i.e. an atom)."""
        tok = self._cur()
        if tok.kind == "EOF":
            return False
        # These tokens definitely do NOT start an argument
        non_arg = {
            ")", "}", "]", "⦄", ":=", "→", "->", "↔", ",", ";",
            "|", "with", "then", "else", "end", "where", "in",
            "∧", "∨", "=", "≠", "<", "≤", ">", "≥", "+", "-",
            "*", "/", "%", "^", "∘", "×", "∈", "∉", "⊆", "⊇",
            "⊔", "⊓", "⋃", "⋂", ":","⊥", "⊤", "∑", "∏",
            "by",
        }
        if tok.value in non_arg:
            return False
        # keywords that start declarations
        if tok.kind == "KW" and tok.value in DECL_KEYWORDS:
            return False
        if tok.kind == "KW" and tok.value in (
            "import", "open", "namespace", "section", "end",
            "variable", "set_option", "universe", "mutual",
        ):
            return False
        return True

    # -- projection -------------------------------------------------------

    def _parse_projection(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        """Parse ``e.field`` projections."""
        expr = self._parse_atom(stop_at)
        while self._check_op("."):
            # '.' followed by an identifier or a number
            if (
                self._peek_token(1).kind in ("IDENT", "NUM")
            ):
                self._advance_token()  # skip '.'
                field = self._advance_token().value
                expr = LeanProj(expr=expr, field=field)
            else:
                break
        return expr

    # -- atoms ------------------------------------------------------------

    def _parse_atom(self, stop_at: Optional[set[str]] = None) -> LeanExpr:
        """
        Parse an atomic expression.

        Handles: parenthesised expressions, anonymous constructors ``⟨…⟩``,
        literals, holes ``_``, ``sorry``, ``fun``/``λ``, ``let``, ``if``,
        ``match``, ``do``, ``by``, ``calc``, ``have``, ``show``, ``suffices``,
        ``Prop``/``Type``/``Sort``, identifiers, ``@explicit``.
        """
        tok = self._cur()

        # parenthesised or tuple
        if tok.value == "(":
            return self._parse_paren_expr()

        # anonymous constructor ⟨ … ⟩
        if tok.value == "⟨":
            return self._parse_anonymous_ctor()

        # numeric literal
        if tok.kind == "NUM":
            self._advance_token()
            if "." in tok.value:
                return LeanLit(value=float(tok.value.replace("_", "")))
            elif tok.value.startswith(("0x", "0X")):
                return LeanLit(value=int(tok.value.replace("_", ""), 16))
            elif tok.value.startswith(("0b", "0B")):
                return LeanLit(value=int(tok.value.replace("_", ""), 2))
            else:
                return LeanLit(value=int(tok.value.replace("_", "")))

        # string literal
        if tok.kind == "STRING":
            self._advance_token()
            # strip surrounding quotes
            inner = tok.value[1:-1] if len(tok.value) >= 2 else tok.value
            return LeanLit(value=inner)

        # char literal
        if tok.kind == "CHAR":
            self._advance_token()
            inner = tok.value[1:-1] if len(tok.value) >= 2 else tok.value
            return LeanLit(value=inner)

        # hole / placeholder
        if tok.value == "_":
            self._advance_token()
            return LeanHole()

        # sorry
        if tok.value == "sorry":
            self._advance_token()
            return LeanSorry()

        # True / False
        if tok.value == "True":
            self._advance_token()
            return LeanLit(value=True)
        if tok.value == "False":
            self._advance_token()
            return LeanLit(value=False)

        # Prop / Type / Sort
        if tok.value == "Prop":
            self._advance_token()
            return LeanSort(level=0)
        if tok.value == "Type":
            self._advance_token()
            level = 1
            if self._cur().kind == "NUM":
                level = int(self._advance_token().value) + 1
            return LeanSort(level=level)
        if tok.value == "Sort":
            self._advance_token()
            level = 0
            if self._cur().kind == "NUM":
                level = int(self._advance_token().value)
            return LeanSort(level=level)

        # fun / λ
        if tok.value in ("fun", "λ"):
            return self._parse_lambda()

        # let
        if tok.value == "let":
            return self._parse_let()

        # if-then-else
        if tok.value == "if":
            return self._parse_if()

        # match
        if tok.value == "match":
            return self._parse_match()

        # do notation
        if tok.value == "do":
            return self._parse_do()

        # by (tactic block)
        if tok.value == "by":
            return self._parse_tactic_block()

        # calc block
        if tok.value == "calc":
            return self._parse_calc()

        # have
        if tok.value == "have":
            return self._parse_have()

        # show
        if tok.value == "show":
            return self._parse_show()

        # suffices
        if tok.value == "suffices":
            return self._parse_suffices()

        # return (in do blocks)
        if tok.value == "return":
            self._advance_token()
            if (
                not self._at_eof()
                and self._is_app_arg_start()
            ):
                val = self._parse_expr(stop_at)
                return LeanApp(fn=LeanVar("return"), args=[val])
            return LeanVar("return")

        # for (in do blocks)
        if tok.value == "for":
            return self._parse_for()

        # @ explicit
        if tok.value == "@":
            self._advance_token()
            inner = self._parse_atom(stop_at)
            return LeanApp(fn=LeanVar("@"), args=[inner])

        # ⊤ / ⊥
        if tok.value == "⊤":
            self._advance_token()
            return LeanVar("Top")
        if tok.value == "⊥":
            self._advance_token()
            return LeanVar("Bot")

        # ∑ / ∏
        if tok.value == "∑":
            self._advance_token()
            return LeanVar("Finset.sum")
        if tok.value == "∏":
            self._advance_token()
            return LeanVar("Finset.prod")

        # identifier (including dotted)
        if tok.kind in ("IDENT", "KW"):
            # some keywords can appear as identifiers in expressions
            self._advance_token()
            return LeanVar(name=tok.value)

        # If we really can't figure it out, skip and return a hole
        self._advance_token()
        return LeanHole()

    # -- parenthesised / tuple --------------------------------------------

    def _parse_paren_expr(self) -> LeanExpr:
        """``(e)`` or ``(e₁, e₂, …)`` (tuple)."""
        self._expect("OP", "(")
        if self._match_op(")"):
            return LeanVar("Unit.unit")

        first = self._parse_expr()
        elems: list[LeanExpr] = [first]

        while self._match_op(","):
            elems.append(self._parse_expr())

        self._match_op(")")

        if len(elems) == 1:
            return elems[0]
        # tuple
        return LeanAnonymousCtor(args=elems)

    # -- anonymous constructor ⟨ … ⟩ --------------------------------------

    def _parse_anonymous_ctor(self) -> LeanAnonymousCtor:
        """Parse ``⟨a, b, c⟩``."""
        self._expect("OP", "⟨")
        args: list[LeanExpr] = []
        while not self._at_eof() and not self._check_op("⟩"):
            args.append(self._parse_expr(stop_at={"⟩", ","}))
            if not self._match_op(","):
                break
        self._match_op("⟩")
        return LeanAnonymousCtor(args=args)

    # -- lambda -----------------------------------------------------------

    def _parse_lambda(self) -> LeanLam:
        """Parse ``fun x y => body`` or ``λ x => body``."""
        self._advance_token()  # skip 'fun' / 'λ'
        params: list[LeanParam] = []

        while not self._at_eof():
            if self._check_op("=>") or self._check_op("⇒"):
                break
            if self._cur().value in ("(", "{", "[", "⦃"):
                params.extend(self._parse_params())
            elif self._cur().kind == "IDENT" or self._cur().value == "_":
                name = self._advance_token().value
                type_expr: Optional[LeanExpr] = None
                if self._match_op(":"):
                    type_expr = self._parse_app()
                params.append(LeanParam(name=name, type_=type_expr, binder="explicit"))
            else:
                break

        # expect =>
        if not (self._match_op("=>") or self._match_op("⇒")):
            # some lambdas use | for match-arms inline
            pass

        body = self._parse_expr()
        return LeanLam(params=params, body=body)

    # -- let binding ------------------------------------------------------

    def _parse_let(self) -> LeanLet:
        """Parse ``let x : T := v; body`` or ``let x := v\\n body``."""
        self._expect("KW", "let")
        name = "_"
        if self._cur().kind == "IDENT" or self._cur().value == "_":
            name = self._advance_token().value

        type_expr: Optional[LeanExpr] = None
        if self._match_op(":"):
            type_expr = self._parse_expr(stop_at={":="})

        self._match_op(":=")
        value = self._parse_expr(stop_at={";", "in"})

        # separator
        self._match_op(";")
        self._match_kw("in")

        body = self._parse_expr()
        return LeanLet(name=name, type_=type_expr, value=value, body=body)

    # -- if-then-else -----------------------------------------------------

    def _parse_if(self) -> LeanIf:
        """Parse ``if c then t else e``."""
        self._expect("KW", "if")

        # optional 'h :' for hypothesis name
        if (
            self._cur().kind == "IDENT"
            and self._peek_token(1).value == ":"
        ):
            self._advance_token()  # skip hypothesis name
            self._advance_token()  # skip ':'

        cond = self._parse_expr(stop_at={"then"})
        self._match_kw("then")
        then_ = self._parse_expr(stop_at={"else"})
        self._match_kw("else")
        else_ = self._parse_expr()
        return LeanIf(cond=cond, then_=then_, else_=else_)

    # -- match ------------------------------------------------------------

    def _parse_match(self) -> LeanMatch:
        """Parse ``match e₁, e₂ with | p => rhs | …``."""
        self._expect("KW", "match")
        scrutinees: list[LeanExpr] = []
        # parse scrutinees (comma-separated)
        while not self._at_eof() and not self._check_kw("with"):
            scrutinees.append(self._parse_expr(stop_at={",", "with"}))
            if not self._match_op(","):
                break

        self._match_kw("with")

        arms: list[MatchArm] = []
        while self._match_op("|"):
            patterns: list[LeanExpr] = []
            while not self._at_eof() and not self._check_op("=>") and not self._check_op("⇒"):
                patterns.append(self._parse_expr(stop_at={",", "=>", "⇒"}))
                if not self._match_op(","):
                    break
            if not (self._match_op("=>") or self._match_op("⇒")):
                pass
            rhs = self._parse_expr(stop_at={"|"})
            arms.append(MatchArm(patterns=patterns, rhs=rhs))

        return LeanMatch(scrutinees=scrutinees, arms=arms)

    # -- do notation ------------------------------------------------------

    def _parse_do(self) -> LeanDo:
        """Parse ``do`` block — a sequence of statements."""
        self._expect("KW", "do")
        stmts: list[LeanExpr] = []

        while not self._at_eof():
            tok = self._cur()
            # heuristic: stop at declaration keywords, end, etc.
            if tok.kind == "KW" and tok.value in (
                "end", "namespace", "section",
                *DECL_KEYWORDS, "import", "open",
            ):
                break
            if tok.kind == "EOF":
                break

            stmt = self._parse_expr(stop_at={";", "end"})
            stmts.append(stmt)
            self._match_op(";")

            # if next token doesn't look like it continues the do block, stop
            if not self._is_app_arg_start() and not self._check_kw("let"):
                break

        return LeanDo(stmts=stmts)

    # -- calc block -------------------------------------------------------

    def _parse_calc(self) -> LeanExpr:
        """
        Parse a ``calc`` proof block::

            calc a = b := by ...
                 _ = c := by ...

        Represented as a ``LeanTacticBlock`` containing individual calc steps.
        """
        self._expect("KW", "calc")
        steps: list[LeanTactic] = []

        while not self._at_eof():
            tok = self._cur()
            if tok.kind == "KW" and tok.value in (
                "end", "namespace", "section", *DECL_KEYWORDS,
            ):
                break
            if tok.kind == "EOF":
                break

            # A calc step: expr op expr := justification
            step_expr = self._parse_expr(stop_at={":="})
            justification: Optional[LeanExpr] = None
            if self._match_op(":="):
                justification = self._parse_expr(stop_at={"_"})

            step_args: list[LeanExpr] = [step_expr]
            if justification is not None:
                step_args.append(justification)
            steps.append(LeanTactic(tactic_name="calc_step", args=step_args))

            # Stop if next token is not '_' (continuation of calc)
            if not self._check_op("_") and not self._check("IDENT"):
                break

        return LeanTacticBlock(tactics=steps)

    # -- have / show / suffices -------------------------------------------

    def _parse_have(self) -> LeanExpr:
        """Parse ``have h : T := proof`` or ``have : T := proof``."""
        self._expect("KW", "have")
        name = "_"
        if self._cur().kind == "IDENT" and self._peek_token(1).value == ":":
            name = self._advance_token().value

        type_expr: Optional[LeanExpr] = None
        if self._match_op(":"):
            type_expr = self._parse_expr(stop_at={":=", "by", "from"})

        value: LeanExpr = LeanHole()
        if self._match_op(":="):
            value = self._parse_expr(stop_at={";", "in"})
        elif self._check_kw("by"):
            value = self._parse_tactic_block()
        elif self._match_kw("from"):
            value = self._parse_expr(stop_at={";", "in"})

        self._match_op(";")
        self._match_kw("in")

        body = self._parse_expr() if not self._at_eof() else LeanHole()

        return LeanLet(name=name, type_=type_expr, value=value, body=body)

    def _parse_show(self) -> LeanExpr:
        """Parse ``show T by tactics`` or ``show T from proof``."""
        self._expect("KW", "show")
        type_expr = self._parse_expr(stop_at={"by", "from", ":="})
        proof: LeanExpr = LeanHole()
        if self._check_kw("by"):
            proof = self._parse_tactic_block()
        elif self._match_kw("from"):
            proof = self._parse_expr()
        elif self._match_op(":="):
            proof = self._parse_expr()
        return LeanApp(fn=LeanVar("show"), args=[type_expr, proof])

    def _parse_suffices(self) -> LeanExpr:
        """Parse ``suffices h : T by ...``."""
        self._expect("KW", "suffices")
        name = "_"
        if self._cur().kind == "IDENT" and self._peek_token(1).value == ":":
            name = self._advance_token().value

        type_expr: Optional[LeanExpr] = None
        if self._match_op(":"):
            type_expr = self._parse_expr(stop_at={"by", "from", ":="})

        proof: LeanExpr = LeanHole()
        if self._check_kw("by"):
            proof = self._parse_tactic_block()
        elif self._match_kw("from"):
            proof = self._parse_expr()

        return LeanLet(name=name, type_=type_expr, value=proof, body=LeanHole())

    # -- for (in do blocks) -----------------------------------------------

    def _parse_for(self) -> LeanExpr:
        """Parse ``for x in collection do body``."""
        self._expect("KW", "for")
        var_name = "_"
        if self._cur().kind == "IDENT":
            var_name = self._advance_token().value
        self._match_kw("in")
        collection = self._parse_expr(stop_at={"do"})
        body: LeanExpr = LeanHole()
        if self._check_kw("do"):
            body = self._parse_do()
        return LeanApp(
            fn=LeanVar("forIn"),
            args=[
                collection,
                LeanLam(
                    params=[LeanParam(name=var_name, type_=None, binder="explicit")],
                    body=body,
                ),
            ],
        )

    # =====================================================================
    # Tactic parsing
    # =====================================================================

    def _parse_tactic_block(self) -> LeanTacticBlock:
        """
        Parse ``by tac₁; tac₂; …`` or a multi-line tactic block.

        The parser collects tactics until it hits a token that unambiguously
        ends the tactic block (a declaration keyword, ``end``, etc.).
        """
        self._expect("KW", "by")
        tactics: list[LeanTactic] = []

        while not self._at_eof():
            tok = self._cur()
            # end markers for tactic blocks
            if tok.kind == "KW" and tok.value in (
                "end", "namespace", "section",
                *DECL_KEYWORDS, "import", "open", "variable",
                "mutual",
            ):
                break
            if tok.kind == "DOC_COMMENT":
                break
            if tok.value in (")", "}", "]", "⦄", "|"):
                break
            if tok.kind == "EOF":
                break

            tactic = self._parse_tactic()
            if tactic is not None:
                tactics.append(tactic)

            # optional semicolon separator
            self._match_op(";")
            # also skip newline-style separators (handled implicitly)

        return LeanTacticBlock(tactics=tactics)

    def _parse_tactic(self) -> Optional[LeanTactic]:
        """
        Parse a single tactic invocation.

        Recognised tactics include: ``simp``, ``ring``, ``omega``,
        ``linarith``, ``norm_num``, ``exact``, ``apply``, ``intro``,
        ``constructor``, ``cases``, ``induction``, ``rfl``, ``congr``,
        ``ext``, ``funext``, ``have``, ``show``, ``suffices``, ``obtain``,
        ``rcases``, ``refine``, ``rw``/``rewrite``, ``conv``,
        ``contradiction``, ``exfalso``, ``by_contra``, ``push_neg``,
        ``field_simp``, ``positivity``, ``gcongr``, ``aesop``, ``decide``,
        ``trivial``, ``assumption``, ``left``, ``right``, ``use``,
        ``calc``, ``intros``, ``specialize``, ``rename_i``, ``next``,
        ``all_goals``, ``any_goals``, ``first``, ``try``, ``repeat``,
        ``skip``, ``done``, ``sorry``.
        """
        tok = self._cur()

        if tok.kind == "EOF":
            return None

        # 'sorry' as tactic
        if tok.value == "sorry":
            self._advance_token()
            return LeanTactic(tactic_name="sorry", args=[])

        # Check if it's a known tactic name
        if tok.value in TACTIC_NAMES:
            tac_name = self._advance_token().value
            args = self._parse_tactic_args(tac_name)
            return LeanTactic(tactic_name=tac_name, args=args)

        # 'rfl' — no args
        if tok.value == "rfl":
            self._advance_token()
            return LeanTactic(tactic_name="rfl", args=[])

        # Unknown tactic — skip one token and wrap as generic tactic
        if tok.kind in ("IDENT", "KW"):
            name = self._advance_token().value
            args = self._parse_tactic_args(name)
            return LeanTactic(tactic_name=name, args=args)

        # Skip operators or other unexpected tokens
        self._advance_token()
        return None

    def _parse_tactic_args(self, tac_name: str) -> list[LeanExpr]:
        """
        Parse arguments for a tactic.

        Different tactics have different argument shapes — this provides
        a reasonable heuristic parse.
        """
        args: list[LeanExpr] = []

        # Tactics that take no arguments
        no_arg_tactics = {
            "constructor", "contradiction", "exfalso", "assumption",
            "left", "right", "trivial", "skip", "done", "rfl",
            "ring", "omega", "linarith", "norm_num", "positivity",
            "aesop", "decide",
        }
        if tac_name in no_arg_tactics:
            # But some of these can have optional args (e.g. simp [...])
            if tac_name in ("ring", "omega", "linarith", "norm_num",
                            "positivity", "aesop", "decide"):
                if self._check_op("["):
                    args.append(self._parse_simp_lemmas())
            return args

        # simp-like: optional [lemma list], optional 'at' hypothesis
        if tac_name in ("simp", "field_simp", "push_neg"):
            if self._check_op("["):
                args.append(self._parse_simp_lemmas())
            if self._match_kw("at") or (self._cur().value == "at"):
                if self._cur().value == "at":
                    self._advance_token()
                if self._cur().kind == "IDENT" or self._cur().value == "*":
                    args.append(LeanVar(self._advance_token().value))
            return args

        # rw / rewrite: [lemma list], optional 'at'
        if tac_name in ("rw", "rewrite"):
            if self._check_op("["):
                args.append(self._parse_simp_lemmas())
            if self._cur().value == "at":
                self._advance_token()
                if self._cur().kind == "IDENT":
                    args.append(LeanVar(self._advance_token().value))
            return args

        # exact / apply / refine: one expression
        if tac_name in ("exact", "apply", "refine", "use", "show"):
            if not self._at_eof() and self._is_tactic_arg_start():
                args.append(self._parse_expr(stop_at={";", "|"}))
            return args

        # intro / intros: list of names
        if tac_name in ("intro", "intros"):
            while not self._at_eof() and (
                self._cur().kind == "IDENT" or self._cur().value == "_"
            ):
                args.append(LeanVar(self._advance_token().value))
            return args

        # cases / induction: scrutinee + optional 'with'
        if tac_name in ("cases", "induction"):
            if self._cur().kind == "IDENT":
                args.append(LeanVar(self._advance_token().value))
            if self._match_kw("with"):
                # skip the 'with' block content — just collect names
                while not self._at_eof():
                    if self._check_op("|"):
                        self._advance_token()
                        # collect arm names
                        while (
                            self._cur().kind == "IDENT"
                            or self._cur().value == "_"
                        ):
                            args.append(LeanVar(self._advance_token().value))
                        if self._check_op("=>") or self._check_op("⇒"):
                            self._advance_token()
                            # parse the tactic for this arm
                            inner = self._parse_tactic()
                            if inner:
                                args.append(inner)
                    else:
                        break
            return args

        # obtain / rcases: pattern + 'with' + pattern
        if tac_name in ("obtain", "rcases"):
            if self._cur().kind != "EOF" and self._is_tactic_arg_start():
                args.append(self._parse_expr(stop_at={";", "with", "|"}))
            if self._match_kw("with"):
                if self._cur().kind != "EOF" and self._is_tactic_arg_start():
                    args.append(self._parse_expr(stop_at={";", "|"}))
            return args

        # have: name? ':' type ':=' proof
        if tac_name == "have":
            name_tok = "_"
            if self._cur().kind == "IDENT" and self._peek_token(1).value == ":":
                name_tok = self._advance_token().value
            if self._match_op(":"):
                args.append(self._parse_expr(stop_at={":=", "by", ";"}))
            if self._match_op(":="):
                args.append(self._parse_expr(stop_at={";"}))
            elif self._check_kw("by"):
                args.append(self._parse_tactic_block())
            return args

        # suffices
        if tac_name == "suffices":
            if self._cur().kind != "EOF" and self._is_tactic_arg_start():
                args.append(self._parse_expr(stop_at={";", "by"}))
            if self._check_kw("by"):
                args.append(self._parse_tactic_block())
            return args

        # conv: in ... => tactics
        if tac_name == "conv":
            if self._match_kw("in"):
                args.append(self._parse_expr(stop_at={"=>", "⇒"}))
            if self._match_op("=>") or self._match_op("⇒"):
                inner = self._parse_tactic()
                if inner:
                    args.append(inner)
            return args

        # congr, ext, funext, gcongr: optional numeric arg or names
        if tac_name in ("congr", "ext", "funext", "gcongr"):
            if self._cur().kind == "NUM":
                args.append(LeanLit(value=int(self._advance_token().value)))
            while self._cur().kind == "IDENT":
                args.append(LeanVar(self._advance_token().value))
            return args

        # specialize: expression
        if tac_name == "specialize":
            if self._is_tactic_arg_start():
                args.append(self._parse_expr(stop_at={";"}))
            return args

        # by_contra: optional hypothesis name
        if tac_name == "by_contra":
            if self._cur().kind == "IDENT":
                args.append(LeanVar(self._advance_token().value))
            return args

        # rename_i: list of names
        if tac_name == "rename_i":
            while self._cur().kind == "IDENT" or self._cur().value == "_":
                args.append(LeanVar(self._advance_token().value))
            return args

        # next: names => tactic
        if tac_name == "next":
            while self._cur().kind == "IDENT" or self._cur().value == "_":
                args.append(LeanVar(self._advance_token().value))
            if self._match_op("=>") or self._match_op("⇒"):
                inner = self._parse_tactic()
                if inner:
                    args.append(inner)
            return args

        # all_goals / any_goals / first / try / repeat: inner tactic
        if tac_name in ("all_goals", "any_goals", "first", "try", "repeat"):
            inner = self._parse_tactic()
            if inner:
                args.append(inner)
            return args

        # calc: delegate to calc parser
        if tac_name == "calc":
            # re-parse as a calc expression
            calc_expr = self._parse_calc_inner()
            args.append(calc_expr)
            return args

        # Generic: try to consume a few argument tokens
        while not self._at_eof() and self._is_tactic_arg_start():
            if self._cur().value in (";", "|", ")", "}", "]"):
                break
            args.append(self._parse_atom())
            # Don't consume too many arguments for unknown tactics
            if len(args) >= 5:
                break

        return args

    def _parse_simp_lemmas(self) -> LeanExpr:
        """Parse ``[lemma1, lemma2, ...]`` list for simp-like tactics."""
        self._expect("OP", "[")
        lemmas: list[LeanExpr] = []
        while not self._at_eof() and not self._check_op("]"):
            # Allow ← / ↑ / ↓ modifiers
            if self._cur().value in ("←", "↑", "↓", "-"):
                mod = self._advance_token().value
                if self._cur().kind in ("IDENT", "KW"):
                    lemmas.append(LeanVar(mod + self._advance_token().value))
                else:
                    lemmas.append(LeanVar(mod))
            elif self._cur().kind in ("IDENT", "KW"):
                lemmas.append(LeanVar(self._advance_token().value))
            elif self._cur().kind == "NUM":
                lemmas.append(LeanLit(value=int(self._advance_token().value)))
            else:
                self._advance_token()
            if not self._match_op(","):
                break
        self._match_op("]")
        return LeanAnonymousCtor(args=lemmas)

    def _is_tactic_arg_start(self) -> bool:
        """Check if the current token can start a tactic argument."""
        tok = self._cur()
        if tok.kind == "EOF":
            return False
        if tok.value in (";", "|", ")", "}", "]", "⦄", "end"):
            return False
        if tok.kind == "KW" and tok.value in DECL_KEYWORDS:
            return False
        return True

    def _parse_calc_inner(self) -> LeanExpr:
        """Parse calc steps inside a tactic context."""
        steps: list[LeanTactic] = []
        while not self._at_eof():
            tok = self._cur()
            if tok.kind == "KW" and tok.value in (
                "end", "namespace", "section", *DECL_KEYWORDS,
            ):
                break
            if tok.value in (";", "|", ")", "}", "]"):
                break
            if tok.kind == "EOF":
                break

            step_expr = self._parse_expr(stop_at={":="})
            justification: Optional[LeanExpr] = None
            if self._match_op(":="):
                justification = self._parse_expr(stop_at={"_", ";", "|"})

            step_args: list[LeanExpr] = [step_expr]
            if justification is not None:
                step_args.append(justification)
            steps.append(LeanTactic(tactic_name="calc_step", args=step_args))

            if not self._check_op("_") and not self._check("IDENT"):
                break

        return LeanTacticBlock(tactics=steps)

    # -- utility ----------------------------------------------------------

    def _skip_balanced(self) -> None:
        """Skip a balanced bracket group ``(…)``, ``{…}``, or ``[…]``."""
        openers = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
        tok = self._cur()
        if tok.value not in openers:
            self._advance_token()
            return
        close = openers[tok.value]
        depth = 0
        while not self._at_eof():
            v = self._cur().value
            if v == tok.value:
                depth += 1
            elif v == close:
                depth -= 1
                if depth == 0:
                    self._advance_token()
                    return
            self._advance_token()


# ---------------------------------------------------------------------------
# Public convenience functions
# ---------------------------------------------------------------------------

_parser = LeanParser()


def parse_lean_file(source: str) -> LeanFile:
    """Parse a complete Lean 4 source file into a ``LeanFile`` AST."""
    return _parser.parse_file(source)


def parse_lean_decl(source: str) -> LeanDecl:
    """Parse a single Lean 4 declaration into a ``LeanDecl`` AST."""
    return _parser.parse_decl(source)


def parse_lean_expr(source: str) -> LeanExpr:
    """Parse a Lean 4 expression into a ``LeanExpr`` AST."""
    return _parser.parse_expr(source)


# ---------------------------------------------------------------------------
# Self-tests
# ---------------------------------------------------------------------------

def _print_expr_summary(expr: Optional[LeanExpr], indent: int = 0) -> str:
    """Return a short human-readable summary of an expression."""
    prefix = "  " * indent
    if expr is None:
        return f"{prefix}(none)"
    if isinstance(expr, LeanVar):
        return f"{prefix}Var({expr.name})"
    if isinstance(expr, LeanApp):
        fn_s = _print_expr_summary(expr.fn)
        args_s = ", ".join(_print_expr_summary(a) for a in expr.args)
        return f"{prefix}App({fn_s}, [{args_s}])"
    if isinstance(expr, LeanPi):
        params_s = ", ".join(f"{p.name}:{_print_expr_summary(p.type_)}" for p in expr.params)
        cod_s = _print_expr_summary(expr.codomain)
        return f"{prefix}Pi([{params_s}], {cod_s})"
    if isinstance(expr, LeanLam):
        params_s = ", ".join(f"{p.name}" for p in expr.params)
        return f"{prefix}Lam([{params_s}], ...)"
    if isinstance(expr, LeanLit):
        return f"{prefix}Lit({expr.value!r})"
    if isinstance(expr, LeanSort):
        names = {0: "Prop", 1: "Type"}
        return f"{prefix}Sort({names.get(expr.level, f'Type {expr.level - 1}')})"
    if isinstance(expr, LeanIf):
        return f"{prefix}If(...)"
    if isinstance(expr, LeanMatch):
        return f"{prefix}Match({len(expr.arms)} arms)"
    if isinstance(expr, LeanTacticBlock):
        names = [t.tactic_name for t in expr.tactics]
        return f"{prefix}TacticBlock({names})"
    if isinstance(expr, LeanHole):
        return f"{prefix}Hole"
    if isinstance(expr, LeanSorry):
        return f"{prefix}Sorry"
    if isinstance(expr, LeanProj):
        return f"{prefix}Proj({_print_expr_summary(expr.expr)}.{expr.field})"
    if isinstance(expr, LeanLet):
        return f"{prefix}Let({expr.name}, ...)"
    if isinstance(expr, LeanAnonymousCtor):
        return f"{prefix}ACtor({len(expr.args)} args)"
    if isinstance(expr, LeanDo):
        return f"{prefix}Do({len(expr.stmts)} stmts)"
    return f"{prefix}{type(expr).__name__}(...)"


def _run_self_tests() -> None:
    """Run self-tests with real Lean 4 theorem statements from Mathlib."""

    tests_passed = 0
    tests_total = 0

    def check(cond: bool, msg: str) -> None:
        nonlocal tests_passed, tests_total
        tests_total += 1
        if cond:
            tests_passed += 1
        else:
            print(f"  FAIL: {msg}")

    # ---- Test 1: List.map_map -------------------------------------------
    src1 = (
        "theorem List.map_map (f : β → γ) (g : α → β) (l : List α) "
        ": List.map f (List.map g l) = List.map (f ∘ g) l := by simp"
    )
    print("=" * 60)
    print("Test 1: List.map_map")
    d1 = parse_lean_decl(src1)
    print(f"  kind: {d1.kind}")
    print(f"  name: {d1.name}")
    print(f"  params: {[(p.name, p.binder) for p in d1.params]}")
    print(f"  return_type: {_print_expr_summary(d1.return_type)}")
    print(f"  body: {_print_expr_summary(d1.body)}")
    check(d1.kind == "theorem", "kind should be 'theorem'")
    check(d1.name == "List.map_map", "name should be 'List.map_map'")
    check(len(d1.params) == 3, "should have 3 params")
    check(d1.params[0].name == "f", "first param should be 'f'")
    check(d1.params[0].binder == "explicit", "first param should be explicit")
    check(d1.return_type is not None, "should have a return type")
    check(d1.body is not None, "should have a body")
    check(isinstance(d1.body, LeanTacticBlock), "body should be a tactic block")

    # ---- Test 2: Nat.add_comm ------------------------------------------
    src2 = "theorem Nat.add_comm (n m : Nat) : n + m = m + n := by omega"
    print("\n" + "=" * 60)
    print("Test 2: Nat.add_comm")
    d2 = parse_lean_decl(src2)
    print(f"  kind: {d2.kind}")
    print(f"  name: {d2.name}")
    print(f"  params: {[(p.name, p.binder) for p in d2.params]}")
    print(f"  return_type: {_print_expr_summary(d2.return_type)}")
    print(f"  body: {_print_expr_summary(d2.body)}")
    check(d2.kind == "theorem", "kind should be 'theorem'")
    check(d2.name == "Nat.add_comm", "name should be 'Nat.add_comm'")
    check(len(d2.params) == 2, "should have 2 params (n, m)")
    check(d2.params[0].name == "n", "first param should be 'n'")
    check(d2.params[1].name == "m", "second param should be 'm'")
    check(d2.return_type is not None, "should have a return type")
    # Return type should be an equality
    check(isinstance(d2.return_type, LeanApp), "return type should be an App (Eq)")

    # ---- Test 3: List.length_append ------------------------------------
    src3 = (
        "theorem List.length_append (l₁ l₂ : List α) "
        ": (l₁ ++ l₂).length = l₁.length + l₂.length := by simp"
    )
    print("\n" + "=" * 60)
    print("Test 3: List.length_append")
    d3 = parse_lean_decl(src3)
    print(f"  kind: {d3.kind}")
    print(f"  name: {d3.name}")
    print(f"  params: {[(p.name, p.binder) for p in d3.params]}")
    print(f"  return_type: {_print_expr_summary(d3.return_type)}")
    check(d3.kind == "theorem", "kind should be 'theorem'")
    check(d3.name == "List.length_append", "name should be 'List.length_append'")
    check(len(d3.params) == 2, "should have 2 params")
    # subscript chars should be preserved in names
    check(d3.params[0].name == "l₁", "first param should be 'l₁'")
    check(d3.params[1].name == "l₂", "second param should be 'l₂'")

    # ---- Test 4: not_not ------------------------------------------------
    src4 = "theorem not_not {p : Prop} : ¬¬p ↔ p := by simp"
    print("\n" + "=" * 60)
    print("Test 4: not_not")
    d4 = parse_lean_decl(src4)
    print(f"  kind: {d4.kind}")
    print(f"  name: {d4.name}")
    print(f"  params: {[(p.name, p.binder) for p in d4.params]}")
    print(f"  return_type: {_print_expr_summary(d4.return_type)}")
    check(d4.kind == "theorem", "kind should be 'theorem'")
    check(d4.name == "not_not", "name should be 'not_not'")
    check(len(d4.params) == 1, "should have 1 implicit param")
    check(d4.params[0].binder == "implicit", "param should be implicit")
    check(d4.params[0].name == "p", "param name should be 'p'")
    # return type involves Iff
    check(d4.return_type is not None, "should have a return type")

    # ---- Test 5: complex with multiple tactics -------------------------
    src5 = """\
theorem mul_comm_and_assoc (a b c : Nat) :
    a * b = b * a ∧ a * (b * c) = (a * b) * c := by
  constructor
  · exact Nat.mul_comm a b
  · exact Nat.mul_assoc a b c
"""
    print("\n" + "=" * 60)
    print("Test 5: mul_comm_and_assoc (multi-tactic)")
    d5 = parse_lean_decl(src5)
    print(f"  kind: {d5.kind}")
    print(f"  name: {d5.name}")
    print(f"  params: {[(p.name, p.binder) for p in d5.params]}")
    print(f"  return_type: {_print_expr_summary(d5.return_type)}")
    print(f"  body: {_print_expr_summary(d5.body)}")
    check(d5.kind == "theorem", "kind should be 'theorem'")
    check(d5.name == "mul_comm_and_assoc", "name should be 'mul_comm_and_assoc'")
    check(len(d5.params) == 3, "should have 3 params")
    check(d5.body is not None, "should have a body")
    check(isinstance(d5.body, LeanTacticBlock), "body should be a tactic block")
    if isinstance(d5.body, LeanTacticBlock):
        check(len(d5.body.tactics) >= 1, "should have at least 1 tactic")
        tac_names = [t.tactic_name for t in d5.body.tactics]
        print(f"  tactics: {tac_names}")
        check("constructor" in tac_names, "should contain 'constructor' tactic")

    # ---- Test 6: parse_file with imports and namespace ------------------
    file_src = """\
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open List Nat

namespace MyProofs

theorem simple (n : Nat) : n = n := by rfl

def double (n : Nat) : Nat := n + n

end MyProofs
"""
    print("\n" + "=" * 60)
    print("Test 6: Full file parse")
    lf = parse_lean_file(file_src)
    print(f"  imports: {lf.imports}")
    print(f"  opens: {lf.opens}")
    print(f"  namespace: {lf.namespace}")
    print(f"  declarations: {[(d.kind, d.name) for d in lf.declarations]}")
    check(len(lf.imports) == 2, "should have 2 imports")
    check("Mathlib.Data.List.Basic" in lf.imports, "first import")
    check(len(lf.opens) >= 2, "should have at least 2 opens")
    check(lf.namespace == "MyProofs", "namespace should be 'MyProofs'")
    check(len(lf.declarations) == 2, "should have 2 declarations")
    check(lf.declarations[0].kind == "theorem", "first decl is theorem")
    check(lf.declarations[1].kind == "def", "second decl is def")

    # ---- Test 7: expression parsing ------------------------------------
    print("\n" + "=" * 60)
    print("Test 7: Expression parsing")

    e1 = parse_lean_expr("fun x => x + 1")
    print(f"  fun x => x + 1  →  {_print_expr_summary(e1)}")
    check(isinstance(e1, LeanLam), "should parse as LeanLam")

    e2 = parse_lean_expr("∀ (n : Nat), n = n")
    print(f"  ∀ (n : Nat), n = n  →  {_print_expr_summary(e2)}")
    check(isinstance(e2, LeanPi), "should parse as LeanPi")

    e3 = parse_lean_expr("if x then a else b")
    print(f"  if x then a else b  →  {_print_expr_summary(e3)}")
    check(isinstance(e3, LeanIf), "should parse as LeanIf")

    e4 = parse_lean_expr("⟨a, b, c⟩")
    print(f"  ⟨a, b, c⟩  →  {_print_expr_summary(e4)}")
    check(isinstance(e4, LeanAnonymousCtor), "should parse as LeanAnonymousCtor")
    if isinstance(e4, LeanAnonymousCtor):
        check(len(e4.args) == 3, "should have 3 args")

    e5 = parse_lean_expr("Prop")
    print(f"  Prop  →  {_print_expr_summary(e5)}")
    check(isinstance(e5, LeanSort) and e5.level == 0, "Prop is Sort 0")

    e6 = parse_lean_expr("Type")
    print(f"  Type  →  {_print_expr_summary(e6)}")
    check(isinstance(e6, LeanSort) and e6.level == 1, "Type is Sort 1")

    e7 = parse_lean_expr("42")
    print(f"  42  →  {_print_expr_summary(e7)}")
    check(isinstance(e7, LeanLit) and e7.value == 42, "numeric literal")

    e8 = parse_lean_expr("sorry")
    print(f"  sorry  →  {_print_expr_summary(e8)}")
    check(isinstance(e8, LeanSorry), "sorry expression")

    e9 = parse_lean_expr("_")
    print(f"  _  →  {_print_expr_summary(e9)}")
    check(isinstance(e9, LeanHole), "hole expression")

    e10 = parse_lean_expr("a → b → c")
    print(f"  a → b → c  →  {_print_expr_summary(e10)}")
    check(isinstance(e10, LeanPi), "arrow type")

    e11 = parse_lean_expr("¬p")
    print(f"  ¬p  →  {_print_expr_summary(e11)}")
    check(isinstance(e11, LeanApp), "negation")
    if isinstance(e11, LeanApp):
        check(isinstance(e11.fn, LeanVar) and e11.fn.name == "Not", "negation fn")

    # ---- Test 8: tokeniser edge cases -----------------------------------
    print("\n" + "=" * 60)
    print("Test 8: Tokeniser edge cases")

    toks = _tokenize("-- this is a comment\nfoo")
    non_eof = [t for t in toks if t.kind != "EOF"]
    print(f"  line comment: {[(t.kind, t.value) for t in non_eof]}")
    check(len(non_eof) == 1 and non_eof[0].value == "foo",
          "line comment should be skipped")

    toks2 = _tokenize("/- nested /- comment -/ -/ bar")
    non_eof2 = [t for t in toks2 if t.kind != "EOF"]
    print(f"  nested block comment: {[(t.kind, t.value) for t in non_eof2]}")
    check(len(non_eof2) == 1 and non_eof2[0].value == "bar",
          "nested block comment should be skipped")

    toks3 = _tokenize('/-- doc comment -/ baz')
    non_eof3 = [t for t in toks3 if t.kind != "EOF"]
    print(f"  doc comment: {[(t.kind, t.value) for t in non_eof3]}")
    has_doc = any(t.kind == "DOC_COMMENT" for t in non_eof3)
    check(has_doc, "doc comment should produce DOC_COMMENT token")

    toks4 = _tokenize('"hello world"')
    non_eof4 = [t for t in toks4 if t.kind != "EOF"]
    print(f"  string literal: {[(t.kind, t.value) for t in non_eof4]}")
    check(
        len(non_eof4) == 1 and non_eof4[0].kind == "STRING",
        "should tokenise string literal",
    )

    toks5 = _tokenize("0xFF 0b1010 123_456")
    non_eof5 = [t for t in toks5 if t.kind != "EOF"]
    print(f"  numeric literals: {[(t.kind, t.value) for t in non_eof5]}")
    check(len(non_eof5) == 3, "should tokenise 3 numeric literals")

    # ---- Test 9: inductive parsing -------------------------------------
    src9 = """\
inductive MyBool where
  | true : MyBool
  | false : MyBool
"""
    print("\n" + "=" * 60)
    print("Test 9: Inductive declaration")
    d9 = parse_lean_decl(src9)
    print(f"  kind: {d9.kind}")
    print(f"  name: {d9.name}")
    check(d9.kind == "inductive", "kind should be 'inductive'")
    check(d9.name == "MyBool", "name should be 'MyBool'")
    check(d9.body is not None, "should have a body with constructors")

    # ---- Test 10: structure parsing ------------------------------------
    src10 = """\
structure Point (α : Type) where
  x : α
  y : α
"""
    print("\n" + "=" * 60)
    print("Test 10: Structure declaration")
    d10 = parse_lean_decl(src10)
    print(f"  kind: {d10.kind}")
    print(f"  name: {d10.name}")
    print(f"  params: {[(p.name, p.binder) for p in d10.params]}")
    check(d10.kind == "structure", "kind should be 'structure'")
    check(d10.name == "Point", "name should be 'Point'")
    check(len(d10.params) == 1, "should have 1 type parameter")
    check(d10.body is not None, "should have a body with fields")

    # ---- Test 11: attributes -------------------------------------------
    src11 = "@[simp, ext] theorem foo : True := trivial"
    print("\n" + "=" * 60)
    print("Test 11: Attributes")
    d11 = parse_lean_decl(src11)
    print(f"  kind: {d11.kind}")
    print(f"  name: {d11.name}")
    print(f"  attributes: {d11.attributes}")
    check(d11.kind == "theorem", "kind should be 'theorem'")
    check("simp" in d11.attributes, "should have 'simp' attribute")
    check("ext" in d11.attributes, "should have 'ext' attribute")

    # ---- Test 12: let expression ----------------------------------------
    src12 = "let x := 5; x + x"
    print("\n" + "=" * 60)
    print("Test 12: Let expression")
    e12 = parse_lean_expr(src12)
    print(f"  {_print_expr_summary(e12)}")
    check(isinstance(e12, LeanLet), "should be a LeanLet")
    if isinstance(e12, LeanLet):
        check(e12.name == "x", "let name should be 'x'")

    # ---- Test 13: match expression --------------------------------------
    src13 = """\
match n with
| 0 => 1
| n + 1 => n
"""
    print("\n" + "=" * 60)
    print("Test 13: Match expression")
    e13 = parse_lean_expr(src13)
    print(f"  {_print_expr_summary(e13)}")
    check(isinstance(e13, LeanMatch), "should be a LeanMatch")
    if isinstance(e13, LeanMatch):
        check(len(e13.arms) == 2, "should have 2 match arms")

    # ---- Summary --------------------------------------------------------
    print("\n" + "=" * 60)
    print(f"Results: {tests_passed}/{tests_total} checks passed")
    if tests_passed == tests_total:
        print("All lean_parser self-tests passed!")
    else:
        print(f"WARNING: {tests_total - tests_passed} check(s) failed")
        sys.exit(1)


if __name__ == "__main__":
    _run_self_tests()
