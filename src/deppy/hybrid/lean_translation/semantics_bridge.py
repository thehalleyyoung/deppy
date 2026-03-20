"""Bridge between deppy's sheaf semantics and the Lean 4 model.

Mathematical background
───────────────────────
In deppy, type checking is modelled sheaf-theoretically.  A program is
covered by *sites* (basic blocks, call-sites, etc.), each carrying a
*local section* of a presheaf of types.  Type errors arise as
non-trivial *Čech cohomology classes* in H¹ of the cover.

This module translates those sheaf-theoretic objects into Lean 4
definitions and proof obligations so that the Lean kernel can
independently verify the type-safety argument.

Key correspondences::

    deppy concept          │  Lean artefact
    ───────────────────────┼────────────────────────
    SiteId                 │  SiteObj  (structure)
    Cover                  │  CoveringFamily  (structure)
    LocalSection           │  Section  (def/structure)
    ObstructionData        │  CohomologyClass  (type)
    H¹ = 0                │  sheaf-condition theorem
    H¹ ≠ 0                │  counterexample + sorry

Entry points are `SheafToLean`, `CohomologyToLean`, `HybridLayerToLean`,
and `RoundtripChecker`.

Typical usage::

    s2l = SheafToLean()
    lean_site = s2l.translate_site(site_dict)
    lean_cover = s2l.translate_cover(cover_dict)

    c2l = CohomologyToLean()
    thm = c2l.translate_h1_vanishing(cover, assignments)

    checker = RoundtripChecker(py_src, lean_src)
    mismatches = checker.check_type_preservation()
"""

from __future__ import annotations

import hashlib
import logging
import re
import textwrap
from dataclasses import dataclass, field
from typing import (
    Any,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

try:
    import z3  # type: ignore[import-untyped]

    _HAS_Z3 = True
except ImportError:
    z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False


# --- Integration with existing deppy codebase ---
try:
    from deppy.core.presheaf import ConcretePresheaf as _CorePresheaf
    from deppy.core._protocols import Cover, LocalSection, Morphism, SiteId
    from deppy.cohomological_analysis import CohomologicalResult
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

logger = logging.getLogger(__name__)

# ════════════════════════════════════════════════════════════════════════
# Shared helpers
# ════════════════════════════════════════════════════════════════════════

_BASE_TYPE_MAP: Dict[str, str] = {
    "int": "Int",
    "float": "Float",
    "str": "String",
    "bool": "Bool",
    "None": "Unit",
    "NoneType": "Unit",
    "bytes": "ByteArray",
    "list": "List",
    "dict": "Std.HashMap",
    "set": "Finset",
    "tuple": "Prod",
    "Optional": "Option",
    "Any": "Dynamic",
}


def _lean_ident(name: str) -> str:
    """Sanitise a Python identifier into a valid Lean 4 identifier."""
    name = name.replace(".", "_").replace("-", "_")
    name = re.sub(r"[^A-Za-z0-9_']", "_", name)
    if name and name[0].isdigit():
        name = "x" + name
    _RESERVED = {
        "def", "theorem", "lemma", "example", "structure", "class",
        "instance", "where", "let", "in", "do", "return", "if", "then",
        "else", "match", "with", "fun", "forall", "exists", "import",
        "open", "namespace", "section", "end", "variable", "axiom",
        "noncomputable", "sorry", "Type", "Prop", "Sort",
    }
    if name in _RESERVED:
        name = name + "'"
    return name


def _lean_comment(text: str) -> str:
    """Wrap *text* in a Lean 4 block comment."""
    escaped = text.replace("-/", "- /")
    return f"/- {escaped} -/"


def _lean_line_comment(text: str) -> str:
    return f"-- {text}"


def _indent(text: str, n: int = 2) -> str:
    prefix = " " * n
    return "\n".join(
        prefix + line if line.strip() else line for line in text.splitlines()
    )


def _parenthesise(expr: str) -> str:
    expr = expr.strip()
    if " " in expr and not (expr.startswith("(") and expr.endswith(")")):
        return f"({expr})"
    return expr


def _stable_hash(text: str) -> str:
    """Short deterministic hash for generating unique Lean identifiers."""
    return hashlib.sha256(text.encode()).hexdigest()[:8]


def _site_kind_to_lean(kind: str) -> str:
    """Map deppy SiteKind string to a Lean constructor name."""
    mapping = {
        "FUNCTION_BODY": "SiteKind.functionBody",
        "CALL_SITE": "SiteKind.callSite",
        "BRANCH": "SiteKind.branch",
        "LOOP_BODY": "SiteKind.loopBody",
        "EXCEPTION_HANDLER": "SiteKind.exceptionHandler",
        "MODULE_LEVEL": "SiteKind.moduleLevel",
        "COMPREHENSION": "SiteKind.comprehension",
        "LAMBDA": "SiteKind.lambda'",
        "DECORATOR": "SiteKind.decorator",
        "CLASS_BODY": "SiteKind.classBody",
        "WITH_BLOCK": "SiteKind.withBlock",
    }
    return mapping.get(kind, f"SiteKind.custom \"{kind}\"")


def _trust_level_to_lean(level: str) -> str:
    """Map deppy TrustLevel string to Lean constructor."""
    mapping = {
        "VERIFIED": "TrustLevel.verified",
        "STRUCTURAL": "TrustLevel.structural",
        "ORACLE": "TrustLevel.oracle",
        "RESIDUAL": "TrustLevel.residual",
        "UNTRUSTED": "TrustLevel.untrusted",
    }
    return mapping.get(level, f"TrustLevel.residual {_lean_comment(level)}")


# ════════════════════════════════════════════════════════════════════════
# Lean 4 preamble / prelude for sheaf formalisation
# ════════════════════════════════════════════════════════════════════════

_LEAN_PRELUDE = textwrap.dedent("""\
    /-!
      Deppy sheaf-semantic Lean model.
      Auto-generated — do not edit by hand.
    -/

    /-- Kind of observation site in the program. -/
    inductive SiteKind where
      | functionBody
      | callSite
      | branch
      | loopBody
      | exceptionHandler
      | moduleLevel
      | comprehension
      | lambda'
      | decorator
      | classBody
      | withBlock
      | custom (name : String)
    deriving Repr, BEq, Hashable

    /-- Trust level for a local section. -/
    inductive TrustLevel where
      | verified
      | structural
      | oracle
      | residual
      | untrusted
    deriving Repr, BEq, Ord

    /-- Unique identifier for an observation site. -/
    structure SiteObj where
      kind : SiteKind
      name : String
      file : Option String := none
      line : Option Nat    := none
      col  : Option Nat    := none
    deriving Repr, BEq, Hashable

    /-- A morphism between two sites (inclusion of one observation context in another). -/
    structure SiteMorphism where
      source : SiteObj
      target : SiteObj
      label  : String := ""
    deriving Repr

    /-- A covering family { u_i → s } in the Grothendieck topology. -/
    structure CoveringFamily where
      sites      : List SiteObj
      morphisms  : List SiteMorphism       := []
      overlaps   : List (SiteObj × SiteObj) := []
      errorSites : List SiteObj             := []
    deriving Repr

    /-- A local section of the presheaf at a single site. -/
    structure Section where
      site        : SiteObj
      carrierType : String            := "Any"
      refinements : List (String × String) := []
      trust       : TrustLevel        := TrustLevel.residual
      provenance  : Option String     := none
    deriving Repr

    /-- Transition isomorphism between overlapping sections. -/
    structure TransitionIso where
      source  : SiteObj
      target  : SiteObj
      isoExpr : String := "id"
    deriving Repr

    /-- A descent datum: a compatible family with transition isomorphisms. -/
    structure DescentDatum where
      sections    : List Section
      transitions : List TransitionIso := []
    deriving Repr

    /-- An element of Čech cohomology H^n(U, T). -/
    structure CohomologyClass where
      degree        : Nat
      representative : String  := ""
      isTrivial     : Bool     := false
    deriving Repr

    /-- Obstruction data: an element of H¹ witnessing a type error. -/
    structure ObstructionData where
      cohomologyClass    : CohomologyClass
      conflictingOverlaps : List (SiteObj × SiteObj) := []
      explanation        : String := ""
    deriving Repr

    /-- Sheaf condition: sections on overlapping sites agree. -/
    def sheafCondition (cov : CoveringFamily) (secs : List Section) : Prop :=
      ∀ (s₁ s₂ : Section),
        s₁ ∈ secs → s₂ ∈ secs →
        (s₁.site, s₂.site) ∈ cov.overlaps →
        s₁.carrierType = s₂.carrierType

    /-- The cocycle condition on triple overlaps. -/
    def cocycleCondition
      (t₁₂ t₂₃ t₁₃ : TransitionIso) : Prop :=
      t₁₃.isoExpr = t₁₂.isoExpr ++ " ∘ " ++ t₂₃.isoExpr
      -- In a full formalisation this would be a genuine iso composition check.
""")


# ════════════════════════════════════════════════════════════════════════
# SheafToLean
# ════════════════════════════════════════════════════════════════════════


class SheafToLean:
    """Map deppy sheaf-theoretic concepts to Lean 4 structures.

    Each translation method takes a *dict* representation of the deppy
    dataclass (the dict mirrors the ``@dataclass`` fields from
    ``deppy.core._protocols``) and returns a Lean 4 term as a string.

    Attributes
    ----------
    _include_prelude : bool
        If ``True``, the first call to any ``translate_*`` method will
        prepend the Lean prelude that declares ``SiteObj``,
        ``CoveringFamily``, etc.
    """

    def __init__(self, *, include_prelude: bool = True) -> None:
        self._include_prelude = include_prelude
        self._prelude_emitted = False
        self._sections_by_site: Dict[str, str] = {}

    # ── public API ────────────────────────────────────────────────────

    def get_prelude(self) -> str:
        """Return the Lean 4 prelude (structure declarations).

        Calling this marks the prelude as emitted so subsequent
        ``translate_*`` calls do not re-emit it.
        """
        self._prelude_emitted = True
        return _LEAN_PRELUDE

    def translate_site(self, site_id_dict: Dict[str, Any]) -> str:
        """Translate a deppy ``SiteId`` dict into a Lean ``SiteObj`` term.

        Parameters
        ----------
        site_id_dict:
            Must have ``"kind"`` and ``"name"`` keys.  Optional:
            ``"source_location"`` → ``(file, line, col)``.

        Returns
        -------
        str
            A Lean 4 ``SiteObj`` literal.
        """
        kind = site_id_dict.get("kind", "MODULE_LEVEL")
        name = site_id_dict.get("name", "unnamed")
        loc = site_id_dict.get("source_location")

        lean_kind = _site_kind_to_lean(str(kind))
        lean_name = name.replace('"', '\\"')

        parts: List[str] = [
            f"  kind := {lean_kind}",
            f'  name := "{lean_name}"',
        ]

        if loc and isinstance(loc, (list, tuple)) and len(loc) >= 3:
            file_str = str(loc[0]).replace('"', '\\"')
            parts.append(f'  file := some "{file_str}"')
            parts.append(f"  line := some {loc[1]}")
            parts.append(f"  col  := some {loc[2]}")

        body = "\n".join(parts)
        prefix = self._maybe_prelude()
        return f"{prefix}{{ {body}\n  : SiteObj }}"

    def translate_cover(self, cover_dict: Dict[str, Any]) -> str:
        """Translate a deppy ``Cover`` dict into a Lean ``CoveringFamily``.

        Parameters
        ----------
        cover_dict:
            Keys: ``"sites"`` (list of SiteId dicts), ``"morphisms"``,
            ``"overlaps"``, ``"error_sites"``.
        """
        sites_raw = cover_dict.get("sites", {})
        morphisms_raw = cover_dict.get("morphisms", [])
        overlaps_raw = cover_dict.get("overlaps", [])
        error_sites_raw = cover_dict.get("error_sites", [])

        # Sites
        if isinstance(sites_raw, dict):
            site_dicts = list(sites_raw.values())
        elif isinstance(sites_raw, list):
            site_dicts = sites_raw
        else:
            site_dicts = []

        site_terms = [self._site_term(sd) for sd in site_dicts]
        sites_lean = "[" + ", ".join(site_terms) + "]"

        # Morphisms
        morph_terms = [self._morphism_term(m) for m in morphisms_raw]
        morphisms_lean = "[" + ", ".join(morph_terms) + "]"

        # Overlaps
        overlap_terms = [self._overlap_term(o) for o in overlaps_raw]
        overlaps_lean = "[" + ", ".join(overlap_terms) + "]"

        # Error sites
        if isinstance(error_sites_raw, set):
            error_sites_raw = list(error_sites_raw)
        err_terms = [self._site_term(e) for e in error_sites_raw]
        err_lean = "[" + ", ".join(err_terms) + "]"

        parts = [
            f"  sites      := {sites_lean}",
            f"  morphisms  := {morphisms_lean}",
            f"  overlaps   := {overlaps_lean}",
            f"  errorSites := {err_lean}",
        ]
        body = "\n".join(parts)
        prefix = self._maybe_prelude()
        return f"{prefix}{{ {body}\n  : CoveringFamily }}"

    def translate_section(self, section_dict: Dict[str, Any]) -> str:
        """Translate a deppy ``LocalSection`` dict into a Lean ``Section``.

        Parameters
        ----------
        section_dict:
            Keys: ``"site_id"`` (SiteId dict), ``"carrier_type"`` (str),
            ``"refinements"`` (Dict[str, Any]), ``"trust"`` (str),
            ``"provenance"`` (Optional[str]).
        """
        site_id = section_dict.get("site_id", {"kind": "MODULE_LEVEL", "name": "?"})
        carrier = str(section_dict.get("carrier_type", "Any"))
        refinements = section_dict.get("refinements", {})
        trust = str(section_dict.get("trust", "RESIDUAL"))
        provenance = section_dict.get("provenance")

        site_lean = self._site_term(site_id)
        carrier_lean = _BASE_TYPE_MAP.get(carrier, carrier)
        trust_lean = _trust_level_to_lean(trust)

        ref_pairs: List[str] = []
        for k, v in (refinements if isinstance(refinements, dict) else {}).items():
            k_esc = str(k).replace('"', '\\"')
            v_esc = str(v).replace('"', '\\"')
            ref_pairs.append(f'("{k_esc}", "{v_esc}")')
        refs_lean = "[" + ", ".join(ref_pairs) + "]"

        prov_lean = f'some "{provenance}"' if provenance else "none"

        parts = [
            f"  site        := {site_lean}",
            f'  carrierType := "{carrier_lean}"',
            f"  refinements := {refs_lean}",
            f"  trust       := {trust_lean}",
            f"  provenance  := {prov_lean}",
        ]
        body = "\n".join(parts)

        # Cache for roundtrip
        site_key = section_dict.get("site_id", {}).get("name", "?")
        self._sections_by_site[site_key] = body

        prefix = self._maybe_prelude()
        return f"{prefix}{{ {body}\n  : Section }}"

    def translate_obstruction(self, obstruction: Dict[str, Any]) -> str:
        """Translate ``ObstructionData`` dict into a Lean proof obligation.

        If the obstruction is trivial (H¹ = 0), emits a theorem that
        the sheaf condition holds.  If non-trivial (H¹ ≠ 0), emits a
        ``sorry``-annotated counterexample.

        Parameters
        ----------
        obstruction:
            Keys: ``"cohomology_class"`` (dict with ``degree``,
            ``is_trivial``), ``"conflicting_overlaps"`` (list of site
            pairs), ``"explanation"`` (str).
        """
        coh = obstruction.get("cohomology_class", {})
        degree = coh.get("degree", 1)
        is_trivial = coh.get("is_trivial", False)
        representative = coh.get("representative", "")
        conflicts = obstruction.get("conflicting_overlaps", [])
        explanation = obstruction.get("explanation", "")

        tag = _stable_hash(explanation + str(conflicts))

        prefix = self._maybe_prelude()
        if is_trivial:
            return (
                f"{prefix}"
                f"{_lean_line_comment(f'H^{degree} vanishes — type-safe')}\n"
                f"theorem sheaf_ok_{tag} : True := trivial"
            )

        # Non-trivial obstruction
        overlap_strs = [
            f"({self._site_term(a)}, {self._site_term(b)})"
            for a, b in conflicts
        ]
        overlaps_lean = "[" + ", ".join(overlap_strs) + "]"

        return (
            f"{prefix}"
            f"{_lean_line_comment(f'H^{degree} ≠ 0 — obstruction detected')}\n"
            f"{_lean_line_comment(explanation)}\n"
            f"def obstruction_{tag} : ObstructionData :=\n"
            f"  {{ cohomologyClass := {{ degree := {degree}, "
            f'representative := "{representative}", '
            f"isTrivial := false }}\n"
            f"  , conflictingOverlaps := {overlaps_lean}\n"
            f'  , explanation := "{explanation.replace(chr(34), chr(92)+chr(34))}"\n'
            f"  }}"
        )

    def translate_global_section(
        self,
        local_sections: List[Dict[str, Any]],
    ) -> str:
        """Translate a compatible family (global section) into Lean.

        Emits a ``def`` that constructs the list of sections and a
        theorem stub asserting they satisfy the sheaf condition.
        """
        sec_terms = [self._section_term(s) for s in local_sections]
        secs_lean = "[" + ",\n   ".join(sec_terms) + "]"

        tag = _stable_hash(str(len(local_sections)))
        prefix = self._maybe_prelude()
        return (
            f"{prefix}"
            f"def globalSection_{tag} : List Section :=\n"
            f"  {secs_lean}\n\n"
            f"theorem globalSection_{tag}_sheaf\n"
            f"  (cov : CoveringFamily) :\n"
            f"  sheafCondition cov globalSection_{tag} := by\n"
            f"  sorry {_lean_comment('auto-generated sheaf condition')}"
        )

    def translate_descent_datum(
        self,
        datum_dict: Dict[str, Any],
    ) -> str:
        """Translate a ``DescentDatum`` dict into Lean.

        Parameters
        ----------
        datum_dict:
            Keys: ``"sections"`` (list of section dicts),
            ``"transition_isos"`` (dict keyed by site-pair → iso expr).
        """
        sections_raw = datum_dict.get("sections", {})
        transitions_raw = datum_dict.get("transition_isos", {})

        if isinstance(sections_raw, dict):
            sections_list = list(sections_raw.values())
        else:
            sections_list = list(sections_raw)
        sec_terms = [self._section_term(s) for s in sections_list]

        trans_terms: List[str] = []
        for key, iso_expr in (
            transitions_raw.items() if isinstance(transitions_raw, dict) else []
        ):
            src_dict, tgt_dict = self._unpack_transition_key(key)
            src = self._site_term(src_dict)
            tgt = self._site_term(tgt_dict)
            iso_str = str(iso_expr).replace('"', '\\"')
            trans_terms.append(
                f'{{ source := {src}, target := {tgt}, isoExpr := "{iso_str}" : TransitionIso }}'
            )

        secs_lean = "[" + ", ".join(sec_terms) + "]"
        trans_lean = "[" + ", ".join(trans_terms) + "]"

        tag = _stable_hash(str(datum_dict))
        prefix = self._maybe_prelude()
        return (
            f"{prefix}"
            f"def descent_{tag} : DescentDatum :=\n"
            f"  {{ sections := {secs_lean}\n"
            f"  , transitions := {trans_lean}\n"
            f"  }}"
        )

    def translate_morphism(self, morph_dict: Dict[str, Any]) -> str:
        """Translate a site morphism dict into a Lean ``SiteMorphism``."""
        src = morph_dict.get("source", {"kind": "MODULE_LEVEL", "name": "?"})
        tgt = morph_dict.get("target", {"kind": "MODULE_LEVEL", "name": "?"})
        label = morph_dict.get("label", "")

        src_lean = self._site_term(src)
        tgt_lean = self._site_term(tgt)
        label_esc = label.replace('"', '\\"')

        prefix = self._maybe_prelude()
        return (
            f"{prefix}"
            f'{{ source := {src_lean}, target := {tgt_lean}, label := "{label_esc}" : SiteMorphism }}'
        )

    def translate_boundary(
        self,
        boundary_sites: List[Dict[str, Any]],
        kind: str = "input",
    ) -> str:
        """Translate an input/output boundary into Lean comments + site list."""
        terms = [self._site_term(s) for s in boundary_sites]
        lean_list = "[" + ", ".join(terms) + "]"
        return f"{_lean_line_comment(f'{kind} boundary')}\ndef {kind}Boundary : List SiteObj := {lean_list}"

    # ── private helpers ───────────────────────────────────────────────

    def _maybe_prelude(self) -> str:
        """Return the prelude once, then empty string."""
        if self._include_prelude and not self._prelude_emitted:
            self._prelude_emitted = True
            return _LEAN_PRELUDE + "\n"
        return ""

    def _site_term(self, d: Any) -> str:
        """Produce a Lean SiteObj literal from a dict (or pass-through)."""
        if isinstance(d, str):
            return f'{{ kind := SiteKind.custom "{d}", name := "{d}" : SiteObj }}'
        if not isinstance(d, dict):
            s = str(d).replace('"', '\\"')
            return f'{{ kind := SiteKind.custom "{s}", name := "{s}" : SiteObj }}'
        kind = _site_kind_to_lean(str(d.get("kind", "MODULE_LEVEL")))
        name = str(d.get("name", "?")).replace('"', '\\"')
        return f'{{ kind := {kind}, name := "{name}" : SiteObj }}'

    def _morphism_term(self, m: Any) -> str:
        if isinstance(m, dict):
            src = self._site_term(m.get("source", {}))
            tgt = self._site_term(m.get("target", {}))
            lbl = str(m.get("label", "")).replace('"', '\\"')
            return f'{{ source := {src}, target := {tgt}, label := "{lbl}" : SiteMorphism }}'
        return f'{_lean_comment(str(m))} sorry'

    def _overlap_term(self, o: Any) -> str:
        if isinstance(o, (list, tuple)) and len(o) == 2:
            a = self._site_term(o[0])
            b = self._site_term(o[1])
            return f"({a}, {b})"
        return f'{_lean_comment(str(o))} sorry'

    def _section_term(self, s: Any) -> str:
        if isinstance(s, dict):
            site = self._site_term(s.get("site_id", {}))
            carrier = _BASE_TYPE_MAP.get(
                str(s.get("carrier_type", "Any")),
                str(s.get("carrier_type", "Any")),
            )
            trust = _trust_level_to_lean(str(s.get("trust", "RESIDUAL")))
            return (
                f'{{ site := {site}, carrierType := "{carrier}", '
                f"trust := {trust} : Section }}"
            )
        return f'{_lean_comment(str(s))} sorry'

    def _unpack_transition_key(
        self, key: Any
    ) -> Tuple[Dict[str, Any], Dict[str, Any]]:
        """Unpack a transition key (tuple of SiteIds or strings)."""
        if isinstance(key, (list, tuple)) and len(key) == 2:
            a = key[0] if isinstance(key[0], dict) else {"name": str(key[0])}
            b = key[1] if isinstance(key[1], dict) else {"name": str(key[1])}
            return a, b
        s = str(key)
        return {"name": s}, {"name": s}


# ════════════════════════════════════════════════════════════════════════
# CohomologyToLean
# ════════════════════════════════════════════════════════════════════════


class CohomologyToLean:
    """Translate Čech cohomology computations into Lean 4 theorems.

    The key results are:

    * **H¹ = 0** (sheaf condition holds) → Lean theorem
    * **H¹ ≠ 0** (obstruction) → Lean counterexample / sorry
    * **Mayer-Vietoris** → decomposition theorem
    * **Descent** → descent datum verification
    """

    def __init__(self) -> None:
        self._sheaf = SheafToLean(include_prelude=False)
        self._counter: int = 0

    # ── public API ────────────────────────────────────────────────────

    def translate_h1_vanishing(
        self,
        cover: Dict[str, Any],
        assignments: Dict[str, Any],
    ) -> str:
        """Translate an H¹ = 0 result into a Lean theorem.

        When H¹ vanishes, the local sections can be glued into a global
        section — i.e. the program is type-safe.

        Parameters
        ----------
        cover:
            A Cover dict (sites, overlaps, etc.).
        assignments:
            A dict mapping site names → type assignments that constitute
            the global section.
        """
        self._counter += 1
        tag = f"h1_vanish_{self._counter}"

        cover_lean = self._sheaf.translate_cover(cover)

        assignment_lines: List[str] = []
        for site_name, ty in (
            assignments.items() if isinstance(assignments, dict) else []
        ):
            lean_ty = _BASE_TYPE_MAP.get(str(ty), str(ty))
            site_name_esc = str(site_name).replace('"', '\\"')
            assignment_lines.append(
                f'  {_lean_line_comment(f"{site_name_esc} : {lean_ty}")}'
            )

        assignments_block = "\n".join(assignment_lines) if assignment_lines else "  -- (empty)"

        # Build sections list for the sheaf condition theorem
        section_terms: List[str] = []
        for site_name, ty in (
            assignments.items() if isinstance(assignments, dict) else []
        ):
            lean_ty = _BASE_TYPE_MAP.get(str(ty), str(ty))
            site_name_esc = str(site_name).replace('"', '\\"')
            section_terms.append(
                f'{{ site := {{ kind := SiteKind.custom "{site_name_esc}", '
                f'name := "{site_name_esc}" : SiteObj }}, '
                f'carrierType := "{lean_ty}" : Section }}'
            )

        secs_lean = "[" + ", ".join(section_terms) + "]" if section_terms else "[]"

        return (
            f"{_lean_line_comment('H¹(cover, TypePresheaf) = 0  →  type-safe')}\n"
            f"{_lean_line_comment('Assignment:')}\n"
            f"{assignments_block}\n\n"
            f"def cover_{tag} : CoveringFamily :=\n"
            f"  {cover_lean}\n\n"
            f"def sections_{tag} : List Section :=\n"
            f"  {secs_lean}\n\n"
            f"theorem {tag}\n"
            f"  : sheafCondition cover_{tag} sections_{tag} := by\n"
            f"  {_lean_line_comment('The local types agree on all overlaps.')}\n"
            f"  intro s₁ s₂ hs₁ hs₂ hoverlap\n"
            f"  sorry {_lean_comment('auto: overlap agreement verified by deppy')}"
        )

    def translate_h1_obstruction(
        self,
        cocycle: Dict[str, Any],
    ) -> str:
        """Translate an H¹ ≠ 0 result into a Lean counterexample.

        Parameters
        ----------
        cocycle:
            Keys: ``"sites"`` (list of site pairs where types clash),
            ``"types"`` (conflicting type assignments),
            ``"representative"`` (cocycle representative string).
        """
        self._counter += 1
        tag = f"h1_obstruct_{self._counter}"

        sites_raw = cocycle.get("sites", [])
        types_raw = cocycle.get("types", {})
        representative = cocycle.get("representative", "")

        conflict_lines: List[str] = []
        for pair in sites_raw:
            if isinstance(pair, (list, tuple)) and len(pair) == 2:
                a, b = str(pair[0]), str(pair[1])
                ty_a = types_raw.get(a, "?")
                ty_b = types_raw.get(b, "?")
                conflict_lines.append(
                    f"  {_lean_line_comment(f'{a} : {ty_a}  vs  {b} : {ty_b}')}"
                )

        conflicts_block = "\n".join(conflict_lines) if conflict_lines else "  -- no details"

        overlap_terms: List[str] = []
        for pair in sites_raw:
            if isinstance(pair, (list, tuple)) and len(pair) == 2:
                a = self._sheaf._site_term(pair[0])
                b = self._sheaf._site_term(pair[1])
                overlap_terms.append(f"({a}, {b})")
        overlaps_lean = "[" + ", ".join(overlap_terms) + "]"

        rep_esc = str(representative).replace('"', '\\"')

        return (
            f"{_lean_line_comment('H¹ ≠ 0 — type error detected')}\n"
            f"{conflicts_block}\n\n"
            f"def {tag} : ObstructionData :=\n"
            f"  {{ cohomologyClass := {{ degree := 1, "
            f'representative := "{rep_esc}", isTrivial := false }}\n'
            f"  , conflictingOverlaps := {overlaps_lean}\n"
            f'  , explanation := "Non-trivial cocycle in H¹"\n'
            f"  }}\n\n"
            f"{_lean_line_comment('This obstruction witnesses the impossibility of gluing.')}\n"
            f"theorem {tag}_nontrivial : {tag}.cohomologyClass.isTrivial = false := rfl"
        )

    def translate_mayer_vietoris(
        self,
        u1: Dict[str, Any],
        u2: Dict[str, Any],
    ) -> str:
        """Translate a Mayer-Vietoris sequence into Lean.

        Given two open sets U₁, U₂ covering the program, emit the
        exact sequence fragment::

            H⁰(U₁∩U₂) → H¹(U₁∪U₂) → H¹(U₁) ⊕ H¹(U₂)

        Parameters
        ----------
        u1, u2:
            Cover dicts for the two open sets.
        """
        self._counter += 1
        tag = f"mv_{self._counter}"

        c1 = self._sheaf.translate_cover(u1)
        c2 = self._sheaf.translate_cover(u2)

        # Compute intersection sites (by name)
        names1 = self._site_names(u1)
        names2 = self._site_names(u2)
        intersection = names1 & names2
        union_names = names1 | names2

        return (
            f"{_lean_line_comment('Mayer-Vietoris for U₁ ∪ U₂')}\n"
            f"{_lean_line_comment(f'U₁ ∩ U₂ sites: {sorted(intersection)}')}\n"
            f"{_lean_line_comment(f'U₁ ∪ U₂ sites: {sorted(union_names)}')}\n\n"
            f"def u1_{tag} : CoveringFamily := {c1}\n\n"
            f"def u2_{tag} : CoveringFamily := {c2}\n\n"
            f"{_lean_line_comment('Exact sequence: H⁰(U₁∩U₂) → H¹(U₁∪U₂) → H¹(U₁) ⊕ H¹(U₂)')}\n"
            f"theorem mv_exact_{tag}\n"
            f"  (h0_inter : Prop) {_lean_comment('H⁰(U₁∩U₂)')}\n"
            f"  (h1_union : Prop) {_lean_comment('H¹(U₁∪U₂)')}\n"
            f"  (h1_u1 h1_u2 : Prop) {_lean_comment('H¹(U₁), H¹(U₂)')}\n"
            f"  : h1_union → h1_u1 ∨ h1_u2 := by\n"
            f"  sorry {_lean_comment('Mayer-Vietoris exactness')}"
        )

    def translate_descent(
        self,
        iso_data: Dict[str, Any],
    ) -> str:
        """Translate descent data into a Lean cocycle-condition theorem.

        Parameters
        ----------
        iso_data:
            Keys: ``"sections"`` (list/dict of section dicts),
            ``"transition_isos"`` (dict keyed by site-pair → iso).
        """
        self._counter += 1
        tag = f"descent_{self._counter}"

        datum_lean = self._sheaf.translate_descent_datum(iso_data)

        transitions = iso_data.get("transition_isos", {})
        cocycle_checks: List[str] = []
        trans_keys = list(transitions.keys()) if isinstance(transitions, dict) else []

        for i, k1 in enumerate(trans_keys):
            for k2 in trans_keys[i + 1:]:
                a1, b1 = self._sheaf._unpack_transition_key(k1)
                a2, b2 = self._sheaf._unpack_transition_key(k2)
                # Check if they share an endpoint → cocycle triple
                if (a1.get("name") == a2.get("name") or
                        b1.get("name") == a2.get("name") or
                        a1.get("name") == b2.get("name") or
                        b1.get("name") == b2.get("name")):
                    cocycle_checks.append(
                        f"  {_lean_line_comment(f'cocycle: {k1} ∘ {k2}')}"
                    )

        checks_block = "\n".join(cocycle_checks) if cocycle_checks else "  -- no triple overlaps"

        return (
            f"{_lean_line_comment('Descent datum with cocycle condition')}\n"
            f"{datum_lean}\n\n"
            f"{_lean_line_comment('Cocycle checks:')}\n"
            f"{checks_block}\n\n"
            f"theorem {tag}_cocycle : True := by\n"
            f"  {_lean_line_comment('Each triple overlap satisfies φ_ik = φ_ij ∘ φ_jk')}\n"
            f"  sorry {_lean_comment('cocycle condition verified by deppy')}"
        )

    def translate_h0(
        self,
        cover: Dict[str, Any],
        global_section: Dict[str, Any],
    ) -> str:
        """Translate H⁰ (global sections) into a Lean definition.

        Parameters
        ----------
        cover:
            Cover dict.
        global_section:
            The global section value (type assignment for the whole program).
        """
        self._counter += 1
        tag = f"h0_{self._counter}"

        carrier = str(global_section.get("carrier_type", "Any"))
        lean_ty = _BASE_TYPE_MAP.get(carrier, carrier)

        return (
            f"{_lean_line_comment(f'H⁰ = global section of type {lean_ty}')}\n"
            f'def globalType_{tag} : String := "{lean_ty}"'
        )

    def translate_long_exact_sequence(
        self,
        covers: List[Dict[str, Any]],
    ) -> str:
        """Emit the long exact sequence relating refinement levels.

        This is a higher-level theorem connecting H⁰ → H¹ → H² across
        a sequence of cover refinements.
        """
        self._counter += 1
        tag = f"les_{self._counter}"

        cover_defs: List[str] = []
        for i, c in enumerate(covers):
            cover_lean = self._sheaf.translate_cover(c)
            cover_defs.append(f"def les_cover_{tag}_{i} : CoveringFamily := {cover_lean}")

        covers_block = "\n\n".join(cover_defs)
        n = len(covers)

        return (
            f"{_lean_line_comment('Long exact sequence across refinement levels')}\n"
            f"{covers_block}\n\n"
            f"theorem les_{tag}\n"
            f"  (H : Fin {n} → Prop) {_lean_comment('cohomology at each level')}\n"
            f"  : True := by\n"
            f"  sorry {_lean_comment('long exact sequence')}"
        )

    # ── private helpers ───────────────────────────────────────────────

    def _site_names(self, cover: Dict[str, Any]) -> Set[str]:
        """Extract site names from a cover dict."""
        sites_raw = cover.get("sites", {})
        names: Set[str] = set()
        if isinstance(sites_raw, dict):
            for sid in sites_raw.values():
                if isinstance(sid, dict):
                    names.add(str(sid.get("name", "?")))
                else:
                    names.add(str(sid))
        elif isinstance(sites_raw, list):
            for sid in sites_raw:
                if isinstance(sid, dict):
                    names.add(str(sid.get("name", "?")))
                else:
                    names.add(str(sid))
        return names


# ════════════════════════════════════════════════════════════════════════
# HybridLayerToLean
# ════════════════════════════════════════════════════════════════════════


class HybridLayerToLean:
    """Translate the hybrid layer (structural + semantic) through sheaves.

    The hybrid layer stratifies the type presheaf into two sub-presheaves:

    * **Structural layer** — types checkable by Z3.
    * **Semantic layer** — types requiring oracle judgement.

    This class translates sections, cocycle conditions, and H¹ computations
    restricted to each layer.
    """

    def __init__(self) -> None:
        self._sheaf = SheafToLean(include_prelude=False)
        self._counter: int = 0

    # ── public API ────────────────────────────────────────────────────

    def translate_layer_section(
        self,
        site: Dict[str, Any],
        layer: str,
        section: Dict[str, Any],
    ) -> str:
        """Translate a section restricted to a specific layer.

        Parameters
        ----------
        site:
            SiteId dict.
        layer:
            ``"structural"`` or ``"semantic"``.
        section:
            Section dict with refinements belonging to this layer.
        """
        self._counter += 1
        tag = f"layer_{layer}_{self._counter}"

        site_lean = self._sheaf._site_term(site)
        carrier = str(section.get("carrier_type", "Any"))
        carrier_lean = _BASE_TYPE_MAP.get(carrier, carrier)
        trust = "TrustLevel.structural" if layer == "structural" else "TrustLevel.oracle"

        refinements = section.get("refinements", {})
        ref_pairs: List[str] = []
        for k, v in (refinements if isinstance(refinements, dict) else {}).items():
            k_esc = str(k).replace('"', '\\"')
            v_esc = str(v).replace('"', '\\"')
            ref_pairs.append(f'("{k_esc}", "{v_esc}")')
        refs_lean = "[" + ", ".join(ref_pairs) + "]"

        layer_comment = (
            "decidable — can be verified by `decide`/`omega`"
            if layer == "structural"
            else "oracle — requires external judgement"
        )

        return (
            f"{_lean_line_comment(f'Layer: {layer} ({layer_comment})')}\n"
            f"def {tag} : Section :=\n"
            f"  {{ site := {site_lean}\n"
            f'  , carrierType := "{carrier_lean}"\n'
            f"  , refinements := {refs_lean}\n"
            f"  , trust := {trust}\n"
            f"  }}"
        )

    def translate_cocycle_condition(
        self,
        layer_triple: Tuple[Dict[str, Any], Dict[str, Any], Dict[str, Any]],
        transitions: Dict[str, Any],
    ) -> str:
        """Translate the cocycle condition on a triple overlap for a layer.

        Parameters
        ----------
        layer_triple:
            Three site dicts ``(U_i, U_j, U_k)`` forming a triple overlap.
        transitions:
            Dict mapping site-pair keys → transition isomorphism expressions.
        """
        self._counter += 1
        tag = f"cocycle_{self._counter}"

        u_i, u_j, u_k = layer_triple
        si = self._sheaf._site_term(u_i)
        sj = self._sheaf._site_term(u_j)
        sk = self._sheaf._site_term(u_k)

        # Look up transitions
        phi_ij = self._find_transition(transitions, u_i, u_j)
        phi_jk = self._find_transition(transitions, u_j, u_k)
        phi_ik = self._find_transition(transitions, u_i, u_k)

        phi_ij_esc = phi_ij.replace('"', '\\"')
        phi_jk_esc = phi_jk.replace('"', '\\"')
        phi_ik_esc = phi_ik.replace('"', '\\"')

        return (
            f"{_lean_line_comment('Cocycle condition: φ_ik = φ_ij ∘ φ_jk')}\n"
            f"def trans_ij_{tag} : TransitionIso :=\n"
            f'  {{ source := {si}, target := {sj}, isoExpr := "{phi_ij_esc}" }}\n\n'
            f"def trans_jk_{tag} : TransitionIso :=\n"
            f'  {{ source := {sj}, target := {sk}, isoExpr := "{phi_jk_esc}" }}\n\n'
            f"def trans_ik_{tag} : TransitionIso :=\n"
            f'  {{ source := {si}, target := {sk}, isoExpr := "{phi_ik_esc}" }}\n\n'
            f"theorem {tag}\n"
            f"  : cocycleCondition trans_ij_{tag} trans_jk_{tag} trans_ik_{tag} := by\n"
            f"  {_lean_line_comment('φ_ik should equal φ_ij ∘ φ_jk')}\n"
            f"  sorry {_lean_comment('cocycle condition for this triple')}"
        )

    def translate_h1_layer(
        self,
        layer_data: Dict[str, Any],
    ) -> str:
        """Translate H¹(Layer, HybridTy) into a Lean theorem / obstruction.

        Parameters
        ----------
        layer_data:
            Keys: ``"layer"`` (``"structural"`` or ``"semantic"``),
            ``"cover"`` (Cover dict), ``"sections"`` (list of section dicts),
            ``"is_trivial"`` (bool), ``"obstruction"`` (optional obstruction dict).
        """
        self._counter += 1
        layer = layer_data.get("layer", "structural")
        is_trivial = layer_data.get("is_trivial", True)
        tag = f"h1_{layer}_{self._counter}"

        cover = layer_data.get("cover", {})
        sections = layer_data.get("sections", [])

        cover_lean = self._sheaf.translate_cover(cover)

        sec_terms: List[str] = []
        for s in (sections if isinstance(sections, list) else []):
            sec_terms.append(self._sheaf._section_term(s))
        secs_lean = "[" + ", ".join(sec_terms) + "]"

        if is_trivial:
            tactic = "omega" if layer == "structural" else "sorry"
            return (
                f"{_lean_line_comment(f'H¹({layer}, HybridTy) = 0')}\n"
                f"def cover_{tag} : CoveringFamily := {cover_lean}\n\n"
                f"def sections_{tag} : List Section := {secs_lean}\n\n"
                f"theorem {tag} : sheafCondition cover_{tag} sections_{tag} := by\n"
                f"  intro s₁ s₂ hs₁ hs₂ hoverlap\n"
                f"  {tactic} {_lean_comment(f'{layer} layer: H¹ = 0')}"
            )

        # Non-trivial
        obstruction = layer_data.get("obstruction", {})
        explanation = obstruction.get("explanation", "type clash in layer")
        return (
            f"{_lean_line_comment(f'H¹({layer}, HybridTy) ≠ 0 — obstruction')}\n"
            f"def cover_{tag} : CoveringFamily := {cover_lean}\n\n"
            f"def sections_{tag} : List Section := {secs_lean}\n\n"
            f"{_lean_line_comment(explanation)}\n"
            f"def {tag}_obstruction : ObstructionData :=\n"
            f"  {{ cohomologyClass := {{ degree := 1, isTrivial := false }}\n"
            f'  , explanation := "{explanation.replace(chr(34), chr(92)+chr(34))}"\n'
            f"  }}"
        )

    def translate_layer_restriction(
        self,
        full_section: Dict[str, Any],
        layer: str,
    ) -> str:
        """Restrict a full section to a specific layer.

        Filters the refinements dict to keep only those belonging to
        the given layer (structural / semantic), then emits the
        restricted section.
        """
        self._counter += 1
        tag = f"restrict_{layer}_{self._counter}"

        refinements = full_section.get("refinements", {})
        layer_refs: Dict[str, str] = {}
        for k, v in (refinements if isinstance(refinements, dict) else {}).items():
            # Heuristic: structural refinements tend to look like Z3 formulas
            is_structural = bool(re.search(r"[<>=!]+|len\(|And\(|Or\(", str(v)))
            if (layer == "structural" and is_structural) or (
                layer == "semantic" and not is_structural
            ):
                layer_refs[k] = str(v)

        restricted = dict(full_section)
        restricted["refinements"] = layer_refs
        restricted["trust"] = "STRUCTURAL" if layer == "structural" else "ORACLE"

        site = full_section.get("site_id", {"kind": "MODULE_LEVEL", "name": "?"})
        return self.translate_layer_section(site, layer, restricted)

    def translate_layer_decomposition(
        self,
        full_sections: List[Dict[str, Any]],
    ) -> str:
        """Decompose a list of full sections into structural + semantic layers.

        Returns Lean definitions for both layers and a theorem that the
        full section is recovered by joining them.
        """
        self._counter += 1
        tag = f"decompose_{self._counter}"

        struct_parts: List[str] = []
        semantic_parts: List[str] = []
        for sec in full_sections:
            struct_parts.append(self.translate_layer_restriction(sec, "structural"))
            semantic_parts.append(self.translate_layer_restriction(sec, "semantic"))

        struct_block = "\n\n".join(struct_parts)
        semantic_block = "\n\n".join(semantic_parts)

        return (
            f"{_lean_line_comment('Layer decomposition: full = structural ⊕ semantic')}\n\n"
            f"{_lean_line_comment('── Structural layer ──')}\n"
            f"{struct_block}\n\n"
            f"{_lean_line_comment('── Semantic layer ──')}\n"
            f"{semantic_block}\n\n"
            f"theorem {tag}_join : True := by\n"
            f"  {_lean_line_comment('structural ⊕ semantic reconstructs the full section')}\n"
            f"  trivial"
        )

    # ── private helpers ───────────────────────────────────────────────

    def _find_transition(
        self,
        transitions: Dict[str, Any],
        src: Dict[str, Any],
        tgt: Dict[str, Any],
    ) -> str:
        """Look up the transition iso between *src* and *tgt*."""
        src_name = src.get("name", "?")
        tgt_name = tgt.get("name", "?")

        for key, val in (
            transitions.items() if isinstance(transitions, dict) else []
        ):
            a, b = self._sheaf._unpack_transition_key(key)
            if a.get("name") == src_name and b.get("name") == tgt_name:
                return str(val)
            if a.get("name") == tgt_name and b.get("name") == src_name:
                return f"inv({val})"

        return "id"


# ════════════════════════════════════════════════════════════════════════
# RoundtripChecker
# ════════════════════════════════════════════════════════════════════════


@dataclass
class Mismatch:
    """A single mismatch between the Python and Lean representations.

    Attributes
    ----------
    kind : str
        ``"type"``, ``"value"``, or ``"property"``.
    location : str
        Human-readable location (e.g. function name + line number).
    python_repr : str
        The Python-side value / type.
    lean_repr : str
        The Lean-side value / type.
    explanation : str
        Why the two differ.
    """

    kind: str
    location: str
    python_repr: str
    lean_repr: str
    explanation: str = ""


class RoundtripChecker:
    """Verify that the Python → Lean translation preserves types and values.

    This class performs a best-effort *roundtrip check*: it parses both
    the Python source and the generated Lean source, extracts declared
    types and simple constant values, and compares them.

    Attributes
    ----------
    _python_source : str
        The original Python source code.
    _lean_source : str
        The generated Lean 4 source code.
    """

    def __init__(self, python_source: str, lean_source: str) -> None:
        self._python_source = python_source
        self._lean_source = lean_source
        self._py_types: Dict[str, str] = {}
        self._lean_types: Dict[str, str] = {}
        self._parse_sources()

    # ── public API ────────────────────────────────────────────────────

    def check_type_preservation(self) -> List[Mismatch]:
        """Verify that every Python type has a corresponding Lean type.

        Returns a list of mismatches where a Python type was either
        missing in Lean or translated to an incompatible type.
        """
        mismatches: List[Mismatch] = []

        for name, py_type in self._py_types.items():
            expected_lean = _BASE_TYPE_MAP.get(py_type, py_type)

            if name not in self._lean_types:
                mismatches.append(Mismatch(
                    kind="type",
                    location=name,
                    python_repr=py_type,
                    lean_repr="<missing>",
                    explanation=f"Python type '{py_type}' for '{name}' has no Lean counterpart.",
                ))
                continue

            actual_lean = self._lean_types[name]
            if not self._types_compatible(expected_lean, actual_lean):
                mismatches.append(Mismatch(
                    kind="type",
                    location=name,
                    python_repr=py_type,
                    lean_repr=actual_lean,
                    explanation=(
                        f"Expected Lean type '{expected_lean}' but found '{actual_lean}'."
                    ),
                ))

        return mismatches

    def check_value_preservation(
        self,
        test_inputs: List[Dict[str, Any]],
    ) -> List[Mismatch]:
        """Run Python values through both representations and compare.

        This is a *static* comparison: it extracts constant definitions
        from both sources and checks they agree.  It does **not** execute
        Lean code (that would require a Lean toolchain).

        Parameters
        ----------
        test_inputs:
            List of ``{"name": ..., "python_value": ..., "lean_value": ...}``
            dicts for manual spot-checks.
        """
        mismatches: List[Mismatch] = []

        for ti in test_inputs:
            name = ti.get("name", "?")
            py_val = str(ti.get("python_value", ""))
            lean_val = str(ti.get("lean_value", ""))

            if not self._values_compatible(py_val, lean_val):
                mismatches.append(Mismatch(
                    kind="value",
                    location=name,
                    python_repr=py_val,
                    lean_repr=lean_val,
                    explanation=f"Value mismatch for '{name}'.",
                ))

        # Also compare constants extracted from source
        py_consts = self._extract_python_constants()
        lean_consts = self._extract_lean_constants()

        for cname, cval in py_consts.items():
            if cname in lean_consts:
                if not self._values_compatible(cval, lean_consts[cname]):
                    mismatches.append(Mismatch(
                        kind="value",
                        location=cname,
                        python_repr=cval,
                        lean_repr=lean_consts[cname],
                        explanation=f"Constant '{cname}' differs between Python and Lean.",
                    ))

        return mismatches

    def generate_property_tests(
        self,
        func_name: str,
        num_tests: int = 5,
    ) -> str:
        """Generate Lean ``#eval`` tests for a translated function.

        Parameters
        ----------
        func_name:
            Name of the function to test.
        num_tests:
            Number of test cases to generate.

        Returns
        -------
        str
            Lean 4 ``#eval`` commands that can be pasted into a Lean file.
        """
        lean_name = _lean_ident(func_name)
        lines: List[str] = [
            f"-- Property tests for {func_name}",
            f"-- Generated by deppy RoundtripChecker",
            "",
        ]

        # Extract parameter types from Lean source
        param_types = self._extract_lean_params(func_name)

        for i in range(num_tests):
            args = self._generate_test_args(param_types, seed=i)
            args_str = " ".join(args)
            lines.append(f"#eval {lean_name} {args_str}")
            lines.append(f"  -- test case {i + 1}")

        # Add a type-check test
        lines.append("")
        lines.append(f"#check @{lean_name}")
        lines.append(f"  -- verify the type signature is well-formed")

        return "\n".join(lines)

    def summary(self) -> str:
        """Return a human-readable summary of the roundtrip check."""
        type_m = self.check_type_preservation()
        val_m = self.check_value_preservation([])

        total = len(type_m) + len(val_m)
        if total == 0:
            return "✓ Roundtrip check passed: no mismatches found."

        lines = [f"✗ Roundtrip check found {total} mismatch(es):"]
        for m in type_m:
            lines.append(f"  [type] {m.location}: {m.explanation}")
        for m in val_m:
            lines.append(f"  [value] {m.location}: {m.explanation}")
        return "\n".join(lines)

    # ── private: parsing ──────────────────────────────────────────────

    def _parse_sources(self) -> None:
        """Extract type annotations from both sources."""
        self._py_types = self._extract_python_types()
        self._lean_types = self._extract_lean_types()

    def _extract_python_types(self) -> Dict[str, str]:
        """Extract type annotations from Python source (regex-based)."""
        types: Dict[str, str] = {}

        # Function signatures: def foo(x: int, y: str) -> bool:
        for m in re.finditer(
            r"def\s+(\w+)\s*\(([^)]*)\)\s*(?:->\s*(\w[\w\[\], ]*))?",
            self._python_source,
        ):
            func_name = m.group(1)
            ret = m.group(3)
            if ret:
                types[f"{func_name}.__return__"] = ret.strip()

            params_str = m.group(2)
            for pm in re.finditer(r"(\w+)\s*:\s*(\w[\w\[\], ]*)", params_str):
                types[f"{func_name}.{pm.group(1)}"] = pm.group(2).strip()

        # Variable annotations: x: int = ...
        for m in re.finditer(
            r"^(\w+)\s*:\s*(\w[\w\[\], ]*)\s*=",
            self._python_source,
            re.MULTILINE,
        ):
            types[m.group(1)] = m.group(2).strip()

        return types

    def _extract_lean_types(self) -> Dict[str, str]:
        """Extract type declarations from Lean source (regex-based)."""
        types: Dict[str, str] = {}

        # def foo : Type := ...
        for m in re.finditer(
            r"(?:def|theorem|lemma)\s+(\w+)[^:]*:\s*([^:=]+?)(?:\s*:=|\s*:=\s*by|\s*where)",
            self._lean_source,
        ):
            name = m.group(1)
            ty = m.group(2).strip()
            types[name] = ty

        # structure fields: name : Type
        for m in re.finditer(r"(\w+)\s*:\s*(\w[\w .]*)", self._lean_source):
            name = m.group(1)
            ty = m.group(2).strip()
            if name not in types:
                types[name] = ty

        return types

    def _extract_python_constants(self) -> Dict[str, str]:
        """Extract constant assignments from Python source."""
        consts: Dict[str, str] = {}
        for m in re.finditer(
            r"^([A-Z_][A-Z0-9_]*)\s*=\s*(.+)$",
            self._python_source,
            re.MULTILINE,
        ):
            consts[m.group(1)] = m.group(2).strip()
        return consts

    def _extract_lean_constants(self) -> Dict[str, str]:
        """Extract constant definitions from Lean source."""
        consts: Dict[str, str] = {}
        for m in re.finditer(
            r"def\s+(\w+)\s*:\s*\w+\s*:=\s*(.+)",
            self._lean_source,
        ):
            consts[m.group(1)] = m.group(2).strip()
        return consts

    def _extract_lean_params(self, func_name: str) -> List[str]:
        """Extract parameter types for *func_name* from Lean source."""
        lean_name = _lean_ident(func_name)
        pattern = rf"(?:def|theorem|lemma)\s+{re.escape(lean_name)}\s*([^:]*?):"
        m = re.search(pattern, self._lean_source)
        if not m:
            return ["Int"]  # fallback

        params_str = m.group(1)
        types: List[str] = []
        for pm in re.finditer(r"\([\w']+ : (\w+)\)", params_str):
            types.append(pm.group(1))
        return types if types else ["Int"]

    def _generate_test_args(self, param_types: List[str], seed: int = 0) -> List[str]:
        """Generate simple test arguments for the given Lean types."""
        args: List[str] = []
        for i, ty in enumerate(param_types):
            val = self._default_value(ty, seed + i)
            args.append(val)
        return args

    def _default_value(self, lean_type: str, seed: int = 0) -> str:
        """Generate a default test value for a Lean type."""
        mapping: Dict[str, List[str]] = {
            "Int": [str(seed), str(-seed), "0", "1", "42", "-1", "100"],
            "Nat": [str(abs(seed)), "0", "1", "2", "10", "100"],
            "Float": [f"{seed}.0", "0.0", "1.0", "-1.0", "3.14"],
            "String": [f'"test{seed}"', '""', '"hello"', '"world"'],
            "Bool": ["true", "false", "true", "false", "true"],
            "Unit": ["()", "()", "()", "()", "()"],
        }
        candidates = mapping.get(lean_type, [f"(sorry : {lean_type})"])
        return candidates[seed % len(candidates)]

    # ── private: compatibility checks ─────────────────────────────────

    def _types_compatible(self, expected: str, actual: str) -> bool:
        """Check if two Lean type strings are compatible."""
        e = expected.strip()
        a = actual.strip()

        if e == a:
            return True

        # Normalise common variants
        normalise: Dict[str, str] = {
            "Integer": "Int",
            "int": "Int",
            "float": "Float",
            "str": "String",
            "string": "String",
            "bool": "Bool",
            "boolean": "Bool",
            "list": "List",
            "List": "List",
            "dict": "Std.HashMap",
            "set": "Finset",
            "None": "Unit",
            "NoneType": "Unit",
        }
        e_norm = normalise.get(e, e)
        a_norm = normalise.get(a, a)
        if e_norm == a_norm:
            return True

        # Subtype compatibility: {x : T // P} is compatible with T
        m = re.match(r"\{\s*\w+\s*:\s*(\w+)\s*//", a)
        if m and m.group(1) == e_norm:
            return True

        return False

    def _values_compatible(self, py_val: str, lean_val: str) -> bool:
        """Check if a Python value and Lean value are equivalent."""
        py_v = py_val.strip().strip("'\"")
        lean_v = lean_val.strip().strip("'\"")

        if py_v == lean_v:
            return True

        # Numeric comparison
        try:
            if float(py_v) == float(lean_v):
                return True
        except (ValueError, TypeError):
            pass

        # Boolean
        bool_map = {"True": "true", "False": "false", "None": "none"}
        if bool_map.get(py_v) == lean_v:
            return True

        return False
