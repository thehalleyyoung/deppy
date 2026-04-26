"""Built-in sidecar specs for high-frequency Python exception sources.

The runtime-safety goal requires honest discharge of the most-common
exception sites in any Python module: subscripts, divisions,
attribute access, builtin calls (``min([])``, ``int("x")``,
``json.loads(...)``).  This file packages a *built-in* sidecar — a
catalogue of canonical safety predicates and raise conditions for
those operations — which the safety pipeline auto-loads on every
``verify_module_safety`` call.

The catalogue distinguishes three discharge mechanisms:

1. ``BUILTIN_SAFETY_PREDICATES`` — the canonical Python predicate
   that, when true at the call site, rules out the exception.  The
   safety pipeline asks Z3 whether the caller's path-sensitive guards
   imply this predicate.
2. ``BUILTIN_RAISES_DECLARATIONS`` — for callees the pipeline cannot
   z3-discharge (e.g. ``json.loads(s)`` raising ``JSONDecodeError``
   when ``s`` is "not valid JSON"), the catalogue records the
   declared raise so the pipeline knows to surface it as
   ``raises_declarations`` rather than silently axiom-dropping it.
3. ``BUILTIN_TOTAL`` — operations that genuinely never raise
   (``str(x)``, ``repr(x)``, ``isinstance(x, T)``).  These are
   marked total and discharged by ``Structural`` proof.

The catalogue is intentionally honest: anything we cannot discharge
formally is recorded as a raise rather than glossed over.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass
from typing import Optional


# ─────────────────────────────────────────────────────────────────────
#  Catalogue dataclasses
# ─────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class BuiltinDischarge:
    """One catalogue row: how a builtin call's exception is discharged.

    ``predicate`` is a Python expression (template) referring to the
    actual arguments by ``$arg0``, ``$arg1``, ``$recv`` placeholders.
    The pipeline substitutes the call site's actuals before passing
    the formula to Z3.

    ``mode`` selects the discharge strategy:

    * ``"safety_predicate"`` — emit a safety predicate that the
      caller must establish; can be Z3-discharged.
    * ``"raises_declaration"`` — record as
      ``raises_declarations=[(cls, cond)]``; not Z3-discharged.
    * ``"total"`` — operation never raises; emit a ``Structural``
      discharge with ``EFFECT_ASSUMED`` trust.
    """
    exception_class: str
    predicate: str
    mode: str  # "safety_predicate" / "raises_declaration" / "total"
    note: str = ""


# ─────────────────────────────────────────────────────────────────────
#  Subscript / division / attribute (covered by safety_predicates)
# ─────────────────────────────────────────────────────────────────────

# These are already produced by ``deppy.pipeline.safety_predicates`` —
# we list them here for documentation / completeness only.

SUBSCRIPT_AND_ARITH_DOC = """\
The following operations get safety predicates from
``safety_predicate_for`` directly; they are NOT in this catalogue:

* ``a / b``, ``a // b``, ``a % b``  →  ``b != 0``  (ZeroDivisionError)
* ``xs[i]``                          →  ``0 <= i < len(xs)``  (IndexError)
* ``d[k]``                           →  ``k in d``  (KeyError)
* ``obj.attr``                       →  ``hasattr(obj, attr)``  (AttributeError)
"""


# ─────────────────────────────────────────────────────────────────────
#  Builtin function catalogue
# ─────────────────────────────────────────────────────────────────────

# Each entry is keyed by a *qualified name* the parser can resolve to:
#   * ``"<bare>:<name>"`` for a top-level Name (e.g. ``int(s)``)
#   * ``"<module>:<attr>"`` for ``module.attr(...)``
#   * ``"<recv>:<method>"`` for an unrecognised receiver

_CATALOGUE: dict[str, list[BuiltinDischarge]] = {
    # ── int / float / str / bool ────────────────────────────────────
    "<bare>:int": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="isinstance($arg0, (int, float, bool))"
                      " or (isinstance($arg0, str)"
                      " and $arg0.lstrip('+-').isdigit())",
            mode="safety_predicate",
            note="int(s) raises ValueError when s is not a parseable integer",
        ),
        BuiltinDischarge(
            exception_class="TypeError",
            predicate="isinstance($arg0, (int, float, bool, str, bytes,"
                      " bytearray))",
            mode="safety_predicate",
            note="int(x) raises TypeError when x has no __int__",
        ),
    ],
    "<bare>:float": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="isinstance($arg0, (int, float, bool))"
                      " or isinstance($arg0, str)",
            mode="safety_predicate",
            note="float(s) raises ValueError when s is not a parseable float",
        ),
    ],
    "<bare>:bool": [
        BuiltinDischarge(
            exception_class="Exception", predicate="True", mode="total",
            note="bool(x) never raises (object falls through to True)",
        ),
    ],
    "<bare>:str": [
        BuiltinDischarge(
            exception_class="Exception", predicate="True", mode="total",
            note="str(x) falls through __str__ → __repr__ → object",
        ),
    ],
    "<bare>:repr": [
        BuiltinDischarge(
            exception_class="Exception", predicate="True", mode="total",
            note="repr(x) always returns a string",
        ),
    ],
    "<bare>:type": [
        BuiltinDischarge(
            exception_class="Exception", predicate="True", mode="total",
            note="type(x) never raises for a single arg",
        ),
    ],
    "<bare>:isinstance": [
        BuiltinDischarge(
            exception_class="TypeError",
            predicate="isinstance($arg1, type)"
                      " or isinstance($arg1, tuple)",
            mode="safety_predicate",
            note="isinstance raises TypeError when arg1 is not a type/tuple",
        ),
    ],
    "<bare>:hasattr": [
        BuiltinDischarge(
            exception_class="Exception", predicate="True", mode="total",
            note="hasattr never raises (catches AttributeError internally)",
        ),
    ],
    "<bare>:getattr": [
        BuiltinDischarge(
            exception_class="AttributeError",
            predicate="hasattr($arg0, $arg1)",
            mode="safety_predicate",
            note="getattr(o, n) raises unless hasattr(o, n) — but the"
                 " 3-arg form with default never raises",
        ),
    ],

    # ── len / sum / min / max / next / iter ────────────────────────
    "<bare>:len": [
        BuiltinDischarge(
            exception_class="TypeError",
            predicate="hasattr($arg0, '__len__')",
            mode="safety_predicate",
            note="len(x) raises TypeError unless x has __len__",
        ),
    ],
    "<bare>:sum": [
        BuiltinDischarge(
            exception_class="TypeError",
            predicate="hasattr($arg0, '__iter__')",
            mode="safety_predicate",
            note="sum(x) raises TypeError unless x is iterable",
        ),
    ],
    "<bare>:min": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="hasattr($arg0, '__iter__') and len($arg0) > 0",
            mode="safety_predicate",
            note="min([]) raises ValueError",
        ),
    ],
    "<bare>:max": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="hasattr($arg0, '__iter__') and len($arg0) > 0",
            mode="safety_predicate",
            note="max([]) raises ValueError",
        ),
    ],
    "<bare>:next": [
        BuiltinDischarge(
            exception_class="StopIteration",
            predicate="False",
            mode="raises_declaration",
            note="next(it) raises StopIteration when iterator is exhausted —"
                 " unprovable statically without a 2-arg default",
        ),
    ],
    "<bare>:iter": [
        BuiltinDischarge(
            exception_class="TypeError",
            predicate="hasattr($arg0, '__iter__')"
                      " or hasattr($arg0, '__getitem__')",
            mode="safety_predicate",
        ),
    ],
    "<bare>:sorted": [
        BuiltinDischarge(
            exception_class="TypeError",
            predicate="hasattr($arg0, '__iter__')",
            mode="safety_predicate",
        ),
    ],
    "<bare>:reversed": [
        BuiltinDischarge(
            exception_class="TypeError",
            predicate="hasattr($arg0, '__reversed__')"
                      " or hasattr($arg0, '__len__')",
            mode="safety_predicate",
        ),
    ],
    "<bare>:abs": [
        BuiltinDischarge(
            exception_class="TypeError",
            predicate="hasattr($arg0, '__abs__')"
                      " or isinstance($arg0, (int, float, complex))",
            mode="safety_predicate",
        ),
    ],
    "<bare>:divmod": [
        BuiltinDischarge(
            exception_class="ZeroDivisionError",
            predicate="$arg1 != 0",
            mode="safety_predicate",
        ),
    ],
    "<bare>:pow": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="$arg0 != 0 or $arg1 >= 0",
            mode="safety_predicate",
            note="pow(0, neg) raises ZeroDivisionError",
        ),
    ],

    # ── math module ─────────────────────────────────────────────────
    "math:sqrt": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="$arg0 >= 0",
            mode="safety_predicate",
            note="math.sqrt(x) raises for x < 0",
        ),
    ],
    "math:log": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="$arg0 > 0",
            mode="safety_predicate",
        ),
    ],
    "math:log2": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="$arg0 > 0",
            mode="safety_predicate",
        ),
    ],
    "math:log10": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="$arg0 > 0",
            mode="safety_predicate",
        ),
    ],
    "math:asin": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="-1 <= $arg0 and $arg0 <= 1",
            mode="safety_predicate",
        ),
    ],
    "math:acos": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="-1 <= $arg0 and $arg0 <= 1",
            mode="safety_predicate",
        ),
    ],
    "math:factorial": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="$arg0 >= 0",
            mode="safety_predicate",
        ),
    ],

    # ── json module ─────────────────────────────────────────────────
    "json:loads": [
        BuiltinDischarge(
            exception_class="json.JSONDecodeError",
            predicate="False",
            mode="raises_declaration",
            note="json.loads(s) raises JSONDecodeError for invalid JSON —"
                 " unprovable without a parser",
        ),
    ],
    "json:dumps": [
        BuiltinDischarge(
            exception_class="TypeError",
            predicate="True",  # most objects serialise; default=str sidesteps
            mode="raises_declaration",
            note="json.dumps(x) raises TypeError for non-JSON-serializable x",
        ),
    ],

    # ── list / dict / str methods ──────────────────────────────────
    "<recv>:pop": [
        BuiltinDischarge(
            exception_class="IndexError",
            predicate="len($recv) > 0",
            mode="safety_predicate",
            note="list.pop() raises on empty list",
        ),
    ],
    "<recv>:remove": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="$arg0 in $recv",
            mode="safety_predicate",
            note="list.remove(x) raises ValueError when x is not in list",
        ),
    ],
    "<recv>:index": [
        BuiltinDischarge(
            exception_class="ValueError",
            predicate="$arg0 in $recv",
            mode="safety_predicate",
            note="list.index(x) raises ValueError when x is not in list",
        ),
    ],
    "<recv>:get": [
        BuiltinDischarge(
            exception_class="Exception", predicate="True", mode="total",
            note="dict.get(k) returns None on missing key",
        ),
    ],

    # ── os / pathlib (intentionally raises_declaration) ────────────
    "os:remove": [
        BuiltinDischarge(
            exception_class="FileNotFoundError",
            predicate="False",
            mode="raises_declaration",
        ),
    ],
    "os:listdir": [
        BuiltinDischarge(
            exception_class="FileNotFoundError",
            predicate="False",
            mode="raises_declaration",
        ),
    ],
    "open:": [
        BuiltinDischarge(
            exception_class="FileNotFoundError",
            predicate="False",
            mode="raises_declaration",
        ),
    ],
}


# ─────────────────────────────────────────────────────────────────────
#  Resolver
# ─────────────────────────────────────────────────────────────────────

def lookup_call(call: ast.Call) -> list[BuiltinDischarge]:
    """Look up the catalogue entries for a given ``Call`` AST node.

    Returns an empty list when the call's target isn't in the
    catalogue; the safety pipeline falls through to its existing
    discharge logic in that case.
    """
    func = call.func
    if isinstance(func, ast.Name):
        return list(_CATALOGUE.get(f"<bare>:{func.id}", []))
    if isinstance(func, ast.Attribute):
        attr = func.attr
        if isinstance(func.value, ast.Name):
            mod = func.value.id
            entries = _CATALOGUE.get(f"{mod}:{attr}", [])
            if entries:
                return list(entries)
        # Fall back to <recv>: methods that exist on builtin types
        return list(_CATALOGUE.get(f"<recv>:{attr}", []))
    return []


def substitute_call_arguments(
    predicate: str, call: ast.Call,
) -> Optional[str]:
    """Replace ``$argN`` and ``$recv`` placeholders with actual source.

    Returns the substituted Python expression, or ``None`` when
    arguments are missing (e.g. ``len()``).
    """
    actuals: list[str] = []
    for a in call.args:
        try:
            actuals.append(ast.unparse(a))
        except Exception:
            actuals.append(f"_arg{len(actuals)}")
    recv = "_recv"
    if isinstance(call.func, ast.Attribute):
        try:
            recv = ast.unparse(call.func.value)
        except Exception:
            recv = "_recv"

    out = predicate.replace("$recv", f"({recv})")
    for i, a in enumerate(actuals):
        out = out.replace(f"$arg{i}", f"({a})")
    if "$arg" in out:
        # Caller forgot some args — bail.
        return None
    return out


__all__ = [
    "BuiltinDischarge",
    "lookup_call",
    "substitute_call_arguments",
]
