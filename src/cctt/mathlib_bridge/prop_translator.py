"""
Lean proposition -> CCTT-checkable predicate translator.

Translates Lean 4 propositions (parsed into LeanExpr AST) into CCTT
predicates expressed as Z3 formulae and/or OTerm patterns.  Also provides
the reverse direction (CCTTPredicateToLeanProp).

Mathematical basis
------------------
A Lean proposition  P : Prop  lives in a universe that is *proof-irrelevant*.
In CCTT we need a *predicate* -- a decidable or semi-decidable test on runtime
values.  The translation therefore factors every proposition into

    P  ~=  P_struct /\\ P_sem

where P_struct is the Z3-decidable fragment (equalities, linear arithmetic,
Boolean connectives, bounded quantifiers) and P_sem is the semantic residue
that must be judged by the LLM oracle.

The translator also classifies each proposition into a *Z3 fragment*:
QF_LIA, QF_NIA, QF_LRA, QF_AUFLIA, AUFNIRA, or UNKNOWN, so that callers
can pick the right Z3 tactic.
"""
from __future__ import annotations

import dataclasses
import enum
import re
from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    FrozenSet,
    List,
    Optional,
    Sequence,
    Set,
    Tuple,
    Union,
)

# -- Z3 guard -----------------------------------------------------------------
try:
    import z3 as _z3

    _HAS_Z3 = True
except ImportError:  # pragma: no cover
    _z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False

# -- Local imports ------------------------------------------------------------
from cctt.mathlib_bridge.lean_parser import (
    LeanApp,
    LeanDecl,
    LeanExpr,
    LeanHole,
    LeanIf,
    LeanLam,
    LeanLet,
    LeanLit,
    LeanMatch,
    LeanParam,
    LeanPi,
    LeanProj,
    LeanSort,
    LeanSorry,
    LeanTactic,
    LeanTacticBlock,
    LeanVar,
    LeanAnonymousCtor,
)
from cctt.mathlib_bridge.lean_type_mapper import LeanToCCTTTypeMapper, TypeMapping
from cctt.denotation import (
    OTerm,
    OVar,
    OLit,
    OOp,
    OFold,
    OCase,
    OFix,
    OSeq,
    ODict,
    OUnknown,
    OQuotient,
    OAbstract,
    OLam,
    OMap,
    OCatch,
)
from cctt.theory import ADD, SUB, MUL, LT, LE, GT, GE, EQ, NE, NEG, MAX, MIN

# -- Constants ----------------------------------------------------------------

_LEAN_PROP_NAMES: Dict[str, str] = {
    "Eq": "eq",
    "Ne": "ne",
    "HEq": "heq",
    "And": "and",
    "Or": "or",
    "Not": "not",
    "Iff": "iff",
    "True": "true",
    "False": "false",
    "Exists": "exists",
    "Sigma": "sigma",
    "PSigma": "psigma",
    "Subtype": "subtype",
    "Decidable": "decidable",
    "Le": "le",
    "Lt": "lt",
    "Ge": "ge",
    "Gt": "gt",
    "LE.le": "le",
    "LT.lt": "lt",
    "GE.ge": "ge",
    "GT.gt": "gt",
    "HasLe.le": "le",
    "HasLt.lt": "lt",
    "Nat.le": "nat_le",
    "Nat.lt": "nat_lt",
    "Int.le": "int_le",
    "Int.lt": "int_lt",
    "List.Mem": "list_mem",
    "List.Nodup": "list_nodup",
    "List.Sorted": "list_sorted",
    "List.Perm": "list_perm",
    "List.Sublist": "list_sublist",
    "List.Chain": "list_chain",
    "List.Forall": "list_forall",
    "Multiset.Nodup": "multiset_nodup",
    "Finset.card": "finset_card",
    "Finset.mem": "finset_mem",
    "Set.Mem": "set_mem",
    "Set.Subset": "set_subset",
    "Set.Finite": "set_finite",
    "Function.Injective": "fun_injective",
    "Function.Surjective": "fun_surjective",
    "Function.Bijective": "fun_bijective",
    "Function.LeftInverse": "fun_left_inv",
    "Function.RightInverse": "fun_right_inv",
    "IsCommutative": "is_comm",
    "IsAssociative": "is_assoc",
    "IsIdempotent": "is_idempotent",
    "Monotone": "monotone",
    "StrictMono": "strict_mono",
    "Antitone": "antitone",
    "StrictAnti": "strict_anti",
    "Nat.Prime": "nat_prime",
    "Int.gcd": "int_gcd",
    "Nat.gcd": "nat_gcd",
    "Dvd": "dvd",
    "Nat.dvd": "nat_dvd",
    "Even": "even",
    "Odd": "odd",
    "Nat.Coprime": "nat_coprime",
}

# Map from normalised prop name -> op code for binary comparisons
_CMP_OP: Dict[str, int] = {
    "le": LE,
    "lt": LT,
    "ge": GE,
    "gt": GT,
    "ne": NE,
    "nat_le": LE,
    "nat_lt": LT,
    "int_le": LE,
    "int_lt": LT,
}

# Map from normalised prop name -> human-readable description fragment
_NL_CMP: Dict[str, str] = {
    "eq": "is equal to",
    "ne": "is not equal to",
    "le": "is less than or equal to",
    "lt": "is less than",
    "ge": "is greater than or equal to",
    "gt": "is greater than",
    "nat_le": "is <= (Nat)",
    "nat_lt": "is < (Nat)",
    "int_le": "is <= (Int)",
    "int_lt": "is < (Int)",
}


# -- Z3 fragment classification -----------------------------------------------


class Z3Fragment(enum.Enum):
    """SMT-LIB logic fragment identifiers."""

    QF_LIA = "QF_LIA"
    QF_NIA = "QF_NIA"
    QF_LRA = "QF_LRA"
    QF_AUFLIA = "QF_AUFLIA"
    AUFNIRA = "AUFNIRA"
    UNKNOWN = "UNKNOWN"


# -- Proposition kind ----------------------------------------------------------


class PropKind(enum.Enum):
    """Coarse classification of the proposition shape."""

    EQUALITY = "equality"
    COMPARISON = "comparison"
    ARITHMETIC = "arithmetic"
    QUANTIFIER = "quantifier"
    CONNECTIVE = "connective"
    LIST_PROP = "list_prop"
    SET_PROP = "set_prop"
    FUNCTION_PROP = "function_prop"
    ALGEBRAIC_PROP = "algebraic_prop"
    ORDER_PROP = "order_prop"
    NUMBER_THEORY = "number_theory"
    LITERAL = "literal"
    UNKNOWN = "unknown"


# -- Output dataclasses --------------------------------------------------------


@dataclass(frozen=True)
class PredicateComponent:
    """One atomic piece of a translated predicate.

    ``kind`` is one of: ``"structural"``, ``"semantic"``, ``"mixed"``.
    ``formula`` is either a Z3 ``BoolRef`` (when Z3 is available) or a
    plain-text formula string.
    ``confidence`` in [0, 1] measures how confident we are the translation
    is faithful.
    """

    kind: str
    formula: Any
    confidence: float = 1.0


@dataclass(frozen=True)
class TranslatedPredicate:
    """Full result of translating a Lean proposition into a CCTT predicate.

    Attributes
    ----------
    lean_prop : LeanExpr
        Original Lean AST node.
    z3_formula : Any
        Z3 ``BoolRef`` when the structural fragment is non-trivial, else
        ``None``.  Falls back to a string representation when Z3 is
        unavailable.
    oterm_pattern : OTerm | None
        OTerm that captures the *value-level* semantics of the proposition
        (e.g. ``OOp("eq", (lhs, rhs))``).
    nl_description : str
        Human-readable English description of the proposition.
    confidence : float
        Overall confidence (product of component confidences).
    prop_kind : PropKind
        Coarse classification.
    free_vars : FrozenSet[str]
        Free variable names occurring in the proposition.
    negated : bool
        Whether the outermost connective is negation.
    decidable : bool
        Whether the proposition is decidable in the Z3 fragment.
    z3_fragment : Z3Fragment
        Finest Z3 logic fragment that contains the structural part.
    components : Tuple[PredicateComponent, ...]
        Decomposed structural / semantic pieces.
    """

    lean_prop: LeanExpr
    z3_formula: Any = None
    oterm_pattern: Optional[OTerm] = None
    nl_description: str = ""
    confidence: float = 1.0
    prop_kind: PropKind = PropKind.UNKNOWN
    free_vars: FrozenSet[str] = field(default_factory=frozenset)
    negated: bool = False
    decidable: bool = False
    z3_fragment: Z3Fragment = Z3Fragment.UNKNOWN
    components: Tuple[PredicateComponent, ...] = ()


# -- Helpers -------------------------------------------------------------------


def _lean_name(expr: LeanExpr) -> Optional[str]:
    """Extract a plain name from a LeanExpr, or ``None``."""
    if isinstance(expr, LeanVar):
        return expr.name
    if isinstance(expr, LeanApp) and isinstance(expr.fn, LeanVar):
        return expr.fn.name
    return None


def _lean_head(expr: LeanExpr) -> Optional[str]:
    """Return the head symbol of an application, or just the var name."""
    if isinstance(expr, LeanVar):
        return expr.name
    if isinstance(expr, LeanApp):
        return _lean_head(expr.fn)
    return None


def _lean_app_args(expr: LeanExpr) -> List[LeanExpr]:
    """Collect all arguments of a (curried) application."""
    if isinstance(expr, LeanApp):
        return list(expr.args)
    return []


def _normalise_prop_name(name: str) -> str:
    """Normalise a Lean proposition/constant name."""
    clean = name.lstrip("@")
    return _LEAN_PROP_NAMES.get(clean, clean)


def _free_vars(
    expr: LeanExpr, bound: FrozenSet[str] = frozenset()
) -> FrozenSet[str]:
    """Collect free variable names in *expr* not in *bound*."""
    if isinstance(expr, LeanVar):
        if expr.name not in bound:
            return frozenset({expr.name})
        return frozenset()
    if isinstance(expr, LeanApp):
        acc: Set[str] = set()
        acc |= _free_vars(expr.fn, bound)
        for a in expr.args:
            acc |= _free_vars(a, bound)
        return frozenset(acc)
    if isinstance(expr, LeanLam):
        new_bound = bound | frozenset(p.name for p in expr.params)
        return _free_vars(expr.body, new_bound)
    if isinstance(expr, LeanPi):
        new_bound = bound | frozenset(p.name for p in expr.params)
        return _free_vars(expr.codomain, new_bound)
    if isinstance(expr, LeanLet):
        inner_bound = bound | {expr.name}
        acc2: Set[str] = set()
        acc2 |= _free_vars(expr.value, bound)
        if expr.type_ is not None:
            acc2 |= _free_vars(expr.type_, bound)
        acc2 |= _free_vars(expr.body, inner_bound)
        return frozenset(acc2)
    if isinstance(expr, LeanIf):
        return (
            _free_vars(expr.cond, bound)
            | _free_vars(expr.then_, bound)
            | _free_vars(expr.else_, bound)
        )
    if isinstance(expr, LeanMatch):
        acc3: Set[str] = set()
        for s in expr.scrutinees:
            acc3 |= _free_vars(s, bound)
        for arm_pats, arm_body in expr.arms:
            arm_bound = bound | frozenset(
                p.name for p in arm_pats if isinstance(p, LeanParam)
            )
            acc3 |= _free_vars(arm_body, arm_bound)
        return frozenset(acc3)
    if isinstance(expr, LeanProj):
        return _free_vars(expr.expr, bound)
    if isinstance(expr, LeanLit):
        return frozenset()
    if isinstance(
        expr, (LeanSort, LeanHole, LeanSorry, LeanTactic, LeanTacticBlock)
    ):
        return frozenset()
    return frozenset()


def _mk_z3_int(name: str) -> Any:
    """Create a Z3 Int constant, or None."""
    if not _HAS_Z3:
        return None
    return _z3.Int(name)


def _mk_z3_bool(name: str) -> Any:
    """Create a Z3 Bool constant, or None."""
    if not _HAS_Z3:
        return None
    return _z3.Bool(name)


def _mk_z3_real(name: str) -> Any:
    """Create a Z3 Real constant, or None."""
    if not _HAS_Z3:
        return None
    return _z3.Real(name)


def _oterm_for_var(name: str) -> OTerm:
    """Produce an OVar for a named variable."""
    return OVar(name)


def _oterm_for_lit(value: Union[int, float, str, bool]) -> OTerm:
    """Produce an OLit for a literal value."""
    return OLit(value)


def _oterm_binop(op_name: str, lhs: OTerm, rhs: OTerm) -> OTerm:
    """Build OOp(op_name, (lhs, rhs))."""
    return OOp(op_name, (lhs, rhs))


def _oterm_unop(op_name: str, arg: OTerm) -> OTerm:
    """Build OOp(op_name, (arg,))."""
    return OOp(op_name, (arg,))


# -- Main translator: Lean -> CCTT --------------------------------------------


class LeanPropToCCTTPredicate:
    """Translate a Lean proposition AST into a ``TranslatedPredicate``.

    The translator is stateful only in that it caches the
    ``LeanToCCTTTypeMapper`` for type lookups.  Each call to
    :meth:`translate` is independent.

    Parameters
    ----------
    type_mapper : LeanToCCTTTypeMapper | None
        Shared type mapper.  One is created internally if not supplied.
    """

    def __init__(
        self,
        type_mapper: Optional[LeanToCCTTTypeMapper] = None,
    ) -> None:
        self._type_mapper = type_mapper or LeanToCCTTTypeMapper()
        self._z3_vars: Dict[str, Any] = {}

    # -- public API -----------------------------------------------------------

    def translate(self, prop: LeanExpr) -> TranslatedPredicate:
        """Translate *prop* and return a ``TranslatedPredicate``."""
        self._z3_vars.clear()
        head = _lean_head(prop)
        norm = _normalise_prop_name(head) if head else None

        # Dispatch by proposition shape
        if norm in ("eq", "heq"):
            return self._translate_equality(prop, norm)
        if norm in _CMP_OP:
            return self._translate_comparison(prop, norm)
        if norm in ("and", "or", "not", "iff", "true", "false"):
            return self._translate_connective(prop, norm)
        if norm in ("exists", "sigma", "psigma", "subtype"):
            return self._translate_quantifier(
                prop, norm, existential=True
            )
        if isinstance(prop, LeanPi):
            return self._translate_quantifier(
                prop, "forall", existential=False
            )
        if norm is not None and norm.startswith("list_"):
            return self._translate_list_prop(prop, norm)
        if norm is not None and (
            norm.startswith("set_") or norm.startswith("finset_")
        ):
            return self._translate_set_prop(prop, norm)
        if norm is not None and norm.startswith("fun_"):
            return self._translate_function_prop(prop, norm)
        if norm in ("is_comm", "is_assoc", "is_idempotent"):
            return self._translate_algebraic_prop(prop, norm)
        if norm in ("monotone", "strict_mono", "antitone", "strict_anti"):
            return self._translate_order_prop(prop, norm)
        if norm in (
            "nat_prime",
            "dvd",
            "nat_dvd",
            "even",
            "odd",
            "nat_coprime",
            "int_gcd",
            "nat_gcd",
        ):
            return self._translate_number_theory(prop, norm)
        if isinstance(prop, LeanLit):
            return self._translate_literal(prop)
        if isinstance(prop, LeanVar):
            return self._translate_bare_var(prop)

        # Fallback -- try arithmetic interpretation
        arith = self._try_translate_arith(prop)
        if arith is not None:
            return arith

        return self._unknown(prop)

    # -- equality -------------------------------------------------------------

    def _translate_equality(
        self, prop: LeanExpr, norm: str
    ) -> TranslatedPredicate:
        """Handle ``Eq a b`` / ``HEq a b`` / ``a = b``."""
        args = _lean_app_args(prop)
        # Eq may carry the type as first arg: Eq alpha a b
        if len(args) >= 3:
            _type_arg, lhs_expr, rhs_expr = args[0], args[1], args[2]
        elif len(args) == 2:
            lhs_expr, rhs_expr = args[0], args[1]
        else:
            return self._unknown(prop)

        lhs_ot = self._expr_to_oterm(lhs_expr)
        rhs_ot = self._expr_to_oterm(rhs_expr)
        oterm = _oterm_binop("eq", lhs_ot, rhs_ot)

        lhs_z3 = self._expr_to_z3(lhs_expr)
        rhs_z3 = self._expr_to_z3(rhs_expr)
        z3f = None
        if lhs_z3 is not None and rhs_z3 is not None and _HAS_Z3:
            z3f = lhs_z3 == rhs_z3

        lhs_s = self._expr_to_str(lhs_expr)
        rhs_s = self._expr_to_str(rhs_expr)
        nl = f"{lhs_s} is equal to {rhs_s}"

        fv = _free_vars(prop)
        frag = self._classify_fragment(z3f, fv)
        dec = frag != Z3Fragment.UNKNOWN

        comp = PredicateComponent(
            "structural", z3f if z3f is not None else nl, 0.95
        )
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=z3f,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=0.95,
            prop_kind=PropKind.EQUALITY,
            free_vars=fv,
            negated=False,
            decidable=dec,
            z3_fragment=frag,
            components=(comp,),
        )

    # -- comparison -----------------------------------------------------------

    def _translate_comparison(
        self, prop: LeanExpr, norm: str
    ) -> TranslatedPredicate:
        """Handle ``LE.le a b``, ``LT.lt a b``, etc."""
        args = _lean_app_args(prop)
        # Lean comparison operators often carry instance args first
        if len(args) >= 2:
            lhs_expr, rhs_expr = args[-2], args[-1]
        else:
            return self._unknown(prop)

        op_code = _CMP_OP[norm]
        op_name = {
            LE: "le",
            LT: "lt",
            GE: "ge",
            GT: "gt",
            EQ: "eq",
            NE: "ne",
        }[op_code]
        lhs_ot = self._expr_to_oterm(lhs_expr)
        rhs_ot = self._expr_to_oterm(rhs_expr)
        oterm = _oterm_binop(op_name, lhs_ot, rhs_ot)

        lhs_z3 = self._expr_to_z3(lhs_expr)
        rhs_z3 = self._expr_to_z3(rhs_expr)
        z3f = self._z3_cmp(op_code, lhs_z3, rhs_z3)

        nl_verb = _NL_CMP.get(norm, norm)
        lhs_s = self._expr_to_str(lhs_expr)
        rhs_s = self._expr_to_str(rhs_expr)
        nl = f"{lhs_s} {nl_verb} {rhs_s}"

        fv = _free_vars(prop)
        frag = self._classify_fragment(z3f, fv)
        dec = frag != Z3Fragment.UNKNOWN

        comp = PredicateComponent(
            "structural", z3f if z3f is not None else nl, 0.95
        )
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=z3f,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=0.95,
            prop_kind=PropKind.COMPARISON,
            free_vars=fv,
            negated=False,
            decidable=dec,
            z3_fragment=frag,
            components=(comp,),
        )

    # -- connectives ----------------------------------------------------------

    def _translate_connective(
        self, prop: LeanExpr, norm: str
    ) -> TranslatedPredicate:
        """Handle And / Or / Not / Iff / True / False."""
        if norm == "true":
            return self._make_literal_pred(prop, True)
        if norm == "false":
            return self._make_literal_pred(prop, False)

        args = _lean_app_args(prop)

        if norm == "not":
            if len(args) < 1:
                return self._unknown(prop)
            inner = self.translate(args[0])
            z3f = None
            if inner.z3_formula is not None and _HAS_Z3:
                z3f = _z3.Not(inner.z3_formula)
            oterm = (
                _oterm_unop("not", inner.oterm_pattern)
                if inner.oterm_pattern
                else None
            )
            nl = f"not ({inner.nl_description})"
            fv = inner.free_vars
            frag = self._classify_fragment(z3f, fv)
            comp = PredicateComponent(
                "structural",
                z3f if z3f is not None else nl,
                inner.confidence,
            )
            return TranslatedPredicate(
                lean_prop=prop,
                z3_formula=z3f,
                oterm_pattern=oterm,
                nl_description=nl,
                confidence=inner.confidence,
                prop_kind=PropKind.CONNECTIVE,
                free_vars=fv,
                negated=True,
                decidable=inner.decidable,
                z3_fragment=frag,
                components=(comp,),
            )

        if len(args) < 2:
            return self._unknown(prop)

        left = self.translate(args[0])
        right = self.translate(args[1])

        z3f: Any = None
        oterm: Optional[OTerm] = None
        nl: str = ""

        if norm == "and":
            z3f = self._z3_and(left.z3_formula, right.z3_formula)
            oterm = (
                _oterm_binop("and", left.oterm_pattern, right.oterm_pattern)
                if left.oterm_pattern and right.oterm_pattern
                else None
            )
            nl = f"({left.nl_description}) and ({right.nl_description})"
        elif norm == "or":
            z3f = self._z3_or(left.z3_formula, right.z3_formula)
            oterm = (
                _oterm_binop("or", left.oterm_pattern, right.oterm_pattern)
                if left.oterm_pattern and right.oterm_pattern
                else None
            )
            nl = f"({left.nl_description}) or ({right.nl_description})"
        elif norm == "iff":
            z3f = self._z3_iff(left.z3_formula, right.z3_formula)
            oterm = (
                _oterm_binop("iff", left.oterm_pattern, right.oterm_pattern)
                if left.oterm_pattern and right.oterm_pattern
                else None
            )
            nl = (
                f"({left.nl_description}) if and only if"
                f" ({right.nl_description})"
            )
        else:
            return self._unknown(prop)

        fv = left.free_vars | right.free_vars
        frag = self._classify_fragment(z3f, fv)
        conf = min(left.confidence, right.confidence)
        dec = left.decidable and right.decidable

        comp_l = PredicateComponent(
            "structural", left.z3_formula, left.confidence
        )
        comp_r = PredicateComponent(
            "structural", right.z3_formula, right.confidence
        )
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=z3f,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=conf,
            prop_kind=PropKind.CONNECTIVE,
            free_vars=fv,
            negated=False,
            decidable=dec,
            z3_fragment=frag,
            components=(comp_l, comp_r),
        )

    # -- quantifiers ----------------------------------------------------------

    def _translate_quantifier(
        self,
        prop: LeanExpr,
        norm: str,
        *,
        existential: bool,
    ) -> TranslatedPredicate:
        """Handle forall (LeanPi) and exists / Sigma (LeanApp)."""
        if isinstance(prop, LeanPi):
            return self._translate_forall(prop)

        args = _lean_app_args(prop)
        # Exists alpha (fun x => body) => args = [alpha, lambda x => body]
        if len(args) < 2:
            return self._unknown(prop)

        _ty_expr = args[0]
        body_lam = args[1]

        var_name = "x"
        body_expr: LeanExpr = body_lam
        if isinstance(body_lam, LeanLam) and body_lam.params:
            var_name = body_lam.params[0].name
            body_expr = body_lam.body

        inner = self.translate(body_expr)

        z3f = None
        if inner.z3_formula is not None and _HAS_Z3:
            z3_var = _z3.Int(var_name)
            z3f = _z3.Exists([z3_var], inner.z3_formula)

        oterm = (
            OLam((var_name,), inner.oterm_pattern)
            if inner.oterm_pattern
            else None
        )
        quant_word = "there exists" if existential else "for all"
        nl = f"{quant_word} {var_name}, {inner.nl_description}"

        fv = inner.free_vars - {var_name}
        frag = self._classify_fragment(z3f, fv)
        # Quantifiers are generally not decidable
        dec = False
        comp = PredicateComponent(
            "mixed",
            z3f if z3f is not None else nl,
            inner.confidence * 0.9,
        )

        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=z3f,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=inner.confidence * 0.9,
            prop_kind=PropKind.QUANTIFIER,
            free_vars=fv,
            negated=False,
            decidable=dec,
            z3_fragment=frag,
            components=(comp,),
        )

    def _translate_forall(self, prop: LeanPi) -> TranslatedPredicate:
        """Translate a Pi-type viewed as forall."""
        params = prop.params
        body = prop.codomain

        inner = self.translate(body)

        var_names = [p.name for p in params]
        z3f = None
        if inner.z3_formula is not None and _HAS_Z3:
            z3_vars = [_z3.Int(v) for v in var_names]
            z3f = _z3.ForAll(z3_vars, inner.z3_formula)

        oterm = (
            OLam(tuple(var_names), inner.oterm_pattern)
            if inner.oterm_pattern
            else None
        )
        var_list = ", ".join(var_names)
        nl = f"for all {var_list}, {inner.nl_description}"

        bound = frozenset(var_names)
        fv = inner.free_vars - bound
        frag = self._classify_fragment(z3f, fv)
        comp = PredicateComponent(
            "mixed",
            z3f if z3f is not None else nl,
            inner.confidence * 0.85,
        )

        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=z3f,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=inner.confidence * 0.85,
            prop_kind=PropKind.QUANTIFIER,
            free_vars=fv,
            negated=False,
            decidable=False,
            z3_fragment=frag,
            components=(comp,),
        )

    # -- list propositions ----------------------------------------------------

    def _translate_list_prop(
        self, prop: LeanExpr, norm: str
    ) -> TranslatedPredicate:
        """Handle List.Mem, List.Nodup, List.Sorted, List.Perm, etc."""
        args = _lean_app_args(prop)
        oterm: Optional[OTerm] = None
        nl = ""
        z3f = None
        confidence = 0.85
        decidable = False

        if norm == "list_mem":
            if len(args) >= 2:
                elem, lst = args[-2], args[-1]
                oterm = _oterm_binop(
                    "list_mem",
                    self._expr_to_oterm(elem),
                    self._expr_to_oterm(lst),
                )
                es = self._expr_to_str(elem)
                ls = self._expr_to_str(lst)
                nl = f"{es} is in {ls}"
                decidable = True
            else:
                nl = "list membership"
        elif norm == "list_nodup":
            if args:
                lst = args[-1]
                oterm = _oterm_unop(
                    "list_nodup", self._expr_to_oterm(lst)
                )
                nl = f"{self._expr_to_str(lst)} has no duplicates"
                decidable = True
            else:
                nl = "list has no duplicates"
        elif norm == "list_sorted":
            if len(args) >= 2:
                rel, lst = args[-2], args[-1]
                oterm = _oterm_binop(
                    "list_sorted",
                    self._expr_to_oterm(rel),
                    self._expr_to_oterm(lst),
                )
                nl = (
                    f"{self._expr_to_str(lst)} is sorted"
                    f" by {self._expr_to_str(rel)}"
                )
                decidable = True
            elif args:
                lst = args[-1]
                oterm = _oterm_unop(
                    "list_sorted", self._expr_to_oterm(lst)
                )
                nl = f"{self._expr_to_str(lst)} is sorted"
                decidable = True
            else:
                nl = "list is sorted"
        elif norm == "list_perm":
            if len(args) >= 2:
                l1, l2 = args[-2], args[-1]
                oterm = _oterm_binop(
                    "list_perm",
                    self._expr_to_oterm(l1),
                    self._expr_to_oterm(l2),
                )
                nl = (
                    f"{self._expr_to_str(l1)} is a permutation"
                    f" of {self._expr_to_str(l2)}"
                )
                decidable = True
            else:
                nl = "lists are permutations"
        elif norm == "list_sublist":
            if len(args) >= 2:
                sub, sup = args[-2], args[-1]
                oterm = _oterm_binop(
                    "list_sublist",
                    self._expr_to_oterm(sub),
                    self._expr_to_oterm(sup),
                )
                nl = (
                    f"{self._expr_to_str(sub)} is a sublist"
                    f" of {self._expr_to_str(sup)}"
                )
                decidable = True
            else:
                nl = "list is a sublist"
        elif norm == "list_chain":
            if len(args) >= 3:
                rel = args[-3]
                head_val = args[-2]
                lst = args[-1]
                oterm = OOp(
                    "list_chain",
                    (
                        self._expr_to_oterm(rel),
                        self._expr_to_oterm(head_val),
                        self._expr_to_oterm(lst),
                    ),
                )
                nl = (
                    f"{self._expr_to_str(lst)} is chained"
                    f" from {self._expr_to_str(head_val)}"
                    f" by {self._expr_to_str(rel)}"
                )
            else:
                nl = "list is chained"
        elif norm == "list_forall":
            if len(args) >= 2:
                pred_arg, lst = args[-2], args[-1]
                oterm = _oterm_binop(
                    "list_forall",
                    self._expr_to_oterm(pred_arg),
                    self._expr_to_oterm(lst),
                )
                nl = (
                    f"all elements of {self._expr_to_str(lst)}"
                    f" satisfy {self._expr_to_str(pred_arg)}"
                )
            else:
                nl = "all list elements satisfy predicate"
        else:
            nl = f"list property: {norm}"
            confidence = 0.6

        fv = _free_vars(prop)
        comp = PredicateComponent("semantic", nl, confidence)
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=z3f,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=confidence,
            prop_kind=PropKind.LIST_PROP,
            free_vars=fv,
            negated=False,
            decidable=decidable,
            z3_fragment=Z3Fragment.UNKNOWN,
            components=(comp,),
        )

    # -- set / finset propositions --------------------------------------------

    def _translate_set_prop(
        self, prop: LeanExpr, norm: str
    ) -> TranslatedPredicate:
        """Handle Set.Mem, Set.Subset, Set.Finite, Finset.mem, etc."""
        args = _lean_app_args(prop)
        oterm: Optional[OTerm] = None
        nl = ""
        confidence = 0.8
        decidable = False

        if norm in ("set_mem", "finset_mem"):
            if len(args) >= 2:
                elem, s = args[-2], args[-1]
                oterm = _oterm_binop(
                    "set_mem",
                    self._expr_to_oterm(elem),
                    self._expr_to_oterm(s),
                )
                es = self._expr_to_str(elem)
                ss = self._expr_to_str(s)
                nl = f"{es} is in {ss}"
                decidable = norm == "finset_mem"
            else:
                nl = "set membership"
        elif norm == "set_subset":
            if len(args) >= 2:
                a, b = args[-2], args[-1]
                oterm = _oterm_binop(
                    "set_subset",
                    self._expr_to_oterm(a),
                    self._expr_to_oterm(b),
                )
                nl = (
                    f"{self._expr_to_str(a)} is a subset"
                    f" of {self._expr_to_str(b)}"
                )
            else:
                nl = "set is a subset"
        elif norm == "set_finite":
            if args:
                s = args[-1]
                oterm = _oterm_unop(
                    "set_finite", self._expr_to_oterm(s)
                )
                nl = f"{self._expr_to_str(s)} is finite"
            else:
                nl = "set is finite"
        elif norm == "finset_card":
            if args:
                s = args[-1]
                oterm = _oterm_unop(
                    "finset_card", self._expr_to_oterm(s)
                )
                nl = f"|{self._expr_to_str(s)}|"
            else:
                nl = "finset cardinality"
        else:
            nl = f"set property: {norm}"
            confidence = 0.6

        fv = _free_vars(prop)
        comp = PredicateComponent("semantic", nl, confidence)
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=None,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=confidence,
            prop_kind=PropKind.SET_PROP,
            free_vars=fv,
            negated=False,
            decidable=decidable,
            z3_fragment=Z3Fragment.UNKNOWN,
            components=(comp,),
        )

    # -- function propositions ------------------------------------------------

    def _translate_function_prop(
        self, prop: LeanExpr, norm: str
    ) -> TranslatedPredicate:
        """Handle Function.Injective, Surjective, Bijective, etc."""
        args = _lean_app_args(prop)
        fn_expr = args[-1] if args else prop
        fn_name = self._expr_to_str(fn_expr)
        oterm: Optional[OTerm] = None
        nl = ""
        confidence = 0.8

        label_map: Dict[str, Tuple[str, str]] = {
            "fun_injective": ("injective", "is injective"),
            "fun_surjective": ("surjective", "is surjective"),
            "fun_bijective": ("bijective", "is bijective"),
            "fun_left_inv": ("left_inverse", "has a left inverse"),
            "fun_right_inv": ("right_inverse", "has a right inverse"),
        }
        op_label, nl_frag = label_map.get(norm, (norm, norm))
        oterm = _oterm_unop(op_label, self._expr_to_oterm(fn_expr))
        nl = f"{fn_name} {nl_frag}"

        fv = _free_vars(prop)
        comp = PredicateComponent("semantic", nl, confidence)
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=None,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=confidence,
            prop_kind=PropKind.FUNCTION_PROP,
            free_vars=fv,
            negated=False,
            decidable=False,
            z3_fragment=Z3Fragment.UNKNOWN,
            components=(comp,),
        )

    # -- algebraic propositions -----------------------------------------------

    def _translate_algebraic_prop(
        self, prop: LeanExpr, norm: str
    ) -> TranslatedPredicate:
        """Handle IsCommutative, IsAssociative, IsIdempotent."""
        args = _lean_app_args(prop)
        op_expr = args[-1] if args else prop
        op_name_str = self._expr_to_str(op_expr)

        label_map: Dict[str, Tuple[str, str]] = {
            "is_comm": ("commutative", "is commutative"),
            "is_assoc": ("associative", "is associative"),
            "is_idempotent": ("idempotent", "is idempotent"),
        }
        op_label, nl_frag = label_map.get(norm, (norm, norm))
        oterm = _oterm_unop(op_label, self._expr_to_oterm(op_expr))
        nl = f"{op_name_str} {nl_frag}"

        fv = _free_vars(prop)
        comp = PredicateComponent("semantic", nl, 0.75)
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=None,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=0.75,
            prop_kind=PropKind.ALGEBRAIC_PROP,
            free_vars=fv,
            negated=False,
            decidable=False,
            z3_fragment=Z3Fragment.UNKNOWN,
            components=(comp,),
        )

    # -- order propositions ---------------------------------------------------

    def _translate_order_prop(
        self, prop: LeanExpr, norm: str
    ) -> TranslatedPredicate:
        """Handle Monotone, StrictMono, Antitone, StrictAnti."""
        args = _lean_app_args(prop)
        fn_expr = args[-1] if args else prop
        fn_name = self._expr_to_str(fn_expr)

        label_map: Dict[str, Tuple[str, str]] = {
            "monotone": ("monotone", "is monotone"),
            "strict_mono": ("strict_mono", "is strictly monotone"),
            "antitone": ("antitone", "is antitone"),
            "strict_anti": ("strict_anti", "is strictly antitone"),
        }
        op_label, nl_frag = label_map.get(norm, (norm, norm))
        oterm = _oterm_unop(op_label, self._expr_to_oterm(fn_expr))
        nl = f"{fn_name} {nl_frag}"

        fv = _free_vars(prop)
        comp = PredicateComponent("semantic", nl, 0.8)
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=None,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=0.8,
            prop_kind=PropKind.ORDER_PROP,
            free_vars=fv,
            negated=False,
            decidable=False,
            z3_fragment=Z3Fragment.UNKNOWN,
            components=(comp,),
        )

    # -- number theory propositions -------------------------------------------

    def _translate_number_theory(
        self, prop: LeanExpr, norm: str
    ) -> TranslatedPredicate:
        """Handle Nat.Prime, Dvd, Even, Odd, Coprime, gcd, etc."""
        args = _lean_app_args(prop)
        oterm: Optional[OTerm] = None
        nl = ""
        z3f = None
        confidence = 0.8
        decidable_flag = True

        if norm == "nat_prime":
            if args:
                n = args[-1]
                oterm = _oterm_unop(
                    "nat_prime", self._expr_to_oterm(n)
                )
                nl = f"{self._expr_to_str(n)} is prime"
            else:
                nl = "number is prime"
        elif norm in ("dvd", "nat_dvd"):
            if len(args) >= 2:
                a, b = args[-2], args[-1]
                oterm = _oterm_binop(
                    "dvd",
                    self._expr_to_oterm(a),
                    self._expr_to_oterm(b),
                )
                nl = (
                    f"{self._expr_to_str(a)} divides"
                    f" {self._expr_to_str(b)}"
                )
                a_z3 = self._expr_to_z3(a)
                b_z3 = self._expr_to_z3(b)
                if (
                    a_z3 is not None
                    and b_z3 is not None
                    and _HAS_Z3
                ):
                    k = _z3.Int("__k_dvd")
                    z3f = _z3.Exists([k], b_z3 == a_z3 * k)
            else:
                nl = "divisibility"
        elif norm == "even":
            if args:
                n = args[-1]
                oterm = _oterm_unop("even", self._expr_to_oterm(n))
                nl = f"{self._expr_to_str(n)} is even"
                n_z3 = self._expr_to_z3(n)
                if n_z3 is not None and _HAS_Z3:
                    k = _z3.Int("__k_even")
                    z3f = _z3.Exists([k], n_z3 == 2 * k)
            else:
                nl = "number is even"
        elif norm == "odd":
            if args:
                n = args[-1]
                oterm = _oterm_unop("odd", self._expr_to_oterm(n))
                nl = f"{self._expr_to_str(n)} is odd"
                n_z3 = self._expr_to_z3(n)
                if n_z3 is not None and _HAS_Z3:
                    k = _z3.Int("__k_odd")
                    z3f = _z3.Exists([k], n_z3 == 2 * k + 1)
            else:
                nl = "number is odd"
        elif norm == "nat_coprime":
            if len(args) >= 2:
                a, b = args[-2], args[-1]
                oterm = _oterm_binop(
                    "coprime",
                    self._expr_to_oterm(a),
                    self._expr_to_oterm(b),
                )
                nl = (
                    f"{self._expr_to_str(a)} and"
                    f" {self._expr_to_str(b)} are coprime"
                )
            else:
                nl = "numbers are coprime"
        elif norm in ("int_gcd", "nat_gcd"):
            if len(args) >= 2:
                a, b = args[-2], args[-1]
                oterm = _oterm_binop(
                    "gcd",
                    self._expr_to_oterm(a),
                    self._expr_to_oterm(b),
                )
                nl = (
                    f"gcd({self._expr_to_str(a)},"
                    f" {self._expr_to_str(b)})"
                )
            else:
                nl = "gcd"
        else:
            nl = f"number theory: {norm}"
            confidence = 0.6

        fv = _free_vars(prop)
        frag = (
            self._classify_fragment(z3f, fv)
            if z3f is not None
            else Z3Fragment.UNKNOWN
        )
        kind = "structural" if z3f is not None else "semantic"
        comp = PredicateComponent(
            kind, z3f if z3f is not None else nl, confidence
        )
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=z3f,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=confidence,
            prop_kind=PropKind.NUMBER_THEORY,
            free_vars=fv,
            negated=False,
            decidable=decidable_flag,
            z3_fragment=frag,
            components=(comp,),
        )

    # -- arithmetic (fallback) ------------------------------------------------

    def _try_translate_arith(
        self, prop: LeanExpr
    ) -> Optional[TranslatedPredicate]:
        """Try to interpret *prop* as an arithmetic expression."""
        if not isinstance(prop, LeanApp):
            return None

        head = _lean_head(prop)
        if head is None:
            return None

        arith_ops: Dict[str, Tuple[str, int]] = {
            "HAdd.hAdd": ("add", ADD),
            "HSub.hSub": ("sub", SUB),
            "HMul.hMul": ("mul", MUL),
            "HDiv.hDiv": ("div", 5),
            "HMod.hMod": ("mod", 6),
            "Neg.neg": ("neg", NEG),
            "Nat.add": ("add", ADD),
            "Nat.sub": ("sub", SUB),
            "Nat.mul": ("mul", MUL),
            "Nat.succ": ("succ", ADD),
            "Nat.pred": ("pred", SUB),
            "Int.add": ("add", ADD),
            "Int.sub": ("sub", SUB),
            "Int.mul": ("mul", MUL),
            "Int.neg": ("neg", NEG),
            "Max.max": ("max", MAX),
            "Min.min": ("min", MIN),
        }

        clean_head = head.lstrip("@")
        if clean_head not in arith_ops:
            return None

        op_label, op_code = arith_ops[clean_head]
        args = _lean_app_args(prop)

        oterm: OTerm
        z3f: Any = None
        nl: str = ""

        if op_label in ("neg", "succ", "pred"):
            if not args:
                return None
            operand = args[-1]
            oterm = _oterm_unop(
                op_label, self._expr_to_oterm(operand)
            )
            z3_operand = self._expr_to_z3(operand)
            if z3_operand is not None and _HAS_Z3:
                if op_label == "neg":
                    z3f = -z3_operand
                elif op_label == "succ":
                    z3f = z3_operand + 1
                else:
                    z3f = z3_operand - 1
            nl = f"{op_label}({self._expr_to_str(operand)})"
        else:
            if len(args) < 2:
                return None
            lhs_expr, rhs_expr = args[-2], args[-1]
            lhs_ot = self._expr_to_oterm(lhs_expr)
            rhs_ot = self._expr_to_oterm(rhs_expr)
            oterm = _oterm_binop(op_label, lhs_ot, rhs_ot)

            lhs_z3 = self._expr_to_z3(lhs_expr)
            rhs_z3 = self._expr_to_z3(rhs_expr)
            z3f = self._z3_arith(op_code, lhs_z3, rhs_z3)
            nl = (
                f"{self._expr_to_str(lhs_expr)} {op_label}"
                f" {self._expr_to_str(rhs_expr)}"
            )

        fv = _free_vars(prop)
        frag = (
            self._classify_fragment(z3f, fv)
            if z3f is not None
            else Z3Fragment.UNKNOWN
        )
        kind = "structural" if z3f is not None else "semantic"
        comp = PredicateComponent(kind, z3f if z3f is not None else nl, 0.9)
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=z3f,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=0.9,
            prop_kind=PropKind.ARITHMETIC,
            free_vars=fv,
            negated=False,
            decidable=z3f is not None,
            z3_fragment=frag,
            components=(comp,),
        )

    # -- literal / bare-var fallbacks -----------------------------------------

    def _translate_literal(self, prop: LeanLit) -> TranslatedPredicate:
        val = prop.value
        oterm = _oterm_for_lit(val)
        nl = str(val)
        comp = PredicateComponent("structural", nl, 1.0)
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=None,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=1.0,
            prop_kind=PropKind.LITERAL,
            free_vars=frozenset(),
            negated=False,
            decidable=True,
            z3_fragment=Z3Fragment.QF_LIA,
            components=(comp,),
        )

    def _translate_bare_var(self, prop: LeanVar) -> TranslatedPredicate:
        oterm = _oterm_for_var(prop.name)
        nl = prop.name
        comp = PredicateComponent("semantic", nl, 0.7)
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=_mk_z3_bool(prop.name),
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=0.7,
            prop_kind=PropKind.UNKNOWN,
            free_vars=frozenset({prop.name}),
            negated=False,
            decidable=True,
            z3_fragment=Z3Fragment.QF_LIA,
            components=(comp,),
        )

    def _make_literal_pred(
        self, prop: LeanExpr, value: bool
    ) -> TranslatedPredicate:
        z3f = _z3.BoolVal(value) if _HAS_Z3 else None
        oterm = _oterm_for_lit(value)
        nl = "True" if value else "False"
        comp = PredicateComponent(
            "structural", z3f if z3f is not None else nl, 1.0
        )
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=z3f,
            oterm_pattern=oterm,
            nl_description=nl,
            confidence=1.0,
            prop_kind=PropKind.LITERAL,
            free_vars=frozenset(),
            negated=not value,
            decidable=True,
            z3_fragment=Z3Fragment.QF_LIA,
            components=(comp,),
        )

    def _unknown(self, prop: LeanExpr) -> TranslatedPredicate:
        nl = f"<untranslated: {self._expr_to_str(prop)}>"
        comp = PredicateComponent("semantic", nl, 0.3)
        return TranslatedPredicate(
            lean_prop=prop,
            z3_formula=None,
            oterm_pattern=OUnknown(nl),
            nl_description=nl,
            confidence=0.3,
            prop_kind=PropKind.UNKNOWN,
            free_vars=_free_vars(prop),
            negated=False,
            decidable=False,
            z3_fragment=Z3Fragment.UNKNOWN,
            components=(comp,),
        )

    # -- Z3 helpers -----------------------------------------------------------

    def _z3_cmp(self, op: int, lhs: Any, rhs: Any) -> Any:
        if lhs is None or rhs is None or not _HAS_Z3:
            return None
        if op == LE:
            return lhs <= rhs
        if op == LT:
            return lhs < rhs
        if op == GE:
            return lhs >= rhs
        if op == GT:
            return lhs > rhs
        if op == EQ:
            return lhs == rhs
        if op == NE:
            return lhs != rhs
        return None

    def _z3_arith(self, op: int, lhs: Any, rhs: Any) -> Any:
        if lhs is None or rhs is None or not _HAS_Z3:
            return None
        if op == ADD:
            return lhs + rhs
        if op == SUB:
            return lhs - rhs
        if op == MUL:
            return lhs * rhs
        if op == MAX:
            return _z3.If(lhs >= rhs, lhs, rhs)
        if op == MIN:
            return _z3.If(lhs <= rhs, lhs, rhs)
        return None

    def _z3_and(self, a: Any, b: Any) -> Any:
        if a is None or b is None or not _HAS_Z3:
            return None
        return _z3.And(a, b)

    def _z3_or(self, a: Any, b: Any) -> Any:
        if a is None or b is None or not _HAS_Z3:
            return None
        return _z3.Or(a, b)

    def _z3_iff(self, a: Any, b: Any) -> Any:
        if a is None or b is None or not _HAS_Z3:
            return None
        return a == b

    # -- fragment classification ----------------------------------------------

    def classify_z3_fragment(self, formula: Any) -> Z3Fragment:
        """Public entry-point for fragment classification."""
        return self._classify_fragment(formula, frozenset())

    def _classify_fragment(
        self, formula: Any, free_vars: FrozenSet[str]
    ) -> Z3Fragment:
        """Heuristic classification of a Z3 formula into an SMT-LIB logic."""
        if formula is None or not _HAS_Z3:
            return Z3Fragment.UNKNOWN

        s = str(formula)

        has_quantifier = "ForAll" in s or "Exists" in s
        has_array = "Store" in s or "Select" in s
        has_mul_vars = bool(re.search(r"\*\s*[a-zA-Z]", s))
        has_real = "Real" in s or "/" in s
        has_int = "Int" in s  # noqa: F841

        if has_quantifier and has_mul_vars:
            return Z3Fragment.AUFNIRA
        if has_quantifier and has_array:
            return Z3Fragment.QF_AUFLIA
        if has_quantifier:
            return Z3Fragment.AUFNIRA
        if has_array:
            return Z3Fragment.QF_AUFLIA
        if has_real:
            return Z3Fragment.QF_LRA
        if has_mul_vars:
            return Z3Fragment.QF_NIA
        return Z3Fragment.QF_LIA

    # -- decidability check ---------------------------------------------------

    def is_decidable(self, prop: LeanExpr) -> bool:
        """Quick check: is the proposition decidable?"""
        pred = self.translate(prop)
        return pred.decidable

    # -- expr -> OTerm --------------------------------------------------------

    def _expr_to_oterm(self, expr: LeanExpr) -> OTerm:
        """Best-effort conversion of a LeanExpr to an OTerm."""
        if isinstance(expr, LeanVar):
            return OVar(expr.name)
        if isinstance(expr, LeanLit):
            return OLit(expr.value)
        if isinstance(expr, LeanApp):
            head = _lean_head(expr)
            args = _lean_app_args(expr)
            if head:
                clean = head.lstrip("@")
                oterm_args = tuple(
                    self._expr_to_oterm(a) for a in args
                )
                return OOp(clean, oterm_args)
            return OUnknown(self._expr_to_str(expr))
        if isinstance(expr, LeanLam):
            param_names = tuple(p.name for p in expr.params)
            return OLam(param_names, self._expr_to_oterm(expr.body))
        if isinstance(expr, LeanIf):
            return OCase(
                self._expr_to_oterm(expr.cond),
                (
                    ("true", self._expr_to_oterm(expr.then_)),
                    ("false", self._expr_to_oterm(expr.else_)),
                ),
            )
        if isinstance(expr, LeanProj):
            return OOp(
                f"proj_{expr.field}",
                (self._expr_to_oterm(expr.expr),),
            )
        if isinstance(expr, LeanLet):
            return OOp(
                "let",
                (
                    OLit(expr.name),
                    self._expr_to_oterm(expr.value),
                    self._expr_to_oterm(expr.body),
                ),
            )
        return OUnknown(self._expr_to_str(expr))

    # -- expr -> Z3 -----------------------------------------------------------

    def _expr_to_z3(self, expr: LeanExpr) -> Any:
        """Best-effort conversion of a LeanExpr to a Z3 expression."""
        if not _HAS_Z3:
            return None
        if isinstance(expr, LeanVar):
            name = expr.name
            if name not in self._z3_vars:
                self._z3_vars[name] = _z3.Int(name)
            return self._z3_vars[name]
        if isinstance(expr, LeanLit):
            v = expr.value
            if isinstance(v, bool):
                return _z3.BoolVal(v)
            if isinstance(v, int):
                return _z3.IntVal(v)
            if isinstance(v, float):
                return _z3.RealVal(v)
            return None
        if isinstance(expr, LeanApp):
            head = _lean_head(expr)
            if head is None:
                return None
            clean = head.lstrip("@")
            args = _lean_app_args(expr)

            arith_bin: Dict[str, Callable[..., Any]] = {
                "HAdd.hAdd": lambda a, b: a + b,
                "HSub.hSub": lambda a, b: a - b,
                "HMul.hMul": lambda a, b: a * b,
                "Nat.add": lambda a, b: a + b,
                "Nat.sub": lambda a, b: a - b,
                "Nat.mul": lambda a, b: a * b,
                "Int.add": lambda a, b: a + b,
                "Int.sub": lambda a, b: a - b,
                "Int.mul": lambda a, b: a * b,
            }
            if clean in arith_bin and len(args) >= 2:
                left = self._expr_to_z3(args[-2])
                right = self._expr_to_z3(args[-1])
                if left is not None and right is not None:
                    return arith_bin[clean](left, right)

            arith_un: Dict[str, Callable[..., Any]] = {
                "Neg.neg": lambda a: -a,
                "Int.neg": lambda a: -a,
                "Nat.succ": lambda a: a + 1,
            }
            if clean in arith_un and args:
                a = self._expr_to_z3(args[-1])
                if a is not None:
                    return arith_un[clean](a)

            cmp_ops: Dict[str, Callable[..., Any]] = {
                "LE.le": lambda a, b: a <= b,
                "LT.lt": lambda a, b: a < b,
                "GE.ge": lambda a, b: a >= b,
                "GT.gt": lambda a, b: a > b,
                "Eq": lambda a, b: a == b,
                "Ne": lambda a, b: a != b,
            }
            if clean in cmp_ops and len(args) >= 2:
                left = self._expr_to_z3(args[-2])
                right = self._expr_to_z3(args[-1])
                if left is not None and right is not None:
                    return cmp_ops[clean](left, right)

            if clean == "Max.max" and len(args) >= 2:
                left = self._expr_to_z3(args[-2])
                right = self._expr_to_z3(args[-1])
                if left is not None and right is not None:
                    return _z3.If(left >= right, left, right)
            if clean == "Min.min" and len(args) >= 2:
                left = self._expr_to_z3(args[-2])
                right = self._expr_to_z3(args[-1])
                if left is not None and right is not None:
                    return _z3.If(left <= right, left, right)

        return None

    # -- expr -> string -------------------------------------------------------

    def _expr_to_str(self, expr: LeanExpr) -> str:
        """Produce a concise human-readable string for *expr*."""
        if isinstance(expr, LeanVar):
            return expr.name
        if isinstance(expr, LeanLit):
            return str(expr.value)
        if isinstance(expr, LeanApp):
            head = _lean_head(expr)
            args = _lean_app_args(expr)
            if head:
                if len(args) == 0:
                    return head
                arg_strs = ", ".join(
                    self._expr_to_str(a) for a in args
                )
                return f"{head}({arg_strs})"
            return "<app>"
        if isinstance(expr, LeanLam):
            params = ", ".join(p.name for p in expr.params)
            body_s = self._expr_to_str(expr.body)
            return f"fun {params} => {body_s}"
        if isinstance(expr, LeanPi):
            params = ", ".join(p.name for p in expr.params)
            cod_s = self._expr_to_str(expr.codomain)
            return f"forall {params}, {cod_s}"
        if isinstance(expr, LeanIf):
            c = self._expr_to_str(expr.cond)
            t = self._expr_to_str(expr.then_)
            e = self._expr_to_str(expr.else_)
            return f"if {c} then {t} else {e}"
        if isinstance(expr, LeanLet):
            v = self._expr_to_str(expr.value)
            b = self._expr_to_str(expr.body)
            return f"let {expr.name} := {v} in {b}"
        if isinstance(expr, LeanProj):
            inner = self._expr_to_str(expr.expr)
            return f"{inner}.{expr.field}"
        if isinstance(expr, LeanSort):
            return f"Sort {expr.level}"
        if isinstance(expr, LeanMatch):
            return "<match>"
        if isinstance(expr, (LeanHole, LeanSorry)):
            return "_"
        return "<expr>"


# -- Reverse translator: CCTT -> Lean -----------------------------------------


class CCTTPredicateToLeanProp:
    """Translate OTerm predicates back to Lean expressions.

    This is the *inverse* of ``LeanPropToCCTTPredicate``.  It is
    necessarily partial -- many OTerm shapes have no canonical Lean
    counterpart -- but it covers the common comparison/arithmetic/
    connective/quantifier shapes that round-trip reliably.
    """

    # op-name -> Lean constant name for binary comparisons
    _BIN_CMP_MAP: Dict[str, str] = {
        "eq": "Eq",
        "ne": "Ne",
        "le": "LE.le",
        "lt": "LT.lt",
        "ge": "GE.ge",
        "gt": "GT.gt",
    }

    _BIN_ARITH_MAP: Dict[str, str] = {
        "add": "HAdd.hAdd",
        "sub": "HSub.hSub",
        "mul": "HMul.hMul",
        "div": "HDiv.hDiv",
        "mod": "HMod.hMod",
        "max": "Max.max",
        "min": "Min.min",
    }

    _UN_MAP: Dict[str, str] = {
        "neg": "Neg.neg",
        "succ": "Nat.succ",
        "pred": "Nat.pred",
        "not": "Not",
        "even": "Even",
        "odd": "Odd",
        "nat_prime": "Nat.Prime",
        "injective": "Function.Injective",
        "surjective": "Function.Surjective",
        "bijective": "Function.Bijective",
        "left_inverse": "Function.LeftInverse",
        "right_inverse": "Function.RightInverse",
        "monotone": "Monotone",
        "strict_mono": "StrictMono",
        "antitone": "Antitone",
        "strict_anti": "StrictAnti",
        "commutative": "IsCommutative",
        "associative": "IsAssociative",
        "idempotent": "IsIdempotent",
        "list_nodup": "List.Nodup",
        "set_finite": "Set.Finite",
        "finset_card": "Finset.card",
    }

    _BIN_MISC_MAP: Dict[str, str] = {
        "and": "And",
        "or": "Or",
        "iff": "Iff",
        "dvd": "Dvd",
        "coprime": "Nat.Coprime",
        "gcd": "Nat.gcd",
        "list_mem": "List.Mem",
        "list_perm": "List.Perm",
        "list_sublist": "List.Sublist",
        "list_sorted": "List.Sorted",
        "list_forall": "List.Forall",
        "set_mem": "Set.Mem",
        "set_subset": "Set.Subset",
    }

    def translate(self, oterm: OTerm) -> LeanExpr:
        """Translate an OTerm to a LeanExpr (best-effort)."""
        if isinstance(oterm, OVar):
            return LeanVar(oterm.name)
        if isinstance(oterm, OLit):
            return LeanLit(oterm.value)
        if isinstance(oterm, OOp):
            return self._translate_op(oterm)
        if isinstance(oterm, OLam):
            params = [
                LeanParam(name=n, type_=None, binder="(")
                for n in oterm.params
            ]
            body = self.translate(oterm.body)
            return LeanLam(params=params, body=body)
        if isinstance(oterm, OCase):
            cond = self.translate(oterm.scrutinee)
            branches = oterm.arms
            if len(branches) >= 2:
                then_ = self.translate(branches[0][1])
                else_ = self.translate(branches[1][1])
                return LeanIf(cond=cond, then_=then_, else_=else_)
            return LeanVar("<case>")
        if isinstance(oterm, OUnknown):
            return LeanVar(f"<unknown:{oterm.tag}>")
        if isinstance(oterm, OSeq):
            elems = [self.translate(e) for e in oterm.items]
            return LeanApp(fn=LeanVar("List.mk"), args=elems)
        if isinstance(oterm, ODict):
            pairs: List[LeanExpr] = []
            for k, v in oterm.entries:
                pairs.append(
                    LeanApp(
                        fn=LeanVar("Prod.mk"),
                        args=[self.translate(k), self.translate(v)],
                    )
                )
            return LeanApp(fn=LeanVar("List.mk"), args=pairs)
        return LeanVar("<untranslated>")

    def _translate_op(self, oterm: OOp) -> LeanExpr:
        """Translate an OOp to a LeanExpr."""
        name = oterm.name
        args = oterm.args

        # Binary comparison
        if name in self._BIN_CMP_MAP and len(args) == 2:
            return self.translate_comparison(name, args[0], args[1])

        # Binary arithmetic
        if name in self._BIN_ARITH_MAP and len(args) == 2:
            lean_name = self._BIN_ARITH_MAP[name]
            return LeanApp(
                fn=LeanVar(lean_name),
                args=[
                    self.translate(args[0]),
                    self.translate(args[1]),
                ],
            )

        # Unary operations
        if name in self._UN_MAP and len(args) == 1:
            lean_name = self._UN_MAP[name]
            return LeanApp(
                fn=LeanVar(lean_name),
                args=[self.translate(args[0])],
            )

        # Binary misc (connectives, list ops, etc.)
        if name in self._BIN_MISC_MAP and len(args) == 2:
            lean_name = self._BIN_MISC_MAP[name]
            return LeanApp(
                fn=LeanVar(lean_name),
                args=[
                    self.translate(args[0]),
                    self.translate(args[1]),
                ],
            )

        # Generic fallback
        lean_args = [self.translate(a) for a in args]
        return LeanApp(fn=LeanVar(name), args=lean_args)

    def translate_comparison(
        self, op_name: str, lhs: OTerm, rhs: OTerm
    ) -> LeanExpr:
        """Translate a comparison OTerm to the Lean form ``Op lhs rhs``."""
        lean_name = self._BIN_CMP_MAP.get(op_name, op_name)
        return LeanApp(
            fn=LeanVar(lean_name),
            args=[self.translate(lhs), self.translate(rhs)],
        )


# -- Round-trip helpers -------------------------------------------------------


def roundtrip_check(prop: LeanExpr) -> bool:
    """Translate Lean -> CCTT -> Lean and check structural equality.

    Structural equality here means the head symbol and argument count
    match; it does *not* check deep alpha-equivalence.
    """
    fwd = LeanPropToCCTTPredicate()
    pred = fwd.translate(prop)
    if pred.oterm_pattern is None:
        return False
    rev = CCTTPredicateToLeanProp()
    back = rev.translate(pred.oterm_pattern)
    return _lean_head(back) == _lean_head(prop)


def batch_translate(
    props: Sequence[LeanExpr],
) -> List[TranslatedPredicate]:
    """Translate a batch of propositions, sharing one translator."""
    t = LeanPropToCCTTPredicate()
    return [t.translate(p) for p in props]


def summarise_predicates(
    preds: Sequence[TranslatedPredicate],
) -> Dict[str, Any]:
    """Produce a summary dict for a list of translated predicates."""
    kinds: Dict[str, int] = {}
    frags: Dict[str, int] = {}
    decidable_count = 0
    total_confidence = 0.0

    for p in preds:
        k = p.prop_kind.value
        kinds[k] = kinds.get(k, 0) + 1
        f = p.z3_fragment.value
        frags[f] = frags.get(f, 0) + 1
        if p.decidable:
            decidable_count += 1
        total_confidence += p.confidence

    n = len(preds) or 1
    return {
        "total": len(preds),
        "decidable": decidable_count,
        "avg_confidence": total_confidence / n,
        "kinds": kinds,
        "fragments": frags,
    }


# -- Self-tests ---------------------------------------------------------------


if __name__ == "__main__":
    import sys

    _pass = 0
    _fail = 0
    _total = 0

    def _check(label: str, cond: bool) -> None:
        global _pass, _fail, _total
        _total += 1
        if cond:
            _pass += 1
            print(f"  [PASS] {label}")
        else:
            _fail += 1
            print(f"  [FAIL] {label}")

    translator = LeanPropToCCTTPredicate()
    reverse = CCTTPredicateToLeanProp()

    print("=" * 60)
    print("prop_translator.py  self-tests")
    print("=" * 60)

    # -- 1. Equality: Eq Nat a b ------------------------------------------
    print("\n--- 1. Equality (Eq Nat a b) ---")
    eq_prop = LeanApp(
        fn=LeanVar("Eq"),
        args=[LeanVar("Nat"), LeanVar("a"), LeanVar("b")],
    )
    r = translator.translate(eq_prop)
    _check("prop_kind == EQUALITY", r.prop_kind == PropKind.EQUALITY)
    _check("confidence >= 0.9", r.confidence >= 0.9)
    _check("nl contains 'equal'", "equal" in r.nl_description)
    _check(
        "free_vars contains a, b",
        {"a", "b"} <= r.free_vars,
    )
    _check(
        "oterm is OOp eq",
        isinstance(r.oterm_pattern, OOp)
        and r.oterm_pattern.name == "eq",
    )

    # -- 2. Comparison: LE.le x y -----------------------------------------
    print("\n--- 2. Comparison (LE.le x y) ---")
    le_prop = LeanApp(
        fn=LeanVar("LE.le"),
        args=[LeanVar("x"), LeanVar("y")],
    )
    r = translator.translate(le_prop)
    _check(
        "prop_kind == COMPARISON",
        r.prop_kind == PropKind.COMPARISON,
    )
    _check(
        "nl contains 'less'",
        "less" in r.nl_description.lower()
        or "<=" in r.nl_description,
    )
    _check(
        "oterm is OOp le",
        isinstance(r.oterm_pattern, OOp)
        and r.oterm_pattern.name == "le",
    )

    # -- 3. And -----------------------------------------------------------
    print("\n--- 3. And ---")
    and_prop = LeanApp(
        fn=LeanVar("And"),
        args=[
            LeanApp(
                fn=LeanVar("Eq"),
                args=[
                    LeanVar("Nat"),
                    LeanVar("a"),
                    LeanVar("b"),
                ],
            ),
            LeanApp(
                fn=LeanVar("LT.lt"),
                args=[LeanVar("c"), LeanVar("d")],
            ),
        ],
    )
    r = translator.translate(and_prop)
    _check(
        "prop_kind == CONNECTIVE",
        r.prop_kind == PropKind.CONNECTIVE,
    )
    _check("nl contains 'and'", "and" in r.nl_description)
    _check(
        "free_vars superset {a,b,c,d}",
        {"a", "b", "c", "d"} <= r.free_vars,
    )

    # -- 4. Or ------------------------------------------------------------
    print("\n--- 4. Or ---")
    or_prop = LeanApp(
        fn=LeanVar("Or"),
        args=[LeanVar("P"), LeanVar("Q")],
    )
    r = translator.translate(or_prop)
    _check(
        "prop_kind == CONNECTIVE",
        r.prop_kind == PropKind.CONNECTIVE,
    )
    _check("nl contains 'or'", "or" in r.nl_description)

    # -- 5. Not -----------------------------------------------------------
    print("\n--- 5. Not ---")
    not_prop = LeanApp(
        fn=LeanVar("Not"), args=[LeanVar("P")]
    )
    r = translator.translate(not_prop)
    _check(
        "prop_kind == CONNECTIVE",
        r.prop_kind == PropKind.CONNECTIVE,
    )
    _check("negated is True", r.negated is True)
    _check(
        "nl contains 'not'", "not" in r.nl_description.lower()
    )

    # -- 6. Iff -----------------------------------------------------------
    print("\n--- 6. Iff ---")
    iff_prop = LeanApp(
        fn=LeanVar("Iff"),
        args=[LeanVar("P"), LeanVar("Q")],
    )
    r = translator.translate(iff_prop)
    _check(
        "prop_kind == CONNECTIVE",
        r.prop_kind == PropKind.CONNECTIVE,
    )
    _check(
        "nl contains 'if and only if'",
        "if and only if" in r.nl_description,
    )

    # -- 7. True / False --------------------------------------------------
    print("\n--- 7. True / False ---")
    r_t = translator.translate(
        LeanApp(fn=LeanVar("True"), args=[])
    )
    r_f = translator.translate(
        LeanApp(fn=LeanVar("False"), args=[])
    )
    _check("True -> LITERAL", r_t.prop_kind == PropKind.LITERAL)
    _check(
        "False -> LITERAL", r_f.prop_kind == PropKind.LITERAL
    )
    _check("True confidence == 1.0", r_t.confidence == 1.0)
    _check("False negated", r_f.negated is True)

    # -- 8. Exists --------------------------------------------------------
    print("\n--- 8. Exists ---")
    exists_prop = LeanApp(
        fn=LeanVar("Exists"),
        args=[
            LeanVar("Nat"),
            LeanLam(
                params=[
                    LeanParam(
                        name="n",
                        type_=LeanVar("Nat"),
                        binder="(",
                    )
                ],
                body=LeanApp(
                    fn=LeanVar("Eq"),
                    args=[
                        LeanVar("Nat"),
                        LeanVar("n"),
                        LeanLit(0),
                    ],
                ),
            ),
        ],
    )
    r = translator.translate(exists_prop)
    _check(
        "prop_kind == QUANTIFIER",
        r.prop_kind == PropKind.QUANTIFIER,
    )
    _check(
        "nl contains 'exists'", "exists" in r.nl_description
    )
    _check("decidable is False", r.decidable is False)

    # -- 9. Forall (Pi) ---------------------------------------------------
    print("\n--- 9. Forall (Pi) ---")
    forall_prop = LeanPi(
        params=[
            LeanParam(
                name="x",
                type_=LeanVar("Nat"),
                binder="(",
            )
        ],
        codomain=LeanApp(
            fn=LeanVar("LE.le"),
            args=[LeanLit(0), LeanVar("x")],
        ),
    )
    r = translator.translate(forall_prop)
    _check(
        "prop_kind == QUANTIFIER",
        r.prop_kind == PropKind.QUANTIFIER,
    )
    _check(
        "nl contains 'for all'",
        "for all" in r.nl_description,
    )

    # -- 10. List.Mem -----------------------------------------------------
    print("\n--- 10. List.Mem ---")
    mem_prop = LeanApp(
        fn=LeanVar("List.Mem"),
        args=[LeanVar("x"), LeanVar("xs")],
    )
    r = translator.translate(mem_prop)
    _check(
        "prop_kind == LIST_PROP",
        r.prop_kind == PropKind.LIST_PROP,
    )
    _check(
        "nl contains 'in'",
        "in" in r.nl_description,
    )
    _check("decidable", r.decidable is True)

    # -- 11. List.Nodup ---------------------------------------------------
    print("\n--- 11. List.Nodup ---")
    nodup_prop = LeanApp(
        fn=LeanVar("List.Nodup"), args=[LeanVar("xs")]
    )
    r = translator.translate(nodup_prop)
    _check(
        "prop_kind == LIST_PROP",
        r.prop_kind == PropKind.LIST_PROP,
    )
    _check(
        "nl contains 'no duplicates'",
        "no duplicates" in r.nl_description,
    )

    # -- 12. List.Sorted --------------------------------------------------
    print("\n--- 12. List.Sorted ---")
    sorted_prop = LeanApp(
        fn=LeanVar("List.Sorted"),
        args=[LeanVar("le"), LeanVar("xs")],
    )
    r = translator.translate(sorted_prop)
    _check(
        "prop_kind == LIST_PROP",
        r.prop_kind == PropKind.LIST_PROP,
    )
    _check(
        "nl contains 'sorted'", "sorted" in r.nl_description
    )

    # -- 13. List.Perm ----------------------------------------------------
    print("\n--- 13. List.Perm ---")
    perm_prop = LeanApp(
        fn=LeanVar("List.Perm"),
        args=[LeanVar("xs"), LeanVar("ys")],
    )
    r = translator.translate(perm_prop)
    _check(
        "prop_kind == LIST_PROP",
        r.prop_kind == PropKind.LIST_PROP,
    )
    _check(
        "nl contains 'permutation'",
        "permutation" in r.nl_description,
    )

    # -- 14. Function.Injective -------------------------------------------
    print("\n--- 14. Function.Injective ---")
    inj_prop = LeanApp(
        fn=LeanVar("Function.Injective"),
        args=[LeanVar("f")],
    )
    r = translator.translate(inj_prop)
    _check(
        "prop_kind == FUNCTION_PROP",
        r.prop_kind == PropKind.FUNCTION_PROP,
    )
    _check(
        "nl contains 'injective'",
        "injective" in r.nl_description,
    )

    # -- 15. Function.Bijective -------------------------------------------
    print("\n--- 15. Function.Bijective ---")
    bij_prop = LeanApp(
        fn=LeanVar("Function.Bijective"),
        args=[LeanVar("g")],
    )
    r = translator.translate(bij_prop)
    _check(
        "prop_kind == FUNCTION_PROP",
        r.prop_kind == PropKind.FUNCTION_PROP,
    )
    _check(
        "nl contains 'bijective'",
        "bijective" in r.nl_description,
    )

    # -- 16. Monotone -----------------------------------------------------
    print("\n--- 16. Monotone ---")
    mono_prop = LeanApp(
        fn=LeanVar("Monotone"), args=[LeanVar("h")]
    )
    r = translator.translate(mono_prop)
    _check(
        "prop_kind == ORDER_PROP",
        r.prop_kind == PropKind.ORDER_PROP,
    )
    _check(
        "nl contains 'monotone'",
        "monotone" in r.nl_description,
    )

    # -- 17. IsCommutative ------------------------------------------------
    print("\n--- 17. IsCommutative ---")
    comm_prop = LeanApp(
        fn=LeanVar("IsCommutative"),
        args=[LeanVar("op")],
    )
    r = translator.translate(comm_prop)
    _check(
        "prop_kind == ALGEBRAIC_PROP",
        r.prop_kind == PropKind.ALGEBRAIC_PROP,
    )
    _check(
        "nl contains 'commutative'",
        "commutative" in r.nl_description,
    )

    # -- 18. Nat.Prime ----------------------------------------------------
    print("\n--- 18. Nat.Prime ---")
    prime_prop = LeanApp(
        fn=LeanVar("Nat.Prime"), args=[LeanVar("p")]
    )
    r = translator.translate(prime_prop)
    _check(
        "prop_kind == NUMBER_THEORY",
        r.prop_kind == PropKind.NUMBER_THEORY,
    )
    _check(
        "nl contains 'prime'", "prime" in r.nl_description
    )

    # -- 19. Even ---------------------------------------------------------
    print("\n--- 19. Even ---")
    even_prop = LeanApp(
        fn=LeanVar("Even"), args=[LeanVar("n")]
    )
    r = translator.translate(even_prop)
    _check(
        "prop_kind == NUMBER_THEORY",
        r.prop_kind == PropKind.NUMBER_THEORY,
    )
    _check(
        "nl contains 'even'", "even" in r.nl_description
    )

    # -- 20. Dvd ----------------------------------------------------------
    print("\n--- 20. Dvd ---")
    dvd_prop = LeanApp(
        fn=LeanVar("Dvd"),
        args=[LeanVar("a"), LeanVar("b")],
    )
    r = translator.translate(dvd_prop)
    _check(
        "prop_kind == NUMBER_THEORY",
        r.prop_kind == PropKind.NUMBER_THEORY,
    )
    _check(
        "nl contains 'divides'",
        "divides" in r.nl_description,
    )

    # -- 21. Arithmetic: HAdd.hAdd ----------------------------------------
    print("\n--- 21. Arithmetic (HAdd.hAdd) ---")
    add_prop = LeanApp(
        fn=LeanVar("HAdd.hAdd"),
        args=[LeanVar("x"), LeanVar("y")],
    )
    r = translator.translate(add_prop)
    _check(
        "prop_kind == ARITHMETIC",
        r.prop_kind == PropKind.ARITHMETIC,
    )
    _check(
        "oterm is OOp add",
        isinstance(r.oterm_pattern, OOp)
        and r.oterm_pattern.name == "add",
    )

    # -- 22. Set.Mem ------------------------------------------------------
    print("\n--- 22. Set.Mem ---")
    set_mem_prop = LeanApp(
        fn=LeanVar("Set.Mem"),
        args=[LeanVar("x"), LeanVar("S")],
    )
    r = translator.translate(set_mem_prop)
    _check(
        "prop_kind == SET_PROP",
        r.prop_kind == PropKind.SET_PROP,
    )
    _check(
        "nl contains 'in'",
        "in" in r.nl_description,
    )

    # -- 23. Set.Subset ---------------------------------------------------
    print("\n--- 23. Set.Subset ---")
    subset_prop = LeanApp(
        fn=LeanVar("Set.Subset"),
        args=[LeanVar("A"), LeanVar("B")],
    )
    r = translator.translate(subset_prop)
    _check(
        "prop_kind == SET_PROP",
        r.prop_kind == PropKind.SET_PROP,
    )
    _check(
        "nl contains 'subset'",
        "subset" in r.nl_description,
    )

    # -- 24. Reverse: OOp eq -> LeanApp Eq --------------------------------
    print("\n--- 24. Reverse: OOp(eq) -> Lean ---")
    eq_ot = OOp("eq", (OVar("a"), OVar("b")))
    lean_back = reverse.translate(eq_ot)
    _check("head is Eq", _lean_head(lean_back) == "Eq")
    _check(
        "has 2 args", len(_lean_app_args(lean_back)) == 2
    )

    # -- 25. Reverse: OOp le -> LeanApp LE.le -----------------------------
    print("\n--- 25. Reverse: OOp(le) -> Lean ---")
    le_ot = OOp("le", (OVar("x"), OVar("y")))
    lean_back = reverse.translate(le_ot)
    _check(
        "head is LE.le", _lean_head(lean_back) == "LE.le"
    )

    # -- 26. Reverse: OOp add -> LeanApp HAdd.hAdd ------------------------
    print("\n--- 26. Reverse: OOp(add) -> Lean ---")
    add_ot = OOp("add", (OVar("x"), OLit(1)))
    lean_back = reverse.translate(add_ot)
    _check(
        "head is HAdd.hAdd",
        _lean_head(lean_back) == "HAdd.hAdd",
    )

    # -- 27. Reverse: OLam -> LeanLam ------------------------------------
    print("\n--- 27. Reverse: OLam -> LeanLam ---")
    lam_ot = OLam(
        ("x",), OOp("eq", (OVar("x"), OLit(0)))
    )
    lean_back = reverse.translate(lam_ot)
    _check(
        "result is LeanLam", isinstance(lean_back, LeanLam)
    )

    # -- 28. roundtrip_check ----------------------------------------------
    print("\n--- 28. roundtrip_check ---")
    _check("Eq roundtrips", roundtrip_check(eq_prop))
    _check("LE.le roundtrips", roundtrip_check(le_prop))

    # -- 29. batch_translate ----------------------------------------------
    print("\n--- 29. batch_translate ---")
    preds = batch_translate(
        [eq_prop, le_prop, and_prop, exists_prop]
    )
    _check("batch returns 4 results", len(preds) == 4)

    # -- 30. summarise_predicates -----------------------------------------
    print("\n--- 30. summarise_predicates ---")
    summary = summarise_predicates(preds)
    _check("total == 4", summary["total"] == 4)
    _check(
        "avg_confidence > 0", summary["avg_confidence"] > 0
    )
    _check(
        "kinds dict non-empty", len(summary["kinds"]) > 0
    )

    # -- 31. LeanLit literal ----------------------------------------------
    print("\n--- 31. LeanLit literal ---")
    r = translator.translate(LeanLit(42))
    _check(
        "prop_kind == LITERAL",
        r.prop_kind == PropKind.LITERAL,
    )
    _check("confidence == 1.0", r.confidence == 1.0)
    _check(
        "oterm is OLit(42)",
        isinstance(r.oterm_pattern, OLit)
        and r.oterm_pattern.value == 42,
    )

    # -- 32. bare variable ------------------------------------------------
    print("\n--- 32. Bare variable ---")
    r = translator.translate(LeanVar("hypothesis"))
    _check(
        "free_vars == {'hypothesis'}",
        r.free_vars == frozenset({"hypothesis"}),
    )

    # -- 33. nested Not(And(...)) -----------------------------------------
    print("\n--- 33. Nested Not(And(P,Q)) ---")
    nested = LeanApp(
        fn=LeanVar("Not"),
        args=[
            LeanApp(
                fn=LeanVar("And"),
                args=[LeanVar("P"), LeanVar("Q")],
            )
        ],
    )
    r = translator.translate(nested)
    _check("negated", r.negated is True)
    _check(
        "nl contains 'not' and 'and'",
        "not" in r.nl_description and "and" in r.nl_description,
    )

    # -- 34. List.Sublist -------------------------------------------------
    print("\n--- 34. List.Sublist ---")
    sub_prop = LeanApp(
        fn=LeanVar("List.Sublist"),
        args=[LeanVar("xs"), LeanVar("ys")],
    )
    r = translator.translate(sub_prop)
    _check(
        "prop_kind == LIST_PROP",
        r.prop_kind == PropKind.LIST_PROP,
    )
    _check(
        "nl contains 'sublist'",
        "sublist" in r.nl_description,
    )

    # -- 35. StrictMono ---------------------------------------------------
    print("\n--- 35. StrictMono ---")
    sm_prop = LeanApp(
        fn=LeanVar("StrictMono"), args=[LeanVar("f")]
    )
    r = translator.translate(sm_prop)
    _check(
        "prop_kind == ORDER_PROP",
        r.prop_kind == PropKind.ORDER_PROP,
    )
    _check(
        "nl contains 'strictly monotone'",
        "strictly monotone" in r.nl_description,
    )

    # -- 36. Odd ----------------------------------------------------------
    print("\n--- 36. Odd ---")
    odd_prop = LeanApp(
        fn=LeanVar("Odd"), args=[LeanVar("m")]
    )
    r = translator.translate(odd_prop)
    _check(
        "prop_kind == NUMBER_THEORY",
        r.prop_kind == PropKind.NUMBER_THEORY,
    )
    _check(
        "nl contains 'odd'", "odd" in r.nl_description
    )

    # -- 37. Nat.Coprime -------------------------------------------------
    print("\n--- 37. Nat.Coprime ---")
    cop_prop = LeanApp(
        fn=LeanVar("Nat.Coprime"),
        args=[LeanVar("a"), LeanVar("b")],
    )
    r = translator.translate(cop_prop)
    _check(
        "prop_kind == NUMBER_THEORY",
        r.prop_kind == PropKind.NUMBER_THEORY,
    )
    _check(
        "nl contains 'coprime'",
        "coprime" in r.nl_description,
    )

    # -- 38. Set.Finite ---------------------------------------------------
    print("\n--- 38. Set.Finite ---")
    fin_prop = LeanApp(
        fn=LeanVar("Set.Finite"), args=[LeanVar("S")]
    )
    r = translator.translate(fin_prop)
    _check(
        "prop_kind == SET_PROP",
        r.prop_kind == PropKind.SET_PROP,
    )
    _check(
        "nl contains 'finite'",
        "finite" in r.nl_description,
    )

    # -- 39. Function.Surjective -----------------------------------------
    print("\n--- 39. Function.Surjective ---")
    surj_prop = LeanApp(
        fn=LeanVar("Function.Surjective"),
        args=[LeanVar("g")],
    )
    r = translator.translate(surj_prop)
    _check(
        "prop_kind == FUNCTION_PROP",
        r.prop_kind == PropKind.FUNCTION_PROP,
    )
    _check(
        "nl contains 'surjective'",
        "surjective" in r.nl_description,
    )

    # -- 40. Reverse: OOp(not, ...) -> Lean Not ---------------------------
    print("\n--- 40. Reverse: not ---")
    not_ot = OOp("not", (OVar("P"),))
    lean_back = reverse.translate(not_ot)
    _check("head is Not", _lean_head(lean_back) == "Not")

    # -- 41. is_decidable helper ------------------------------------------
    print("\n--- 41. is_decidable ---")
    _check(
        "Eq is decidable",
        translator.is_decidable(eq_prop),
    )
    _check(
        "Exists is not decidable",
        not translator.is_decidable(exists_prop),
    )

    # -- 42. classify_z3_fragment -----------------------------------------
    print("\n--- 42. classify_z3_fragment ---")
    if _HAS_Z3:
        x = _z3.Int("x")
        y = _z3.Int("y")
        frag = translator.classify_z3_fragment(x + y == 0)
        _check(
            "x+y==0 -> QF_LIA",
            frag == Z3Fragment.QF_LIA,
        )
        frag2 = translator.classify_z3_fragment(x * y == 0)
        _check(
            "x*y==0 -> QF_NIA",
            frag2 == Z3Fragment.QF_NIA,
        )
    else:
        _check("(Z3 not available, skip)", True)
        _check("(Z3 not available, skip)", True)

    # -- Summary ----------------------------------------------------------
    print("\n" + "=" * 60)
    print(f"Results: {_pass} passed, {_fail} failed, {_total} total")
    print("=" * 60)

    sys.exit(0 if _fail == 0 else 1)
