"""
lean_type_mapper.py — Maps between Lean's type universe and CCTT's OTerm/Z3 PyObj universe.

Bidirectional mapping:
  • LeanToCCTTTypeMapper  : Lean types  → CCTT OTerms / Z3 sorts & constraints
  • CCTTToLeanTypeMapper  : CCTT OTerms → Lean types

Every Lean type (base, compound, typeclass) gets a canonical CCTT representation
and, where possible, a Z3 sort + constraint set for automated verification.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple, Union

# ── Z3 import guard ──────────────────────────────────────────────────────────
try:
    import z3 as _z3
    _HAS_Z3 = True
except ImportError:
    _z3 = None
    _HAS_Z3 = False

# ── Lean AST nodes ───────────────────────────────────────────────────────────
from cctt.mathlib_bridge.lean_parser import (
    LeanExpr, LeanVar, LeanApp, LeanLam, LeanPi, LeanMatch,
    LeanLet, LeanLit, LeanSort, LeanProj, LeanIf, LeanTactic,
    LeanTacticBlock, LeanParam, LeanDecl, LeanHole, LeanSorry,
    LeanAnonymousCtor,
)

# ── CCTT denotation ─────────────────────────────────────────────────────────
from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

# ── CCTT operation codes ────────────────────────────────────────────────────
from cctt.theory import (
    ADD, SUB, MUL, FLOORDIV, MOD,
    LT, LE, GT, GE, EQ, NE,
    NEG, MAX, MIN,
)


# ═══════════════════════════════════════════════════════════════════════════════
#  Data structures
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class TypeMapping:
    """Result of mapping a single Lean type into the CCTT world."""

    lean_type: LeanExpr
    cctt_pattern: str                        # human-readable description
    z3_sort_name: Optional[str] = None       # Z3 sort if applicable
    z3_constraints: list = field(default_factory=list)  # constraint descriptions
    oterm_constructor: Optional[str] = None  # which OTerm class to use
    confidence: float = 1.0                  # 0.0 – 1.0

    def __repr__(self) -> str:
        return (
            f"TypeMapping(cctt={self.cctt_pattern!r}, "
            f"z3_sort={self.z3_sort_name!r}, "
            f"confidence={self.confidence})"
        )


@dataclass
class TypeclassMapping:
    """Result of mapping a Lean typeclass into CCTT operations + axioms."""

    lean_class: str
    operations: list          # list of (op_name, op_code) tuples
    axioms: list              # axiom descriptions
    cctt_pattern: str         # how CCTT represents this algebraically

    def __repr__(self) -> str:
        return (
            f"TypeclassMapping(class={self.lean_class!r}, "
            f"ops={[o[0] for o in self.operations]!r})"
        )


# ═══════════════════════════════════════════════════════════════════════════════
#  Helpers
# ═══════════════════════════════════════════════════════════════════════════════

def _lean_name(expr: LeanExpr) -> Optional[str]:
    """Extract the head name from an expression (LeanVar or LeanApp head)."""
    if isinstance(expr, LeanVar):
        return expr.name
    if isinstance(expr, LeanApp):
        return _lean_name(expr.fn)
    return None


def _lean_args(expr: LeanExpr) -> List[LeanExpr]:
    """Collect top-level arguments of an application spine."""
    if isinstance(expr, LeanApp):
        return list(expr.args)
    return []


def _mk_var(name: str) -> LeanVar:
    return LeanVar(name=name)


def _mk_app(fn_name: str, *args: LeanExpr) -> LeanApp:
    return LeanApp(fn=LeanVar(name=fn_name), args=list(args))


def _mk_pi(param_name: str, domain: LeanExpr, codomain: LeanExpr) -> LeanPi:
    return LeanPi(
        params=[LeanParam(name=param_name, type_=domain, binder="(")],
        codomain=codomain,
    )


# ═══════════════════════════════════════════════════════════════════════════════
#  Massive TYPE_MAP — Lean base type name → TypeMapping template
# ═══════════════════════════════════════════════════════════════════════════════

_NAT  = "Nat"
_INT  = "Int"
_BOOL = "Bool"
_STR  = "String"
_UNIT = "Unit"
_EMPTY = "Empty"
_FALSE_PROP = "False"
_TRUE_PROP  = "True"
_CHAR  = "Char"
_FLOAT = "Float"

TYPE_MAP: Dict[str, dict] = {
    # ── Numeric ───────────────────────────────────────────────────────────
    _NAT: dict(
        cctt_pattern="IntObj (non-negative)",
        z3_sort_name="IntSort",
        z3_constraints=["ival >= 0"],
        oterm_constructor="OLit",
        confidence=1.0,
    ),
    _INT: dict(
        cctt_pattern="IntObj",
        z3_sort_name="IntSort",
        z3_constraints=[],
        oterm_constructor="OLit",
        confidence=1.0,
    ),
    _FLOAT: dict(
        cctt_pattern="FloatObj",
        z3_sort_name="RealSort",
        z3_constraints=[],
        oterm_constructor="OLit",
        confidence=0.9,
    ),

    # ── Boolean ───────────────────────────────────────────────────────────
    _BOOL: dict(
        cctt_pattern="BoolObj",
        z3_sort_name="BoolSort",
        z3_constraints=[],
        oterm_constructor="OLit",
        confidence=1.0,
    ),

    # ── String / Char ────────────────────────────────────────────────────
    _STR: dict(
        cctt_pattern="StrObj",
        z3_sort_name="StringSort",
        z3_constraints=[],
        oterm_constructor="OLit",
        confidence=1.0,
    ),
    _CHAR: dict(
        cctt_pattern="StrObj (single char)",
        z3_sort_name="StringSort",
        z3_constraints=["len(s) == 1"],
        oterm_constructor="OLit",
        confidence=1.0,
    ),

    # ── Unit / Empty / Propositions ──────────────────────────────────────
    _UNIT: dict(
        cctt_pattern="NoneObj",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OLit",
        confidence=1.0,
    ),
    _EMPTY: dict(
        cctt_pattern="Bottom",
        z3_sort_name=None,
        z3_constraints=["False"],
        oterm_constructor=None,
        confidence=1.0,
    ),
    _FALSE_PROP: dict(
        cctt_pattern="Bottom",
        z3_sort_name=None,
        z3_constraints=["False"],
        oterm_constructor=None,
        confidence=1.0,
    ),
    _TRUE_PROP: dict(
        cctt_pattern="BoolObj(True)",
        z3_sort_name="BoolSort",
        z3_constraints=["val == True"],
        oterm_constructor="OLit",
        confidence=1.0,
    ),

    # ── PUnit / PEmpty (prop-level) ──────────────────────────────────────
    "PUnit": dict(
        cctt_pattern="NoneObj (prop-unit)",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OLit",
        confidence=1.0,
    ),
    "PEmpty": dict(
        cctt_pattern="Bottom (prop-empty)",
        z3_sort_name=None,
        z3_constraints=["False"],
        oterm_constructor=None,
        confidence=1.0,
    ),

    # ── Rational / Real ─────────────────────────────────────────────────
    "Rat": dict(
        cctt_pattern="RatObj (pair of IntObj)",
        z3_sort_name="RealSort",
        z3_constraints=[],
        oterm_constructor="OOp",
        confidence=0.85,
    ),
    "Real": dict(
        cctt_pattern="FloatObj (approximation)",
        z3_sort_name="RealSort",
        z3_constraints=[],
        oterm_constructor="OLit",
        confidence=0.7,
    ),
    "Complex": dict(
        cctt_pattern="Pair(FloatObj, FloatObj) (re, im)",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OOp",
        confidence=0.65,
    ),

    # ── ZMod ─────────────────────────────────────────────────────────────
    "ZMod": dict(
        cctt_pattern="IntObj mod n",
        z3_sort_name="IntSort",
        z3_constraints=["0 <= ival", "ival < n"],
        oterm_constructor="OOp",
        confidence=0.9,
    ),

    # ── Ordering ─────────────────────────────────────────────────────────
    "Ordering": dict(
        cctt_pattern="IntObj ∈ {-1, 0, 1}",
        z3_sort_name="IntSort",
        z3_constraints=["ival >= -1", "ival <= 1"],
        oterm_constructor="OLit",
        confidence=1.0,
    ),

    # ── WithBot / WithTop ────────────────────────────────────────────────
    "WithBot": dict(
        cctt_pattern="OCase (None=bot | Some=value)",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OCase",
        confidence=0.9,
    ),
    "WithTop": dict(
        cctt_pattern="OCase (None=top | Some=value)",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OCase",
        confidence=0.9,
    ),

    # ── ENNReal / NNReal ────────────────────────────────────────────────
    "NNReal": dict(
        cctt_pattern="FloatObj (non-negative real)",
        z3_sort_name="RealSort",
        z3_constraints=["rval >= 0"],
        oterm_constructor="OLit",
        confidence=0.8,
    ),
    "ENNReal": dict(
        cctt_pattern="OCase (finite NNReal | ∞)",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OCase",
        confidence=0.75,
    ),

    # ── Name / Syntax (Lean meta) ───────────────────────────────────────
    "Name": dict(
        cctt_pattern="StrObj (qualified name)",
        z3_sort_name="StringSort",
        z3_constraints=[],
        oterm_constructor="OLit",
        confidence=0.8,
    ),
    "Syntax": dict(
        cctt_pattern="OUnknown (Lean syntax object)",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OUnknown",
        confidence=0.5,
    ),
    "Expr": dict(
        cctt_pattern="OUnknown (Lean Expr reflection)",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OUnknown",
        confidence=0.4,
    ),

    # ── Prop / Type / Sort ──────────────────────────────────────────────
    "Prop": dict(
        cctt_pattern="BoolObj (proposition as bool)",
        z3_sort_name="BoolSort",
        z3_constraints=[],
        oterm_constructor="OLit",
        confidence=0.8,
    ),
    "Type": dict(
        cctt_pattern="OUnknown (universe Type)",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OUnknown",
        confidence=0.5,
    ),
    "Sort": dict(
        cctt_pattern="OUnknown (universe Sort)",
        z3_sort_name=None,
        z3_constraints=[],
        oterm_constructor="OUnknown",
        confidence=0.5,
    ),
}


# ═══════════════════════════════════════════════════════════════════════════════
#  Compound type table — parameterised Lean types
# ═══════════════════════════════════════════════════════════════════════════════

COMPOUND_TYPE_MAP: Dict[str, dict] = {
    "List": dict(
        cctt_pattern="OSeq (homogeneous list)",
        z3_sort_name=None,
        oterm_constructor="OSeq",
        confidence=1.0,
    ),
    "Array": dict(
        cctt_pattern="OSeq (array → list in Python)",
        z3_sort_name=None,
        oterm_constructor="OSeq",
        confidence=1.0,
    ),
    "Option": dict(
        cctt_pattern="OCase (None | Some a)",
        z3_sort_name=None,
        oterm_constructor="OCase",
        confidence=1.0,
    ),
    "Prod": dict(
        cctt_pattern="Pair(a, b)",
        z3_sort_name=None,
        oterm_constructor="OOp",
        confidence=1.0,
    ),
    "Sum": dict(
        cctt_pattern="OCase (Inl a | Inr b)",
        z3_sort_name=None,
        oterm_constructor="OCase",
        confidence=1.0,
    ),
    "Fin": dict(
        cctt_pattern="IntObj bounded [0, n)",
        z3_sort_name="IntSort",
        oterm_constructor="OLit",
        confidence=1.0,
    ),
    "Multiset": dict(
        cctt_pattern="OQuotient(OSeq, 'perm') — sorted canonical form",
        z3_sort_name=None,
        oterm_constructor="OQuotient",
        confidence=0.95,
    ),
    "Finset": dict(
        cctt_pattern="OQuotient(OSeq, 'perm') — sorted, unique",
        z3_sort_name=None,
        oterm_constructor="OQuotient",
        confidence=0.95,
    ),
    "Set": dict(
        cctt_pattern="OLam predicate (characteristic function)",
        z3_sort_name=None,
        oterm_constructor="OLam",
        confidence=0.8,
    ),
    "Finmap": dict(
        cctt_pattern="ODict (finite map)",
        z3_sort_name=None,
        oterm_constructor="ODict",
        confidence=0.9,
    ),
    "HashMap": dict(
        cctt_pattern="ODict (hash map)",
        z3_sort_name=None,
        oterm_constructor="ODict",
        confidence=0.9,
    ),
    "RBMap": dict(
        cctt_pattern="ODict (red-black tree map)",
        z3_sort_name=None,
        oterm_constructor="ODict",
        confidence=0.9,
    ),
    "Sigma": dict(
        cctt_pattern="Dependent pair (fst, snd where snd : β fst)",
        z3_sort_name=None,
        oterm_constructor="OOp",
        confidence=0.85,
    ),
    "PSigma": dict(
        cctt_pattern="Dependent pair (prop-level Sigma)",
        z3_sort_name=None,
        oterm_constructor="OOp",
        confidence=0.85,
    ),
    "Subtype": dict(
        cctt_pattern="Refinement type (value + Z3 constraint from predicate)",
        z3_sort_name=None,
        oterm_constructor="OOp",
        confidence=0.9,
    ),
    "Equiv": dict(
        cctt_pattern="Bidirectional axiom pair (toFun / invFun)",
        z3_sort_name=None,
        oterm_constructor="OAbstract",
        confidence=0.8,
    ),
    "Vector": dict(
        cctt_pattern="OSeq with fixed length",
        z3_sort_name=None,
        oterm_constructor="OSeq",
        confidence=0.95,
    ),
    "Dvector": dict(
        cctt_pattern="OSeq (dependent vector)",
        z3_sort_name=None,
        oterm_constructor="OSeq",
        confidence=0.8,
    ),
    "Tree": dict(
        cctt_pattern="OFix (recursive algebraic tree)",
        z3_sort_name=None,
        oterm_constructor="OFix",
        confidence=0.7,
    ),
    "RBNode": dict(
        cctt_pattern="OFix (red-black tree node)",
        z3_sort_name=None,
        oterm_constructor="OFix",
        confidence=0.7,
    ),
    "MLList": dict(
        cctt_pattern="OSeq (monadic lazy list)",
        z3_sort_name=None,
        oterm_constructor="OSeq",
        confidence=0.75,
    ),
    "Stream'": dict(
        cctt_pattern="OFix (coinductive stream)",
        z3_sort_name=None,
        oterm_constructor="OFix",
        confidence=0.65,
    ),
    "LazyList": dict(
        cctt_pattern="OSeq (lazy list)",
        z3_sort_name=None,
        oterm_constructor="OSeq",
        confidence=0.75,
    ),
    "Except": dict(
        cctt_pattern="OCatch (error | value)",
        z3_sort_name=None,
        oterm_constructor="OCatch",
        confidence=0.9,
    ),
    "EStateM": dict(
        cctt_pattern="OLam (state → Except × state)",
        z3_sort_name=None,
        oterm_constructor="OLam",
        confidence=0.7,
    ),
    "ReaderT": dict(
        cctt_pattern="OLam (env → m a)",
        z3_sort_name=None,
        oterm_constructor="OLam",
        confidence=0.7,
    ),
    "StateT": dict(
        cctt_pattern="OLam (state → m (a × state))",
        z3_sort_name=None,
        oterm_constructor="OLam",
        confidence=0.7,
    ),
    "WriterT": dict(
        cctt_pattern="OOp (a × w)",
        z3_sort_name=None,
        oterm_constructor="OOp",
        confidence=0.7,
    ),
    "IO": dict(
        cctt_pattern="OAbstract (IO action)",
        z3_sort_name=None,
        oterm_constructor="OAbstract",
        confidence=0.6,
    ),
    "Task": dict(
        cctt_pattern="OAbstract (async task)",
        z3_sort_name=None,
        oterm_constructor="OAbstract",
        confidence=0.5,
    ),
}


# ═══════════════════════════════════════════════════════════════════════════════
#  TYPECLASS_MAP — Lean typeclasses → (operations, axioms, cctt_pattern)
# ═══════════════════════════════════════════════════════════════════════════════

TYPECLASS_MAP: Dict[str, dict] = {
    # ── Arithmetic ───────────────────────────────────────────────────────
    "Add": dict(
        operations=[("add", ADD)],
        axioms=[],
        cctt_pattern="binop(ADD, a, b)",
    ),
    "Mul": dict(
        operations=[("mul", MUL)],
        axioms=[],
        cctt_pattern="binop(MUL, a, b)",
    ),
    "Neg": dict(
        operations=[("neg", NEG)],
        axioms=[],
        cctt_pattern="unop(NEG, a)",
    ),
    "Sub": dict(
        operations=[("sub", SUB)],
        axioms=[],
        cctt_pattern="binop(SUB, a, b)",
    ),
    "Div": dict(
        operations=[("div", FLOORDIV)],
        axioms=[],
        cctt_pattern="binop(FLOORDIV, a, b)",
    ),
    "Mod": dict(
        operations=[("mod", MOD)],
        axioms=[],
        cctt_pattern="binop(MOD, a, b)",
    ),
    "HAdd": dict(
        operations=[("hAdd", ADD)],
        axioms=[],
        cctt_pattern="binop(ADD, a, b)  -- heterogeneous",
    ),
    "HMul": dict(
        operations=[("hMul", MUL)],
        axioms=[],
        cctt_pattern="binop(MUL, a, b)  -- heterogeneous",
    ),
    "HSub": dict(
        operations=[("hSub", SUB)],
        axioms=[],
        cctt_pattern="binop(SUB, a, b)  -- heterogeneous",
    ),
    "HDiv": dict(
        operations=[("hDiv", FLOORDIV)],
        axioms=[],
        cctt_pattern="binop(FLOORDIV, a, b)  -- heterogeneous",
    ),
    "HMod": dict(
        operations=[("hMod", MOD)],
        axioms=[],
        cctt_pattern="binop(MOD, a, b)  -- heterogeneous",
    ),
    "HPow": dict(
        operations=[("hPow", 7)],  # POW = 7
        axioms=[],
        cctt_pattern="binop(POW, a, b)  -- heterogeneous",
    ),

    # ── Comparison / Order ───────────────────────────────────────────────
    "LE": dict(
        operations=[("le", LE)],
        axioms=[],
        cctt_pattern="binop(LE, a, b)",
    ),
    "LT": dict(
        operations=[("lt", LT)],
        axioms=[],
        cctt_pattern="binop(LT, a, b)",
    ),
    "BEq": dict(
        operations=[("beq", EQ)],
        axioms=[],
        cctt_pattern="binop(EQ, a, b)",
    ),
    "DecidableEq": dict(
        operations=[("decEq", EQ)],
        axioms=["decidability"],
        cctt_pattern="binop(EQ, a, b) with decidable witness",
    ),
    "Ord": dict(
        operations=[("compare", EQ), ("lt_of", LT), ("le_of", LE)],
        axioms=["trichotomy", "transitivity"],
        cctt_pattern="binop(compare, a, b) → Ordering",
    ),
    "LinearOrder": dict(
        operations=[("le", LE), ("lt", LT), ("compare", EQ)],
        axioms=["totality", "antisymmetry", "transitivity"],
        cctt_pattern="LE + LT with totality",
    ),
    "PartialOrder": dict(
        operations=[("le", LE)],
        axioms=["reflexivity", "antisymmetry", "transitivity"],
        cctt_pattern="LE with partial order axioms",
    ),
    "Preorder": dict(
        operations=[("le", LE)],
        axioms=["reflexivity", "transitivity"],
        cctt_pattern="LE with preorder axioms",
    ),
    "Max": dict(
        operations=[("max", MAX)],
        axioms=[],
        cctt_pattern="binop(MAX, a, b)",
    ),
    "Min": dict(
        operations=[("min", MIN)],
        axioms=[],
        cctt_pattern="binop(MIN, a, b)",
    ),

    # ── Algebraic structures ─────────────────────────────────────────────
    "Semigroup": dict(
        operations=[("op", ADD)],
        axioms=["associativity"],
        cctt_pattern="OFold(op, ...) with associativity",
    ),
    "Monoid": dict(
        operations=[("op", ADD), ("identity", ADD)],
        axioms=["associativity", "left_identity", "right_identity"],
        cctt_pattern="OFold(op, identity, ...) with monoid axioms",
    ),
    "CommMonoid": dict(
        operations=[("op", ADD), ("identity", ADD)],
        axioms=["associativity", "commutativity", "left_identity", "right_identity"],
        cctt_pattern="OFold(op, identity, ...) with commutativity",
    ),
    "Group": dict(
        operations=[("op", ADD), ("identity", ADD), ("inv", NEG)],
        axioms=["associativity", "left_identity", "right_identity",
                "left_inverse", "right_inverse"],
        cctt_pattern="OFold(op, identity, ...) + unop(inv)",
    ),
    "CommGroup": dict(
        operations=[("op", ADD), ("identity", ADD), ("inv", NEG)],
        axioms=["associativity", "commutativity", "left_identity",
                "right_identity", "left_inverse", "right_inverse"],
        cctt_pattern="OFold(op, identity, ...) + unop(inv) + commutativity",
    ),
    "AddSemigroup": dict(
        operations=[("add", ADD)],
        axioms=["associativity"],
        cctt_pattern="binop(ADD) with associativity",
    ),
    "AddMonoid": dict(
        operations=[("add", ADD), ("zero", ADD)],
        axioms=["associativity", "add_zero", "zero_add"],
        cctt_pattern="binop(ADD) + zero with monoid axioms",
    ),
    "AddCommMonoid": dict(
        operations=[("add", ADD), ("zero", ADD)],
        axioms=["associativity", "commutativity", "add_zero", "zero_add"],
        cctt_pattern="binop(ADD) + zero with commutative monoid axioms",
    ),
    "AddGroup": dict(
        operations=[("add", ADD), ("zero", ADD), ("neg", NEG)],
        axioms=["associativity", "add_zero", "zero_add",
                "add_left_neg"],
        cctt_pattern="binop(ADD) + zero + neg with group axioms",
    ),
    "AddCommGroup": dict(
        operations=[("add", ADD), ("zero", ADD), ("neg", NEG)],
        axioms=["associativity", "commutativity", "add_zero", "zero_add",
                "add_left_neg"],
        cctt_pattern="binop(ADD) + zero + neg with abelian group axioms",
    ),
    "MulOneClass": dict(
        operations=[("mul", MUL), ("one", MUL)],
        axioms=["one_mul", "mul_one"],
        cctt_pattern="binop(MUL) + one",
    ),
    "Semiring": dict(
        operations=[("add", ADD), ("mul", MUL), ("zero", ADD), ("one", MUL)],
        axioms=["add_assoc", "add_comm", "mul_assoc",
                "left_distrib", "right_distrib",
                "zero_mul", "mul_zero", "add_zero", "zero_add",
                "one_mul", "mul_one"],
        cctt_pattern="ADD-monoid + MUL-monoid + distributivity",
    ),
    "Ring": dict(
        operations=[("add", ADD), ("mul", MUL), ("zero", ADD),
                    ("one", MUL), ("neg", NEG)],
        axioms=["add_assoc", "add_comm", "mul_assoc",
                "left_distrib", "right_distrib",
                "add_zero", "zero_add", "add_left_neg",
                "one_mul", "mul_one"],
        cctt_pattern="ADD-group + MUL-monoid + distributivity",
    ),
    "CommRing": dict(
        operations=[("add", ADD), ("mul", MUL), ("zero", ADD),
                    ("one", MUL), ("neg", NEG)],
        axioms=["add_assoc", "add_comm", "mul_assoc", "mul_comm",
                "left_distrib", "right_distrib",
                "add_zero", "zero_add", "add_left_neg",
                "one_mul", "mul_one"],
        cctt_pattern="ADD-group + commutative MUL-monoid + distributivity",
    ),
    "Field": dict(
        operations=[("add", ADD), ("mul", MUL), ("zero", ADD),
                    ("one", MUL), ("neg", NEG), ("inv", FLOORDIV)],
        axioms=["add_assoc", "add_comm", "mul_assoc", "mul_comm",
                "left_distrib", "right_distrib",
                "add_zero", "zero_add", "add_left_neg",
                "one_mul", "mul_one", "mul_inv_cancel"],
        cctt_pattern="CommRing + multiplicative inverse",
    ),
    "OrderedSemiring": dict(
        operations=[("add", ADD), ("mul", MUL), ("zero", ADD),
                    ("one", MUL), ("le", LE)],
        axioms=["add_assoc", "add_comm", "mul_assoc",
                "left_distrib", "right_distrib",
                "add_le_add_left", "mul_le_mul_of_nonneg"],
        cctt_pattern="Semiring + compatible LE order",
    ),
    "OrderedRing": dict(
        operations=[("add", ADD), ("mul", MUL), ("zero", ADD),
                    ("one", MUL), ("neg", NEG), ("le", LE)],
        axioms=["ring_axioms", "add_le_add_left",
                "mul_nonneg"],
        cctt_pattern="Ring + compatible LE order",
    ),
    "LinearOrderedField": dict(
        operations=[("add", ADD), ("mul", MUL), ("zero", ADD),
                    ("one", MUL), ("neg", NEG), ("inv", FLOORDIV),
                    ("le", LE), ("lt", LT)],
        axioms=["field_axioms", "linear_order", "compatible_order"],
        cctt_pattern="Field + LinearOrder + compatibility",
    ),

    # ── Lattice / Boolean algebra ────────────────────────────────────────
    "Lattice": dict(
        operations=[("sup", MAX), ("inf", MIN)],
        axioms=["sup_comm", "inf_comm", "sup_assoc", "inf_assoc",
                "sup_inf_self", "inf_sup_self"],
        cctt_pattern="binop(MAX/sup) + binop(MIN/inf) with lattice axioms",
    ),
    "SemilatticeSup": dict(
        operations=[("sup", MAX)],
        axioms=["sup_comm", "sup_assoc", "sup_idem"],
        cctt_pattern="binop(MAX/sup) with semilattice axioms",
    ),
    "SemilatticeInf": dict(
        operations=[("inf", MIN)],
        axioms=["inf_comm", "inf_assoc", "inf_idem"],
        cctt_pattern="binop(MIN/inf) with semilattice axioms",
    ),
    "CompleteLattice": dict(
        operations=[("sup", MAX), ("inf", MIN),
                    ("sSup", MAX), ("sInf", MIN)],
        axioms=["lattice_axioms", "sSup_le", "le_sInf"],
        cctt_pattern="Lattice + arbitrary sup/inf (OFold(MAX/MIN, ...))",
    ),
    "BooleanAlgebra": dict(
        operations=[("sup", MAX), ("inf", MIN), ("compl", NEG)],
        axioms=["lattice_axioms", "inf_compl_le_bot",
                "top_le_sup_compl"],
        cctt_pattern="Lattice + complement (negation)",
    ),

    # ── Functor / Monad ──────────────────────────────────────────────────
    "Functor": dict(
        operations=[("map", -1)],
        axioms=["map_id", "map_comp"],
        cctt_pattern="OMap(transform, collection)",
    ),
    "Applicative": dict(
        operations=[("map", -1), ("pure", -1), ("seq", -1)],
        axioms=["map_id", "map_comp", "pure_seq"],
        cctt_pattern="OMap + pure + seq",
    ),
    "Monad": dict(
        operations=[("bind", -1), ("pure", -1)],
        axioms=["bind_pure_left", "bind_pure_right", "bind_assoc"],
        cctt_pattern="OOp('bind', m, f)",
    ),
    "MonadLift": dict(
        operations=[("monadLift", -1)],
        axioms=[],
        cctt_pattern="OOp('lift', inner_monad)",
    ),
    "Alternative": dict(
        operations=[("failure", -1), ("orElse", -1)],
        axioms=[],
        cctt_pattern="OCatch(body, default)",
    ),

    # ── Traversable / Foldable ───────────────────────────────────────────
    "Foldable": dict(
        operations=[("foldl", -1), ("foldr", -1)],
        axioms=[],
        cctt_pattern="OFold(op, init, collection)",
    ),
    "Traversable": dict(
        operations=[("traverse", -1)],
        axioms=["traverse_id", "traverse_comp"],
        cctt_pattern="OMap with applicative effect",
    ),

    # ── Membership / Collection ──────────────────────────────────────────
    "Membership": dict(
        operations=[("mem", EQ)],
        axioms=[],
        cctt_pattern="OOp('contains', collection, element)",
    ),
    "EmptyCollection": dict(
        operations=[("emptyCollection", -1)],
        axioms=[],
        cctt_pattern="OSeq(())",
    ),
    "Singleton": dict(
        operations=[("singleton", -1)],
        axioms=[],
        cctt_pattern="OSeq((element,))",
    ),
    "Insert": dict(
        operations=[("insert", -1)],
        axioms=[],
        cctt_pattern="OOp('insert', collection, element)",
    ),

    # ── Repr / ToString ──────────────────────────────────────────────────
    "Repr": dict(
        operations=[("reprPrec", -1)],
        axioms=[],
        cctt_pattern="OOp('repr', a)",
    ),
    "ToString": dict(
        operations=[("toString", -1)],
        axioms=[],
        cctt_pattern="OOp('str', a)",
    ),

    # ── Hashable / Inhabited ─────────────────────────────────────────────
    "Hashable": dict(
        operations=[("hash", -1)],
        axioms=[],
        cctt_pattern="OOp('hash', a)",
    ),
    "Inhabited": dict(
        operations=[("default", -1)],
        axioms=[],
        cctt_pattern="OLit(default_value)",
    ),
    "Nonempty": dict(
        operations=[],
        axioms=["nonempty_witness"],
        cctt_pattern="∃ x, True",
    ),

    # ── Decidable ────────────────────────────────────────────────────────
    "Decidable": dict(
        operations=[("decide", -1)],
        axioms=["decidability"],
        cctt_pattern="OCase(True, False) — decidable prop",
    ),
}


# ═══════════════════════════════════════════════════════════════════════════════
#  LeanToCCTTTypeMapper
# ═══════════════════════════════════════════════════════════════════════════════

class LeanToCCTTTypeMapper:
    """Map Lean types → CCTT TypeMapping objects.

    Handles simple types (via TYPE_MAP), compound/parameterised types
    (via COMPOUND_TYPE_MAP), function types (LeanPi), and typeclasses
    (via TYPECLASS_MAP).
    """

    def __init__(self) -> None:
        self._cache: Dict[str, TypeMapping] = {}
        self._typeclass_cache: Dict[str, TypeclassMapping] = {}

    # ── public API ───────────────────────────────────────────────────────

    def map_type(self, lean_type: LeanExpr) -> TypeMapping:
        """Main entry point — map any Lean type to a TypeMapping."""
        if isinstance(lean_type, LeanVar):
            return self._map_var(lean_type)
        if isinstance(lean_type, LeanApp):
            return self.map_compound_type(lean_type)
        if isinstance(lean_type, LeanPi):
            return self.map_function_type(lean_type)
        if isinstance(lean_type, LeanLit):
            return self._map_literal_type(lean_type)
        if isinstance(lean_type, LeanSort):
            return self._map_sort(lean_type)
        if isinstance(lean_type, LeanHole):
            return TypeMapping(
                lean_type=lean_type,
                cctt_pattern="OUnknown (hole)",
                z3_sort_name=None,
                z3_constraints=[],
                oterm_constructor="OUnknown",
                confidence=0.0,
            )
        if isinstance(lean_type, LeanSorry):
            return TypeMapping(
                lean_type=lean_type,
                cctt_pattern="OUnknown (sorry — unfinished proof)",
                z3_sort_name=None,
                z3_constraints=[],
                oterm_constructor="OUnknown",
                confidence=0.0,
            )
        if isinstance(lean_type, LeanLam):
            return self._map_lambda_type(lean_type)
        if isinstance(lean_type, LeanLet):
            return self._map_let_type(lean_type)
        if isinstance(lean_type, LeanMatch):
            return self._map_match_type(lean_type)
        if isinstance(lean_type, LeanIf):
            return self._map_if_type(lean_type)
        if isinstance(lean_type, LeanProj):
            return self._map_proj_type(lean_type)
        if isinstance(lean_type, LeanAnonymousCtor):
            return self._map_anon_ctor(lean_type)
        # Fallback
        return TypeMapping(
            lean_type=lean_type,
            cctt_pattern=f"OUnknown ({type(lean_type).__name__})",
            z3_sort_name=None,
            z3_constraints=[],
            oterm_constructor="OUnknown",
            confidence=0.1,
        )

    def map_simple_type(self, name: str) -> Optional[TypeMapping]:
        """Look up a simple (non-parameterised) Lean type by name."""
        if name in self._cache:
            return self._cache[name]
        entry = TYPE_MAP.get(name)
        if entry is None:
            return None
        mapping = TypeMapping(
            lean_type=LeanVar(name=name),
            cctt_pattern=entry["cctt_pattern"],
            z3_sort_name=entry.get("z3_sort_name"),
            z3_constraints=list(entry.get("z3_constraints", [])),
            oterm_constructor=entry.get("oterm_constructor"),
            confidence=entry.get("confidence", 1.0),
        )
        self._cache[name] = mapping
        return mapping

    def map_compound_type(self, app: LeanApp) -> TypeMapping:
        """Map a parameterised Lean type (LeanApp) to a TypeMapping."""
        head = _lean_name(app)
        args = _lean_args(app)

        if head is None:
            return TypeMapping(
                lean_type=app,
                cctt_pattern="OUnknown (unresolvable application head)",
                z3_sort_name=None,
                z3_constraints=[],
                oterm_constructor="OUnknown",
                confidence=0.1,
            )

        # Check simple map first (e.g., ``Nat`` sometimes shows up as App)
        simple = self.map_simple_type(head)
        if simple is not None and len(args) == 0:
            return simple

        # Specific compound types with custom logic (checked first)
        # Arrow sugar: ``α × β`` is ``Prod α β``
        if head == "HProd" or head == "And":
            return self._build_prod_mapping(app, args)

        # Sigma types: ``Σ x : α, β x``
        if head in ("Sigma", "PSigma"):
            return self._build_sigma_mapping(app, args)

        # Subtype: ``{x : α // p x}``
        if head == "Subtype":
            return self._build_subtype_mapping(app, args)

        # Equiv
        if head == "Equiv":
            return self._build_equiv_mapping(app, args)

        # Check compound map (generic handler)
        entry = COMPOUND_TYPE_MAP.get(head)
        if entry is not None:
            return self._build_compound_mapping(app, head, args, entry)

        # Typeclass applications
        tc = TYPECLASS_MAP.get(head)
        if tc is not None:
            tc_mapping = self.map_typeclass(head)
            return TypeMapping(
                lean_type=app,
                cctt_pattern=tc_mapping.cctt_pattern,
                z3_sort_name=None,
                z3_constraints=[],
                oterm_constructor=None,
                confidence=0.7,
            )

        # Fallback — unknown compound type
        arg_patterns = []
        for a in args:
            m = self.map_type(a)
            arg_patterns.append(m.cctt_pattern)
        return TypeMapping(
            lean_type=app,
            cctt_pattern=f"OUnknown({head} {' '.join(arg_patterns)})",
            z3_sort_name=None,
            z3_constraints=[],
            oterm_constructor="OUnknown",
            confidence=0.2,
        )

    def map_function_type(self, pi: LeanPi) -> TypeMapping:
        """Map a Lean function type (Pi/forall) to a CCTT OLam."""
        param_patterns: list = []
        constraints: list = []
        for p in pi.params:
            if p.type_ is not None:
                pm = self.map_type(p.type_)
                param_patterns.append(f"{p.name}: {pm.cctt_pattern}")
                constraints.extend(pm.z3_constraints)
            else:
                param_patterns.append(p.name)
        codomain_m = self.map_type(pi.codomain)
        constraints.extend(codomain_m.z3_constraints)
        cctt_pat = (
            f"OLam(({', '.join(param_patterns)}) → {codomain_m.cctt_pattern})"
        )
        return TypeMapping(
            lean_type=pi,
            cctt_pattern=cctt_pat,
            z3_sort_name=None,
            z3_constraints=constraints,
            oterm_constructor="OLam",
            confidence=min(0.95, codomain_m.confidence),
        )

    def map_typeclass(self, name: str) -> TypeclassMapping:
        """Map a Lean typeclass name to a TypeclassMapping."""
        if name in self._typeclass_cache:
            return self._typeclass_cache[name]
        entry = TYPECLASS_MAP.get(name)
        if entry is None:
            mapping = TypeclassMapping(
                lean_class=name,
                operations=[],
                axioms=[],
                cctt_pattern=f"OUnknown (unknown typeclass {name})",
            )
        else:
            mapping = TypeclassMapping(
                lean_class=name,
                operations=list(entry["operations"]),
                axioms=list(entry["axioms"]),
                cctt_pattern=entry["cctt_pattern"],
            )
        self._typeclass_cache[name] = mapping
        return mapping

    def z3_sort(self, lean_type: LeanExpr) -> Optional[Any]:
        """Return a Z3 SortRef for the given Lean type, or None."""
        if not _HAS_Z3:
            return None
        mapping = self.map_type(lean_type)
        sort_name = mapping.z3_sort_name
        if sort_name is None:
            return None
        return _Z3_SORT_BUILDERS.get(sort_name, lambda: None)()

    def z3_constraint(
        self, lean_type: LeanExpr, var_name: str
    ) -> Optional[Any]:
        """Generate Z3 constraints for a variable of the given Lean type.

        Returns a Z3 BoolRef conjunction, or None if no constraints apply.
        """
        if not _HAS_Z3:
            return None
        mapping = self.map_type(lean_type)
        if not mapping.z3_constraints:
            return None
        z3_sort = self.z3_sort(lean_type)
        if z3_sort is None:
            return None
        return _build_z3_constraint(
            mapping.z3_sort_name, mapping.z3_constraints, var_name, lean_type
        )

    # ── private helpers ──────────────────────────────────────────────────

    def _map_var(self, v: LeanVar) -> TypeMapping:
        simple = self.map_simple_type(v.name)
        if simple is not None:
            return simple
        # Type variable or unknown identifier
        return TypeMapping(
            lean_type=v,
            cctt_pattern=f"OVar({v.name!r})",
            z3_sort_name=None,
            z3_constraints=[],
            oterm_constructor="OVar",
            confidence=0.5,
        )

    def _map_literal_type(self, lit: LeanLit) -> TypeMapping:
        v = lit.value
        if isinstance(v, bool):
            return TypeMapping(
                lean_type=lit, cctt_pattern="BoolObj",
                z3_sort_name="BoolSort", z3_constraints=[],
                oterm_constructor="OLit", confidence=1.0,
            )
        if isinstance(v, int):
            cs = ["ival >= 0"] if v >= 0 else []
            return TypeMapping(
                lean_type=lit,
                cctt_pattern="IntObj" + (" (non-negative)" if v >= 0 else ""),
                z3_sort_name="IntSort", z3_constraints=cs,
                oterm_constructor="OLit", confidence=1.0,
            )
        if isinstance(v, float):
            return TypeMapping(
                lean_type=lit, cctt_pattern="FloatObj",
                z3_sort_name="RealSort", z3_constraints=[],
                oterm_constructor="OLit", confidence=0.9,
            )
        if isinstance(v, str):
            return TypeMapping(
                lean_type=lit, cctt_pattern="StrObj",
                z3_sort_name="StringSort", z3_constraints=[],
                oterm_constructor="OLit", confidence=1.0,
            )
        return TypeMapping(
            lean_type=lit,
            cctt_pattern=f"OLit({type(v).__name__})",
            z3_sort_name=None, z3_constraints=[],
            oterm_constructor="OLit", confidence=0.6,
        )

    def _map_sort(self, s: LeanSort) -> TypeMapping:
        if s.level == 0:
            desc = "Prop (universe level 0)"
        else:
            desc = f"Type (universe level {s.level})"
        return TypeMapping(
            lean_type=s,
            cctt_pattern=f"OUnknown ({desc})",
            z3_sort_name=None,
            z3_constraints=[],
            oterm_constructor="OUnknown",
            confidence=0.4,
        )

    def _map_lambda_type(self, lam: LeanLam) -> TypeMapping:
        param_names = [p.name for p in lam.params]
        body_m = self.map_type(lam.body)
        return TypeMapping(
            lean_type=lam,
            cctt_pattern=f"OLam(λ {' '.join(param_names)} → {body_m.cctt_pattern})",
            z3_sort_name=None,
            z3_constraints=body_m.z3_constraints,
            oterm_constructor="OLam",
            confidence=body_m.confidence * 0.9,
        )

    def _map_let_type(self, let: LeanLet) -> TypeMapping:
        body_m = self.map_type(let.body)
        return TypeMapping(
            lean_type=let,
            cctt_pattern=f"let {let.name} = ... in {body_m.cctt_pattern}",
            z3_sort_name=body_m.z3_sort_name,
            z3_constraints=body_m.z3_constraints,
            oterm_constructor=body_m.oterm_constructor,
            confidence=body_m.confidence * 0.9,
        )

    def _map_match_type(self, m: LeanMatch) -> TypeMapping:
        return TypeMapping(
            lean_type=m,
            cctt_pattern="OCase (match expression)",
            z3_sort_name=None,
            z3_constraints=[],
            oterm_constructor="OCase",
            confidence=0.6,
        )

    def _map_if_type(self, if_: LeanIf) -> TypeMapping:
        then_m = self.map_type(if_.then_)
        else_m = self.map_type(if_.else_)
        conf = min(then_m.confidence, else_m.confidence)
        return TypeMapping(
            lean_type=if_,
            cctt_pattern=f"OCase (if ... then {then_m.cctt_pattern} else {else_m.cctt_pattern})",
            z3_sort_name=then_m.z3_sort_name,
            z3_constraints=then_m.z3_constraints + else_m.z3_constraints,
            oterm_constructor="OCase",
            confidence=conf,
        )

    def _map_proj_type(self, proj: LeanProj) -> TypeMapping:
        inner_m = self.map_type(proj.expr)
        return TypeMapping(
            lean_type=proj,
            cctt_pattern=f"proj({inner_m.cctt_pattern}, {proj.field!r})",
            z3_sort_name=None,
            z3_constraints=[],
            oterm_constructor="OOp",
            confidence=inner_m.confidence * 0.8,
        )

    def _map_anon_ctor(self, ac: LeanAnonymousCtor) -> TypeMapping:
        return TypeMapping(
            lean_type=ac,
            cctt_pattern=f"OOp('ctor', {len(ac.args)} args)",
            z3_sort_name=None,
            z3_constraints=[],
            oterm_constructor="OOp",
            confidence=0.5,
        )

    # ── compound helpers ─────────────────────────────────────────────────

    def _build_compound_mapping(
        self,
        app: LeanApp,
        head: str,
        args: List[LeanExpr],
        entry: dict,
    ) -> TypeMapping:
        """Build a TypeMapping for a known compound type."""
        arg_mappings = [self.map_type(a) for a in args]
        z3_constraints: list = []

        if head == "Fin" and len(args) >= 1:
            z3_constraints = ["ival >= 0"]
            bound_m = self.map_type(args[0])
            if isinstance(args[0], LeanLit) and isinstance(args[0].value, int):
                z3_constraints.append(f"ival < {args[0].value}")
            else:
                z3_constraints.append(f"ival < n ({bound_m.cctt_pattern})")

        if head in ("Multiset", "Finset"):
            inner_desc = arg_mappings[0].cctt_pattern if arg_mappings else "?"
            extra = " unique" if head == "Finset" else ""
            cctt = f"OQuotient(OSeq of {inner_desc}, 'perm') — sorted{extra}"
            return TypeMapping(
                lean_type=app, cctt_pattern=cctt,
                z3_sort_name=None, z3_constraints=[],
                oterm_constructor="OQuotient",
                confidence=entry.get("confidence", 0.95),
            )

        if head == "Option" and len(args) >= 1:
            inner = arg_mappings[0].cctt_pattern
            return TypeMapping(
                lean_type=app,
                cctt_pattern=f"OCase (None | Some({inner}))",
                z3_sort_name=None, z3_constraints=[],
                oterm_constructor="OCase",
                confidence=1.0,
            )

        if head == "Except" and len(args) >= 2:
            err_pat = arg_mappings[0].cctt_pattern
            ok_pat = arg_mappings[1].cctt_pattern
            return TypeMapping(
                lean_type=app,
                cctt_pattern=f"OCatch(body={ok_pat}, default={err_pat})",
                z3_sort_name=None, z3_constraints=[],
                oterm_constructor="OCatch",
                confidence=0.9,
            )

        if head in ("List", "Array", "Vector"):
            inner = arg_mappings[0].cctt_pattern if arg_mappings else "?"
            qualifier = ""
            if head == "Vector" and len(args) >= 2:
                qualifier = f" (len={_lean_name(args[1]) or '?'})"
            return TypeMapping(
                lean_type=app,
                cctt_pattern=f"OSeq of {inner}{qualifier}",
                z3_sort_name=None,
                z3_constraints=z3_constraints,
                oterm_constructor="OSeq",
                confidence=entry.get("confidence", 1.0),
            )

        if head == "Prod" and len(args) >= 2:
            return self._build_prod_mapping(app, args)

        if head in ("Finmap", "HashMap", "RBMap"):
            kpat = arg_mappings[0].cctt_pattern if len(arg_mappings) > 0 else "?"
            vpat = arg_mappings[1].cctt_pattern if len(arg_mappings) > 1 else "?"
            return TypeMapping(
                lean_type=app,
                cctt_pattern=f"ODict({kpat} → {vpat})",
                z3_sort_name=None, z3_constraints=[],
                oterm_constructor="ODict",
                confidence=entry.get("confidence", 0.9),
            )

        if head in ("Sum",):
            lpat = arg_mappings[0].cctt_pattern if len(arg_mappings) > 0 else "?"
            rpat = arg_mappings[1].cctt_pattern if len(arg_mappings) > 1 else "?"
            return TypeMapping(
                lean_type=app,
                cctt_pattern=f"OCase(Inl({lpat}) | Inr({rpat}))",
                z3_sort_name=None, z3_constraints=[],
                oterm_constructor="OCase",
                confidence=1.0,
            )

        if head == "Set":
            inner = arg_mappings[0].cctt_pattern if arg_mappings else "?"
            return TypeMapping(
                lean_type=app,
                cctt_pattern=f"OLam (predicate on {inner})",
                z3_sort_name=None, z3_constraints=[],
                oterm_constructor="OLam",
                confidence=0.8,
            )

        # Generic compound type from COMPOUND_TYPE_MAP
        sub = " ".join(m.cctt_pattern for m in arg_mappings) if arg_mappings else ""
        base_pattern = entry["cctt_pattern"]
        cctt_pat = f"{base_pattern}({sub})" if sub else base_pattern
        return TypeMapping(
            lean_type=app,
            cctt_pattern=cctt_pat,
            z3_sort_name=entry.get("z3_sort_name"),
            z3_constraints=z3_constraints,
            oterm_constructor=entry.get("oterm_constructor"),
            confidence=entry.get("confidence", 0.8),
        )

    def _build_prod_mapping(
        self, app: LeanApp, args: List[LeanExpr]
    ) -> TypeMapping:
        if len(args) >= 2:
            a_m = self.map_type(args[0])
            b_m = self.map_type(args[1])
            return TypeMapping(
                lean_type=app,
                cctt_pattern=f"Pair({a_m.cctt_pattern}, {b_m.cctt_pattern})",
                z3_sort_name=None, z3_constraints=[],
                oterm_constructor="OOp",
                confidence=1.0,
            )
        return TypeMapping(
            lean_type=app, cctt_pattern="Pair(?)", z3_sort_name=None,
            z3_constraints=[], oterm_constructor="OOp", confidence=0.5,
        )

    def _build_sigma_mapping(
        self, app: LeanApp, args: List[LeanExpr]
    ) -> TypeMapping:
        if len(args) >= 2:
            fst_m = self.map_type(args[0])
            snd_m = self.map_type(args[1])
            return TypeMapping(
                lean_type=app,
                cctt_pattern=(
                    f"DepPair(fst: {fst_m.cctt_pattern}, "
                    f"snd: {snd_m.cctt_pattern}(fst))"
                ),
                z3_sort_name=None, z3_constraints=[],
                oterm_constructor="OOp",
                confidence=0.85,
            )
        return TypeMapping(
            lean_type=app, cctt_pattern="DepPair(?)", z3_sort_name=None,
            z3_constraints=[], oterm_constructor="OOp", confidence=0.4,
        )

    def _build_subtype_mapping(
        self, app: LeanApp, args: List[LeanExpr]
    ) -> TypeMapping:
        if len(args) >= 1:
            pred_m = self.map_type(args[0])
            return TypeMapping(
                lean_type=app,
                cctt_pattern=f"RefinementType(pred={pred_m.cctt_pattern})",
                z3_sort_name=None,
                z3_constraints=["pred(x) holds"],
                oterm_constructor="OOp",
                confidence=0.9,
            )
        return TypeMapping(
            lean_type=app, cctt_pattern="RefinementType(?)", z3_sort_name=None,
            z3_constraints=[], oterm_constructor="OOp", confidence=0.4,
        )

    def _build_equiv_mapping(
        self, app: LeanApp, args: List[LeanExpr]
    ) -> TypeMapping:
        if len(args) >= 2:
            a_m = self.map_type(args[0])
            b_m = self.map_type(args[1])
            return TypeMapping(
                lean_type=app,
                cctt_pattern=(
                    f"Equiv({a_m.cctt_pattern} ≃ {b_m.cctt_pattern}) "
                    f"— bidirectional axiom pair"
                ),
                z3_sort_name=None, z3_constraints=[],
                oterm_constructor="OAbstract",
                confidence=0.8,
            )
        return TypeMapping(
            lean_type=app, cctt_pattern="Equiv(?)", z3_sort_name=None,
            z3_constraints=[], oterm_constructor="OAbstract", confidence=0.3,
        )


# ═══════════════════════════════════════════════════════════════════════════════
#  Z3 sort / constraint builders
# ═══════════════════════════════════════════════════════════════════════════════

def _z3_int_sort() -> Any:
    if not _HAS_Z3:
        return None
    return _z3.IntSort()


def _z3_bool_sort() -> Any:
    if not _HAS_Z3:
        return None
    return _z3.BoolSort()


def _z3_real_sort() -> Any:
    if not _HAS_Z3:
        return None
    return _z3.RealSort()


def _z3_string_sort() -> Any:
    if not _HAS_Z3:
        return None
    return _z3.StringSort()


_Z3_SORT_BUILDERS: Dict[str, Any] = {
    "IntSort": _z3_int_sort,
    "BoolSort": _z3_bool_sort,
    "RealSort": _z3_real_sort,
    "StringSort": _z3_string_sort,
}


def _build_z3_constraint(
    sort_name: Optional[str],
    constraint_descs: List[str],
    var_name: str,
    lean_type: LeanExpr,
) -> Optional[Any]:
    """Build a Z3 BoolRef from constraint descriptions."""
    if not _HAS_Z3 or sort_name is None:
        return None

    parts: list = []

    if sort_name == "IntSort":
        v = _z3.Int(var_name)
        for desc in constraint_descs:
            c = _parse_int_constraint(v, desc, lean_type)
            if c is not None:
                parts.append(c)
    elif sort_name == "BoolSort":
        v = _z3.Bool(var_name)
        for desc in constraint_descs:
            c = _parse_bool_constraint(v, desc)
            if c is not None:
                parts.append(c)
    elif sort_name == "RealSort":
        v = _z3.Real(var_name)
        for desc in constraint_descs:
            c = _parse_real_constraint(v, desc)
            if c is not None:
                parts.append(c)
    elif sort_name == "StringSort":
        v = _z3.String(var_name)
        for desc in constraint_descs:
            c = _parse_string_constraint(v, desc)
            if c is not None:
                parts.append(c)

    if not parts:
        return None
    if len(parts) == 1:
        return parts[0]
    return _z3.And(*parts)


def _parse_int_constraint(v: Any, desc: str, lean_type: LeanExpr) -> Optional[Any]:
    """Parse an integer constraint description into a Z3 BoolRef."""
    if not _HAS_Z3:
        return None
    desc = desc.strip()
    if desc == "ival >= 0":
        return v >= 0
    if desc == "ival <= 1":
        return v <= 1
    if desc == "ival >= -1":
        return v >= -1
    if desc.startswith("ival < ") and not desc.endswith(")"):
        try:
            bound = int(desc.split("< ")[1])
            return v < bound
        except (ValueError, IndexError):
            return None
    if desc.startswith("0 <= ival"):
        return v >= 0
    if desc == "False":
        return _z3.BoolVal(False)
    return None


def _parse_bool_constraint(v: Any, desc: str) -> Optional[Any]:
    if not _HAS_Z3:
        return None
    desc = desc.strip()
    if desc == "val == True":
        return v == _z3.BoolVal(True)
    if desc == "val == False":
        return v == _z3.BoolVal(False)
    if desc == "False":
        return _z3.BoolVal(False)
    return None


def _parse_real_constraint(v: Any, desc: str) -> Optional[Any]:
    if not _HAS_Z3:
        return None
    desc = desc.strip()
    if desc == "rval >= 0":
        return v >= 0
    if desc == "False":
        return _z3.BoolVal(False)
    return None


def _parse_string_constraint(v: Any, desc: str) -> Optional[Any]:
    if not _HAS_Z3:
        return None
    desc = desc.strip()
    if desc == "len(s) == 1":
        return _z3.Length(v) == 1
    if desc == "False":
        return _z3.BoolVal(False)
    return None


# ═══════════════════════════════════════════════════════════════════════════════
#  CCTTToLeanTypeMapper — reverse direction
# ═══════════════════════════════════════════════════════════════════════════════

class CCTTToLeanTypeMapper:
    """Map CCTT OTerms back to Lean type expressions.

    This is an *inference* mapper — it guesses the Lean type from the
    structure and values of an OTerm.  The mapping is necessarily
    lossy: CCTT is dynamically typed, Lean is not.
    """

    def __init__(self) -> None:
        pass

    # ── public API ───────────────────────────────────────────────────────

    def map_oterm(self, term: OTerm) -> LeanExpr:
        """Map an OTerm to the most likely LeanExpr type."""
        return self.infer_lean_type(term)

    def infer_lean_type(self, term: OTerm) -> LeanExpr:
        """Infer the Lean type of an OTerm value."""
        return self._infer(term)

    # ── private dispatch ─────────────────────────────────────────────────

    def _infer(self, term: OTerm) -> LeanExpr:
        if isinstance(term, OLit):
            return self._infer_lit(term)
        if isinstance(term, OVar):
            return self._infer_var(term)
        if isinstance(term, OOp):
            return self._infer_op(term)
        if isinstance(term, OSeq):
            return self._infer_seq(term)
        if isinstance(term, ODict):
            return self._infer_dict(term)
        if isinstance(term, OLam):
            return self._infer_lam(term)
        if isinstance(term, OFold):
            return self._infer_fold(term)
        if isinstance(term, OCase):
            return self._infer_case(term)
        if isinstance(term, OFix):
            return self._infer_fix(term)
        if isinstance(term, OMap):
            return self._infer_map(term)
        if isinstance(term, OQuotient):
            return self._infer_quotient(term)
        if isinstance(term, OAbstract):
            return self._infer_abstract(term)
        if isinstance(term, OCatch):
            return self._infer_catch(term)
        if isinstance(term, OUnknown):
            return self._infer_unknown(term)
        # Fallback
        return _mk_var("Unknown")

    def _infer_lit(self, lit: OLit) -> LeanExpr:
        v = lit.value
        if isinstance(v, bool):
            return _mk_var("Bool")
        if isinstance(v, int):
            return _mk_var("Nat") if v >= 0 else _mk_var("Int")
        if isinstance(v, float):
            return _mk_var("Float")
        if isinstance(v, str):
            return _mk_var("String")
        if v is None:
            return _mk_var("Unit")
        return _mk_var("Unknown")

    def _infer_var(self, var: OVar) -> LeanExpr:
        # A free variable — we cannot infer much
        return _mk_var(var.name)

    def _infer_op(self, op: OOp) -> LeanExpr:
        name = op.name
        # Arithmetic ops → numeric type
        if name in ("add", "sub", "mul", "neg", "floordiv", "mod", "pow"):
            if op.args:
                return self.infer_lean_type(op.args[0])
            return _mk_var("Int")
        # Comparison ops → Bool
        if name in ("lt", "le", "gt", "ge", "eq", "ne"):
            return _mk_var("Bool")
        # Pair construction
        if name == "pair" and len(op.args) >= 2:
            a_t = self.infer_lean_type(op.args[0])
            b_t = self.infer_lean_type(op.args[1])
            return _mk_app("Prod", a_t, b_t)
        # String ops
        if name in ("concat", "append", "str"):
            return _mk_var("String")
        # Bind  →  Monad result type
        if name == "bind" and len(op.args) >= 2:
            return self.infer_lean_type(op.args[1])
        # Sorted → List
        if name == "sorted" and len(op.args) >= 1:
            inner_t = self._element_type(op.args[0])
            return _mk_app("List", inner_t)
        # Contains → Bool
        if name == "contains":
            return _mk_var("Bool")
        # Length → Nat
        if name in ("len", "length", "size"):
            return _mk_var("Nat")
        # Hash → Nat
        if name == "hash":
            return _mk_var("Nat")
        # Repr → String
        if name in ("repr", "toString"):
            return _mk_var("String")
        # Constructor
        if name == "ctor":
            return _mk_var("Unknown")
        # Fallback
        if op.args:
            return self.infer_lean_type(op.args[0])
        return _mk_var("Unknown")

    def _infer_seq(self, seq: OSeq) -> LeanExpr:
        if not seq.elements:
            return _mk_app("List", _mk_var("Unknown"))
        elem_type = self.infer_lean_type(seq.elements[0])
        return _mk_app("List", elem_type)

    def _infer_dict(self, d: ODict) -> LeanExpr:
        if not d.pairs:
            return _mk_app("Finmap", _mk_var("Unknown"), _mk_var("Unknown"))
        k_t = self.infer_lean_type(d.pairs[0][0])
        v_t = self.infer_lean_type(d.pairs[0][1])
        return _mk_app("Finmap", k_t, v_t)

    def _infer_lam(self, lam: OLam) -> LeanExpr:
        body_t = self.infer_lean_type(lam.body)
        if len(lam.params) == 0:
            return body_t
        # Build a chain of Pi types
        result = body_t
        for pname in reversed(lam.params):
            result = _mk_pi(pname, _mk_var("Unknown"), result)
        return result

    def _infer_fold(self, fold: OFold) -> LeanExpr:
        return self.infer_lean_type(fold.init)

    def _infer_case(self, case: OCase) -> LeanExpr:
        true_t = self.infer_lean_type(case.true_branch)
        return true_t

    def _infer_fix(self, fix: OFix) -> LeanExpr:
        return self.infer_lean_type(fix.body)

    def _infer_map(self, m: OMap) -> LeanExpr:
        coll_t = self.infer_lean_type(m.collection)
        head = _lean_name(coll_t)
        if head == "List":
            inner_args = _lean_args(coll_t)
            if inner_args:
                # Transform changes element type; hard to infer the output
                return _mk_app("List", _mk_var("Unknown"))
        return coll_t

    def _infer_quotient(self, q: OQuotient) -> LeanExpr:
        inner_t = self.infer_lean_type(q.inner)
        if q.equiv_class == "perm":
            head = _lean_name(inner_t)
            if head == "List":
                inner_args = _lean_args(inner_t)
                elem = inner_args[0] if inner_args else _mk_var("Unknown")
                return _mk_app("Multiset", elem)
        return inner_t

    def _infer_abstract(self, ab: OAbstract) -> LeanExpr:
        return _mk_var("Unknown")

    def _infer_catch(self, c: OCatch) -> LeanExpr:
        body_t = self.infer_lean_type(c.body)
        default_t = self.infer_lean_type(c.default)
        return _mk_app("Except", default_t, body_t)

    def _infer_unknown(self, u: OUnknown) -> LeanExpr:
        return _mk_var("Unknown")

    # ── utilities ────────────────────────────────────────────────────────

    def _element_type(self, term: OTerm) -> LeanExpr:
        """Try to extract the element type from a collection OTerm."""
        if isinstance(term, OSeq) and term.elements:
            return self.infer_lean_type(term.elements[0])
        t = self.infer_lean_type(term)
        args = _lean_args(t)
        if args:
            return args[0]
        return _mk_var("Unknown")


# ═══════════════════════════════════════════════════════════════════════════════
#  Convenience functions
# ═══════════════════════════════════════════════════════════════════════════════

_default_forward: Optional[LeanToCCTTTypeMapper] = None
_default_reverse: Optional[CCTTToLeanTypeMapper] = None


def get_forward_mapper() -> LeanToCCTTTypeMapper:
    """Return a module-level cached LeanToCCTTTypeMapper."""
    global _default_forward
    if _default_forward is None:
        _default_forward = LeanToCCTTTypeMapper()
    return _default_forward


def get_reverse_mapper() -> CCTTToLeanTypeMapper:
    """Return a module-level cached CCTTToLeanTypeMapper."""
    global _default_reverse
    if _default_reverse is None:
        _default_reverse = CCTTToLeanTypeMapper()
    return _default_reverse


def lean_to_cctt(lean_type: LeanExpr) -> TypeMapping:
    """Convenience: map a Lean type to CCTT."""
    return get_forward_mapper().map_type(lean_type)


def cctt_to_lean(term: OTerm) -> LeanExpr:
    """Convenience: infer a Lean type from a CCTT OTerm."""
    return get_reverse_mapper().infer_lean_type(term)


def z3_sort_for(lean_type: LeanExpr) -> Optional[Any]:
    """Convenience: get Z3 sort for a Lean type."""
    return get_forward_mapper().z3_sort(lean_type)


def z3_constraint_for(lean_type: LeanExpr, var_name: str) -> Optional[Any]:
    """Convenience: get Z3 constraint for a Lean type."""
    return get_forward_mapper().z3_constraint(lean_type, var_name)


# ═══════════════════════════════════════════════════════════════════════════════
#  Roundtrip helpers
# ═══════════════════════════════════════════════════════════════════════════════

def roundtrip_lean_type(lean_type: LeanExpr) -> Tuple[TypeMapping, LeanExpr]:
    """Map Lean → CCTT → Lean and return both results.

    Useful for checking that the bidirectional mapping is coherent.
    """
    fwd = get_forward_mapper()
    rev = get_reverse_mapper()
    mapping = fwd.map_type(lean_type)
    # Build a representative OTerm based on mapping.oterm_constructor
    representative = _representative_oterm(mapping)
    inferred = rev.infer_lean_type(representative)
    return mapping, inferred


def _representative_oterm(mapping: TypeMapping) -> OTerm:
    """Build a representative OTerm from a TypeMapping for roundtrip testing."""
    ctor = mapping.oterm_constructor
    if ctor == "OLit":
        if mapping.z3_sort_name == "IntSort":
            return OLit(value=0)
        if mapping.z3_sort_name == "BoolSort":
            return OLit(value=True)
        if mapping.z3_sort_name == "RealSort":
            return OLit(value=0.0)
        if mapping.z3_sort_name == "StringSort":
            return OLit(value="")
        return OLit(value=None)
    if ctor == "OSeq":
        return OSeq(elements=())
    if ctor == "ODict":
        return ODict(pairs=())
    if ctor == "OLam":
        return OLam(params=("x",), body=OVar(name="x"))
    if ctor == "OCase":
        return OCase(
            test=OLit(value=True),
            true_branch=OLit(value=0),
            false_branch=OLit(value=None),
        )
    if ctor == "OOp":
        return OOp(name="pair", args=(OLit(value=0), OLit(value=0)))
    if ctor == "OFold":
        return OFold(op_name="add", init=OLit(value=0), collection=OSeq(elements=()))
    if ctor == "OQuotient":
        return OQuotient(inner=OSeq(elements=()), equiv_class="perm")
    if ctor == "OAbstract":
        return OAbstract(spec="equiv", inputs=())
    if ctor == "OCatch":
        return OCatch(body=OLit(value=0), default=OLit(value=None))
    if ctor == "OFix":
        return OFix(name="rec", body=OLit(value=0))
    if ctor == "OVar":
        return OVar(name="x")
    if ctor == "OMap":
        return OMap(
            transform=OLam(params=("x",), body=OVar(name="x")),
            collection=OSeq(elements=()),
        )
    # Default: OUnknown
    return OUnknown(desc=mapping.cctt_pattern)


# ═══════════════════════════════════════════════════════════════════════════════
#  Batch mapping utilities
# ═══════════════════════════════════════════════════════════════════════════════

def map_decl_types(decl: LeanDecl) -> Dict[str, TypeMapping]:
    """Map all types in a Lean declaration to CCTT.

    Returns a dict: ``{ "param:<name>": mapping, "return": mapping, ... }``.
    """
    mapper = get_forward_mapper()
    result: Dict[str, TypeMapping] = {}
    for p in decl.params:
        if p.type_ is not None:
            result[f"param:{p.name}"] = mapper.map_type(p.type_)
    if decl.return_type is not None:
        result["return"] = mapper.map_type(decl.return_type)
    if decl.body is not None:
        result["body"] = mapper.map_type(decl.body)
    return result


def map_all_decl_constraints(
    decl: LeanDecl,
) -> Dict[str, Optional[Any]]:
    """Generate Z3 constraints for all parameters in a declaration."""
    mapper = get_forward_mapper()
    result: Dict[str, Optional[Any]] = {}
    for p in decl.params:
        if p.type_ is not None:
            result[p.name] = mapper.z3_constraint(p.type_, p.name)
    return result


# ═══════════════════════════════════════════════════════════════════════════════
#  Summary / reporting
# ═══════════════════════════════════════════════════════════════════════════════

def type_map_summary() -> str:
    """Return a human-readable summary of the entire TYPE_MAP + COMPOUND_TYPE_MAP."""
    lines: list = ["=== Simple Types ==="]
    for name, entry in sorted(TYPE_MAP.items()):
        z3 = entry.get("z3_sort_name", "—")
        lines.append(f"  {name:20s} → {entry['cctt_pattern']:40s}  [Z3: {z3}]")
    lines.append("")
    lines.append("=== Compound Types ===")
    for name, entry in sorted(COMPOUND_TYPE_MAP.items()):
        lines.append(f"  {name:20s} → {entry['cctt_pattern']}")
    lines.append("")
    lines.append("=== Typeclasses ===")
    for name, entry in sorted(TYPECLASS_MAP.items()):
        ops = ", ".join(o[0] for o in entry["operations"])
        axiom_count = len(entry["axioms"])
        lines.append(
            f"  {name:25s} ops=[{ops}]  axioms={axiom_count}"
        )
    return "\n".join(lines)


def typeclass_summary(name: str) -> str:
    """Return a detailed summary of a single typeclass mapping."""
    mapper = get_forward_mapper()
    tc = mapper.map_typeclass(name)
    lines = [
        f"Typeclass: {tc.lean_class}",
        f"  CCTT pattern: {tc.cctt_pattern}",
        f"  Operations:",
    ]
    for op_name, op_code in tc.operations:
        lines.append(f"    {op_name} → op_code={op_code}")
    lines.append("  Axioms:")
    for ax in tc.axioms:
        lines.append(f"    • {ax}")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════════
#  Self-tests
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import textwrap

    print("Running lean_type_mapper self-tests...\n")
    _test_passed = 0
    _test_failed = 0

    def _assert(cond: bool, msg: str) -> None:
        global _test_passed, _test_failed
        if cond:
            _test_passed += 1
        else:
            _test_failed += 1
            print(f"  FAIL: {msg}")

    _test_passed = 0
    _test_failed = 0

    # ── Test 1: simple type mapping ──────────────────────────────────────
    print("Test 1: simple types")
    mapper = LeanToCCTTTypeMapper()

    m_nat = mapper.map_type(_mk_var("Nat"))
    _assert(m_nat.cctt_pattern == "IntObj (non-negative)", "Nat pattern")
    _assert(m_nat.z3_sort_name == "IntSort", "Nat z3 sort")
    _assert("ival >= 0" in m_nat.z3_constraints, "Nat constraint")
    _assert(m_nat.oterm_constructor == "OLit", "Nat constructor")
    _assert(m_nat.confidence == 1.0, "Nat confidence")

    m_int = mapper.map_type(_mk_var("Int"))
    _assert(m_int.cctt_pattern == "IntObj", "Int pattern")
    _assert(m_int.z3_constraints == [], "Int no constraints")

    m_bool = mapper.map_type(_mk_var("Bool"))
    _assert(m_bool.cctt_pattern == "BoolObj", "Bool pattern")
    _assert(m_bool.z3_sort_name == "BoolSort", "Bool z3 sort")

    m_str = mapper.map_type(_mk_var("String"))
    _assert(m_str.cctt_pattern == "StrObj", "String pattern")

    m_unit = mapper.map_type(_mk_var("Unit"))
    _assert(m_unit.cctt_pattern == "NoneObj", "Unit pattern")

    m_empty = mapper.map_type(_mk_var("Empty"))
    _assert(m_empty.cctt_pattern == "Bottom", "Empty pattern")
    _assert("False" in m_empty.z3_constraints, "Empty constraint")

    m_true = mapper.map_type(_mk_var("True"))
    _assert("True" in m_true.cctt_pattern, "True pattern")

    m_char = mapper.map_type(_mk_var("Char"))
    _assert("single char" in m_char.cctt_pattern, "Char pattern")
    _assert("len(s) == 1" in m_char.z3_constraints, "Char constraint")

    m_rat = mapper.map_type(_mk_var("Rat"))
    _assert("Rat" in m_rat.cctt_pattern, "Rat pattern")

    m_float = mapper.map_type(_mk_var("Float"))
    _assert("Float" in m_float.cctt_pattern, "Float pattern")

    print(f"  simple types: {_test_passed} passed\n")

    # ── Test 2: compound type mapping ────────────────────────────────────
    print("Test 2: compound types")
    p0 = _test_passed

    m_list = mapper.map_type(_mk_app("List", _mk_var("Nat")))
    _assert("OSeq" in m_list.cctt_pattern, "List → OSeq")
    _assert(m_list.oterm_constructor == "OSeq", "List constructor")

    m_option = mapper.map_type(_mk_app("Option", _mk_var("Int")))
    _assert("OCase" in m_option.cctt_pattern, "Option → OCase")
    _assert("None" in m_option.cctt_pattern, "Option has None")

    m_prod = mapper.map_type(
        _mk_app("Prod", _mk_var("Nat"), _mk_var("Bool"))
    )
    _assert("Pair" in m_prod.cctt_pattern, "Prod → Pair")

    m_fin = mapper.map_type(_mk_app("Fin", LeanLit(value=10)))
    _assert("bounded" in m_fin.cctt_pattern or "IntObj" in m_fin.cctt_pattern,
            "Fin → bounded IntObj")
    _assert(any("< 10" in c for c in m_fin.z3_constraints), "Fin upper bound")

    m_multiset = mapper.map_type(_mk_app("Multiset", _mk_var("Nat")))
    _assert("OQuotient" in m_multiset.cctt_pattern, "Multiset → OQuotient")
    _assert("perm" in m_multiset.cctt_pattern, "Multiset perm equiv")

    m_finset = mapper.map_type(_mk_app("Finset", _mk_var("Int")))
    _assert("OQuotient" in m_finset.cctt_pattern, "Finset → OQuotient")

    m_array = mapper.map_type(_mk_app("Array", _mk_var("Bool")))
    _assert("OSeq" in m_array.cctt_pattern, "Array → OSeq")

    m_sigma = mapper.map_type(
        _mk_app("Sigma", _mk_var("Nat"), _mk_var("β"))
    )
    _assert("DepPair" in m_sigma.cctt_pattern, "Sigma → DepPair")

    m_sub = mapper.map_type(_mk_app("Subtype", _mk_var("p")))
    _assert("Refinement" in m_sub.cctt_pattern, "Subtype → Refinement")

    m_equiv = mapper.map_type(
        _mk_app("Equiv", _mk_var("α"), _mk_var("β"))
    )
    _assert("Equiv" in m_equiv.cctt_pattern, "Equiv mapping")
    _assert("bidirectional" in m_equiv.cctt_pattern, "Equiv bidirectional")

    m_sum = mapper.map_type(
        _mk_app("Sum", _mk_var("Nat"), _mk_var("Bool"))
    )
    _assert("OCase" in m_sum.cctt_pattern, "Sum → OCase")

    m_dict = mapper.map_type(
        _mk_app("HashMap", _mk_var("String"), _mk_var("Nat"))
    )
    _assert("ODict" in m_dict.cctt_pattern, "HashMap → ODict")

    m_except = mapper.map_type(
        _mk_app("Except", _mk_var("String"), _mk_var("Int"))
    )
    _assert("OCatch" in m_except.cctt_pattern, "Except → OCatch")

    m_set = mapper.map_type(_mk_app("Set", _mk_var("Nat")))
    _assert("OLam" in m_set.cctt_pattern or "predicate" in m_set.cctt_pattern,
            "Set → predicate")

    print(f"  compound types: {_test_passed - p0} passed\n")

    # ── Test 3: function type mapping ────────────────────────────────────
    print("Test 3: function types")
    p0 = _test_passed

    m_fn = mapper.map_type(
        _mk_pi("x", _mk_var("Nat"), _mk_var("Bool"))
    )
    _assert("OLam" in m_fn.cctt_pattern, "Pi → OLam")
    _assert(m_fn.oterm_constructor == "OLam", "Pi constructor")
    _assert("Nat" in m_fn.cctt_pattern or "non-negative" in m_fn.cctt_pattern,
            "Pi domain")

    m_fn2 = mapper.map_type(
        _mk_pi("f", _mk_pi("a", _mk_var("Int"), _mk_var("Int")),
                _mk_var("Bool"))
    )
    _assert("OLam" in m_fn2.cctt_pattern, "Nested Pi")

    print(f"  function types: {_test_passed - p0} passed\n")

    # ── Test 4: typeclass mapping ────────────────────────────────────────
    print("Test 4: typeclasses")
    p0 = _test_passed

    tc_add = mapper.map_typeclass("Add")
    _assert(tc_add.lean_class == "Add", "Add class name")
    _assert(any(o[0] == "add" for o in tc_add.operations), "Add has add op")
    _assert(tc_add.operations[0][1] == ADD, "Add op code")

    tc_mul = mapper.map_typeclass("Mul")
    _assert(tc_mul.operations[0][1] == MUL, "Mul op code")

    tc_neg = mapper.map_typeclass("Neg")
    _assert(tc_neg.operations[0][1] == NEG, "Neg op code")

    tc_ring = mapper.map_typeclass("Ring")
    _assert(len(tc_ring.operations) >= 4, "Ring has many ops")
    _assert("left_distrib" in tc_ring.axioms, "Ring distributivity")
    _assert("add_left_neg" in tc_ring.axioms, "Ring has neg axiom")

    tc_comm = mapper.map_typeclass("CommRing")
    _assert("mul_comm" in tc_comm.axioms, "CommRing commutativity")

    tc_lat = mapper.map_typeclass("Lattice")
    _assert(any(o[0] == "sup" for o in tc_lat.operations), "Lattice has sup")
    _assert(any(o[0] == "inf" for o in tc_lat.operations), "Lattice has inf")

    tc_monad = mapper.map_typeclass("Monad")
    _assert(any(o[0] == "bind" for o in tc_monad.operations), "Monad bind")
    _assert("bind_assoc" in tc_monad.axioms, "Monad associativity")

    tc_functor = mapper.map_typeclass("Functor")
    _assert("OMap" in tc_functor.cctt_pattern, "Functor → OMap")

    tc_monoid = mapper.map_typeclass("Monoid")
    _assert("associativity" in tc_monoid.axioms, "Monoid assoc")
    _assert("left_identity" in tc_monoid.axioms, "Monoid identity")

    tc_group = mapper.map_typeclass("Group")
    _assert("left_inverse" in tc_group.axioms, "Group inverse")

    tc_field = mapper.map_typeclass("Field")
    _assert("mul_inv_cancel" in tc_field.axioms, "Field inverse cancel")

    tc_ord_semi = mapper.map_typeclass("OrderedSemiring")
    _assert(any(o[0] == "le" for o in tc_ord_semi.operations),
            "OrderedSemiring has le")

    tc_unknown = mapper.map_typeclass("NonExistentClass")
    _assert("unknown" in tc_unknown.cctt_pattern.lower(), "Unknown typeclass")

    print(f"  typeclasses: {_test_passed - p0} passed\n")

    # ── Test 5: Z3 constraint generation ─────────────────────────────────
    print("Test 5: Z3 constraints")
    p0 = _test_passed

    if _HAS_Z3:
        c_nat = mapper.z3_constraint(_mk_var("Nat"), "n")
        _assert(c_nat is not None, "Nat constraint not None")
        s = _z3.Solver()
        s.add(c_nat)
        s.add(_z3.Int("n") == 5)
        _assert(s.check() == _z3.sat, "Nat n=5 is sat")

        s2 = _z3.Solver()
        s2.add(c_nat)
        s2.add(_z3.Int("n") == -1)
        _assert(s2.check() == _z3.unsat, "Nat n=-1 is unsat")

        c_int = mapper.z3_constraint(_mk_var("Int"), "i")
        _assert(c_int is None, "Int has no constraint")

        c_char = mapper.z3_constraint(_mk_var("Char"), "ch")
        _assert(c_char is not None, "Char constraint not None")

        c_fin = mapper.z3_constraint(
            _mk_app("Fin", LeanLit(value=5)), "k"
        )
        _assert(c_fin is not None, "Fin constraint not None")
        s3 = _z3.Solver()
        s3.add(c_fin)
        s3.add(_z3.Int("k") == 4)
        _assert(s3.check() == _z3.sat, "Fin 5 k=4 is sat")
        s4 = _z3.Solver()
        s4.add(c_fin)
        s4.add(_z3.Int("k") == 5)
        _assert(s4.check() == _z3.unsat, "Fin 5 k=5 is unsat")

        c_bool = mapper.z3_sort(_mk_var("Bool"))
        _assert(c_bool is not None, "Bool sort exists")

        c_empty = mapper.z3_constraint(_mk_var("Empty"), "e")
        # Empty has "False" constraint but no valid Z3 sort — should be None
        _assert(c_empty is None, "Empty has no Z3 sort")

        c_true_prop = mapper.z3_constraint(_mk_var("True"), "t")
        _assert(c_true_prop is not None, "True constraint not None")

        c_nnreal = mapper.z3_constraint(_mk_var("NNReal"), "r")
        _assert(c_nnreal is not None, "NNReal constraint not None")
    else:
        print("  (Z3 not available — skipping Z3 tests)")

    print(f"  Z3 constraints: {_test_passed - p0} passed\n")

    # ── Test 6: reverse mapping (CCTT → Lean) ───────────────────────────
    print("Test 6: CCTT → Lean reverse mapping")
    p0 = _test_passed

    rev = CCTTToLeanTypeMapper()

    r_int = rev.infer_lean_type(OLit(value=42))
    _assert(_lean_name(r_int) == "Nat", "OLit(42) → Nat")

    r_neg = rev.infer_lean_type(OLit(value=-3))
    _assert(_lean_name(r_neg) == "Int", "OLit(-3) → Int")

    r_bool = rev.infer_lean_type(OLit(value=True))
    _assert(_lean_name(r_bool) == "Bool", "OLit(True) → Bool")

    r_str = rev.infer_lean_type(OLit(value="hello"))
    _assert(_lean_name(r_str) == "String", "OLit('hello') → String")

    r_none = rev.infer_lean_type(OLit(value=None))
    _assert(_lean_name(r_none) == "Unit", "OLit(None) → Unit")

    r_seq = rev.infer_lean_type(OSeq(elements=(OLit(value=1), OLit(value=2))))
    _assert(_lean_name(r_seq) == "List", "OSeq → List")

    r_empty_seq = rev.infer_lean_type(OSeq(elements=()))
    _assert(_lean_name(r_empty_seq) == "List", "Empty OSeq → List")

    r_dict = rev.infer_lean_type(
        ODict(pairs=((OLit(value="a"), OLit(value=1)),))
    )
    _assert(_lean_name(r_dict) == "Finmap", "ODict → Finmap")

    r_lam = rev.infer_lean_type(
        OLam(params=("x",), body=OLit(value=True))
    )
    # Should be some Pi-type structure
    _assert(isinstance(r_lam, LeanPi), "OLam → Pi type")

    r_fold = rev.infer_lean_type(
        OFold(op_name="add", init=OLit(value=0), collection=OSeq(elements=()))
    )
    _assert(_lean_name(r_fold) == "Nat", "OFold(init=0) → Nat")

    r_case = rev.infer_lean_type(
        OCase(
            test=OLit(value=True),
            true_branch=OLit(value=1),
            false_branch=OLit(value=0),
        )
    )
    _assert(_lean_name(r_case) == "Nat", "OCase true_branch=1 → Nat")

    r_op_eq = rev.infer_lean_type(
        OOp(name="eq", args=(OLit(value=1), OLit(value=2)))
    )
    _assert(_lean_name(r_op_eq) == "Bool", "OOp(eq) → Bool")

    r_op_add = rev.infer_lean_type(
        OOp(name="add", args=(OLit(value=1), OLit(value=2)))
    )
    _assert(_lean_name(r_op_add) == "Nat", "OOp(add) → Nat")

    r_op_pair = rev.infer_lean_type(
        OOp(name="pair", args=(OLit(value=1), OLit(value=True)))
    )
    _assert(_lean_name(r_op_pair) == "Prod", "OOp(pair) → Prod")

    r_op_len = rev.infer_lean_type(
        OOp(name="len", args=(OSeq(elements=()),))
    )
    _assert(_lean_name(r_op_len) == "Nat", "OOp(len) → Nat")

    r_op_sorted = rev.infer_lean_type(
        OOp(name="sorted", args=(OSeq(elements=(OLit(value=3),)),))
    )
    _assert(_lean_name(r_op_sorted) == "List", "OOp(sorted) → List")

    r_catch = rev.infer_lean_type(
        OCatch(body=OLit(value=42), default=OLit(value="err"))
    )
    _assert(_lean_name(r_catch) == "Except", "OCatch → Except")

    r_quotient = rev.infer_lean_type(
        OQuotient(
            inner=OSeq(elements=(OLit(value=1),)),
            equiv_class="perm",
        )
    )
    _assert(_lean_name(r_quotient) == "Multiset", "OQuotient(perm) → Multiset")

    r_float = rev.infer_lean_type(OLit(value=3.14))
    _assert(_lean_name(r_float) == "Float", "OLit(3.14) → Float")

    r_unknown = rev.infer_lean_type(OUnknown(desc="???"))
    _assert(_lean_name(r_unknown) == "Unknown", "OUnknown → Unknown")

    r_fix = rev.infer_lean_type(OFix(name="f", body=OLit(value=0)))
    _assert(_lean_name(r_fix) == "Nat", "OFix body=0 → Nat")

    r_abstract = rev.infer_lean_type(OAbstract(spec="test", inputs=()))
    _assert(_lean_name(r_abstract) == "Unknown", "OAbstract → Unknown")

    r_map = rev.infer_lean_type(
        OMap(
            transform=OLam(params=("x",), body=OVar(name="x")),
            collection=OSeq(elements=(OLit(value=1),)),
        )
    )
    _assert(_lean_name(r_map) == "List", "OMap over List → List")

    print(f"  reverse mapping: {_test_passed - p0} passed\n")

    # ── Test 7: verify TYPE_MAP coverage ─────────────────────────────────
    print("Test 7: TYPE_MAP coverage")
    p0 = _test_passed

    _assert(len(TYPE_MAP) >= 20, f"TYPE_MAP has {len(TYPE_MAP)} entries (≥ 20)")
    _assert(len(COMPOUND_TYPE_MAP) >= 15,
            f"COMPOUND_TYPE_MAP has {len(COMPOUND_TYPE_MAP)} entries (≥ 15)")
    _assert(len(TYPECLASS_MAP) >= 30,
            f"TYPECLASS_MAP has {len(TYPECLASS_MAP)} entries (≥ 30)")

    for name, entry in TYPE_MAP.items():
        _assert("cctt_pattern" in entry, f"TYPE_MAP[{name}] has cctt_pattern")
        _assert(isinstance(entry.get("z3_constraints", []), list),
                f"TYPE_MAP[{name}] constraints is list")

    for name, entry in TYPECLASS_MAP.items():
        _assert("operations" in entry, f"TYPECLASS_MAP[{name}] has operations")
        _assert("axioms" in entry, f"TYPECLASS_MAP[{name}] has axioms")
        _assert(isinstance(entry["operations"], list),
                f"TYPECLASS_MAP[{name}] operations is list")

    for name, entry in COMPOUND_TYPE_MAP.items():
        _assert("cctt_pattern" in entry,
                f"COMPOUND_TYPE_MAP[{name}] has cctt_pattern")
        _assert("oterm_constructor" in entry,
                f"COMPOUND_TYPE_MAP[{name}] has oterm_constructor")

    print(f"  TYPE_MAP coverage: {_test_passed - p0} passed\n")

    # ── Test 8: edge cases ───────────────────────────────────────────────
    print("Test 8: edge cases")
    p0 = _test_passed

    m_hole = mapper.map_type(LeanHole())
    _assert(m_hole.confidence == 0.0, "Hole confidence = 0")
    _assert("hole" in m_hole.cctt_pattern.lower(), "Hole pattern")

    m_sorry = mapper.map_type(LeanSorry())
    _assert(m_sorry.confidence == 0.0, "Sorry confidence = 0")

    m_sort0 = mapper.map_type(LeanSort(level=0))
    _assert("Prop" in m_sort0.cctt_pattern, "Sort 0 = Prop")

    m_sort1 = mapper.map_type(LeanSort(level=1))
    _assert("Type" in m_sort1.cctt_pattern, "Sort 1 = Type")

    m_lit_int = mapper.map_type(LeanLit(value=42))
    _assert(m_lit_int.z3_sort_name == "IntSort", "LeanLit(42) z3 sort")

    m_lit_str = mapper.map_type(LeanLit(value="x"))
    _assert(m_lit_str.z3_sort_name == "StringSort", "LeanLit('x') z3 sort")

    m_unknown_var = mapper.map_type(_mk_var("MyCustomType"))
    _assert(m_unknown_var.oterm_constructor == "OVar", "Unknown var → OVar")
    _assert(m_unknown_var.confidence == 0.5, "Unknown var confidence")

    m_unknown_app = mapper.map_type(_mk_app("MyThing", _mk_var("Nat")))
    _assert("OUnknown" in m_unknown_app.cctt_pattern, "Unknown app → OUnknown")

    m_lam = mapper.map_type(
        LeanLam(params=[LeanParam(name="x", type_=None, binder="(")],
                body=_mk_var("Nat"))
    )
    _assert("OLam" in m_lam.cctt_pattern, "Lambda → OLam")

    m_let = mapper.map_type(
        LeanLet(name="y", type_=None, value=LeanLit(value=1),
                body=_mk_var("Bool"))
    )
    _assert("let y" in m_let.cctt_pattern, "Let binding")

    m_match = mapper.map_type(
        LeanMatch(scrutinees=[_mk_var("x")], arms=[])
    )
    _assert("OCase" in m_match.cctt_pattern, "Match → OCase")

    m_if = mapper.map_type(
        LeanIf(cond=_mk_var("b"),
               then_=_mk_var("Nat"),
               else_=_mk_var("Nat"))
    )
    _assert("OCase" in m_if.cctt_pattern, "If → OCase")

    m_proj = mapper.map_type(
        LeanProj(expr=_mk_var("p"), field="fst")
    )
    _assert("proj" in m_proj.cctt_pattern, "Proj mapping")

    m_anon = mapper.map_type(LeanAnonymousCtor(args=[_mk_var("x")]))
    _assert("ctor" in m_anon.cctt_pattern, "AnonymousCtor mapping")

    print(f"  edge cases: {_test_passed - p0} passed\n")

    # ── Test 9: convenience functions ────────────────────────────────────
    print("Test 9: convenience functions")
    p0 = _test_passed

    m_conv = lean_to_cctt(_mk_var("Nat"))
    _assert(m_conv.cctt_pattern == "IntObj (non-negative)", "lean_to_cctt Nat")

    r_conv = cctt_to_lean(OLit(value=42))
    _assert(_lean_name(r_conv) == "Nat", "cctt_to_lean OLit(42)")

    z_sort = z3_sort_for(_mk_var("Bool"))
    if _HAS_Z3:
        _assert(z_sort is not None, "z3_sort_for Bool")
    else:
        _assert(z_sort is None, "z3_sort_for Bool (no Z3)")

    z_con = z3_constraint_for(_mk_var("Nat"), "n")
    if _HAS_Z3:
        _assert(z_con is not None, "z3_constraint_for Nat")
    else:
        _assert(z_con is None, "z3_constraint_for Nat (no Z3)")

    print(f"  convenience: {_test_passed - p0} passed\n")

    # ── Test 10: roundtrip ───────────────────────────────────────────────
    print("Test 10: roundtrip helpers")
    p0 = _test_passed

    for tname in ["Nat", "Int", "Bool", "String", "Unit"]:
        mapping, inferred = roundtrip_lean_type(_mk_var(tname))
        _assert(mapping.confidence > 0, f"Roundtrip {tname} mapping exists")
        _assert(isinstance(inferred, LeanExpr), f"Roundtrip {tname} inferred")

    print(f"  roundtrip: {_test_passed - p0} passed\n")

    # ── Test 11: summary functions ───────────────────────────────────────
    print("Test 11: summary functions")
    p0 = _test_passed

    summary = type_map_summary()
    _assert("Simple Types" in summary, "Summary has simple types section")
    _assert("Compound Types" in summary, "Summary has compound types section")
    _assert("Typeclasses" in summary, "Summary has typeclasses section")
    _assert("Nat" in summary, "Summary mentions Nat")
    _assert("Ring" in summary, "Summary mentions Ring")

    tc_sum = typeclass_summary("Monoid")
    _assert("Monoid" in tc_sum, "Typeclass summary has Monoid")
    _assert("associativity" in tc_sum, "Typeclass summary has assoc")

    print(f"  summary: {_test_passed - p0} passed\n")

    # ── Final report ─────────────────────────────────────────────────────
    print(f"{'=' * 50}")
    print(f"  Total: {_test_passed} passed, {_test_failed} failed")
    print(f"{'=' * 50}")
    if _test_failed > 0:
        print(f"\n  *** {_test_failed} test(s) FAILED ***")
        sys.exit(1)
    else:
        print("\nAll lean_type_mapper self-tests passed!")
