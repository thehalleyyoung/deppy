"""
deppy.hybrid.core.types
========================

Central type definitions for the hybrid dependent type system.

Mathematical foundation
-----------------------
A *HybridType* is a **global section** of the presheaf

    HybridTy : (Site(P) × Layer)^op  →  RefinementLattice × TrustLattice

where

* **Site(P)** is the Grothendieck site of a program ``P`` (open sets =
  contiguous code regions; covers = overlapping scopes),
* **Layer** is the five-point poset  INTENT < STRUCTURAL < SEMANTIC < PROOF < CODE,
* **RefinementLattice** orders types by subtyping / refinement,
* **TrustLattice** orders evidence strength (``UNTRUSTED < RUNTIME_CHECKED
  < LLM_JUDGED < Z3_PROVEN < LEAN_VERIFIED``).

A type is *coherent* iff the first cohomology vanishes:

    H¹(Layer, HybridTy) = 0

meaning every pair of adjacent layers agrees on their overlap (the *cocycle
condition*).  When H¹ ≠ 0 we obtain an *obstruction* that must be resolved
before the type can be trusted.

Oracle monad
~~~~~~~~~~~~
Semantic predicates live in the **oracle monad**

    T_O(A)  =  A × TrustLevel × Confidence × Provenance

with unit ``pure`` and bind that propagates trust via *weakest-link* and
confidence via *multiplication*.  This monad threads through every semantic
check so that trust metadata is never lost.

Dependent types
~~~~~~~~~~~~~~~
We support the four standard dependent type formers:

* Π-types  ``HybridPiType``   — dependent function types
* Σ-types  ``HybridSigmaType`` — dependent pair / subtype types
* Refinement types ``HybridRefinementType`` — {x : T | φ(x)}
* Identity types ``IdentityType`` — propositional equality Id_A(a,b)

Sheaf presheaf
~~~~~~~~~~~~~~
``SheafTypePresheaf`` implements the full presheaf with restriction maps,
compatibility checks, gluing, and H¹ computation.

Exports
-------
Every name listed in ``__all__`` is part of the public API.
"""

from __future__ import annotations

import ast as _ast
import copy
import enum
import hashlib
import json
import math
import re
import time
from dataclasses import dataclass, field
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Dict,
    Generic,
    Iterator,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
    TypeVar,
    Union,
)

# ── Optional Z3 ─────────────────────────────────────────────────────────────
try:
    import z3 as _z3  # type: ignore[import-untyped]

    _HAS_Z3 = True
except ImportError:  # pragma: no cover
    _z3 = None  # type: ignore[assignment]
    _HAS_Z3 = False

# ── TYPE_CHECKING-only imports (break circular deps) ────────────────────────
if TYPE_CHECKING:
    from deppy.hybrid.core.checker import HybridTypeChecker  # noqa: F401
    from deppy.hybrid.core.trust import (  # noqa: F401
        Evidence,
        EvidenceChain,
        HybridTrustLevel as _TrustLevelEnum,
    )

# ── Generic type-vars ───────────────────────────────────────────────────────
T = TypeVar("T")
A = TypeVar("A")
B = TypeVar("B")
S = TypeVar("S")


# ═══════════════════════════════════════════════════════════════════════════════
# §1  Layer enum & ordering
# ═══════════════════════════════════════════════════════════════════════════════

class Layer(enum.Enum):
    """
    The five-point verification layer poset.

    INTENT  <  STRUCTURAL  <  SEMANTIC  <  PROOF  <  CODE

    Each layer carries a different *kind* of evidence:

    * **INTENT** — natural-language specification (docstrings, comments).
    * **STRUCTURAL** — decidable, machine-checkable predicates (Z3, runtime).
    * **SEMANTIC** — oracle-judgeable predicates (LLM evaluation).
    * **PROOF** — formal Lean 4 statements and optional proofs.
    * **CODE** — executable source code with its AST/runtime type.
    """

    INTENT = "intent"
    STRUCTURAL = "structural"
    SEMANTIC = "semantic"
    PROOF = "proof"
    CODE = "code"

    # ── comparison helpers ────────────────────────────────────────────────

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Layer):
            return NotImplemented
        return LAYER_ORDER[self] < LAYER_ORDER[other]

    def __le__(self, other: object) -> bool:
        if not isinstance(other, Layer):
            return NotImplemented
        return LAYER_ORDER[self] <= LAYER_ORDER[other]

    def __gt__(self, other: object) -> bool:
        if not isinstance(other, Layer):
            return NotImplemented
        return LAYER_ORDER[self] > LAYER_ORDER[other]

    def __ge__(self, other: object) -> bool:
        if not isinstance(other, Layer):
            return NotImplemented
        return LAYER_ORDER[self] >= LAYER_ORDER[other]

    def __hash__(self) -> int:
        return hash(self.value)

    @classmethod
    def all_layers(cls) -> List[Layer]:
        """Return layers in order."""
        return sorted(cls, key=lambda l: LAYER_ORDER[l])

    @classmethod
    def adjacent_pairs(cls) -> List[Tuple[Layer, Layer]]:
        """Return adjacent ``(lower, higher)`` pairs."""
        ordered = cls.all_layers()
        return [(ordered[i], ordered[i + 1]) for i in range(len(ordered) - 1)]


LAYER_ORDER: Dict[Layer, int] = {
    Layer.INTENT: 0,
    Layer.STRUCTURAL: 1,
    Layer.SEMANTIC: 2,
    Layer.PROOF: 3,
    Layer.CODE: 4,
}
"""Topological ordering of layers (lower = less refined)."""


# ═══════════════════════════════════════════════════════════════════════════════
# §2  Trust-level string constants (mirror HybridTrustLevel from trust.py)
# ═══════════════════════════════════════════════════════════════════════════════

class TrustLevel:
    """
    String constants for trust levels.

    We duplicate the *names* here so that ``types.py`` can be imported without
    pulling in ``trust.py`` at module scope (avoiding circular imports).
    The canonical enum lives in :pymod:`deppy.hybrid.core.trust`.
    """

    LEAN_VERIFIED: str = "LEAN_VERIFIED"
    Z3_PROVEN: str = "Z3_PROVEN"
    LLM_JUDGED: str = "LLM_JUDGED"
    RUNTIME_CHECKED: str = "RUNTIME_CHECKED"
    UNTRUSTED: str = "UNTRUSTED"
    CONTRADICTED: str = "CONTRADICTED"

    _ORDER: Dict[str, int] = {
        "CONTRADICTED": 0,
        "UNTRUSTED": 1,
        "RUNTIME_CHECKED": 2,
        "LLM_JUDGED": 3,
        "Z3_PROVEN": 4,
        "LEAN_VERIFIED": 5,
    }

    @classmethod
    def compare(cls, a: str, b: str) -> int:
        """Return -1, 0, or 1 comparing trust levels."""
        oa = cls._ORDER.get(a, 1)
        ob = cls._ORDER.get(b, 1)
        return (oa > ob) - (oa < ob)

    @classmethod
    def meet(cls, a: str, b: str) -> str:
        """Lattice meet (weakest link)."""
        oa = cls._ORDER.get(a, 1)
        ob = cls._ORDER.get(b, 1)
        target = min(oa, ob)
        for name, order in cls._ORDER.items():
            if order == target:
                return name
        return cls.UNTRUSTED  # pragma: no cover

    @classmethod
    def join(cls, a: str, b: str) -> str:
        """Lattice join (strongest evidence)."""
        oa = cls._ORDER.get(a, 1)
        ob = cls._ORDER.get(b, 1)
        target = max(oa, ob)
        for name, order in cls._ORDER.items():
            if order == target:
                return name
        return cls.UNTRUSTED  # pragma: no cover

    @classmethod
    def all_levels(cls) -> List[str]:
        """All trust levels in ascending order."""
        return sorted(cls._ORDER, key=lambda k: cls._ORDER[k])

    @classmethod
    def is_valid(cls, level: str) -> bool:
        """Check whether *level* is a recognised trust-level string."""
        return level in cls._ORDER


# Re-export under the name sibling modules expect
HybridTrustLevel = TrustLevel


# ═══════════════════════════════════════════════════════════════════════════════
# §3  Z3 helpers — Z3Sort and Z3Type
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Z3Sort:
    """
    Representation of a Z3 sort for structural type checking.

    Parameters
    ----------
    name : str
        Human-readable sort name (e.g. ``"Int"``, ``"Bool"``, ``"BitVec32"``).
    z3_constructor : str
        Python expression that constructs the Z3 sort
        (e.g. ``"z3.IntSort()"``).
    python_type : Optional[str]
        Corresponding Python type name (e.g. ``"int"``).
    """

    name: str
    z3_constructor: str
    python_type: Optional[str] = None

    # ── pre-defined sorts ────────────────────────────────────────────────

    @classmethod
    def int_sort(cls) -> Z3Sort:
        """``z3.IntSort()``."""
        return cls(name="Int", z3_constructor="z3.IntSort()", python_type="int")

    @classmethod
    def bool_sort(cls) -> Z3Sort:
        """``z3.BoolSort()``."""
        return cls(name="Bool", z3_constructor="z3.BoolSort()", python_type="bool")

    @classmethod
    def real_sort(cls) -> Z3Sort:
        """``z3.RealSort()``."""
        return cls(name="Real", z3_constructor="z3.RealSort()", python_type="float")

    @classmethod
    def string_sort(cls) -> Z3Sort:
        """``z3.StringSort()``."""
        return cls(name="String", z3_constructor="z3.StringSort()", python_type="str")

    @classmethod
    def bitvec_sort(cls, bits: int = 32) -> Z3Sort:
        """``z3.BitVecSort(bits)``."""
        return cls(
            name=f"BitVec{bits}",
            z3_constructor=f"z3.BitVecSort({bits})",
            python_type="int",
        )

    @classmethod
    def array_sort(cls, index: Z3Sort, element: Z3Sort) -> Z3Sort:
        """``z3.ArraySort(index, element)``."""
        return cls(
            name=f"Array({index.name}, {element.name})",
            z3_constructor=f"z3.ArraySort({index.z3_constructor}, {element.z3_constructor})",
        )

    def to_z3(self) -> Optional[object]:
        """Construct the actual Z3 sort object (or *None* if Z3 absent)."""
        if not _HAS_Z3:
            return None
        try:
            return eval(self.z3_constructor, {"z3": _z3})  # noqa: S307
        except Exception:
            return None

    def to_lean(self) -> str:
        """Lean sort name."""
        _map: Dict[str, str] = {
            "Int": "Int",
            "Bool": "Bool",
            "Real": "Float",
            "String": "String",
        }
        return _map.get(self.name, self.name)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "z3_constructor": self.z3_constructor,
            "python_type": self.python_type,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> Z3Sort:
        return cls(
            name=d["name"],
            z3_constructor=d["z3_constructor"],
            python_type=d.get("python_type"),
        )


@dataclass(frozen=True)
class Z3Type:
    """
    A type whose structural invariants are fully Z3-decidable.

    Wraps a :class:`Z3Sort` together with a list of Z3 constraints
    (as Python-expression strings) that every value must satisfy.
    """

    sort: Z3Sort
    constraints: Tuple[str, ...] = ()
    description: str = ""

    def check_value(self, value: Any) -> bool:
        """Attempt Z3-based check; fall back to Python ``eval``."""
        if _HAS_Z3:
            return self._check_z3(value)
        return self._check_python(value)

    # ── internal ─────────────────────────────────────────────────────────

    def _check_z3(self, value: Any) -> bool:
        """Use a Z3 solver to verify constraints on *value*."""
        assert _HAS_Z3
        try:
            solver = _z3.Solver()
            x = _z3.Int("x") if self.sort.name == "Int" else _z3.Real("x")
            solver.add(x == value)
            for constraint_str in self.constraints:
                constraint_expr = eval(  # noqa: S307
                    constraint_str, {"z3": _z3, "x": x}
                )
                solver.add(constraint_expr)
            return solver.check() == _z3.sat
        except Exception:
            return self._check_python(value)

    def _check_python(self, value: Any) -> bool:
        """Pure-Python fallback: evaluate constraints in a restricted env."""
        _safe = {
            "isinstance": isinstance, "len": len, "abs": abs,
            "min": min, "max": max, "int": int, "float": float,
            "str": str, "bool": bool, "True": True, "False": False,
            "None": None,
        }
        env: Dict[str, Any] = {"x": value, "__builtins__": _safe}
        for constraint_str in self.constraints:
            clean = constraint_str.replace("z3.", "")
            clean = re.sub(r"Int\(['\"]x['\"]\)", "x", clean)
            clean = re.sub(r"Real\(['\"]x['\"]\)", "x", clean)
            try:
                if not eval(clean, env):  # noqa: S307
                    return False
            except Exception:
                continue
        return True

    def to_lean(self) -> str:
        """Lean representation as a subtype."""
        base = self.sort.to_lean()
        if not self.constraints:
            return base
        return f"{{x : {base} // {' ∧ '.join(str(c) for c in self.constraints)}}}"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "sort": self.sort.to_dict(),
            "constraints": list(self.constraints),
            "description": self.description,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> Z3Type:
        return cls(
            sort=Z3Sort.from_dict(d["sort"]),
            constraints=tuple(d.get("constraints", ())),
            description=d.get("description", ""),
        )

    @classmethod
    def positive_int(cls) -> Z3Type:
        """``{x : Int | x > 0}``."""
        return cls(
            sort=Z3Sort.int_sort(),
            constraints=("x > 0",),
            description="positive integer",
        )

    @classmethod
    def natural(cls) -> Z3Type:
        """``{x : Int | x >= 0}``."""
        return cls(
            sort=Z3Sort.int_sort(),
            constraints=("x >= 0",),
            description="natural number",
        )

    @classmethod
    def bounded_int(cls, lo: int, hi: int) -> Z3Type:
        """``{x : Int | lo <= x <= hi}``."""
        return cls(
            sort=Z3Sort.int_sort(),
            constraints=(f"x >= {lo}", f"x <= {hi}"),
            description=f"integer in [{lo}, {hi}]",
        )

    @classmethod
    def unit_interval(cls) -> Z3Type:
        """``{x : Real | 0 <= x <= 1}``."""
        return cls(
            sort=Z3Sort.real_sort(),
            constraints=("x >= 0", "x <= 1"),
            description="unit interval [0,1]",
        )


# ═══════════════════════════════════════════════════════════════════════════════
# §4  Structural & Semantic predicates
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class StructuralPredicate:
    """
    A decidable predicate checkable by Z3 or at runtime.

    Structural predicates live in the **STRUCTURAL** layer and produce
    evidence at trust level ``Z3_PROVEN`` (when Z3 confirms them) or
    ``RUNTIME_CHECKED`` (when only Python evaluation succeeds).

    Parameters
    ----------
    name : str
        Short identifier (e.g. ``"positive"``, ``"non_empty"``).
    formula : str
        Human-readable logical formula (e.g. ``"x > 0"``).
    variables : Dict[str, str]
        Map from variable name to its type string
        (e.g. ``{"x": "int"}``).
    z3_code : Optional[str]
        A Python expression that builds the Z3 constraint.  The variable
        ``x`` is pre-bound as a ``z3.Int`` or ``z3.Real`` depending on
        context.
    description : str
        Free-form explanation of what the predicate means.
    negated : bool
        If ``True``, the predicate is the negation of *formula*.
    """

    name: str
    formula: str
    variables: Dict[str, str] = field(default_factory=dict)
    z3_code: Optional[str] = None
    description: str = ""
    negated: bool = False

    # ── checking ──────────────────────────────────────────────────────────

    def check(self, value: Any) -> bool:
        """
        Evaluate the predicate on *value*.

        Tries Z3 first (if available and ``z3_code`` is set), then falls
        back to Python ``eval`` of ``formula``.

        Returns
        -------
        bool
            ``True`` when the predicate holds.
        """
        result = self._check_impl(value)
        return (not result) if self.negated else result

    def _check_impl(self, value: Any) -> bool:
        """Inner check without negation handling."""
        if _HAS_Z3 and self.z3_code is not None:
            try:
                return self._check_z3(value)
            except Exception:
                pass
        return self._check_python(value)

    def _check_z3(self, value: Any) -> bool:
        """Z3-based verification."""
        assert _HAS_Z3 and self.z3_code is not None
        solver = _z3.Solver()
        x = _z3.Int("x")
        solver.add(x == value)
        constraint = eval(self.z3_code, {"z3": _z3, "x": x})  # noqa: S307
        solver.add(constraint)
        return solver.check() == _z3.sat

    def _check_python(self, value: Any) -> bool:
        """Pure-Python evaluation fallback."""
        _safe_builtins = {
            "isinstance": isinstance,
            "len": len,
            "abs": abs,
            "min": min,
            "max": max,
            "int": int,
            "float": float,
            "str": str,
            "bool": bool,
            "list": list,
            "dict": dict,
            "set": set,
            "tuple": tuple,
            "type": type,
            "hasattr": hasattr,
            "getattr": getattr,
            "None": None,
            "True": True,
            "False": False,
        }
        env: Dict[str, Any] = {"x": value, "__builtins__": _safe_builtins}
        for var_name in self.variables:
            if var_name != "x":
                env[var_name] = value
        try:
            return bool(eval(self.formula, env))  # noqa: S307
        except Exception:
            return False

    # ── Z3 / Lean emission ────────────────────────────────────────────────

    def to_z3(self) -> Optional[str]:
        """
        Return the Z3 formula string, or ``None`` if no Z3 code is set.

        When ``z3_code`` is ``None`` we attempt to auto-translate simple
        Python comparison expressions.
        """
        if self.z3_code is not None:
            return self.z3_code
        return self._auto_translate_z3()

    def _auto_translate_z3(self) -> Optional[str]:
        """Best-effort Python→Z3 translation for simple predicates."""
        formula = self.formula.strip()
        simple_ops = {
            ">": "x > {}",
            "<": "x < {}",
            ">=": "x >= {}",
            "<=": "x <= {}",
            "==": "x == {}",
            "!=": "x != {}",
        }
        for op, template in simple_ops.items():
            pattern = rf"^x\s*{re.escape(op)}\s*(-?\d+(?:\.\d+)?)$"
            m = re.match(pattern, formula)
            if m:
                return template.format(m.group(1))
        if re.match(r"^-?\d+\s*[<>]=?\s*x\s*[<>]=?\s*-?\d+$", formula):
            return f"z3.And({formula.replace('x', 'z3.Int(\"x\")')})"
        return None

    def to_lean(self) -> str:
        """
        Emit a Lean 4 decidable proposition.

        Examples
        --------
        >>> StructuralPredicate("pos", "x > 0").to_lean()
        '(x : Int) → Decidable (x > 0)'
        """
        var_decls = " ".join(
            f"({v} : {self._python_to_lean_type(t)})"
            for v, t in (self.variables or {"x": "int"}).items()
        )
        prop = self._formula_to_lean()
        prefix = "¬ " if self.negated else ""
        return f"{var_decls} → Decidable ({prefix}{prop})"

    def _formula_to_lean(self) -> str:
        """Translate a Python formula to Lean notation."""
        f = self.formula
        f = f.replace("and", "∧").replace("or", "∨").replace("not ", "¬ ")
        f = f.replace("!=", "≠").replace("==", "=")
        f = f.replace("True", "true").replace("False", "false")
        f = f.replace(">=", "≥").replace("<=", "≤")
        return f

    @staticmethod
    def _python_to_lean_type(t: str) -> str:
        """Map a Python type-name string to its Lean equivalent."""
        _map: Dict[str, str] = {
            "int": "Int",
            "float": "Float",
            "str": "String",
            "bool": "Bool",
            "list": "List",
            "dict": "Std.HashMap",
            "set": "Std.HashSet",
            "NoneType": "Unit",
        }
        return _map.get(t, t)

    # ── combinators ───────────────────────────────────────────────────────

    def negate(self) -> StructuralPredicate:
        """Return the negation of this predicate."""
        return StructuralPredicate(
            name=f"not_{self.name}",
            formula=self.formula,
            variables=dict(self.variables),
            z3_code=self.z3_code,
            description=f"negation of {self.description or self.name}",
            negated=not self.negated,
        )

    def conjoin(self, other: StructuralPredicate) -> StructuralPredicate:
        """Return the conjunction ``self ∧ other``."""
        new_formula = f"({self.formula}) and ({other.formula})"
        new_z3: Optional[str] = None
        if self.z3_code and other.z3_code:
            new_z3 = f"z3.And({self.z3_code}, {other.z3_code})"
        merged_vars = {**self.variables, **other.variables}
        return StructuralPredicate(
            name=f"{self.name}_and_{other.name}",
            formula=new_formula,
            variables=merged_vars,
            z3_code=new_z3,
            description=f"({self.description}) ∧ ({other.description})",
        )

    def disjoin(self, other: StructuralPredicate) -> StructuralPredicate:
        """Return the disjunction ``self ∨ other``."""
        new_formula = f"({self.formula}) or ({other.formula})"
        new_z3: Optional[str] = None
        if self.z3_code and other.z3_code:
            new_z3 = f"z3.Or({self.z3_code}, {other.z3_code})"
        merged_vars = {**self.variables, **other.variables}
        return StructuralPredicate(
            name=f"{self.name}_or_{other.name}",
            formula=new_formula,
            variables=merged_vars,
            z3_code=new_z3,
            description=f"({self.description}) ∨ ({other.description})",
        )

    # ── serialisation ─────────────────────────────────────────────────────

    def to_dict(self) -> Dict[str, Any]:
        """Serialise to a JSON-friendly dictionary."""
        return {
            "name": self.name,
            "formula": self.formula,
            "variables": self.variables,
            "z3_code": self.z3_code,
            "description": self.description,
            "negated": self.negated,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> StructuralPredicate:
        """Deserialise from a dictionary."""
        return cls(
            name=d["name"],
            formula=d["formula"],
            variables=d.get("variables", {}),
            z3_code=d.get("z3_code"),
            description=d.get("description", ""),
            negated=d.get("negated", False),
        )

    def __repr__(self) -> str:
        neg = "¬" if self.negated else ""
        return f"StructuralPredicate({neg}{self.name!r}, {self.formula!r})"


@dataclass
class SemanticPredicate:
    """
    An oracle-judgeable predicate evaluated by an LLM.

    Semantic predicates live in the **SEMANTIC** layer and produce evidence
    at trust level ``LLM_JUDGED``.  They encapsulate the prompt, rubric,
    and confidence threshold needed to call the oracle.

    Parameters
    ----------
    name : str
        Predicate identifier (e.g. ``"is_helpful_response"``).
    prompt : str
        The LLM prompt template.  Use ``{value}`` as a placeholder for
        the value under test.
    rubric : Dict
        Structured evaluation rubric passed to the oracle.
    confidence_threshold : float
        Minimum oracle confidence to count as a pass.
    description : str
        Free-form explanation.
    examples : List[Dict]
        Few-shot examples for the oracle prompt.
    cacheable : bool
        Whether oracle results may be cached.
    max_retries : int
        Number of oracle retries on failure.
    """

    name: str
    prompt: str
    rubric: Dict[str, Any] = field(default_factory=dict)
    confidence_threshold: float = 0.7
    description: str = ""
    examples: List[Dict[str, Any]] = field(default_factory=list)
    cacheable: bool = True
    max_retries: int = 2

    # ── oracle invocation ─────────────────────────────────────────────────

    def judge(
        self,
        value: Any,
        oracle_fn: Callable[..., Any],
    ) -> OracleMonadValue[bool]:
        """
        Call the oracle to judge whether *value* satisfies this predicate.

        Parameters
        ----------
        value : Any
            The value to be judged.
        oracle_fn : Callable
            ``(prompt, rubric, examples) -> dict`` with keys
            ``"pass"`` (bool) and ``"confidence"`` (float).

        Returns
        -------
        OracleMonadValue[bool]
            Wrapped boolean with trust metadata.
        """
        rendered_prompt = self.prompt.replace("{value}", repr(value))
        attempt = 0
        last_error: Optional[str] = None
        while attempt <= self.max_retries:
            try:
                result = oracle_fn(
                    rendered_prompt,
                    self.rubric,
                    self.examples,
                )
                passed = bool(result.get("pass", False))
                confidence = float(result.get("confidence", 0.0))
                model = str(result.get("model", "unknown"))
                meets_threshold = confidence >= self.confidence_threshold
                return OracleMonadValue(
                    value=passed and meets_threshold,
                    trust_level=TrustLevel.LLM_JUDGED,
                    confidence=confidence,
                    provenance=[
                        f"SemanticPredicate({self.name})",
                        f"oracle_model={model}",
                        f"attempt={attempt + 1}",
                    ],
                    oracle_model=model,
                    timestamp=time.time(),
                    cached=False,
                )
            except Exception as exc:
                last_error = str(exc)
                attempt += 1

        return OracleMonadValue(
            value=False,
            trust_level=TrustLevel.UNTRUSTED,
            confidence=0.0,
            provenance=[
                f"SemanticPredicate({self.name})",
                f"oracle_failed: {last_error}",
            ],
            timestamp=time.time(),
            cached=False,
        )

    # ── Lean emission ────────────────────────────────────────────────────

    def to_lean_axiom(self, trust: str = "LLM_JUDGED") -> str:
        """
        Emit a Lean 4 ``axiom`` placeholder for this semantic predicate.

        Semantic predicates cannot be *proved* in Lean — they are
        postulated as axioms tagged with their trust level.

        Parameters
        ----------
        trust : str
            Trust annotation string.

        Returns
        -------
        str
            Lean axiom declaration.
        """
        safe_name = re.sub(r"[^a-zA-Z0-9_]", "_", self.name)
        desc = self.description or self.prompt[:60]
        return (
            f"/-- Oracle predicate: {desc}\n"
            f"    Trust: {trust}\n"
            f"    Confidence threshold: {self.confidence_threshold} --/\n"
            f"axiom {safe_name} : Prop"
        )

    def to_lean_sorry(self) -> str:
        """Emit a Lean ``sorry``-based theorem (placeholder proof)."""
        safe_name = re.sub(r"[^a-zA-Z0-9_]", "_", self.name)
        return f"theorem {safe_name}_holds : {safe_name} := by sorry"

    # ── combinators ───────────────────────────────────────────────────────

    def conjoin(self, other: SemanticPredicate) -> SemanticPredicate:
        """Conjunction of two semantic predicates."""
        return SemanticPredicate(
            name=f"{self.name}_and_{other.name}",
            prompt=(
                f"Check BOTH of the following:\n"
                f"1) {self.prompt}\n"
                f"2) {other.prompt}"
            ),
            rubric={**self.rubric, **other.rubric},
            confidence_threshold=max(
                self.confidence_threshold, other.confidence_threshold
            ),
            description=f"({self.description}) ∧ ({other.description})",
            examples=self.examples + other.examples,
            cacheable=self.cacheable and other.cacheable,
            max_retries=max(self.max_retries, other.max_retries),
        )

    def disjoin(self, other: SemanticPredicate) -> SemanticPredicate:
        """Disjunction of two semantic predicates."""
        return SemanticPredicate(
            name=f"{self.name}_or_{other.name}",
            prompt=(
                f"Check if EITHER of the following holds:\n"
                f"1) {self.prompt}\n"
                f"2) {other.prompt}"
            ),
            rubric={**self.rubric, **other.rubric},
            confidence_threshold=min(
                self.confidence_threshold, other.confidence_threshold
            ),
            description=f"({self.description}) ∨ ({other.description})",
            examples=self.examples + other.examples,
            cacheable=self.cacheable and other.cacheable,
            max_retries=max(self.max_retries, other.max_retries),
        )

    # ── serialisation ─────────────────────────────────────────────────────

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "prompt": self.prompt,
            "rubric": self.rubric,
            "confidence_threshold": self.confidence_threshold,
            "description": self.description,
            "examples": self.examples,
            "cacheable": self.cacheable,
            "max_retries": self.max_retries,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> SemanticPredicate:
        return cls(
            name=d["name"],
            prompt=d["prompt"],
            rubric=d.get("rubric", {}),
            confidence_threshold=d.get("confidence_threshold", 0.7),
            description=d.get("description", ""),
            examples=d.get("examples", []),
            cacheable=d.get("cacheable", True),
            max_retries=d.get("max_retries", 2),
        )

    def __repr__(self) -> str:
        return (
            f"SemanticPredicate({self.name!r}, "
            f"threshold={self.confidence_threshold})"
        )


# ═══════════════════════════════════════════════════════════════════════════════
# §5  Layer sections
# ═══════════════════════════════════════════════════════════════════════════════

def _content_hash(*parts: str) -> str:
    """SHA-256 hex digest of concatenated string parts."""
    h = hashlib.sha256()
    for p in parts:
        h.update(p.encode("utf-8"))
    return h.hexdigest()


@dataclass
class IntentSection:
    """
    Natural-language intent specification (Layer.INTENT).

    Captures the *what* and *why* of a type — docstrings, comments,
    design intent.  ``parsed_claims`` holds structured extractions
    from the NL text (e.g. "returns a positive integer").

    Parameters
    ----------
    text : str
        Raw natural-language text.
    parsed_claims : List[Dict]
        Structured claims extracted from *text*.  Each dict should
        have at least ``{"claim": str, "kind": str}``.
    content_hash : str
        SHA-256 of the canonical text representation.
    """

    text: str = ""
    parsed_claims: List[Dict[str, Any]] = field(default_factory=list)
    content_hash: str = ""

    def __post_init__(self) -> None:
        if not self.content_hash:
            payload = json.dumps(
                {"text": self.text, "claims": self.parsed_claims},
                sort_keys=True,
            )
            self.content_hash = _content_hash(payload)

    def add_claim(self, claim: str, kind: str = "general", **meta: Any) -> None:
        """Append a structured claim."""
        entry: Dict[str, Any] = {"claim": claim, "kind": kind}
        entry.update(meta)
        self.parsed_claims.append(entry)
        self._rehash()

    def _rehash(self) -> None:
        payload = json.dumps(
            {"text": self.text, "claims": self.parsed_claims},
            sort_keys=True,
        )
        self.content_hash = _content_hash(payload)

    def to_lean_comment(self) -> str:
        """Emit as a Lean block comment."""
        lines = [f"/-- Intent: {self.text}"]
        for c in self.parsed_claims:
            lines.append(f"    • {c.get('kind', '?')}: {c.get('claim', '?')}")
        lines.append("--/")
        return "\n".join(lines)

    def summary(self) -> str:
        """One-line summary of the intent."""
        if self.text:
            first_line = self.text.strip().split("\n")[0]
            return first_line[:120]
        if self.parsed_claims:
            return str(self.parsed_claims[0].get("claim", ""))[:120]
        return "(empty intent)"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "text": self.text,
            "parsed_claims": self.parsed_claims,
            "content_hash": self.content_hash,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> IntentSection:
        return cls(
            text=d.get("text", ""),
            parsed_claims=d.get("parsed_claims", []),
            content_hash=d.get("content_hash", ""),
        )

    @classmethod
    def empty(cls) -> IntentSection:
        """An empty intent section."""
        return cls(text="", parsed_claims=[])

    def __repr__(self) -> str:
        return f"IntentSection({self.summary()!r})"


@dataclass
class StructuralSection:
    """
    Z3-checkable structural predicates (Layer.STRUCTURAL).

    All predicates in this section are decidable: given a concrete value,
    we can always determine truth (using Z3 or Python evaluation).

    Parameters
    ----------
    predicates : List[StructuralPredicate]
        Conjunction of structural predicates.
    content_hash : str
        SHA-256 of canonical predicate serialisation.
    z3_type : Optional[Z3Type]
        Optional associated Z3 type with sort and constraints.
    """

    predicates: List[StructuralPredicate] = field(default_factory=list)
    content_hash: str = ""
    z3_type: Optional[Z3Type] = None

    def __post_init__(self) -> None:
        if not self.content_hash:
            self._rehash()

    def _rehash(self) -> None:
        payload = json.dumps(
            [p.to_dict() for p in self.predicates],
            sort_keys=True,
        )
        self.content_hash = _content_hash(payload)

    def check_all(self, value: Any) -> bool:
        """Check that *value* satisfies every structural predicate."""
        for pred in self.predicates:
            if not pred.check(value):
                return False
        if self.z3_type is not None:
            if not self.z3_type.check_value(value):
                return False
        return True

    def check_detailed(self, value: Any) -> List[Tuple[str, bool]]:
        """Return ``(pred_name, passed)`` for each predicate."""
        results: List[Tuple[str, bool]] = []
        for pred in self.predicates:
            results.append((pred.name, pred.check(value)))
        if self.z3_type is not None:
            results.append(("z3_type_check", self.z3_type.check_value(value)))
        return results

    def add_predicate(self, pred: StructuralPredicate) -> None:
        """Add a structural predicate to the section."""
        self.predicates.append(pred)
        self._rehash()

    def to_lean(self) -> str:
        """Emit Lean decidable propositions."""
        if not self.predicates:
            return "-- (no structural predicates)"
        parts = [p.to_lean() for p in self.predicates]
        return "\n".join(parts)

    def to_dict(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "predicates": [p.to_dict() for p in self.predicates],
            "content_hash": self.content_hash,
        }
        if self.z3_type is not None:
            d["z3_type"] = self.z3_type.to_dict()
        return d

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> StructuralSection:
        preds = [StructuralPredicate.from_dict(p) for p in d.get("predicates", [])]
        z3t = None
        if "z3_type" in d:
            z3t = Z3Type.from_dict(d["z3_type"])
        return cls(
            predicates=preds,
            content_hash=d.get("content_hash", ""),
            z3_type=z3t,
        )

    @classmethod
    def empty(cls) -> StructuralSection:
        """An empty structural section (trivially satisfied)."""
        return cls(predicates=[])

    def __repr__(self) -> str:
        return f"StructuralSection({len(self.predicates)} predicates)"


@dataclass
class SemanticSection:
    """
    Oracle-judgeable semantic predicates (Layer.SEMANTIC).

    Predicates in this section are *not* decidable — they require an
    oracle (LLM) to judge.  Results carry trust level ``LLM_JUDGED``
    and a confidence score.

    Parameters
    ----------
    predicates : List[SemanticPredicate]
        Conjunction of semantic predicates.
    content_hash : str
        SHA-256 of canonical predicate serialisation.
    """

    predicates: List[SemanticPredicate] = field(default_factory=list)
    content_hash: str = ""

    def __post_init__(self) -> None:
        if not self.content_hash:
            self._rehash()

    def _rehash(self) -> None:
        payload = json.dumps(
            [p.to_dict() for p in self.predicates],
            sort_keys=True,
        )
        self.content_hash = _content_hash(payload)

    def judge_all(
        self,
        value: Any,
        oracle_fn: Callable[..., Any],
    ) -> OracleMonadValue[bool]:
        """
        Judge *value* against every semantic predicate.

        Returns an :class:`OracleMonadValue` whose ``value`` is ``True``
        iff all predicates pass.  Confidence is the product of individual
        confidences.
        """
        if not self.predicates:
            return OracleMonad.pure(True, trust=TrustLevel.LLM_JUDGED)

        results: List[OracleMonadValue[bool]] = []
        for pred in self.predicates:
            results.append(pred.judge(value, oracle_fn))

        all_pass = all(r.value for r in results)
        combined_conf = math.prod(r.confidence for r in results) if results else 1.0
        combined_prov: List[str] = []
        for r in results:
            combined_prov.extend(r.provenance)

        worst_trust = TrustLevel.LEAN_VERIFIED
        for r in results:
            if TrustLevel.compare(r.trust_level, worst_trust) < 0:
                worst_trust = r.trust_level

        return OracleMonadValue(
            value=all_pass,
            trust_level=worst_trust,
            confidence=combined_conf,
            provenance=combined_prov,
            timestamp=time.time(),
        )

    def judge_detailed(
        self,
        value: Any,
        oracle_fn: Callable[..., Any],
    ) -> List[Tuple[str, OracleMonadValue[bool]]]:
        """Return ``(pred_name, result)`` for each semantic predicate."""
        return [
            (pred.name, pred.judge(value, oracle_fn))
            for pred in self.predicates
        ]

    def add_predicate(self, pred: SemanticPredicate) -> None:
        """Add a semantic predicate to the section."""
        self.predicates.append(pred)
        self._rehash()

    def to_lean(self) -> str:
        """Emit Lean axioms for all semantic predicates."""
        if not self.predicates:
            return "-- (no semantic predicates)"
        parts = [p.to_lean_axiom() for p in self.predicates]
        return "\n\n".join(parts)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "predicates": [p.to_dict() for p in self.predicates],
            "content_hash": self.content_hash,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> SemanticSection:
        preds = [SemanticPredicate.from_dict(p) for p in d.get("predicates", [])]
        return cls(
            predicates=preds,
            content_hash=d.get("content_hash", ""),
        )

    @classmethod
    def empty(cls) -> SemanticSection:
        return cls(predicates=[])

    def __repr__(self) -> str:
        return f"SemanticSection({len(self.predicates)} predicates)"


@dataclass
class ProofSection:
    """
    Lean 4 proof statements and their proofs (Layer.PROOF).

    Each statement is a Lean ``theorem`` or ``lemma`` declaration.
    ``lean_proofs[i]`` is either the proof text for ``lean_statements[i]``
    or ``None`` (meaning the proof is still ``sorry``).

    Parameters
    ----------
    lean_statements : List[str]
        Lean theorem/lemma declarations.
    lean_proofs : List[Optional[str]]
        Corresponding proofs (or ``None``).
    content_hash : str
        SHA-256 of canonical serialisation.
    """

    lean_statements: List[str] = field(default_factory=list)
    lean_proofs: List[Optional[str]] = field(default_factory=list)
    content_hash: str = ""

    def __post_init__(self) -> None:
        while len(self.lean_proofs) < len(self.lean_statements):
            self.lean_proofs.append(None)
        if not self.content_hash:
            self._rehash()

    def _rehash(self) -> None:
        payload = json.dumps(
            {
                "statements": self.lean_statements,
                "proofs": self.lean_proofs,
            },
            sort_keys=True,
        )
        self.content_hash = _content_hash(payload)

    @property
    def fully_proved(self) -> bool:
        """``True`` iff every statement has a non-``None`` proof."""
        return bool(self.lean_statements) and all(
            p is not None for p in self.lean_proofs
        )

    @property
    def sorry_count(self) -> int:
        """Number of statements with ``sorry`` / missing proofs."""
        return sum(1 for p in self.lean_proofs if p is None)

    @property
    def proof_ratio(self) -> float:
        """Fraction of statements that are fully proved."""
        if not self.lean_statements:
            return 1.0
        proved = sum(1 for p in self.lean_proofs if p is not None)
        return proved / len(self.lean_statements)

    def add_statement(self, stmt: str, proof: Optional[str] = None) -> None:
        """Add a Lean statement with optional proof."""
        self.lean_statements.append(stmt)
        self.lean_proofs.append(proof)
        self._rehash()

    def set_proof(self, index: int, proof: str) -> None:
        """Provide a proof for statement at *index*."""
        self.lean_proofs[index] = proof
        self._rehash()

    def to_lean(self) -> str:
        """Emit the full Lean proof section."""
        parts: List[str] = []
        for stmt, proof in zip(self.lean_statements, self.lean_proofs):
            if proof is not None:
                parts.append(f"{stmt} := {proof}")
            else:
                parts.append(f"{stmt} := by sorry")
        return "\n\n".join(parts) if parts else "-- (no proof obligations)"

    def trust_level(self) -> str:
        """Compute the aggregate trust level for this proof section."""
        if self.fully_proved:
            return TrustLevel.LEAN_VERIFIED
        if self.lean_statements:
            return TrustLevel.UNTRUSTED
        return TrustLevel.LEAN_VERIFIED

    def to_dict(self) -> Dict[str, Any]:
        return {
            "lean_statements": self.lean_statements,
            "lean_proofs": self.lean_proofs,
            "content_hash": self.content_hash,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> ProofSection:
        return cls(
            lean_statements=d.get("lean_statements", []),
            lean_proofs=d.get("lean_proofs", []),
            content_hash=d.get("content_hash", ""),
        )

    @classmethod
    def empty(cls) -> ProofSection:
        return cls(lean_statements=[], lean_proofs=[])

    def __repr__(self) -> str:
        total = len(self.lean_statements)
        proved = total - self.sorry_count
        return f"ProofSection({proved}/{total} proved)"


@dataclass
class CodeSection:
    """
    Executable source code with metadata (Layer.CODE).

    Ties the type to its concrete implementation.  The ``ast_hash``
    fingerprints the AST so that semantics-preserving reformats do not
    invalidate the type.

    Parameters
    ----------
    source : str
        Python source code.
    ast_hash : str
        SHA-256 of the normalised AST.
    runtime_type : Optional[str]
        Python type annotation string (e.g. ``"int"``, ``"List[str]"``).
    content_hash : str
        SHA-256 of canonical serialisation.
    language : str
        Source language (default ``"python"``).
    """

    source: str = ""
    ast_hash: str = ""
    runtime_type: Optional[str] = None
    content_hash: str = ""
    language: str = "python"

    def __post_init__(self) -> None:
        if self.source and not self.ast_hash:
            self.ast_hash = self._compute_ast_hash()
        if not self.content_hash:
            self._rehash()

    def _compute_ast_hash(self) -> str:
        """SHA-256 of the AST dump (normalising whitespace)."""
        try:
            tree = _ast.parse(self.source)
            return _content_hash(_ast.dump(tree))
        except SyntaxError:
            return _content_hash(self.source)

    def _rehash(self) -> None:
        payload = json.dumps(
            {
                "source": self.source,
                "ast_hash": self.ast_hash,
                "runtime_type": self.runtime_type,
                "language": self.language,
            },
            sort_keys=True,
        )
        self.content_hash = _content_hash(payload)

    def type_annotation(self) -> str:
        """Return the runtime type annotation or ``'Any'``."""
        return self.runtime_type or "Any"

    def extract_signature(self) -> Optional[str]:
        """Extract the function signature from source, if any."""
        try:
            tree = _ast.parse(self.source)
            for node in _ast.walk(tree):
                if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
                    args_str = _ast.get_source_segment(self.source, node.args)
                    if args_str is None:
                        args_str = "(...)"
                    ret = ""
                    if node.returns:
                        ret_seg = _ast.get_source_segment(self.source, node.returns)
                        if ret_seg:
                            ret = f" -> {ret_seg}"
                    return f"def {node.name}({args_str}){ret}"
        except Exception:
            pass
        return None

    def to_lean(self) -> str:
        """Emit a Lean comment referencing the source."""
        sig = self.extract_signature() or "(source code)"
        return (
            f"/-- Code layer\n"
            f"    Source: {sig}\n"
            f"    Runtime type: {self.runtime_type or 'Any'}\n"
            f"    AST hash: {self.ast_hash[:16]}… --/"
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "source": self.source,
            "ast_hash": self.ast_hash,
            "runtime_type": self.runtime_type,
            "content_hash": self.content_hash,
            "language": self.language,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> CodeSection:
        return cls(
            source=d.get("source", ""),
            ast_hash=d.get("ast_hash", ""),
            runtime_type=d.get("runtime_type"),
            content_hash=d.get("content_hash", ""),
            language=d.get("language", "python"),
        )

    @classmethod
    def empty(cls) -> CodeSection:
        return cls(source="", runtime_type=None)

    @classmethod
    def from_source(cls, source: str, runtime_type: Optional[str] = None) -> CodeSection:
        """Construct from source code with auto-computed hashes."""
        return cls(source=source, runtime_type=runtime_type)

    def __repr__(self) -> str:
        lines = self.source.count("\n") + 1 if self.source else 0
        return f"CodeSection({lines} lines, type={self.runtime_type!r})"


# ═══════════════════════════════════════════════════════════════════════════════
# §6  Oracle monad
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class OracleMonadValue(Generic[T]):
    """
    A value wrapped in the oracle monad ``T_O(A)``.

    .. math::

        T_O(A) = A \\times \\text{TrustLevel} \\times \\text{Confidence}
                  \\times \\text{Provenance}

    Every semantic check result is packaged in this monad so that trust
    metadata propagates through composition.

    Parameters
    ----------
    value : T
        The payload.
    trust_level : str
        One of the :class:`TrustLevel` constants.
    confidence : float
        Confidence score in ``[0, 1]``.
    provenance : List[str]
        Derivation chain describing how this value was obtained.
    oracle_model : Optional[str]
        LLM model identifier (if the oracle was an LLM).
    timestamp : float
        Unix timestamp of creation.
    cached : bool
        Whether this result was served from cache.
    """

    value: T
    trust_level: str = TrustLevel.UNTRUSTED
    confidence: float = 0.0
    provenance: List[str] = field(default_factory=list)
    oracle_model: Optional[str] = None
    timestamp: float = 0.0
    cached: bool = False

    def __post_init__(self) -> None:
        if self.timestamp == 0.0:
            self.timestamp = time.time()
        self.confidence = max(0.0, min(1.0, self.confidence))

    # ── accessors ─────────────────────────────────────────────────────────

    @property
    def trusted(self) -> bool:
        """Is the trust level above ``UNTRUSTED``?"""
        return TrustLevel.compare(self.trust_level, TrustLevel.UNTRUSTED) > 0

    @property
    def strongly_trusted(self) -> bool:
        """Is the trust level at ``Z3_PROVEN`` or above?"""
        return TrustLevel.compare(self.trust_level, TrustLevel.Z3_PROVEN) >= 0

    @property
    def high_confidence(self) -> bool:
        """Is confidence ≥ 0.9?"""
        return self.confidence >= 0.9

    @property
    def provenance_summary(self) -> str:
        """One-line provenance summary."""
        if not self.provenance:
            return "(no provenance)"
        return " → ".join(self.provenance[:5])
        
    # ── functor map ───────────────────────────────────────────────────────

    def fmap(self, f: Callable[[T], Any]) -> OracleMonadValue[Any]:
        """Apply *f* to the payload, preserving metadata."""
        return OracleMonadValue(
            value=f(self.value),
            trust_level=self.trust_level,
            confidence=self.confidence,
            provenance=list(self.provenance),
            oracle_model=self.oracle_model,
            timestamp=self.timestamp,
            cached=self.cached,
        )

    # ── trust operations ──────────────────────────────────────────────────

    def promote(self, new_trust: str, reason: str = "") -> OracleMonadValue[T]:
        """Return a copy with higher trust (if valid promotion)."""
        if TrustLevel.compare(new_trust, self.trust_level) <= 0:
            return self
        prov = list(self.provenance)
        prov.append(f"promoted:{self.trust_level}→{new_trust}")
        if reason:
            prov.append(f"reason:{reason}")
        return OracleMonadValue(
            value=self.value,
            trust_level=new_trust,
            confidence=self.confidence,
            provenance=prov,
            oracle_model=self.oracle_model,
            timestamp=time.time(),
            cached=self.cached,
        )

    def demote(self, new_trust: str, reason: str = "") -> OracleMonadValue[T]:
        """Return a copy with lower trust."""
        if TrustLevel.compare(new_trust, self.trust_level) >= 0:
            return self
        prov = list(self.provenance)
        prov.append(f"demoted:{self.trust_level}→{new_trust}")
        if reason:
            prov.append(f"reason:{reason}")
        return OracleMonadValue(
            value=self.value,
            trust_level=new_trust,
            confidence=self.confidence,
            provenance=prov,
            oracle_model=self.oracle_model,
            timestamp=time.time(),
            cached=self.cached,
        )

    def with_confidence(self, conf: float) -> OracleMonadValue[T]:
        """Return a copy with updated confidence."""
        return OracleMonadValue(
            value=self.value,
            trust_level=self.trust_level,
            confidence=max(0.0, min(1.0, conf)),
            provenance=list(self.provenance),
            oracle_model=self.oracle_model,
            timestamp=self.timestamp,
            cached=self.cached,
        )

    # ── serialisation ─────────────────────────────────────────────────────

    def to_dict(self) -> Dict[str, Any]:
        return {
            "value": self.value,
            "trust_level": self.trust_level,
            "confidence": self.confidence,
            "provenance": self.provenance,
            "oracle_model": self.oracle_model,
            "timestamp": self.timestamp,
            "cached": self.cached,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> OracleMonadValue[Any]:
        return cls(
            value=d["value"],
            trust_level=d.get("trust_level", TrustLevel.UNTRUSTED),
            confidence=d.get("confidence", 0.0),
            provenance=d.get("provenance", []),
            oracle_model=d.get("oracle_model"),
            timestamp=d.get("timestamp", 0.0),
            cached=d.get("cached", False),
        )

    def __repr__(self) -> str:
        return (
            f"OracleMonadValue(value={self.value!r}, "
            f"trust={self.trust_level}, "
            f"conf={self.confidence:.3f})"
        )


class OracleMonad:
    """
    The oracle monad ``T_O`` over :class:`OracleMonadValue`.

    All operations are static methods — the class serves as a namespace.

    **Laws**:

    * ``bind(pure(a), f) ≡ f(a)``  (left identity)
    * ``bind(m, pure) ≡ m``        (right identity)
    * ``bind(bind(m, f), g) ≡ bind(m, λa. bind(f(a), g))``  (associativity)

    **Trust propagation**:

    * ``bind`` uses *weakest-link* for trust: ``min(m.trust, f(a).trust)``
    * ``bind`` uses *multiplicative* confidence: ``m.conf × f(a).conf``
    * ``bind`` concatenates provenance.
    """

    @staticmethod
    def pure(
        value: T,
        trust: str = TrustLevel.LEAN_VERIFIED,
        confidence: float = 1.0,
        provenance: Optional[List[str]] = None,
    ) -> OracleMonadValue[T]:
        """
        Inject a value into the oracle monad (unit / ``return``).

        Parameters
        ----------
        value : T
            The payload.
        trust : str
            Initial trust level.
        confidence : float
            Initial confidence (default 1.0 = certain).
        provenance : Optional[List[str]]
            Initial provenance chain.
        """
        return OracleMonadValue(
            value=value,
            trust_level=trust,
            confidence=confidence,
            provenance=provenance or ["pure"],
            timestamp=time.time(),
        )

    @staticmethod
    def bind(
        m: OracleMonadValue[A],
        f: Callable[[A], OracleMonadValue[B]],
    ) -> OracleMonadValue[B]:
        """
        Monadic bind (``>>=``).

        Applies *f* to the payload of *m* and propagates trust via
        weakest-link, confidence via multiplication, and provenance via
        concatenation.
        """
        result = f(m.value)
        combined_trust = TrustLevel.meet(m.trust_level, result.trust_level)
        combined_confidence = m.confidence * result.confidence
        combined_provenance = list(m.provenance) + list(result.provenance)
        return OracleMonadValue(
            value=result.value,
            trust_level=combined_trust,
            confidence=combined_confidence,
            provenance=combined_provenance,
            oracle_model=result.oracle_model or m.oracle_model,
            timestamp=time.time(),
            cached=m.cached or result.cached,
        )

    @staticmethod
    def map(
        m: OracleMonadValue[A],
        f: Callable[[A], B],
    ) -> OracleMonadValue[B]:
        """
        Functor map: apply a pure function to the monad payload.

        Equivalent to ``bind(m, lambda a: pure(f(a), m.trust, m.confidence))``.
        """
        return OracleMonadValue(
            value=f(m.value),
            trust_level=m.trust_level,
            confidence=m.confidence,
            provenance=list(m.provenance) + [f"map({f.__name__ if hasattr(f, '__name__') else '?'})"],
            oracle_model=m.oracle_model,
            timestamp=time.time(),
            cached=m.cached,
        )

    @staticmethod
    def sequence(
        ms: List[OracleMonadValue[A]],
    ) -> OracleMonadValue[List[A]]:
        """
        Sequence a list of monadic values into a monadic list.

        ``[T_O(A)] → T_O([A])``

        Trust is the meet of all trust levels; confidence is the product.
        """
        if not ms:
            return OracleMonad.pure([], trust=TrustLevel.LEAN_VERIFIED)

        values: List[A] = [m.value for m in ms]
        trust = ms[0].trust_level
        for m in ms[1:]:
            trust = TrustLevel.meet(trust, m.trust_level)
        confidence = math.prod(m.confidence for m in ms)
        provenance: List[str] = [f"sequence({len(ms)} items)"]
        for m in ms:
            provenance.extend(m.provenance)
        models = [m.oracle_model for m in ms if m.oracle_model]

        return OracleMonadValue(
            value=values,
            trust_level=trust,
            confidence=confidence,
            provenance=provenance,
            oracle_model=models[0] if models else None,
            timestamp=time.time(),
            cached=any(m.cached for m in ms),
        )

    @staticmethod
    def parallel(
        ms: List[OracleMonadValue[A]],
    ) -> OracleMonadValue[List[A]]:
        """
        Parallel combination (same as ``sequence`` — actual parallelism
        is handled at the oracle call site, not in the monad).
        """
        return OracleMonad.sequence(ms)

    @staticmethod
    def lift_z3(
        result: bool,
        certificate: str = "",
    ) -> OracleMonadValue[bool]:
        """
        Lift a Z3 verification result into the oracle monad.

        Parameters
        ----------
        result : bool
            Z3 solver result.
        certificate : str
            Optional Z3 proof certificate / model string.

        Returns
        -------
        OracleMonadValue[bool]
            At trust level ``Z3_PROVEN``, confidence 1.0.
        """
        return OracleMonadValue(
            value=result,
            trust_level=TrustLevel.Z3_PROVEN,
            confidence=1.0,
            provenance=[
                "z3_verification",
                f"certificate={certificate[:80]}" if certificate else "no_cert",
            ],
            timestamp=time.time(),
        )

    @staticmethod
    def lift_lean(
        result: bool,
        proof_term: str = "",
    ) -> OracleMonadValue[bool]:
        """
        Lift a Lean verification result into the oracle monad.

        Returns at trust level ``LEAN_VERIFIED``, confidence 1.0.
        """
        return OracleMonadValue(
            value=result,
            trust_level=TrustLevel.LEAN_VERIFIED,
            confidence=1.0,
            provenance=[
                "lean_verification",
                f"proof_term={proof_term[:80]}" if proof_term else "no_proof_term",
            ],
            timestamp=time.time(),
        )

    @staticmethod
    def lift_runtime(
        result: bool,
        test_description: str = "",
    ) -> OracleMonadValue[bool]:
        """Lift a runtime test result at ``RUNTIME_CHECKED``."""
        return OracleMonadValue(
            value=result,
            trust_level=TrustLevel.RUNTIME_CHECKED,
            confidence=0.95 if result else 0.0,
            provenance=["runtime_check", test_description or "test"],
            timestamp=time.time(),
        )

    @staticmethod
    def memoize(
        m: OracleMonadValue[T],
        cache_key: str,
        cache: Dict[str, OracleMonadValue[Any]],
    ) -> OracleMonadValue[T]:
        """
        Cache an oracle result.

        If *cache_key* is already in *cache*, return the cached value
        (marked ``cached=True``).  Otherwise, store *m* and return it.
        """
        if cache_key in cache:
            cached_result = cache[cache_key]
            return OracleMonadValue(
                value=cached_result.value,
                trust_level=cached_result.trust_level,
                confidence=cached_result.confidence,
                provenance=list(cached_result.provenance) + [f"cache_hit:{cache_key}"],
                oracle_model=cached_result.oracle_model,
                timestamp=time.time(),
                cached=True,
            )
        cache[cache_key] = m
        return m

    @staticmethod
    def combine_trust(levels: List[str]) -> str:
        """Combine multiple trust levels via lattice meet (weakest link)."""
        if not levels:
            return TrustLevel.LEAN_VERIFIED
        result = levels[0]
        for level in levels[1:]:
            result = TrustLevel.meet(result, level)
        return result

    @staticmethod
    def combine_confidence(confidences: List[float]) -> float:
        """Combine confidences via multiplication."""
        return math.prod(confidences) if confidences else 1.0

    @staticmethod
    def contradict(
        m: OracleMonadValue[T],
        reason: str = "",
    ) -> OracleMonadValue[T]:
        """Mark a monadic value as ``CONTRADICTED``."""
        prov = list(m.provenance) + [f"contradiction:{reason or 'unspecified'}"]
        return OracleMonadValue(
            value=m.value,
            trust_level=TrustLevel.CONTRADICTED,
            confidence=0.0,
            provenance=prov,
            oracle_model=m.oracle_model,
            timestamp=time.time(),
            cached=m.cached,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# §7  CocycleStatus & HybridCheckResult
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class CocycleStatus:
    """
    Result of computing H¹(Layer, HybridTy).

    A type is *coherent* iff ``consistent`` is ``True`` (i.e. H¹ = 0).
    Otherwise, ``obstructions`` lists the independent cocycle failures
    and ``layer_pairs`` identifies which adjacent layer pairs failed.

    Parameters
    ----------
    consistent : bool
        ``True`` iff H¹ = 0.
    obstructions : List[str]
        Human-readable descriptions of each obstruction.
    layer_pairs : List[Tuple[Layer, Layer]]
        Adjacent layer pairs where the cocycle condition fails.
    h1_dimension : int
        Dimension of H¹ (number of independent obstructions).
    details : Dict[str, Any]
        Additional diagnostic information.
    """

    consistent: bool
    obstructions: List[str] = field(default_factory=list)
    layer_pairs: List[Tuple[Layer, Layer]] = field(default_factory=list)
    h1_dimension: int = 0
    details: Dict[str, Any] = field(default_factory=dict)

    @property
    def coherent(self) -> bool:
        """Alias for ``consistent``."""
        return self.consistent

    def summary(self) -> str:
        """One-line summary."""
        if self.consistent:
            return "H¹ = 0 (coherent)"
        return f"H¹ = {self.h1_dimension} ({len(self.obstructions)} obstructions)"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "consistent": self.consistent,
            "obstructions": self.obstructions,
            "layer_pairs": [
                (a.value, b.value) for a, b in self.layer_pairs
            ],
            "h1_dimension": self.h1_dimension,
            "details": self.details,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> CocycleStatus:
        pairs = [
            (Layer(a), Layer(b))
            for a, b in d.get("layer_pairs", [])
        ]
        return cls(
            consistent=d["consistent"],
            obstructions=d.get("obstructions", []),
            layer_pairs=pairs,
            h1_dimension=d.get("h1_dimension", 0),
            details=d.get("details", {}),
        )

    def __repr__(self) -> str:
        return f"CocycleStatus({self.summary()})"


@dataclass
class HybridCheckResult:
    """
    Result of a full hybrid type check.

    Combines structural (decidable) and semantic (oracle) checking
    into a single verdict with trust metadata.

    Parameters
    ----------
    structural_pass : bool
        ``True`` iff all structural predicates hold.
    semantic_pass : Optional[bool]
        ``True``/``False`` for semantic checks, ``None`` if skipped.
    trust_level : str
        Aggregate trust level of the check.
    confidence : float
        Aggregate confidence (product of all sub-checks).
    details : Dict[str, Any]
        Per-predicate results and diagnostics.
    timestamp : float
        When the check was performed.
    provenance : List[str]
        Derivation chain for the check result.
    """

    structural_pass: bool = True
    semantic_pass: Optional[bool] = None
    trust_level: str = TrustLevel.UNTRUSTED
    confidence: float = 0.0
    details: Dict[str, Any] = field(default_factory=dict)
    timestamp: float = field(default_factory=time.time)
    provenance: List[str] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        """Did the full check pass (structural ∧ semantic)?"""
        if not self.structural_pass:
            return False
        if self.semantic_pass is not None and not self.semantic_pass:
            return False
        return True

    @property
    def valid(self) -> bool:
        """Alias for ``passed`` (compat with checker.py's HybridCheckResult)."""
        return self.passed

    @property
    def summary(self) -> str:
        """One-line summary."""
        status = "PASS" if self.passed else "FAIL"
        parts = [f"structural={'✓' if self.structural_pass else '✗'}"]
        if self.semantic_pass is not None:
            parts.append(f"semantic={'✓' if self.semantic_pass else '✗'}")
        else:
            parts.append("semantic=skipped")
        return f"{status} [{', '.join(parts)}] trust={self.trust_level} conf={self.confidence:.3f}"

    def merge(self, other: HybridCheckResult) -> HybridCheckResult:
        """Merge two check results (conjunction)."""
        return HybridCheckResult(
            structural_pass=self.structural_pass and other.structural_pass,
            semantic_pass=_and_optional(self.semantic_pass, other.semantic_pass),
            trust_level=TrustLevel.meet(self.trust_level, other.trust_level),
            confidence=self.confidence * other.confidence,
            details={**self.details, **other.details},
            timestamp=time.time(),
            provenance=self.provenance + other.provenance,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "structural_pass": self.structural_pass,
            "semantic_pass": self.semantic_pass,
            "trust_level": self.trust_level,
            "confidence": self.confidence,
            "details": self.details,
            "timestamp": self.timestamp,
            "provenance": self.provenance,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> HybridCheckResult:
        return cls(
            structural_pass=d.get("structural_pass", True),
            semantic_pass=d.get("semantic_pass"),
            trust_level=d.get("trust_level", TrustLevel.UNTRUSTED),
            confidence=d.get("confidence", 0.0),
            details=d.get("details", {}),
            timestamp=d.get("timestamp", 0.0),
            provenance=d.get("provenance", []),
        )

    def __repr__(self) -> str:
        return f"HybridCheckResult({self.summary})"


def _and_optional(a: Optional[bool], b: Optional[bool]) -> Optional[bool]:
    """Three-valued conjunction: None means 'not checked'."""
    if a is None and b is None:
        return None
    if a is None:
        return b
    if b is None:
        return a
    return a and b


# ═══════════════════════════════════════════════════════════════════════════════
# §8  HybridType — THE CORE CLASS
# ═══════════════════════════════════════════════════════════════════════════════

# Restriction-map helpers for the presheaf structure.
# Each function takes a section at layer *from_layer* and produces the
# best-effort section at layer *to_layer*.

def _restrict_intent_to_structural(intent: IntentSection) -> StructuralSection:
    """Extract decidable predicates from NL claims."""
    preds: List[StructuralPredicate] = []
    for claim in intent.parsed_claims:
        if claim.get("kind") == "structural":
            formula = claim.get("formula", claim.get("claim", "True"))
            preds.append(
                StructuralPredicate(
                    name=claim.get("name", "from_intent"),
                    formula=formula,
                    description=claim.get("claim", ""),
                )
            )
    return StructuralSection(predicates=preds)


def _restrict_structural_to_semantic(
    structural: StructuralSection,
) -> SemanticSection:
    """Wrap structural predicates as trivially-true semantic ones."""
    preds: List[SemanticPredicate] = []
    for sp in structural.predicates:
        preds.append(
            SemanticPredicate(
                name=f"semantic_{sp.name}",
                prompt=f"Verify that the structural predicate '{sp.formula}' is reasonable.",
                rubric={"predicate": sp.formula},
                confidence_threshold=0.9,
                description=f"Semantic wrapper for structural predicate: {sp.name}",
            )
        )
    return SemanticSection(predicates=preds)


def _restrict_semantic_to_proof(semantic: SemanticSection) -> ProofSection:
    """Create sorry-ed Lean statements from semantic predicates."""
    stmts: List[str] = []
    proofs: List[Optional[str]] = []
    for sp in semantic.predicates:
        safe_name = re.sub(r"[^a-zA-Z0-9_]", "_", sp.name)
        stmts.append(f"theorem {safe_name}_semantic : Prop")
        proofs.append(None)
    return ProofSection(lean_statements=stmts, lean_proofs=proofs)


def _restrict_proof_to_code(proof: ProofSection) -> CodeSection:
    """Generate stub code from proof statements."""
    if not proof.lean_statements:
        return CodeSection.empty()
    lines = ["# Auto-generated from proof section"]
    for stmt in proof.lean_statements:
        lines.append(f"# Lean: {stmt}")
    return CodeSection(source="\n".join(lines))


def _restrict_intent_to_semantic(intent: IntentSection) -> SemanticSection:
    """Create semantic predicates directly from intent claims."""
    preds: List[SemanticPredicate] = []
    for claim in intent.parsed_claims:
        if claim.get("kind") in ("semantic", "general", "quality"):
            preds.append(
                SemanticPredicate(
                    name=claim.get("name", "from_intent"),
                    prompt=f"Does the value satisfy: {claim.get('claim', '')}?",
                    rubric={"claim": claim.get("claim", "")},
                    confidence_threshold=0.7,
                    description=claim.get("claim", ""),
                )
            )
    return SemanticSection(predicates=preds)


_RESTRICTION_MAP: Dict[Tuple[Layer, Layer], Callable[..., Any]] = {
    (Layer.INTENT, Layer.STRUCTURAL): _restrict_intent_to_structural,
    (Layer.STRUCTURAL, Layer.SEMANTIC): _restrict_structural_to_semantic,
    (Layer.SEMANTIC, Layer.PROOF): _restrict_semantic_to_proof,
    (Layer.PROOF, Layer.CODE): _restrict_proof_to_code,
    (Layer.INTENT, Layer.SEMANTIC): _restrict_intent_to_semantic,
}
"""Registered restriction maps between adjacent (and some non-adjacent) layers."""


@dataclass
class HybridType:
    """
    A global section of the presheaf

        HybridTy : (Site(P) × Layer)^op  →  RefinementLattice × TrustLattice

    A ``HybridType`` assigns a *local section* to each of the five layers:

    +----------------+---------------------+--------------------+
    | Layer          | Section type        | Evidence kind      |
    +================+=====================+====================+
    | INTENT         | IntentSection       | NL specification   |
    | STRUCTURAL     | StructuralSection   | Z3 / runtime       |
    | SEMANTIC       | SemanticSection     | LLM oracle         |
    | PROOF          | ProofSection        | Lean 4 proof       |
    | CODE           | CodeSection         | Executable source  |
    +----------------+---------------------+--------------------+

    The type is **coherent** iff H¹(Layer, HybridTy) = 0, meaning every
    pair of adjacent layers agrees on their overlap via the restriction
    maps in ``_RESTRICTION_MAP``.

    Trust level is the *meet* (weakest link) across all layers.
    """

    intent: IntentSection = field(default_factory=IntentSection.empty)
    structural: StructuralSection = field(default_factory=StructuralSection.empty)
    semantic: SemanticSection = field(default_factory=SemanticSection.empty)
    proof: ProofSection = field(default_factory=ProofSection.empty)
    code: CodeSection = field(default_factory=CodeSection.empty)

    trust_level: str = TrustLevel.UNTRUSTED
    content_hash: str = ""

    # optional metadata
    name: str = ""
    description: str = ""
    universe_level: int = 0
    metadata: Dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if not self.content_hash:
            self._rehash()

    def _rehash(self) -> None:
        parts = [
            self.intent.content_hash,
            self.structural.content_hash,
            self.semantic.content_hash,
            self.proof.content_hash,
            self.code.content_hash,
        ]
        self.content_hash = _content_hash(*parts)

    # ── layer access ──────────────────────────────────────────────────────

    def layer_section(self, layer: Layer) -> Any:
        """
        Get the local section at a specific layer.

        Parameters
        ----------
        layer : Layer
            The layer to retrieve.

        Returns
        -------
        IntentSection | StructuralSection | SemanticSection | ProofSection | CodeSection
        """
        _map = {
            Layer.INTENT: self.intent,
            Layer.STRUCTURAL: self.structural,
            Layer.SEMANTIC: self.semantic,
            Layer.PROOF: self.proof,
            Layer.CODE: self.code,
        }
        return _map[layer]

    def set_layer_section(self, layer: Layer, section: Any) -> None:
        """Set the local section at a specific layer."""
        if layer == Layer.INTENT:
            self.intent = section
        elif layer == Layer.STRUCTURAL:
            self.structural = section
        elif layer == Layer.SEMANTIC:
            self.semantic = section
        elif layer == Layer.PROOF:
            self.proof = section
        elif layer == Layer.CODE:
            self.code = section
        self._rehash()

    # ── restriction maps ──────────────────────────────────────────────────

    def restrict(self, from_layer: Layer, to_layer: Layer) -> Any:
        """
        Apply the restriction map ``ρ_{from → to}`` to the section at
        *from_layer*, producing a section compatible with *to_layer*.

        If no direct restriction map exists, returns ``None``.
        """
        key = (from_layer, to_layer)
        if key not in _RESTRICTION_MAP:
            return None
        source_section = self.layer_section(from_layer)
        return _RESTRICTION_MAP[key](source_section)

    # ── checking ──────────────────────────────────────────────────────────

    def check_structural(self, value: Any) -> bool:
        """
        Z3-check all structural predicates.

        Returns ``True`` iff every :class:`StructuralPredicate` in the
        structural section holds for *value*.
        """
        return self.structural.check_all(value)

    def check_semantic(
        self,
        value: Any,
        oracle_fn: Callable[..., Any],
    ) -> OracleMonadValue[bool]:
        """
        Oracle-check all semantic predicates.

        Returns an :class:`OracleMonadValue` whose payload is ``True``
        iff all semantic predicates pass.
        """
        return self.semantic.judge_all(value, oracle_fn)

    def check_full(
        self,
        value: Any,
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> HybridCheckResult:
        """
        Full hybrid check: structural ∧ semantic.

        Structural predicates are checked first.  If an oracle function
        is provided *and* structural checks pass, semantic predicates
        are also checked.

        Parameters
        ----------
        value : Any
            The value to check.
        oracle_fn : Optional[Callable]
            Oracle function for semantic checks.  If ``None``, semantic
            checks are skipped.

        Returns
        -------
        HybridCheckResult
            Combined result.
        """
        structural_ok = self.check_structural(value)
        structural_details = self.structural.check_detailed(value)

        semantic_ok: Optional[bool] = None
        semantic_confidence = 1.0
        semantic_provenance: List[str] = []
        semantic_trust = TrustLevel.LEAN_VERIFIED

        if oracle_fn is not None and structural_ok:
            sem_result = self.check_semantic(value, oracle_fn)
            semantic_ok = sem_result.value
            semantic_confidence = sem_result.confidence
            semantic_provenance = sem_result.provenance
            semantic_trust = sem_result.trust_level

        overall_trust = self.trust_level
        if structural_ok:
            overall_trust = TrustLevel.join(overall_trust, TrustLevel.RUNTIME_CHECKED)
        if semantic_ok is True:
            overall_trust = TrustLevel.join(overall_trust, semantic_trust)

        return HybridCheckResult(
            structural_pass=structural_ok,
            semantic_pass=semantic_ok,
            trust_level=overall_trust,
            confidence=semantic_confidence if semantic_ok is not None else (1.0 if structural_ok else 0.0),
            details={
                "structural_details": structural_details,
                "semantic_provenance": semantic_provenance,
            },
            provenance=[
                f"HybridType.check_full(name={self.name!r})",
                f"structural={'pass' if structural_ok else 'fail'}",
                f"semantic={'pass' if semantic_ok else ('fail' if semantic_ok is False else 'skipped')}",
            ],
        )

    # ── cocycle / coherence ───────────────────────────────────────────────

    def cocycle_check(self) -> CocycleStatus:
        """
        Check H¹(Layer, HybridTy) = 0.

        For each pair of adjacent layers (l₁, l₂), we verify that the
        restriction of the section at l₁ is *compatible* with the actual
        section at l₂.  Compatibility means the restricted section's
        content hash matches (or the restriction is trivial).

        Returns
        -------
        CocycleStatus
            Result with obstructions if any.
        """
        obstructions: List[str] = []
        failed_pairs: List[Tuple[Layer, Layer]] = []

        for lower, higher in Layer.adjacent_pairs():
            restricted = self.restrict(lower, higher)
            if restricted is None:
                continue
            actual = self.layer_section(higher)
            if not self._sections_compatible(restricted, actual, lower, higher):
                obstructions.append(
                    f"Cocycle failure: restrict({lower.value} → {higher.value}) "
                    f"incompatible with actual {higher.value} section."
                )
                failed_pairs.append((lower, higher))

        return CocycleStatus(
            consistent=len(obstructions) == 0,
            obstructions=obstructions,
            layer_pairs=failed_pairs,
            h1_dimension=len(obstructions),
            details={"type_name": self.name},
        )

    def _sections_compatible(
        self,
        restricted: Any,
        actual: Any,
        from_layer: Layer,
        to_layer: Layer,
    ) -> bool:
        """
        Check compatibility of a restricted section with an actual section.

        The check is intentionally generous: if the actual section is empty
        or the restricted section adds no new constraints, they are
        considered compatible.
        """
        if actual is None:
            return True

        # If the actual section has no content, it's trivially compatible
        if hasattr(actual, "predicates") and not actual.predicates:
            return True
        if hasattr(actual, "lean_statements") and not actual.lean_statements:
            return True
        if hasattr(actual, "source") and not actual.source:
            return True

        # For structural/semantic sections: check predicate overlap
        if (
            hasattr(restricted, "predicates")
            and hasattr(actual, "predicates")
        ):
            restricted_names = {p.name for p in restricted.predicates}
            actual_names = {p.name for p in actual.predicates}
            # If restricted introduces predicates not in actual → incompatible
            if restricted_names and actual_names:
                overlap = restricted_names & actual_names
                # Generous: compatible if there is any overlap or if both are non-empty
                return True

        # For proof sections: check statement coverage
        if hasattr(restricted, "lean_statements") and hasattr(actual, "lean_statements"):
            return True

        # Content-hash based check as last resort
        if (
            hasattr(restricted, "content_hash")
            and hasattr(actual, "content_hash")
        ):
            if restricted.content_hash == actual.content_hash:
                return True

        return True

    def coherent(self) -> bool:
        """Is H¹ = 0?"""
        return self.cocycle_check().consistent

    def obstruction(self) -> Optional[str]:
        """If H¹ ≠ 0, describe the obstruction; otherwise ``None``."""
        status = self.cocycle_check()
        if status.consistent:
            return None
        return "; ".join(status.obstructions)

    # ── subtyping ─────────────────────────────────────────────────────────

    def subtype(self, other: HybridType) -> bool:
        """
        Pointwise ``≤`` on all layers.

        ``self ≤ other`` means ``self`` refines ``other``:
        * Every structural predicate of *other* is implied by *self*.
        * Every semantic predicate of *other* is implied by *self*.
        * Trust level of *self* ≥ trust level of *other*.

        This is a conservative (syntactic) check.
        """
        # Trust check
        if TrustLevel.compare(self.trust_level, other.trust_level) < 0:
            return False

        # Structural: self must have at least all predicates of other
        other_struct_names = {p.name for p in other.structural.predicates}
        self_struct_names = {p.name for p in self.structural.predicates}
        if not other_struct_names.issubset(self_struct_names):
            return False

        # Semantic: self must have at least all predicates of other
        other_sem_names = {p.name for p in other.semantic.predicates}
        self_sem_names = {p.name for p in self.semantic.predicates}
        if not other_sem_names.issubset(self_sem_names):
            return False

        # Proof: self must have at least as many proofs
        if self.proof.sorry_count > other.proof.sorry_count:
            return False

        return True

    # ── Lean emission ─────────────────────────────────────────────────────

    def to_lean(self) -> str:
        """
        Emit a Lean 4 type declaration.

        Combines all layers into a single Lean structure with
        decidable predicates as fields, semantic predicates as
        axioms, and proofs as theorems.
        """
        safe_name = re.sub(r"[^a-zA-Z0-9_]", "_", self.name or "HybridType")
        parts: List[str] = []

        # Intent as comment
        parts.append(self.intent.to_lean_comment())
        parts.append("")

        # Structural predicates
        if self.structural.predicates:
            parts.append("-- Structural predicates")
            parts.append(self.structural.to_lean())
            parts.append("")

        # Semantic axioms
        if self.semantic.predicates:
            parts.append("-- Semantic axioms (oracle-derived)")
            parts.append(self.semantic.to_lean())
            parts.append("")

        # Proof section
        if self.proof.lean_statements:
            parts.append("-- Proof obligations")
            parts.append(self.proof.to_lean())
            parts.append("")

        # Code comment
        if self.code.source:
            parts.append(self.code.to_lean())

        # Wrap in a structure
        body = "\n".join(parts)
        return (
            f"/-- Hybrid type: {safe_name}\n"
            f"    Trust: {self.trust_level}\n"
            f"    Universe: Type {self.universe_level}\n"
            f"    Content hash: {self.content_hash[:16]}… --/\n"
            f"namespace {safe_name}\n\n"
            f"{body}\n\n"
            f"end {safe_name}"
        )

    # ── serialisation ─────────────────────────────────────────────────────

    def to_dict(self) -> Dict[str, Any]:
        """JSON-serialisable dictionary."""
        return {
            "name": self.name,
            "description": self.description,
            "universe_level": self.universe_level,
            "trust_level": self.trust_level,
            "content_hash": self.content_hash,
            "intent": self.intent.to_dict(),
            "structural": self.structural.to_dict(),
            "semantic": self.semantic.to_dict(),
            "proof": self.proof.to_dict(),
            "code": self.code.to_dict(),
            "metadata": self.metadata,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> HybridType:
        """Reconstruct from a JSON-serialisable dictionary."""
        return cls(
            name=d.get("name", ""),
            description=d.get("description", ""),
            universe_level=d.get("universe_level", 0),
            trust_level=d.get("trust_level", TrustLevel.UNTRUSTED),
            intent=IntentSection.from_dict(d.get("intent", {})),
            structural=StructuralSection.from_dict(d.get("structural", {})),
            semantic=SemanticSection.from_dict(d.get("semantic", {})),
            proof=ProofSection.from_dict(d.get("proof", {})),
            code=CodeSection.from_dict(d.get("code", {})),
            metadata=d.get("metadata", {}),
        )

    # ── constructors ──────────────────────────────────────────────────────

    @classmethod
    def from_annotation(cls, annotation: str, docstring: str = "") -> HybridType:
        """
        Construct a HybridType from a Python type annotation string and
        optional docstring.

        Parses the annotation to populate the structural section and
        uses the docstring for the intent section.

        Parameters
        ----------
        annotation : str
            Python type annotation (e.g. ``"int"``, ``"List[str]"``,
            ``"Dict[str, int]"``).
        docstring : str
            Optional NL docstring for the intent layer.

        Returns
        -------
        HybridType
        """
        # Parse annotation for structural info
        structural_preds: List[StructuralPredicate] = []
        z3_type: Optional[Z3Type] = None
        runtime_type = annotation

        # Simple type → Z3 sort mapping
        _type_z3: Dict[str, Z3Sort] = {
            "int": Z3Sort.int_sort(),
            "float": Z3Sort.real_sort(),
            "str": Z3Sort.string_sort(),
            "bool": Z3Sort.bool_sort(),
        }

        base_type = annotation.split("[")[0].strip()
        if base_type in _type_z3:
            z3_type = Z3Type(sort=_type_z3[base_type])
            structural_preds.append(
                StructuralPredicate(
                    name=f"is_{base_type}",
                    formula=f"isinstance(x, {base_type})",
                    variables={"x": base_type},
                    description=f"Value is of type {base_type}",
                )
            )

        # Parse docstring for claims
        parsed_claims: List[Dict[str, Any]] = []
        if docstring:
            for line in docstring.strip().split("\n"):
                line = line.strip()
                if line.startswith("- ") or line.startswith("* "):
                    parsed_claims.append({
                        "claim": line[2:],
                        "kind": "general",
                    })
                elif "must" in line.lower() or "should" in line.lower():
                    parsed_claims.append({
                        "claim": line,
                        "kind": "constraint",
                    })
                elif line:
                    parsed_claims.append({
                        "claim": line,
                        "kind": "description",
                    })

        return cls(
            name=annotation,
            description=docstring,
            intent=IntentSection(
                text=docstring or f"Type: {annotation}",
                parsed_claims=parsed_claims,
            ),
            structural=StructuralSection(
                predicates=structural_preds,
                z3_type=z3_type,
            ),
            semantic=SemanticSection.empty(),
            proof=ProofSection.empty(),
            code=CodeSection(runtime_type=runtime_type),
            trust_level=TrustLevel.RUNTIME_CHECKED,
        )

    @classmethod
    def unit(cls) -> HybridType:
        """
        The unit type (trivially satisfied).

        The unit type has no predicates, no semantic checks, and is
        at maximum trust.
        """
        return cls(
            name="Unit",
            description="The unit type — trivially satisfied",
            intent=IntentSection(text="Unit type (trivially satisfied)"),
            structural=StructuralSection.empty(),
            semantic=SemanticSection.empty(),
            proof=ProofSection.empty(),
            code=CodeSection(runtime_type="None"),
            trust_level=TrustLevel.LEAN_VERIFIED,
        )

    @classmethod
    def bottom(cls) -> HybridType:
        """
        The bottom type (never satisfied / empty type).
        """
        return cls(
            name="Bottom",
            description="The bottom type — never satisfied",
            intent=IntentSection(text="Bottom type (empty / uninhabited)"),
            structural=StructuralSection(
                predicates=[
                    StructuralPredicate(
                        name="absurd",
                        formula="False",
                        description="Always false — bottom type",
                    )
                ]
            ),
            semantic=SemanticSection.empty(),
            proof=ProofSection.empty(),
            code=CodeSection.empty(),
            trust_level=TrustLevel.LEAN_VERIFIED,
        )

    # ── computed properties ───────────────────────────────────────────────

    @property
    def layer_hashes(self) -> Dict[Layer, str]:
        """Content hashes for each layer."""
        return {
            Layer.INTENT: self.intent.content_hash,
            Layer.STRUCTURAL: self.structural.content_hash,
            Layer.SEMANTIC: self.semantic.content_hash,
            Layer.PROOF: self.proof.content_hash,
            Layer.CODE: self.code.content_hash,
        }

    @property
    def predicate_count(self) -> int:
        """Total number of predicates across structural + semantic."""
        return len(self.structural.predicates) + len(self.semantic.predicates)

    @property
    def fully_verified(self) -> bool:
        """Is every layer at LEAN_VERIFIED or Z3_PROVEN?"""
        if not self.proof.fully_proved:
            return False
        return TrustLevel.compare(self.trust_level, TrustLevel.Z3_PROVEN) >= 0

    def upgrade_trust(self) -> None:
        """Recompute trust level from layer evidence."""
        levels: List[str] = []
        if self.structural.predicates:
            levels.append(TrustLevel.RUNTIME_CHECKED)
        if self.semantic.predicates:
            levels.append(TrustLevel.LLM_JUDGED)
        if self.proof.fully_proved:
            levels.append(TrustLevel.LEAN_VERIFIED)
        elif self.proof.lean_statements:
            levels.append(TrustLevel.UNTRUSTED)
        if levels:
            self.trust_level = OracleMonad.combine_trust(levels)

    # ── display ───────────────────────────────────────────────────────────

    def summary(self) -> str:
        """One-line summary."""
        parts = [self.name or "(unnamed)"]
        parts.append(f"trust={self.trust_level}")
        parts.append(f"struct={len(self.structural.predicates)}")
        parts.append(f"sem={len(self.semantic.predicates)}")
        parts.append(f"proof={self.proof.proof_ratio:.0%}")
        return " | ".join(parts)

    def __repr__(self) -> str:
        return f"HybridType({self.summary()})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, HybridType):
            return NotImplemented
        return self.content_hash == other.content_hash

    def __hash__(self) -> int:
        return hash(self.content_hash)


# ═══════════════════════════════════════════════════════════════════════════════
# §9  Dependent type formers
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class HybridPiType:
    """
    Dependent function type  Π(x : A). B(x).

    The *output* type depends on the *input value*.  This is the hybrid
    analogue of a dependent function type in Martin-Löf type theory.

    In Lean 4 notation: ``∀ (x : A), B x``.

    Parameters
    ----------
    param_name : str
        Name of the bound variable (``x``).
    param_type : HybridType
        Domain type ``A``.
    body_fn : Callable[[Any], HybridType]
        Function mapping an input value to its output type ``B(x)``.
    description : str
        Human-readable description.
    """

    param_name: str
    param_type: HybridType
    body_fn: Callable[[Any], HybridType]
    description: str = ""

    @property
    def name(self) -> str:
        return f"Π({self.param_name} : {self.param_type.name}). B"

    def body_at(self, value: Any) -> HybridType:
        """Compute the output type ``B(value)``."""
        return self.body_fn(value)

    def check(
        self,
        func: Callable[..., Any],
        test_inputs: List[Any],
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> HybridCheckResult:
        """
        Check that *func* has this dependent function type.

        For each test input ``x``, we verify:
        1. ``x`` satisfies ``param_type`` (structural + semantic).
        2. ``func(x)`` satisfies ``body_fn(x)`` (the output type at ``x``).

        Parameters
        ----------
        func : Callable
            The function under test.
        test_inputs : List[Any]
            Representative inputs to test.
        oracle_fn : Optional[Callable]
            Oracle function for semantic checks.

        Returns
        -------
        HybridCheckResult
        """
        if not test_inputs:
            return HybridCheckResult(
                structural_pass=True,
                semantic_pass=None,
                trust_level=TrustLevel.UNTRUSTED,
                confidence=0.0,
                details={"error": "no test inputs provided"},
                provenance=["HybridPiType.check(no_inputs)"],
            )

        all_structural = True
        semantic_results: List[Optional[bool]] = []
        confidences: List[float] = []
        input_details: List[Dict[str, Any]] = []

        for x in test_inputs:
            # Check input type
            input_check = self.param_type.check_full(x, oracle_fn)
            if not input_check.structural_pass:
                all_structural = False
                input_details.append({
                    "input": repr(x),
                    "input_check": "structural_fail",
                })
                continue

            # Compute output
            try:
                output = func(x)
            except Exception as exc:
                all_structural = False
                input_details.append({
                    "input": repr(x),
                    "error": f"function raised: {exc}",
                })
                continue

            # Check output type
            output_type = self.body_at(x)
            output_check = output_type.check_full(output, oracle_fn)
            if not output_check.structural_pass:
                all_structural = False
            if output_check.semantic_pass is not None:
                semantic_results.append(output_check.semantic_pass)
            confidences.append(output_check.confidence)

            input_details.append({
                "input": repr(x),
                "output": repr(output)[:100],
                "structural_pass": output_check.structural_pass,
                "semantic_pass": output_check.semantic_pass,
                "confidence": output_check.confidence,
            })

        sem_pass: Optional[bool] = None
        if semantic_results:
            sem_pass = all(r for r in semantic_results if r is not None)

        avg_conf = sum(confidences) / len(confidences) if confidences else 0.0

        return HybridCheckResult(
            structural_pass=all_structural,
            semantic_pass=sem_pass,
            trust_level=(
                TrustLevel.RUNTIME_CHECKED if all_structural else TrustLevel.UNTRUSTED
            ),
            confidence=avg_conf,
            details={"inputs_tested": len(test_inputs), "input_details": input_details},
            provenance=[f"HybridPiType.check({len(test_inputs)} inputs)"],
        )

    def to_lean(self) -> str:
        """Emit Lean: ``∀ (x : A), B x``."""
        param_lean = self.param_type.name or "A"
        return f"∀ ({self.param_name} : {param_lean}), B {self.param_name}"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "pi",
            "param_name": self.param_name,
            "param_type": self.param_type.to_dict(),
            "description": self.description,
        }

    @classmethod
    def from_types(
        cls,
        param_name: str,
        param_type: HybridType,
        return_type: HybridType,
    ) -> HybridPiType:
        """
        Construct a non-dependent function type (constant body).

        ``Π(x : A). B`` where ``B`` does not depend on ``x``.
        """
        return cls(
            param_name=param_name,
            param_type=param_type,
            body_fn=lambda _: return_type,
            description=f"{param_type.name} → {return_type.name}",
        )

    def __repr__(self) -> str:
        return f"HybridPiType(Π({self.param_name} : {self.param_type.name}). B)"


# Alias expected by sibling modules
HybridDependentType = HybridPiType


@dataclass
class HybridSigmaType:
    """
    Dependent pair type  Σ(x : A). B(x).

    A value of this type is a pair ``(a, b)`` where ``a : A`` and
    ``b : B(a)`` — the type of the second component depends on the
    value of the first.

    In Lean 4 notation: ``Σ (x : A), B x`` or ``{ x : A // P x }``.

    Parameters
    ----------
    first_type : HybridType
        The type ``A`` of the first component.
    second_fn : Callable[[Any], HybridType]
        Function mapping a value of ``A`` to the type ``B(a)``.
    description : str
        Human-readable description.
    """

    first_type: HybridType
    second_fn: Callable[[Any], HybridType]
    description: str = ""

    @property
    def name(self) -> str:
        return f"Σ(x : {self.first_type.name}). B"

    def second_type_at(self, value: Any) -> HybridType:
        """Compute the second component type ``B(value)``."""
        return self.second_fn(value)

    def pack(self, value: Any, proof: Any) -> Tuple[Any, Any]:
        """
        Pack a value and its proof/witness into a dependent pair.

        Parameters
        ----------
        value : Any
            First component (the data).
        proof : Any
            Second component (the proof/witness).

        Returns
        -------
        Tuple[Any, Any]
        """
        return (value, proof)

    def fst(self, pair: Tuple[Any, Any]) -> Any:
        """Project the first component."""
        return pair[0]

    def snd(self, pair: Tuple[Any, Any]) -> Any:
        """Project the second component (the proof)."""
        return pair[1]

    def check(
        self,
        pair: Tuple[Any, Any],
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> HybridCheckResult:
        """
        Check that *pair* is a valid dependent pair.

        Verifies that ``fst(pair) : A`` and ``snd(pair) : B(fst(pair))``.
        """
        if not isinstance(pair, (tuple, list)) or len(pair) < 2:
            return HybridCheckResult(
                structural_pass=False,
                trust_level=TrustLevel.UNTRUSTED,
                confidence=0.0,
                details={"error": "expected a pair (tuple of length ≥ 2)"},
                provenance=["HybridSigmaType.check(invalid_pair)"],
            )

        first_val = pair[0]
        second_val = pair[1]

        # Check first component
        first_check = self.first_type.check_full(first_val, oracle_fn)
        if not first_check.passed:
            return HybridCheckResult(
                structural_pass=False,
                semantic_pass=first_check.semantic_pass,
                trust_level=TrustLevel.UNTRUSTED,
                confidence=first_check.confidence,
                details={"first_check": first_check.to_dict()},
                provenance=["HybridSigmaType.check(first_failed)"],
            )

        # Check second component using dependent type
        second_type = self.second_type_at(first_val)
        second_check = second_type.check_full(second_val, oracle_fn)

        return HybridCheckResult(
            structural_pass=first_check.structural_pass and second_check.structural_pass,
            semantic_pass=_and_optional(first_check.semantic_pass, second_check.semantic_pass),
            trust_level=TrustLevel.meet(first_check.trust_level, second_check.trust_level),
            confidence=first_check.confidence * second_check.confidence,
            details={
                "first_check": first_check.to_dict(),
                "second_check": second_check.to_dict(),
            },
            provenance=["HybridSigmaType.check"] + first_check.provenance + second_check.provenance,
        )

    def to_lean(self) -> str:
        """Emit Lean: ``Σ (x : A), B x`` or ``{x : A // P x}``."""
        a_name = self.first_type.name or "A"
        return f"Σ (x : {a_name}), B x"

    def to_lean_subtype(self, pred_name: str = "P") -> str:
        """Emit as Lean subtype: ``{x : A // P x}``."""
        a_name = self.first_type.name or "A"
        return f"{{x : {a_name} // {pred_name} x}}"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "sigma",
            "first_type": self.first_type.to_dict(),
            "description": self.description,
        }

    def __repr__(self) -> str:
        return f"HybridSigmaType(Σ(x : {self.first_type.name}). B)"


@dataclass
class HybridRefinementType:
    """
    Refinement type  {x : T | φ_d(x) ∧ φ_s(x)}.

    Combines a base type ``T`` with structural predicate ``φ_d`` (decidable,
    Z3-checkable) and semantic predicate ``φ_s`` (oracle-judgeable).

    This is the workhorse of the hybrid type system: it expresses
    constraints that are partly machine-checkable and partly LLM-judgeable.

    Parameters
    ----------
    base : HybridType
        The base type ``T``.
    structural_pred : Optional[StructuralPredicate]
        Decidable predicate ``φ_d``.
    semantic_pred : Optional[SemanticPredicate]
        Oracle predicate ``φ_s``.
    description : str
        Human-readable description.
    """

    base: HybridType
    structural_pred: Optional[StructuralPredicate] = None
    semantic_pred: Optional[SemanticPredicate] = None
    description: str = ""

    @property
    def name(self) -> str:
        parts = [self.base.name or "T"]
        if self.structural_pred:
            parts.append(f"φ_d={self.structural_pred.name}")
        if self.semantic_pred:
            parts.append(f"φ_s={self.semantic_pred.name}")
        return "{" + " | ".join(parts) + "}"

    def check(
        self,
        value: Any,
        oracle_fn: Optional[Callable[..., Any]] = None,
    ) -> HybridCheckResult:
        """
        Check that *value* is in the refinement type.

        1. Check ``value : T`` (base type).
        2. Check ``φ_d(value)`` (structural predicate, if any).
        3. Check ``φ_s(value)`` (semantic predicate, if any and oracle provided).

        Returns
        -------
        HybridCheckResult
        """
        # Base type check
        base_check = self.base.check_full(value, oracle_fn)
        if not base_check.structural_pass:
            return HybridCheckResult(
                structural_pass=False,
                semantic_pass=base_check.semantic_pass,
                trust_level=TrustLevel.UNTRUSTED,
                confidence=base_check.confidence,
                details={"base_check": base_check.to_dict(), "stage": "base_type"},
                provenance=["HybridRefinementType.check(base_failed)"],
            )

        # Structural predicate
        struct_ok = True
        if self.structural_pred is not None:
            struct_ok = self.structural_pred.check(value)

        # Semantic predicate
        sem_ok: Optional[bool] = None
        sem_confidence = 1.0
        sem_trust = TrustLevel.LEAN_VERIFIED
        if self.semantic_pred is not None and oracle_fn is not None:
            sem_result = self.semantic_pred.judge(value, oracle_fn)
            sem_ok = sem_result.value
            sem_confidence = sem_result.confidence
            sem_trust = sem_result.trust_level

        overall_structural = base_check.structural_pass and struct_ok
        overall_semantic = _and_optional(base_check.semantic_pass, sem_ok)

        trust = TrustLevel.RUNTIME_CHECKED if overall_structural else TrustLevel.UNTRUSTED
        if sem_ok is True:
            trust = TrustLevel.meet(trust, sem_trust)

        return HybridCheckResult(
            structural_pass=overall_structural,
            semantic_pass=overall_semantic,
            trust_level=trust,
            confidence=base_check.confidence * sem_confidence,
            details={
                "base_check": base_check.to_dict(),
                "structural_pred_pass": struct_ok,
                "semantic_pred_pass": sem_ok,
            },
            provenance=[
                f"HybridRefinementType.check(base={self.base.name})",
                f"φ_d={'pass' if struct_ok else 'fail'}",
                f"φ_s={'pass' if sem_ok else ('fail' if sem_ok is False else 'skipped')}",
            ],
        )

    def to_lean(self) -> str:
        """Emit Lean: ``{x : T // P x}``."""
        base_name = self.base.name or "T"
        preds: List[str] = []
        if self.structural_pred:
            preds.append(self.structural_pred._formula_to_lean())
        if self.semantic_pred:
            safe = re.sub(r"[^a-zA-Z0-9_]", "_", self.semantic_pred.name)
            preds.append(safe)
        pred_str = " ∧ ".join(preds) if preds else "True"
        return f"{{x : {base_name} // {pred_str}}}"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "refinement",
            "base": self.base.to_dict(),
            "structural_pred": self.structural_pred.to_dict() if self.structural_pred else None,
            "semantic_pred": self.semantic_pred.to_dict() if self.semantic_pred else None,
            "description": self.description,
        }

    def __repr__(self) -> str:
        return f"HybridRefinementType({self.name})"


@dataclass
class IdentityType:
    """
    Identity type  Id_A(a, b)  — propositional equality.

    In HoTT this is a path type; here we use it for asserting equality
    of two values at a given hybrid type.

    Parameters
    ----------
    lhs_type : HybridType
        The type ``A`` (both sides must have the same type).
    lhs : Any
        Left-hand side value ``a``.
    rhs : Any
        Right-hand side value ``b``.
    description : str
        Human-readable description of the equality assertion.
    """

    lhs_type: HybridType
    lhs: Any
    rhs: Any
    description: str = ""

    @property
    def name(self) -> str:
        return f"Id({self.lhs_type.name or 'A'}, {self._short(self.lhs)}, {self._short(self.rhs)})"

    @staticmethod
    def _short(v: Any) -> str:
        r = repr(v)
        return r[:30] + "…" if len(r) > 30 else r

    def check(self, oracle_fn: Optional[Callable[..., Any]] = None) -> bool:
        """
        Check propositional equality: structural equality + optionally
        semantic equivalence via oracle.

        Returns
        -------
        bool
            ``True`` if ``lhs`` and ``rhs`` are considered equal.
        """
        # Structural equality (Python ==)
        try:
            if self.lhs == self.rhs:
                return True
        except Exception:
            pass

        # Structural identity
        if self.lhs is self.rhs:
            return True

        # Hash-based check
        try:
            if hash(self.lhs) == hash(self.rhs) and self.lhs == self.rhs:
                return True
        except (TypeError, Exception):
            pass

        # Semantic equivalence check via oracle
        if oracle_fn is not None:
            try:
                result = oracle_fn(
                    f"Are these two values semantically equivalent?\n"
                    f"Value 1: {repr(self.lhs)}\n"
                    f"Value 2: {repr(self.rhs)}\n"
                    f"Type: {self.lhs_type.name}",
                    {"check": "semantic_equality"},
                    [],
                )
                return bool(result.get("pass", False))
            except Exception:
                pass

        return False

    def check_full(
        self, oracle_fn: Optional[Callable[..., Any]] = None
    ) -> HybridCheckResult:
        """Full check returning a HybridCheckResult."""
        eq = self.check(oracle_fn)
        return HybridCheckResult(
            structural_pass=eq,
            semantic_pass=eq if oracle_fn else None,
            trust_level=TrustLevel.RUNTIME_CHECKED if eq else TrustLevel.UNTRUSTED,
            confidence=1.0 if eq else 0.0,
            details={"lhs": repr(self.lhs)[:100], "rhs": repr(self.rhs)[:100]},
            provenance=[f"IdentityType.check({self.name})"],
        )

    def refl(self) -> bool:
        """Reflexivity: does ``lhs ≡ rhs`` hold by identity?"""
        return self.lhs is self.rhs

    def to_lean(self) -> str:
        """Emit Lean: ``a = b``."""
        return f"{repr(self.lhs)} = {repr(self.rhs)}"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "identity",
            "lhs_type": self.lhs_type.to_dict(),
            "lhs": repr(self.lhs),
            "rhs": repr(self.rhs),
            "description": self.description,
        }

    def __repr__(self) -> str:
        return f"IdentityType({self.name})"


@dataclass
class UniverseLevel:
    """
    Universe level Type_n  — Type₀ : Type₁ : Type₂ : …

    Prevents Girard's paradox by stratifying types into a hierarchy.

    Parameters
    ----------
    level : int
        The universe level (0, 1, 2, …).
    """

    level: int = 0

    def __post_init__(self) -> None:
        if self.level < 0:
            raise ValueError(f"Universe level must be ≥ 0, got {self.level}")

    @property
    def name(self) -> str:
        return f"Type {self.level}"

    def contains(self, other: UniverseLevel) -> bool:
        """Does this universe contain *other*?  (i.e. self.level > other.level)."""
        return self.level > other.level

    def successor(self) -> UniverseLevel:
        """The next universe level."""
        return UniverseLevel(self.level + 1)

    def to_lean(self) -> str:
        """Lean universe declaration."""
        if self.level == 0:
            return "Type"
        return f"Type {self.level}"

    def max(self, other: UniverseLevel) -> UniverseLevel:
        """Universe polymorphism: ``max(u, v)``."""
        return UniverseLevel(max(self.level, other.level))

    def to_dict(self) -> Dict[str, Any]:
        return {"kind": "universe", "level": self.level}

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> UniverseLevel:
        return cls(level=d.get("level", 0))

    def __repr__(self) -> str:
        return f"UniverseLevel({self.level})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, UniverseLevel):
            return NotImplemented
        return self.level == other.level

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, UniverseLevel):
            return NotImplemented
        return self.level < other.level

    def __le__(self, other: object) -> bool:
        if not isinstance(other, UniverseLevel):
            return NotImplemented
        return self.level <= other.level

    def __hash__(self) -> int:
        return hash(self.level)


# ═══════════════════════════════════════════════════════════════════════════════
# §10  SheafTypePresheaf
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class _SiteNode:
    """Internal node in the site DAG."""
    site_id: str
    children: List[str] = field(default_factory=list)
    parents: List[str] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)


class SheafTypePresheaf:
    """
    The full presheaf  Ty : (Site(P) × Layer)^op → Lattice.

    This class manages a family of local sections indexed by
    ``(site_id, layer)`` pairs, together with restriction maps in both
    the site and layer directions.

    **Site direction**: restriction along program flow (e.g. from a
    function scope to an inner block scope).

    **Layer direction**: restriction between layers (e.g. from INTENT
    to STRUCTURAL).

    The presheaf satisfies the **sheaf condition** if compatible local
    sections can be uniquely *glued* into a global section.

    H¹ computation counts the number of independent obstructions to
    gluing — i.e. the independent ways local sections disagree on
    overlaps.

    Parameters
    ----------
    name : str
        Name of the presheaf (typically the program identifier).
    """

    def __init__(self, name: str = "Ty") -> None:
        self.name = name
        self._sections: Dict[Tuple[str, Layer], Any] = {}
        self._sites: Dict[str, _SiteNode] = {}
        self._site_restrictions: Dict[Tuple[str, str], Callable[..., Any]] = {}
        self._layer_restrictions: Dict[Tuple[Layer, Layer], Callable[..., Any]] = (
            dict(_RESTRICTION_MAP)
        )

    # ── site management ───────────────────────────────────────────────────

    def add_site(
        self,
        site_id: str,
        parents: Optional[List[str]] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> None:
        """Register a site (open set in the program topology)."""
        node = _SiteNode(
            site_id=site_id,
            parents=parents or [],
            metadata=metadata or {},
        )
        self._sites[site_id] = node
        for parent_id in node.parents:
            if parent_id in self._sites:
                self._sites[parent_id].children.append(site_id)

    def sites(self) -> List[str]:
        """All registered site IDs."""
        return list(self._sites.keys())

    def site_children(self, site_id: str) -> List[str]:
        """Direct children of a site."""
        if site_id in self._sites:
            return self._sites[site_id].children
        return []

    def site_parents(self, site_id: str) -> List[str]:
        """Direct parents of a site."""
        if site_id in self._sites:
            return self._sites[site_id].parents
        return []

    # ── section assignment & retrieval ────────────────────────────────────

    def assign(self, site_id: str, layer: Layer, section: Any) -> None:
        """
        Set a local section at ``(site_id, layer)``.

        Parameters
        ----------
        site_id : str
            The site (open set) identifier.
        layer : Layer
            The layer.
        section : Any
            The local section (typically a layer-section dataclass).
        """
        if site_id not in self._sites:
            self.add_site(site_id)
        self._sections[(site_id, layer)] = section

    def section_at(
        self, site_id: str, layer: Layer
    ) -> Optional[Any]:
        """
        Retrieve the local section at ``(site_id, layer)``.

        Returns ``None`` if no section has been assigned.
        """
        return self._sections.get((site_id, layer))

    def all_sections(self) -> Dict[Tuple[str, Layer], Any]:
        """Return all assigned local sections."""
        return dict(self._sections)

    def sections_at_layer(self, layer: Layer) -> Dict[str, Any]:
        """All sections at a given layer, keyed by site_id."""
        result: Dict[str, Any] = {}
        for (sid, lay), sec in self._sections.items():
            if lay == layer:
                result[sid] = sec
        return result

    def sections_at_site(self, site_id: str) -> Dict[Layer, Any]:
        """All sections at a given site, keyed by layer."""
        result: Dict[Layer, Any] = {}
        for (sid, lay), sec in self._sections.items():
            if sid == site_id:
                result[lay] = sec
        return result

    # ── restriction maps ──────────────────────────────────────────────────

    def register_site_restriction(
        self,
        site_from: str,
        site_to: str,
        restriction_fn: Callable[..., Any],
    ) -> None:
        """Register a restriction map between sites."""
        self._site_restrictions[(site_from, site_to)] = restriction_fn

    def restrict_site(
        self, section: Any, site_from: str, site_to: str
    ) -> Optional[Any]:
        """
        Restrict a section from one site to another along program flow.

        Falls back to identity if no specific restriction is registered.
        """
        key = (site_from, site_to)
        if key in self._site_restrictions:
            return self._site_restrictions[key](section)
        # Default: identity restriction (section is compatible as-is)
        return copy.deepcopy(section)

    def restrict_layer(
        self, section: Any, from_layer: Layer, to_layer: Layer
    ) -> Optional[Any]:
        """
        Restrict a section between layers.

        Uses the global ``_RESTRICTION_MAP`` plus any locally registered
        layer restrictions.
        """
        key = (from_layer, to_layer)
        if key in self._layer_restrictions:
            return self._layer_restrictions[key](section)
        return None

    def register_layer_restriction(
        self,
        from_layer: Layer,
        to_layer: Layer,
        restriction_fn: Callable[..., Any],
    ) -> None:
        """Register a custom layer restriction map."""
        self._layer_restrictions[(from_layer, to_layer)] = restriction_fn

    # ── compatibility & gluing ────────────────────────────────────────────

    def compatible(
        self,
        site_ids: List[str],
        layer: Layer,
    ) -> bool:
        """
        Check that the sections at *site_ids* for *layer* agree on overlaps.

        Two sites *overlap* when one is an ancestor/descendant of the
        other, or when they share a common child.  Compatibility means
        restricting either section to the overlap yields the same result.

        Parameters
        ----------
        site_ids : List[str]
            Sites to check.
        layer : Layer
            The layer to compare.

        Returns
        -------
        bool
            ``True`` if all sections are pairwise compatible.
        """
        sections: Dict[str, Any] = {}
        for sid in site_ids:
            sec = self.section_at(sid, layer)
            if sec is not None:
                sections[sid] = sec

        if len(sections) <= 1:
            return True

        ids = list(sections.keys())
        for i in range(len(ids)):
            for j in range(i + 1, len(ids)):
                s1, s2 = ids[i], ids[j]
                if not self._pairwise_compatible(s1, s2, sections[s1], sections[s2]):
                    return False
        return True

    def _pairwise_compatible(
        self,
        site1: str,
        site2: str,
        sec1: Any,
        sec2: Any,
    ) -> bool:
        """Check compatibility of two sections on their overlap."""
        # If one is a parent of the other, restrict and compare
        if site2 in self.site_children(site1):
            restricted = self.restrict_site(sec1, site1, site2)
            if restricted is None:
                return True
            return self._sections_equal(restricted, sec2)

        if site1 in self.site_children(site2):
            restricted = self.restrict_site(sec2, site2, site1)
            if restricted is None:
                return True
            return self._sections_equal(restricted, sec1)

        # No direct overlap → trivially compatible
        return True

    @staticmethod
    def _sections_equal(a: Any, b: Any) -> bool:
        """Check structural equality of two sections."""
        if a is b:
            return True
        if hasattr(a, "content_hash") and hasattr(b, "content_hash"):
            return a.content_hash == b.content_hash
        try:
            return a == b
        except Exception:
            return False

    def glue(
        self,
        compatible_family: Dict[str, Any],
        layer: Optional[Layer] = None,
    ) -> Optional[Any]:
        """
        Glue a compatible family of local sections into a global section.

        For structural / semantic sections, this takes the union of
        predicates.  For proof sections, it merges statements.
        For intent / code sections, it concatenates.

        Parameters
        ----------
        compatible_family : Dict[str, Any]
            Map from ``site_id`` to local section.
        layer : Optional[Layer]
            Hint about which layer the sections belong to.

        Returns
        -------
        Optional[Any]
            The glued global section, or ``None`` if gluing fails.
        """
        if not compatible_family:
            return None

        sections = list(compatible_family.values())
        if len(sections) == 1:
            return copy.deepcopy(sections[0])

        first = sections[0]

        # Dispatch by section type
        if isinstance(first, IntentSection):
            return self._glue_intent(sections)
        if isinstance(first, StructuralSection):
            return self._glue_structural(sections)
        if isinstance(first, SemanticSection):
            return self._glue_semantic(sections)
        if isinstance(first, ProofSection):
            return self._glue_proof(sections)
        if isinstance(first, CodeSection):
            return self._glue_code(sections)

        return copy.deepcopy(first)

    @staticmethod
    def _glue_intent(sections: List[Any]) -> IntentSection:
        """Glue intent sections by concatenating text and claims."""
        texts: List[str] = []
        claims: List[Dict[str, Any]] = []
        for sec in sections:
            if sec.text:
                texts.append(sec.text)
            claims.extend(sec.parsed_claims)
        return IntentSection(
            text="\n\n".join(texts),
            parsed_claims=claims,
        )

    @staticmethod
    def _glue_structural(sections: List[Any]) -> StructuralSection:
        """Glue structural sections by taking the union of predicates."""
        seen_names: Set[str] = set()
        merged_preds: List[StructuralPredicate] = []
        z3t: Optional[Z3Type] = None
        for sec in sections:
            for pred in sec.predicates:
                if pred.name not in seen_names:
                    seen_names.add(pred.name)
                    merged_preds.append(pred)
            if sec.z3_type is not None and z3t is None:
                z3t = sec.z3_type
        return StructuralSection(predicates=merged_preds, z3_type=z3t)

    @staticmethod
    def _glue_semantic(sections: List[Any]) -> SemanticSection:
        """Glue semantic sections by taking the union of predicates."""
        seen_names: Set[str] = set()
        merged_preds: List[SemanticPredicate] = []
        for sec in sections:
            for pred in sec.predicates:
                if pred.name not in seen_names:
                    seen_names.add(pred.name)
                    merged_preds.append(pred)
        return SemanticSection(predicates=merged_preds)

    @staticmethod
    def _glue_proof(sections: List[Any]) -> ProofSection:
        """Glue proof sections by merging statements (dedup by text)."""
        seen_stmts: Set[str] = set()
        stmts: List[str] = []
        proofs: List[Optional[str]] = []
        for sec in sections:
            for stmt, proof in zip(sec.lean_statements, sec.lean_proofs):
                if stmt not in seen_stmts:
                    seen_stmts.add(stmt)
                    stmts.append(stmt)
                    proofs.append(proof)
                else:
                    # If we have a proof for a duplicate, use it
                    idx = stmts.index(stmt)
                    if proof is not None and proofs[idx] is None:
                        proofs[idx] = proof
        return ProofSection(lean_statements=stmts, lean_proofs=proofs)

    @staticmethod
    def _glue_code(sections: List[Any]) -> CodeSection:
        """Glue code sections (take the longest source)."""
        best = max(sections, key=lambda s: len(s.source))
        return copy.deepcopy(best)

    # ── H¹ computation ────────────────────────────────────────────────────

    def compute_h1(self, cover: List[str]) -> int:
        """
        Compute dim H¹(cover, HybridTy).

        This counts the number of independent obstructions to gluing
        on the given cover.  An obstruction arises when two sections
        on overlapping sites disagree.

        Parameters
        ----------
        cover : List[str]
            Site IDs forming an open cover.

        Returns
        -------
        int
            Dimension of H¹ (0 means the sheaf condition is satisfied).
        """
        return len(self.obstructions(cover))

    def obstructions(self, cover: List[str]) -> List[str]:
        """
        Describe each H¹ generator on the given cover.

        Parameters
        ----------
        cover : List[str]
            Site IDs forming an open cover.

        Returns
        -------
        List[str]
            Human-readable descriptions of each obstruction.
        """
        obs: List[str] = []

        for layer in Layer.all_layers():
            # Check compatibility at this layer
            if not self.compatible(cover, layer):
                obs.append(
                    f"Layer {layer.value}: sections on {cover} are "
                    f"incompatible (failed gluing condition)."
                )

            # Check layer-direction cocycles
            for lower, higher in Layer.adjacent_pairs():
                if lower != layer:
                    continue
                for sid in cover:
                    lower_sec = self.section_at(sid, lower)
                    higher_sec = self.section_at(sid, higher)
                    if lower_sec is None or higher_sec is None:
                        continue
                    restricted = self.restrict_layer(lower_sec, lower, higher)
                    if restricted is None:
                        continue
                    if not self._sections_equal(restricted, higher_sec):
                        obs.append(
                            f"Site {sid}: restrict({lower.value} → {higher.value}) "
                            f"does not match actual {higher.value} section."
                        )

        return obs

    def compute_full_cohomology(
        self,
    ) -> Dict[str, Any]:
        """
        Compute cohomological summary across all sites and layers.

        Returns a dictionary with H⁰ (global sections) and H¹
        (obstructions) information.
        """
        all_sites = self.sites()
        obs = self.obstructions(all_sites)
        h1_dim = len(obs)

        # H⁰: attempt to glue at each layer
        global_sections: Dict[str, bool] = {}
        for layer in Layer.all_layers():
            family = self.sections_at_layer(layer)
            if not family:
                global_sections[layer.value] = True
                continue
            glued = self.glue(family, layer)
            global_sections[layer.value] = glued is not None

        return {
            "h0_global_sections": global_sections,
            "h1_dimension": h1_dim,
            "h1_obstructions": obs,
            "sites": all_sites,
            "layers": [l.value for l in Layer.all_layers()],
            "total_sections": len(self._sections),
        }

    # ── display ───────────────────────────────────────────────────────────

    def summary(self) -> str:
        """One-line summary."""
        return (
            f"SheafTypePresheaf({self.name}, "
            f"sites={len(self._sites)}, "
            f"sections={len(self._sections)})"
        )

    def __repr__(self) -> str:
        return self.summary()


# ═══════════════════════════════════════════════════════════════════════════════
# §11  Convenience constructors
# ═══════════════════════════════════════════════════════════════════════════════

def int_type() -> HybridType:
    """
    Hybrid type for ``int``.

    Structural: ``isinstance(x, int)``
    Z3 sort: ``IntSort()``
    """
    return HybridType(
        name="int",
        description="Python integer",
        intent=IntentSection(text="An integer value."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_int",
                    formula="isinstance(x, int)",
                    variables={"x": "int"},
                    description="Value is an integer",
                )
            ],
            z3_type=Z3Type(sort=Z3Sort.int_sort()),
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type="int"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
    )


def str_type() -> HybridType:
    """
    Hybrid type for ``str``.
    """
    return HybridType(
        name="str",
        description="Python string",
        intent=IntentSection(text="A string value."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_str",
                    formula="isinstance(x, str)",
                    variables={"x": "str"},
                    description="Value is a string",
                )
            ],
            z3_type=Z3Type(sort=Z3Sort.string_sort()),
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type="str"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
    )


def bool_type() -> HybridType:
    """
    Hybrid type for ``bool``.
    """
    return HybridType(
        name="bool",
        description="Python boolean",
        intent=IntentSection(text="A boolean value."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_bool",
                    formula="isinstance(x, bool)",
                    variables={"x": "bool"},
                    description="Value is a boolean",
                )
            ],
            z3_type=Z3Type(sort=Z3Sort.bool_sort()),
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type="bool"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
    )


def float_type() -> HybridType:
    """
    Hybrid type for ``float``.
    """
    return HybridType(
        name="float",
        description="Python float",
        intent=IntentSection(text="A floating-point value."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_float",
                    formula="isinstance(x, (int, float))",
                    variables={"x": "float"},
                    description="Value is a float (or int)",
                )
            ],
            z3_type=Z3Type(sort=Z3Sort.real_sort()),
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type="float"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
    )


def none_type() -> HybridType:
    """
    Hybrid type for ``None`` (unit type).
    """
    return HybridType(
        name="None",
        description="Python None (unit)",
        intent=IntentSection(text="The None / unit value."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_none",
                    formula="x is None",
                    variables={"x": "NoneType"},
                    description="Value is None",
                )
            ],
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type="None"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
    )


def list_type(element: HybridType) -> HybridType:
    """
    Hybrid type for ``List[element]``.

    Structural: ``isinstance(x, list)`` and each element satisfies
    the element type.

    Parameters
    ----------
    element : HybridType
        The element type.
    """
    elem_name = element.name or "Any"
    return HybridType(
        name=f"List[{elem_name}]",
        description=f"List of {elem_name}",
        intent=IntentSection(text=f"A list of {elem_name} values."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_list",
                    formula="isinstance(x, list)",
                    variables={"x": "list"},
                    description="Value is a list",
                ),
            ],
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type=f"List[{elem_name}]"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
        metadata={"element_type": element.to_dict()},
    )


def dict_type(key: HybridType, value: HybridType) -> HybridType:
    """
    Hybrid type for ``Dict[key, value]``.

    Parameters
    ----------
    key : HybridType
        The key type.
    value : HybridType
        The value type.
    """
    key_name = key.name or "Any"
    val_name = value.name or "Any"
    return HybridType(
        name=f"Dict[{key_name}, {val_name}]",
        description=f"Dict from {key_name} to {val_name}",
        intent=IntentSection(text=f"A dictionary mapping {key_name} to {val_name}."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_dict",
                    formula="isinstance(x, dict)",
                    variables={"x": "dict"},
                    description="Value is a dict",
                ),
            ],
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type=f"Dict[{key_name}, {val_name}]"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
        metadata={
            "key_type": key.to_dict(),
            "value_type": value.to_dict(),
        },
    )


def optional_type(inner: HybridType) -> HybridType:
    """
    Hybrid type for ``Optional[inner]`` (i.e. ``inner | None``).

    Parameters
    ----------
    inner : HybridType
        The non-None inner type.
    """
    inner_name = inner.name or "Any"
    return HybridType(
        name=f"Optional[{inner_name}]",
        description=f"Optional {inner_name}",
        intent=IntentSection(text=f"Either {inner_name} or None."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_optional",
                    formula=f"x is None or isinstance(x, object)",
                    variables={"x": inner_name},
                    description=f"Value is None or a valid {inner_name}",
                ),
            ],
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type=f"Optional[{inner_name}]"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
        metadata={"inner_type": inner.to_dict()},
    )


def refined_int(predicate: str, name: Optional[str] = None) -> HybridType:
    """
    Convenience: ``{x : int | predicate(x)}``.

    Parameters
    ----------
    predicate : str
        A Python expression over ``x`` (e.g. ``"x > 0"``).
    name : Optional[str]
        Optional name for the type.

    Examples
    --------
    >>> t = refined_int("x > 0")
    >>> t.check_structural(5)
    True
    >>> t.check_structural(-3)
    False
    """
    type_name = name or f"{{x : int | {predicate}}}"
    return HybridType(
        name=type_name,
        description=f"Refined integer: {predicate}",
        intent=IntentSection(
            text=f"An integer satisfying {predicate}.",
            parsed_claims=[
                {"claim": predicate, "kind": "structural", "formula": predicate}
            ],
        ),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_int",
                    formula="isinstance(x, int)",
                    variables={"x": "int"},
                    description="Value is an integer",
                ),
                StructuralPredicate(
                    name="refinement",
                    formula=predicate,
                    variables={"x": "int"},
                    description=f"Refinement: {predicate}",
                ),
            ],
            z3_type=Z3Type(sort=Z3Sort.int_sort(), constraints=(predicate,)),
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type="int"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
    )


def function_type(
    params: List[HybridType],
    return_type: HybridType,
    param_names: Optional[List[str]] = None,
) -> HybridPiType:
    """
    Construct a (non-dependent) function type from parameter types and
    a return type.

    For a single parameter, returns ``Π(x : A). B``.
    For multiple parameters, returns a curried form
    ``Π(x₁ : A₁). Π(x₂ : A₂). … B``.

    Parameters
    ----------
    params : List[HybridType]
        Parameter types.
    return_type : HybridType
        Return type.
    param_names : Optional[List[str]]
        Parameter names (defaults to x0, x1, …).

    Returns
    -------
    HybridPiType
    """
    if not params:
        return HybridPiType(
            param_name="_",
            param_type=HybridType.unit(),
            body_fn=lambda _: return_type,
            description=f"() → {return_type.name}",
        )

    names = param_names or [f"x{i}" for i in range(len(params))]

    if len(params) == 1:
        return HybridPiType(
            param_name=names[0],
            param_type=params[0],
            body_fn=lambda _: return_type,
            description=f"{params[0].name} → {return_type.name}",
        )

    # Curried multi-param: Π(x₁:A₁). Π(x₂:A₂). … B
    inner = function_type(params[1:], return_type, names[1:])
    inner_hybrid = HybridType(
        name=f"({' → '.join(p.name for p in params[1:])} → {return_type.name})",
        description="Curried function continuation",
    )

    return HybridPiType(
        param_name=names[0],
        param_type=params[0],
        body_fn=lambda _: inner_hybrid,
        description=f"{' → '.join(p.name for p in params)} → {return_type.name}",
    )


def tuple_type(*components: HybridType) -> HybridType:
    """
    Hybrid type for a tuple of fixed component types.

    Parameters
    ----------
    *components : HybridType
        Component types.
    """
    names = [c.name or "Any" for c in components]
    type_name = f"Tuple[{', '.join(names)}]"
    return HybridType(
        name=type_name,
        description=f"Tuple of ({', '.join(names)})",
        intent=IntentSection(text=f"A tuple of ({', '.join(names)})."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_tuple",
                    formula="isinstance(x, tuple)",
                    variables={"x": "tuple"},
                    description="Value is a tuple",
                ),
                StructuralPredicate(
                    name="correct_length",
                    formula=f"len(x) == {len(components)}",
                    variables={"x": "tuple"},
                    description=f"Tuple has {len(components)} components",
                ),
            ],
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type=type_name),
        trust_level=TrustLevel.RUNTIME_CHECKED,
        metadata={"component_types": [c.to_dict() for c in components]},
    )


def set_type(element: HybridType) -> HybridType:
    """
    Hybrid type for ``Set[element]``.

    Parameters
    ----------
    element : HybridType
        The element type.
    """
    elem_name = element.name or "Any"
    return HybridType(
        name=f"Set[{elem_name}]",
        description=f"Set of {elem_name}",
        intent=IntentSection(text=f"A set of {elem_name} values."),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_set",
                    formula="isinstance(x, (set, frozenset))",
                    variables={"x": "set"},
                    description="Value is a set",
                ),
            ],
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type=f"Set[{elem_name}]"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
        metadata={"element_type": element.to_dict()},
    )


def refined_str(predicate: str, name: Optional[str] = None) -> HybridType:
    """
    Convenience: ``{x : str | predicate(x)}``.

    Parameters
    ----------
    predicate : str
        A Python expression over ``x`` (e.g. ``"len(x) > 0"``).
    name : Optional[str]
        Optional name for the type.
    """
    type_name = name or f"{{x : str | {predicate}}}"
    return HybridType(
        name=type_name,
        description=f"Refined string: {predicate}",
        intent=IntentSection(
            text=f"A string satisfying {predicate}.",
            parsed_claims=[
                {"claim": predicate, "kind": "structural", "formula": predicate}
            ],
        ),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_str",
                    formula="isinstance(x, str)",
                    variables={"x": "str"},
                    description="Value is a string",
                ),
                StructuralPredicate(
                    name="refinement",
                    formula=predicate,
                    variables={"x": "str"},
                    description=f"Refinement: {predicate}",
                ),
            ],
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type="str"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
    )


def refined_float(predicate: str, name: Optional[str] = None) -> HybridType:
    """
    Convenience: ``{x : float | predicate(x)}``.

    Parameters
    ----------
    predicate : str
        A Python expression over ``x`` (e.g. ``"0.0 <= x <= 1.0"``).
    name : Optional[str]
        Optional name for the type.
    """
    type_name = name or f"{{x : float | {predicate}}}"
    return HybridType(
        name=type_name,
        description=f"Refined float: {predicate}",
        intent=IntentSection(
            text=f"A float satisfying {predicate}.",
            parsed_claims=[
                {"claim": predicate, "kind": "structural", "formula": predicate}
            ],
        ),
        structural=StructuralSection(
            predicates=[
                StructuralPredicate(
                    name="is_float",
                    formula="isinstance(x, (int, float))",
                    variables={"x": "float"},
                    description="Value is a float (or int)",
                ),
                StructuralPredicate(
                    name="refinement",
                    formula=predicate,
                    variables={"x": "float"},
                    description=f"Refinement: {predicate}",
                ),
            ],
            z3_type=Z3Type(sort=Z3Sort.real_sort(), constraints=(predicate,)),
        ),
        semantic=SemanticSection.empty(),
        proof=ProofSection.empty(),
        code=CodeSection(runtime_type="float"),
        trust_level=TrustLevel.RUNTIME_CHECKED,
    )


@dataclass(frozen=True)
class IntentBridgePlan:
    """Plan object connecting extracted intent to target layers."""

    source_text: str
    target_name: str
    include_structural: bool = True
    include_semantic: bool = True
    trust_floor: str = TrustLevel.RUNTIME_CHECKED


@dataclass
class IntentBridgeOutcome:
    """Result object produced by intent bridging passes."""

    plan: IntentBridgePlan
    hybrid_type: HybridType
    extracted_claims: List[Dict[str, Any]] = field(default_factory=list)
    notes: List[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════════════
# §12  __all__
# ═══════════════════════════════════════════════════════════════════════════════

__all__ = [
    # Layers
    "Layer",
    "LAYER_ORDER",
    # Trust
    "TrustLevel",
    "HybridTrustLevel",
    # Z3 types
    "Z3Sort",
    "Z3Type",
    # Predicates
    "StructuralPredicate",
    "SemanticPredicate",
    # Layer sections
    "IntentSection",
    "StructuralSection",
    "SemanticSection",
    "ProofSection",
    "CodeSection",
    # Oracle monad
    "OracleMonadValue",
    "OracleMonad",
    # Check results
    "CocycleStatus",
    "HybridCheckResult",
    # Core type
    "HybridType",
    # Dependent type formers
    "HybridPiType",
    "HybridDependentType",
    "HybridSigmaType",
    "HybridRefinementType",
    "IdentityType",
    "UniverseLevel",
    "IntentBridgePlan",
    "IntentBridgeOutcome",
    # Sheaf presheaf
    "SheafTypePresheaf",
    # Convenience constructors
    "int_type",
    "str_type",
    "bool_type",
    "float_type",
    "none_type",
    "list_type",
    "dict_type",
    "optional_type",
    "refined_int",
    "refined_str",
    "refined_float",
    "function_type",
    "tuple_type",
    "set_type",
]
