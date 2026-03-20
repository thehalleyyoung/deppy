"""
Compile structural NL specifications into Z3 constraints.

Each ``Z3Constraint`` carries:
    * a human-readable formula string,
    * executable Z3-solver Python code,
    * and a best-effort Lean 4 translation.

``Z3SpecCompiler`` converts parsed claims into constraints.
``Z3Solver`` wraps Z3 to check / find counterexamples.
``LeanFromZ3`` translates constraints into Lean propositions.
"""
from __future__ import annotations

import re
import time
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple


# ===================================================================
# Z3Constraint  (~50 lines)
# ===================================================================


# --- Integration with existing deppy codebase ---
try:
    from deppy.solver import Z3Backend, FragmentDispatcher, SolverObligation, SolverResult
    from deppy.solver.z3_encoder import Z3Encoder as _CoreZ3Encoder, encode_predicate
    from deppy.types.refinement import RefinementType as _CoreRefinementType
    _HAS_DEPPY_CORE = True
except ImportError:
    _HAS_DEPPY_CORE = False

@dataclass
class Z3Constraint:
    """
    A single Z3 constraint compiled from a structural NL claim.
    """

    name: str
    formula_str: str
    variables: Dict[str, str] = field(default_factory=dict)
    z3_code: str = ""
    lean_equivalent: str = ""

    # -- helpers --

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "formula_str": self.formula_str,
            "variables": self.variables,
            "z3_code": self.z3_code,
            "lean_equivalent": self.lean_equivalent,
        }

    def pretty(self) -> str:
        return f"[Z3] {self.name}: {self.formula_str}"

    def has_lean(self) -> bool:
        return bool(self.lean_equivalent.strip())


# ===================================================================
# Z3Result
# ===================================================================

@dataclass
class Z3Result:
    """Outcome of a Z3 solver invocation."""

    satisfiable: bool
    model: Optional[Dict[str, Any]] = None
    certificate: Optional[str] = None
    time_ms: float = 0.0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "satisfiable": self.satisfiable,
            "model": self.model,
            "certificate": self.certificate,
            "time_ms": self.time_ms,
        }


# ===================================================================
# Z3SpecCompiler  (~600 lines)
# ===================================================================

class Z3SpecCompiler:
    """
    Convert a list of structural claims (dicts with at least ``text``
    and ``formula`` keys) into ``Z3Constraint`` objects with runnable
    Z3 Python code and Lean equivalents.
    """

    # ---- type-to-Z3-sort mapping ----
    _TYPE_MAP: Dict[str, str] = {
        "int": "IntSort()",
        "float": "RealSort()",
        "real": "RealSort()",
        "bool": "BoolSort()",
        "str": "StringSort()",
        "string": "StringSort()",
        "list": "ArraySort(IntSort(), IntSort())",
        "set": "SetSort(IntSort())",
        "dict": "ArraySort(IntSort(), IntSort())",
    }

    # ---- Lean type mapping ----
    _LEAN_TYPE_MAP: Dict[str, str] = {
        "int": "Int",
        "float": "Float",
        "real": "Real",
        "bool": "Bool",
        "str": "String",
        "string": "String",
        "list": "List Int",
        "set": "Finset Int",
    }

    # ================================================================ public

    def compile(self, claims: List[Dict[str, Any]]) -> List[Z3Constraint]:
        """
        Main entry point.  Each dict should contain at least:
            ``text``    — the original NL text
            ``formula`` — a formula string (from the NL parser / encoder)
        Optional keys: ``variables``, ``name``.
        """
        constraints: List[Z3Constraint] = []
        for idx, claim in enumerate(claims):
            text = claim.get("text", "")
            formula = claim.get("formula", claim.get("structural_formula", ""))
            variables = claim.get("variables", {})
            name = claim.get("name", f"c{idx}")

            constraint = self._compile_one(name, text, formula, variables)
            constraints.append(constraint)
        return constraints

    # ---- specialised compile methods ----

    def compile_bound(self, text: str, var: str, bound: Any) -> Z3Constraint:
        """``var >= bound`` or ``var <= bound`` etc."""
        op = self._detect_op(text)
        formula = f"{var} {op} {bound}"
        z3 = self._z3_declare(var, "int") + f"\ns.add({var} {op} {bound})"
        lean = f"theorem bound_{var} : {var} {self._lean_op(op)} {bound} := by omega"
        return Z3Constraint(
            name=f"bound_{var}",
            formula_str=formula,
            variables={var: "int"},
            z3_code=z3,
            lean_equivalent=lean,
        )

    def compile_sorted(self, array_var: str) -> Z3Constraint:
        formula = f"ForAll i, 0 <= i < len({array_var})-1 => {array_var}[i] <= {array_var}[i+1]"
        z3 = self._z3_array_decl(array_var) + "\n" + "\n".join([
            f"n = Int('n_{array_var}')",
            f"i = Int('i_{array_var}')",
            f"s.add(n >= 0)",
            f"s.add(ForAll([i], Implies(And(i >= 0, i < n - 1), "
            f"Select({array_var}, i) <= Select({array_var}, i + 1))))",
        ])
        lean = (
            f"theorem sorted_{array_var} (a : List Int) :\n"
            f"  ∀ i, i + 1 < a.length → a.get ⟨i, by omega⟩ ≤ a.get ⟨i+1, by omega⟩ := by\n"
            f"  intro i hi; omega"
        )
        return Z3Constraint(
            name=f"sorted_{array_var}",
            formula_str=formula,
            variables={array_var: "list"},
            z3_code=z3,
            lean_equivalent=lean,
        )

    def compile_membership(self, element: str, collection: str) -> Z3Constraint:
        formula = f"IsMember({element}, {collection})"
        z3 = (
            self._z3_declare(element, "int")
            + "\n"
            + self._z3_set_decl(collection)
            + f"\ns.add(IsMember({element}, {collection}))"
        )
        lean = f"theorem mem_{element}_{collection} : {element} ∈ {collection} := by decide"
        return Z3Constraint(
            name=f"member_{element}_in_{collection}",
            formula_str=formula,
            variables={element: "int", collection: "set"},
            z3_code=z3,
            lean_equivalent=lean,
        )

    def compile_cardinality(self, collection: str, op: str, n: int) -> Z3Constraint:
        formula = f"|{collection}| {op} {n}"
        z3 = (
            self._z3_set_decl(collection)
            + f"\ncard = Int('card_{collection}')"
            + f"\ns.add(card_{collection} {op} {n})"
        )
        lean = f"theorem card_{collection} : {collection}.card {self._lean_op(op)} {n} := by omega"
        return Z3Constraint(
            name=f"card_{collection}_{op}_{n}",
            formula_str=formula,
            variables={collection: "set"},
            z3_code=z3,
            lean_equivalent=lean,
        )

    def compile_uniqueness(self, collection: str) -> Z3Constraint:
        formula = f"Distinct(elements_of({collection}))"
        z3 = (
            self._z3_array_decl(collection)
            + "\n"
            + f"n = Int('n_{collection}')\n"
            + f"i, j = Ints('i_{collection} j_{collection}')\n"
            + f"s.add(ForAll([i, j], Implies(And(i >= 0, j >= 0, i < n, j < n, i != j), "
            + f"Select({collection}, i) != Select({collection}, j))))"
        )
        lean = (
            f"theorem unique_{collection} (a : List Int) :\n"
            f"  a.Nodup := by\n"
            f"  decide"
        )
        return Z3Constraint(
            name=f"unique_{collection}",
            formula_str=formula,
            variables={collection: "list"},
            z3_code=z3,
            lean_equivalent=lean,
        )

    def compile_equality(self, lhs: str, rhs: str) -> Z3Constraint:
        formula = f"{lhs} == {rhs}"
        z3 = (
            self._z3_declare(lhs, "int")
            + "\n"
            + self._z3_declare(rhs, "int")
            + f"\ns.add({lhs} == {rhs})"
        )
        lean = f"theorem eq_{lhs}_{rhs} : {lhs} = {rhs} := by omega"
        return Z3Constraint(
            name=f"eq_{lhs}_{rhs}",
            formula_str=formula,
            variables={lhs: "int", rhs: "int"},
            z3_code=z3,
            lean_equivalent=lean,
        )

    def compile_implication(self, antecedent: str, consequent: str) -> Z3Constraint:
        formula = f"Implies({antecedent}, {consequent})"
        z3 = f"# antecedent and consequent must be pre-compiled\ns.add(Implies({antecedent}, {consequent}))"
        lean = (
            f"theorem impl : {antecedent} → {consequent} := by\n"
            f"  intro h; exact h"
        )
        return Z3Constraint(
            name=f"impl_{_sanitize(antecedent)}_{_sanitize(consequent)}",
            formula_str=formula,
            variables={},
            z3_code=z3,
            lean_equivalent=lean,
        )

    def compile_type_constraint(self, var: str, type_name: str) -> Z3Constraint:
        formula = f"isinstance({var}, {type_name})"
        z3_sort = self._TYPE_MAP.get(type_name.lower(), "IntSort()")
        z3 = f"{var} = Const('{var}', {z3_sort})\n# type constraint embedded in sort"
        lean_ty = self._LEAN_TYPE_MAP.get(type_name.lower(), type_name)
        lean = f"-- {var} : {lean_ty}  (type-level, no runtime assertion needed)"
        return Z3Constraint(
            name=f"type_{var}_{type_name}",
            formula_str=formula,
            variables={var: type_name},
            z3_code=z3,
            lean_equivalent=lean,
        )

    # ---- batch convenience ----

    def compile_all_bounds(
        self,
        bounds: List[Tuple[str, str, Any]],
    ) -> List[Z3Constraint]:
        """Compile a list of ``(text, var, bound)`` tuples."""
        return [self.compile_bound(t, v, b) for t, v, b in bounds]

    # ========================= internals ==================================

    def _compile_one(
        self,
        name: str,
        text: str,
        formula: str,
        variables: Dict[str, str],
    ) -> Z3Constraint:
        """Dispatch to the right specialised compiler."""
        lower = text.lower()

        # Sorted
        if "sorted" in lower or "ascending" in lower or "descending" in lower:
            var = self._first_var(variables, fallback="arr")
            return self.compile_sorted(var)

        # Uniqueness
        if "unique" in lower or "distinct" in lower or "no duplicates" in lower:
            var = self._first_var(variables, fallback="arr")
            return self.compile_uniqueness(var)

        # Membership
        m = re.search(r"\b(\w+)\s+(?:in|∈|member\s+of|belongs?\s+to)\s+(\w+)\b", lower)
        if m:
            return self.compile_membership(m.group(1), m.group(2))
        if "contains" in lower:
            m2 = re.search(r"\b(\w+)\s+contains?\s+(\w+)\b", lower)
            if m2:
                return self.compile_membership(m2.group(2), m2.group(1))

        # Type check
        m = re.search(r"\b(?:type\s+is|instance\s+of|isinstance)\s+(\w+)\b", lower)
        if m:
            var = self._first_var(variables, fallback="x")
            return self.compile_type_constraint(var, m.group(1))

        # Equality
        m = re.search(r"\b(\w+)\s+(?:==|equals?|equal\s+to)\s+(\w+)\b", lower)
        if m:
            return self.compile_equality(m.group(1), m.group(2))

        # Cardinality
        m = re.search(r"\b(?:length|size|count|cardinality)\s*(?:of\s+)?(\w+)\s*(>=?|<=?|==|!=)\s*(\d+)\b", lower)
        if m:
            return self.compile_cardinality(m.group(1), m.group(2), int(m.group(3)))

        # Implication
        if "implies" in lower or "if " in lower:
            m = re.search(r"\bif\s+(.+?)\s+then\s+(.+)", lower)
            if m:
                return self.compile_implication(m.group(1).strip(), m.group(2).strip())

        # Bound (fallback)
        m = re.search(r"\b(\w+)\s*(>=?|<=?|==|!=)\s*(-?\d+(?:\.\d+)?)\b", formula or text)
        if m:
            return self.compile_bound(text, m.group(1), m.group(3))

        # Generic: just wrap the formula
        z3 = self._generic_z3(formula, variables)
        lean = self._generic_lean(formula)
        return Z3Constraint(
            name=name,
            formula_str=formula or text,
            variables=variables,
            z3_code=z3,
            lean_equivalent=lean,
        )

    # ---- Z3 code-gen helpers ----

    def _z3_declare(self, var: str, typ: str = "int") -> str:
        sort = self._TYPE_MAP.get(typ.lower(), "IntSort()")
        return f"{var} = Const('{var}', {sort})"

    def _z3_array_decl(self, var: str) -> str:
        return f"{var} = Array('{var}', IntSort(), IntSort())"

    def _z3_set_decl(self, var: str) -> str:
        return f"{var} = Const('{var}', SetSort(IntSort()))"

    def _generic_z3(self, formula: str, variables: Dict[str, str]) -> str:
        lines: List[str] = []
        lines.append("from z3 import *")
        lines.append("s = Solver()")
        for vname, vtype in variables.items():
            lines.append(self._z3_declare(vname, vtype))
        if formula:
            lines.append(f"s.add({formula})")
        lines.append("result = s.check()")
        return "\n".join(lines)

    def _generic_lean(self, formula: str) -> str:
        if not formula:
            return "-- (no formula)"
        safe = formula.replace(">=", "≥").replace("<=", "≤").replace("!=", "≠").replace("==", "=")
        return f"-- Lean stub: {safe}"

    # ---- misc helpers ----

    @staticmethod
    def _detect_op(text: str) -> str:
        lower = text.lower()
        if "at least" in lower or ">=" in text:
            return ">="
        if "at most" in lower or "<=" in text:
            return "<="
        if "exactly" in lower or "==" in text:
            return "=="
        if "greater" in lower or ">" in text:
            return ">"
        if "less" in lower or "<" in text:
            return "<"
        return ">="

    @staticmethod
    def _lean_op(op: str) -> str:
        return {
            ">=": "≥", "<=": "≤", "==": "=",
            "!=": "≠", ">": ">", "<": "<",
        }.get(op, op)

    @staticmethod
    def _first_var(variables: Dict[str, str], fallback: str = "x") -> str:
        if variables:
            return next(iter(variables))
        return fallback


# ===================================================================
# Z3Solver  (~300 lines)
# ===================================================================

class Z3Solver:
    """
    Thin wrapper around Z3's Python API that operates on
    ``Z3Constraint`` objects.

    When z3-solver is not installed the solver degrades gracefully
    to a "cannot check" state rather than crashing.
    """

    def __init__(self, timeout_ms: int = 5000) -> None:
        self.timeout_ms = timeout_ms
        self._z3: Any = None
        self._available: bool = False
        self._try_import_z3()

    # ---- lazy import ----

    def _try_import_z3(self) -> None:
        try:
            import z3 as _z3  # type: ignore[import-untyped]
            self._z3 = _z3
            self._available = True
        except ImportError:
            self._z3 = None
            self._available = False

    @property
    def available(self) -> bool:
        return self._available

    # ========================= public API =================================

    def check(
        self,
        constraints: List[Z3Constraint],
        model: Optional[Dict[str, Any]] = None,
    ) -> Z3Result:
        """
        Check whether *constraints* are simultaneously satisfiable.

        If *model* is supplied, the variable assignments in it are
        added as extra equalities (useful for checking a concrete
        execution trace against the spec).
        """
        if not self._available:
            return self._unavailable_result()

        z3 = self._z3
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)

        ns: Dict[str, Any] = {"z3": z3}
        self._populate_namespace(ns, z3)

        t0 = time.monotonic()

        for c in constraints:
            try:
                self._add_constraint(solver, c, ns, z3)
            except Exception:
                pass

        if model:
            self._add_model_equalities(solver, model, ns, z3)

        result_status = solver.check()
        elapsed = (time.monotonic() - t0) * 1000.0

        if result_status == z3.sat:
            z3_model = solver.model()
            extracted = self._extract_model(z3_model)
            return Z3Result(
                satisfiable=True,
                model=extracted,
                certificate=str(z3_model),
                time_ms=round(elapsed, 2),
            )
        elif result_status == z3.unsat:
            core = self._unsat_core(solver)
            return Z3Result(
                satisfiable=False,
                model=None,
                certificate=core,
                time_ms=round(elapsed, 2),
            )
        else:
            return Z3Result(
                satisfiable=False,
                model=None,
                certificate="unknown / timeout",
                time_ms=round(elapsed, 2),
            )

    def check_satisfiable(self, constraints: List[Z3Constraint]) -> bool:
        result = self.check(constraints)
        return result.satisfiable

    def find_counterexample(
        self,
        constraints: List[Z3Constraint],
    ) -> Optional[Dict[str, Any]]:
        """
        Negate the conjunction and look for a satisfying assignment
        (which is a counterexample to the original spec).
        """
        if not self._available:
            return None

        z3 = self._z3
        solver = z3.Solver()
        solver.set("timeout", self.timeout_ms)

        ns: Dict[str, Any] = {"z3": z3}
        self._populate_namespace(ns, z3)

        parts: List[Any] = []
        for c in constraints:
            expr = self._parse_expr(c.z3_code, ns, z3)
            if expr is not None:
                parts.append(expr)

        if not parts:
            return None

        conjunction = z3.And(*parts) if len(parts) > 1 else parts[0]
        solver.add(z3.Not(conjunction))

        if solver.check() == z3.sat:
            return self._extract_model(solver.model())
        return None

    # ---- batch helpers ----

    def check_each(
        self,
        constraints: List[Z3Constraint],
        model: Optional[Dict[str, Any]] = None,
    ) -> List[Z3Result]:
        """Check each constraint independently."""
        return [self.check([c], model) for c in constraints]

    def check_incremental(
        self,
        constraints: List[Z3Constraint],
    ) -> List[Z3Result]:
        """Add constraints one at a time, reporting status at each step."""
        results: List[Z3Result] = []
        for i in range(1, len(constraints) + 1):
            results.append(self.check(constraints[:i]))
        return results

    # ========================= internals ==================================

    def _unavailable_result(self) -> Z3Result:
        return Z3Result(
            satisfiable=False,
            model=None,
            certificate="z3 not installed",
            time_ms=0.0,
        )

    @staticmethod
    def _populate_namespace(ns: Dict[str, Any], z3: Any) -> None:
        """Export commonly used Z3 symbols into a namespace dict."""
        names = [
            "Int", "Real", "Bool", "String",
            "IntSort", "RealSort", "BoolSort", "StringSort",
            "Array", "Select", "Store", "Const",
            "SetSort", "EmptySet", "IsMember", "SetAdd", "SetUnion", "SetIntersect",
            "ForAll", "Exists", "Implies", "And", "Or", "Not", "If",
            "Ints", "Reals", "Bools",
            "Distinct",
            "sat", "unsat", "unknown",
            "Solver",
        ]
        for n in names:
            val = getattr(z3, n, None)
            if val is not None:
                ns[n] = val

    def _add_constraint(
        self,
        solver: Any,
        constraint: Z3Constraint,
        ns: Dict[str, Any],
        z3: Any,
    ) -> None:
        """Try to eval the constraint's Z3 code in *ns* and add to *solver*."""
        code = constraint.z3_code
        if not code.strip():
            return

        local_ns: Dict[str, Any] = dict(ns)
        local_ns["s"] = solver

        if "s.add(" in code:
            exec(code, local_ns)  # noqa: S102
        else:
            expr = self._parse_expr(code, ns, z3)
            if expr is not None:
                solver.add(expr)

    def _parse_expr(
        self,
        code: str,
        ns: Dict[str, Any],
        z3: Any,
    ) -> Any:
        """Try to evaluate *code* as a Z3 expression."""
        try:
            lines = code.strip().splitlines()
            local_ns = dict(ns)
            for line in lines[:-1]:
                exec(line, local_ns)  # noqa: S102
            return eval(lines[-1], local_ns)  # noqa: S307
        except Exception:
            return None

    def _add_model_equalities(
        self,
        solver: Any,
        model: Dict[str, Any],
        ns: Dict[str, Any],
        z3: Any,
    ) -> None:
        for vname, vval in model.items():
            try:
                if isinstance(vval, int):
                    v = z3.Int(vname)
                    solver.add(v == vval)
                elif isinstance(vval, float):
                    v = z3.Real(vname)
                    solver.add(v == z3.RealVal(str(vval)))
                elif isinstance(vval, bool):
                    v = z3.Bool(vname)
                    solver.add(v == vval)
                elif isinstance(vval, str):
                    v = z3.String(vname)
                    solver.add(v == z3.StringVal(vval))
            except Exception:
                pass

    @staticmethod
    def _extract_model(z3_model: Any) -> Dict[str, Any]:
        result: Dict[str, Any] = {}
        for decl in z3_model.decls():
            name = decl.name()
            val = z3_model[decl]
            try:
                result[name] = val.as_long()
            except (AttributeError, Exception):
                result[name] = str(val)
        return result

    @staticmethod
    def _unsat_core(solver: Any) -> str:
        try:
            core = solver.unsat_core()
            return str(core) if core else "unsat (no core available)"
        except Exception:
            return "unsat"


# ===================================================================
# LeanFromZ3  (~200 lines)
# ===================================================================

class LeanFromZ3:
    """
    Translate Z3 constraints and certificates into Lean 4 syntax.
    """

    # ---- operator mapping ----
    _OP_MAP: Dict[str, str] = {
        ">=": "≥",
        "<=": "≤",
        "==": "=",
        "!=": "≠",
        "&&": "∧",
        "||": "∨",
        "!": "¬",
        "->": "→",
        "=>": "→",
        "ForAll": "∀",
        "Exists": "∃",
        "And": "∧",
        "Or": "∨",
        "Not": "¬",
        "Implies": "→",
        "True": "True",
        "False": "False",
    }

    # ---- Z3 function → Lean mapping ----
    _FUNC_MAP: Dict[str, str] = {
        "IsMember": "∈",
        "IsSubset": "⊆",
        "SetUnion": "∪",
        "SetIntersect": "∩",
        "Length": "List.length",
        "Select": "List.get",
        "Distinct": "List.Nodup",
    }

    # ================================================================ public

    def translate_constraint(self, z3c: Z3Constraint) -> str:
        """
        Translate a single ``Z3Constraint`` into a Lean 4 proposition string.
        """
        if z3c.lean_equivalent and z3c.lean_equivalent.strip() != "-- (no formula)":
            return z3c.lean_equivalent

        formula = z3c.formula_str
        if not formula:
            return f"-- No formula for constraint '{z3c.name}'"

        lean = self._translate_formula(formula, z3c.variables)
        return lean

    def translate_certificate(self, z3_cert: str) -> str:
        """
        Attempt to translate a Z3 proof / model certificate into
        a Lean tactic sketch.
        """
        if not z3_cert or z3_cert.strip() in ("", "unsat", "unknown / timeout"):
            return "sorry  -- no Z3 certificate available"

        if "unsat" in z3_cert.lower():
            return self._translate_unsat_cert(z3_cert)

        return self._translate_sat_cert(z3_cert)

    # ---- batch ----

    def translate_all(self, constraints: List[Z3Constraint]) -> List[str]:
        return [self.translate_constraint(c) for c in constraints]

    def translate_to_file(
        self,
        constraints: List[Z3Constraint],
        module_name: str = "Spec",
    ) -> str:
        """
        Generate a complete Lean 4 file with all constraints as theorems.
        """
        lines: List[str] = []
        lines.append(f"-- Auto-generated Lean 4 spec from Z3 constraints")
        lines.append(f"namespace {module_name}")
        lines.append("")

        for idx, c in enumerate(constraints):
            lean = self.translate_constraint(c)
            if lean.startswith("--"):
                lines.append(lean)
            elif lean.startswith("theorem") or lean.startswith("def"):
                lines.append(lean)
            else:
                lines.append(f"theorem {_sanitize(c.name)} : {lean} := by")
                lines.append("  sorry")
            lines.append("")

        lines.append(f"end {module_name}")
        return "\n".join(lines)

    # ========================= internals ==================================

    def _translate_formula(self, formula: str, variables: Dict[str, str]) -> str:
        result = formula

        for z3_op, lean_op in self._OP_MAP.items():
            result = result.replace(z3_op, lean_op)

        for z3_func, lean_func in self._FUNC_MAP.items():
            result = result.replace(z3_func, lean_func)

        result = self._translate_quantifiers(result)
        result = self._translate_function_calls(result)
        result = self._cleanup_lean(result)

        return result

    def _translate_quantifiers(self, text: str) -> str:
        text = re.sub(
            r"∀\s*\(\[(\w+)\]\)",
            r"∀ \1,",
            text,
        )
        text = re.sub(
            r"∀\s*\(\[(\w+),\s*(\w+)\]\)",
            r"∀ \1 \2,",
            text,
        )
        text = re.sub(
            r"∃\s*\(\[(\w+)\]\)",
            r"∃ \1,",
            text,
        )
        text = re.sub(
            r"∃\s*\(\[(\w+),\s*(\w+)\]\)",
            r"∃ \1 \2,",
            text,
        )
        return text

    def _translate_function_calls(self, text: str) -> str:
        text = re.sub(r"∈\((\w+),\s*(\w+)\)", r"\1 ∈ \2", text)
        text = re.sub(r"⊆\((\w+),\s*(\w+)\)", r"\1 ⊆ \2", text)
        text = re.sub(r"∪\((\w+),\s*(\w+)\)", r"\1 ∪ \2", text)
        text = re.sub(r"∩\((\w+),\s*(\w+)\)", r"\1 ∩ \2", text)
        text = re.sub(r"List\.length\((\w+)\)", r"\1.length", text)
        text = re.sub(r"List\.Nodup\((\w+)\)", r"\1.Nodup", text)
        return text

    @staticmethod
    def _cleanup_lean(text: str) -> str:
        text = text.replace("  ", " ")
        text = text.replace(" ,", ",")
        text = re.sub(r"\(\s+", "(", text)
        text = re.sub(r"\s+\)", ")", text)
        return text.strip()

    # ---- certificate translation ----

    def _translate_unsat_cert(self, cert: str) -> str:
        lines: List[str] = [
            "-- Z3 reported UNSAT; the constraints are contradictory.",
            "-- This means the negation is a tautology.",
            "by",
            "  omega  -- or: contradiction",
        ]
        return "\n".join(lines)

    def _translate_sat_cert(self, cert: str) -> str:
        """
        From a Z3 model string, produce a Lean ``exact`` or ``decide``
        proof attempt.
        """
        lines: List[str] = ["-- Z3 model / witness:"]

        assignments = re.findall(r"(\w+)\s*=\s*(-?\d+)", cert)
        if assignments:
            for vname, vval in assignments:
                lines.append(f"--   {vname} := {vval}")
            lines.append("by")
            lines.append("  decide")
        else:
            lines.append(f"-- raw: {cert[:200]}")
            lines.append("by")
            lines.append("  sorry  -- manual proof required")

        return "\n".join(lines)

    # ---- helpers ----

    def variable_declarations(self, constraints: List[Z3Constraint]) -> str:
        """Emit Lean variable declarations for all variables in *constraints*."""
        all_vars: Dict[str, str] = {}
        for c in constraints:
            all_vars.update(c.variables)

        lean_type_map: Dict[str, str] = {
            "int": "Int", "float": "Float", "real": "Real",
            "bool": "Bool", "str": "String", "string": "String",
            "list": "List Int", "set": "Finset Int",
        }

        lines: List[str] = []
        for vname, vtype in sorted(all_vars.items()):
            lt = lean_type_map.get(vtype.lower(), vtype)
            lines.append(f"variable ({vname} : {lt})")
        return "\n".join(lines)


# ===================================================================
# Helpers
# ===================================================================

def _sanitize(name: str) -> str:
    """Sanitize a string for use as a Lean / Z3 identifier."""
    s = re.sub(r"[^a-zA-Z0-9_]", "_", name)
    if s and s[0].isdigit():
        s = "_" + s
    return s or "_unnamed"


# ===================================================================
# Module-level convenience
# ===================================================================

_DEFAULT_COMPILER: Optional[Z3SpecCompiler] = None
_DEFAULT_SOLVER: Optional[Z3Solver] = None
_DEFAULT_LEAN: Optional[LeanFromZ3] = None


def get_compiler() -> Z3SpecCompiler:
    global _DEFAULT_COMPILER
    if _DEFAULT_COMPILER is None:
        _DEFAULT_COMPILER = Z3SpecCompiler()
    return _DEFAULT_COMPILER


def get_solver(timeout_ms: int = 5000) -> Z3Solver:
    global _DEFAULT_SOLVER
    if _DEFAULT_SOLVER is None:
        _DEFAULT_SOLVER = Z3Solver(timeout_ms=timeout_ms)
    return _DEFAULT_SOLVER


def get_lean_translator() -> LeanFromZ3:
    global _DEFAULT_LEAN
    if _DEFAULT_LEAN is None:
        _DEFAULT_LEAN = LeanFromZ3()
    return _DEFAULT_LEAN


def compile_claims(claims: List[Dict[str, Any]]) -> List[Z3Constraint]:
    return get_compiler().compile(claims)


def check_constraints(
    constraints: List[Z3Constraint],
    model: Optional[Dict[str, Any]] = None,
) -> Z3Result:
    return get_solver().check(constraints, model)


# ===================================================================
# Z3SpecValidator — validate compiled specs before solving
# ===================================================================

class Z3SpecValidator:
    """
    Pre-flight checks on a list of ``Z3Constraint`` objects before
    passing them to the solver.  Catches common authoring errors early.
    """

    # ---- known Z3 sorts ----
    KNOWN_SORTS: List[str] = [
        "IntSort()", "RealSort()", "BoolSort()", "StringSort()",
        "ArraySort(IntSort(), IntSort())", "SetSort(IntSort())",
    ]

    def validate(self, constraints: List[Z3Constraint]) -> List[str]:
        """
        Return a list of warning / error strings.  Empty = all OK.
        """
        issues: List[str] = []

        for c in constraints:
            issues.extend(self._check_single(c))

        issues.extend(self._check_cross(constraints))
        return issues

    def _check_single(self, c: Z3Constraint) -> List[str]:
        issues: List[str] = []

        if not c.name:
            issues.append(f"Constraint has empty name: {c.formula_str[:60]}")

        if not c.formula_str and not c.z3_code:
            issues.append(f"Constraint '{c.name}' has no formula and no Z3 code")

        if c.z3_code:
            issues.extend(self._check_z3_code(c.name, c.z3_code))

        for vname, vtype in c.variables.items():
            if not re.match(r"^[a-zA-Z_]\w*$", vname):
                issues.append(
                    f"Constraint '{c.name}': variable '{vname}' is not a valid identifier"
                )

        return issues

    def _check_z3_code(self, name: str, code: str) -> List[str]:
        issues: List[str] = []

        # Check balanced parentheses
        opens = code.count("(")
        closes = code.count(")")
        if opens != closes:
            issues.append(
                f"Constraint '{name}': unbalanced parentheses in Z3 code "
                f"({opens} open, {closes} close)"
            )

        # Check for common mistakes
        if "import os" in code or "import sys" in code:
            issues.append(
                f"Constraint '{name}': Z3 code should not import os/sys"
            )

        if "__" in code and "builtins" not in code:
            if "__import__" in code or "__class__" in code:
                issues.append(
                    f"Constraint '{name}': suspicious dunder in Z3 code"
                )

        return issues

    def _check_cross(self, constraints: List[Z3Constraint]) -> List[str]:
        issues: List[str] = []

        names = [c.name for c in constraints]
        seen: Dict[str, int] = {}
        for n in names:
            seen[n] = seen.get(n, 0) + 1
        for n, count in seen.items():
            if count > 1:
                issues.append(f"Duplicate constraint name: '{n}' appears {count} times")

        all_vars: Dict[str, List[str]] = {}
        for c in constraints:
            for vname, vtype in c.variables.items():
                if vname not in all_vars:
                    all_vars[vname] = []
                if vtype not in all_vars[vname]:
                    all_vars[vname].append(vtype)
        for vname, types in all_vars.items():
            if len(types) > 1:
                issues.append(
                    f"Variable '{vname}' has inconsistent types across constraints: "
                    f"{', '.join(types)}"
                )

        return issues


# ===================================================================
# Z3CodeGenerator — emit standalone runnable Z3 scripts
# ===================================================================

class Z3CodeGenerator:
    """
    Generate a complete, runnable Z3 Python script from a list of
    compiled constraints.  Useful for:
      * debugging in isolation
      * exporting to CI checks
      * archiving proof obligations
    """

    HEADER: str = (
        "#!/usr/bin/env python3\n"
        '"""Auto-generated Z3 verification script."""\n'
        "from z3 import *\n\n"
    )

    def generate(
        self,
        constraints: List[Z3Constraint],
        model: Optional[Dict[str, Any]] = None,
    ) -> str:
        lines: List[str] = [self.HEADER]
        lines.append("s = Solver()")
        lines.append("s.set('timeout', 5000)")
        lines.append("")

        declared: set[str] = set()

        for c in constraints:
            lines.append(f"# --- {c.name}: {c.formula_str[:80]} ---")
            for vname, vtype in c.variables.items():
                if vname not in declared:
                    lines.append(self._declare(vname, vtype))
                    declared.add(vname)
            if c.z3_code and "s.add(" in c.z3_code:
                for code_line in c.z3_code.splitlines():
                    if code_line.strip().startswith("s.add("):
                        lines.append(code_line)
            elif c.formula_str:
                lines.append(f"# s.add({c.formula_str})")
            lines.append("")

        if model:
            lines.append("# --- model equalities ---")
            for vname, vval in model.items():
                if vname not in declared:
                    if isinstance(vval, int):
                        lines.append(f"{vname} = Int('{vname}')")
                    elif isinstance(vval, float):
                        lines.append(f"{vname} = Real('{vname}')")
                    else:
                        lines.append(f"{vname} = Int('{vname}')")
                    declared.add(vname)
                lines.append(f"s.add({vname} == {vval!r})")
            lines.append("")

        lines.append("result = s.check()")
        lines.append("if result == sat:")
        lines.append("    print('SAT')")
        lines.append("    print(s.model())")
        lines.append("elif result == unsat:")
        lines.append("    print('UNSAT')")
        lines.append("else:")
        lines.append("    print('UNKNOWN')")

        return "\n".join(lines)

    def generate_counterexample_script(
        self,
        constraints: List[Z3Constraint],
    ) -> str:
        """Generate a script that searches for counterexamples."""
        lines: List[str] = [self.HEADER]
        lines.append("s = Solver()")
        lines.append("s.set('timeout', 5000)")
        lines.append("")

        declared: set[str] = set()
        parts: List[str] = []

        for c in constraints:
            lines.append(f"# --- {c.name} ---")
            for vname, vtype in c.variables.items():
                if vname not in declared:
                    lines.append(self._declare(vname, vtype))
                    declared.add(vname)
            if c.formula_str:
                parts.append(c.formula_str)
            lines.append("")

        if parts:
            conjunction = " , ".join(parts)
            lines.append(f"# Negate the spec to find counterexamples")
            lines.append(f"spec = And({conjunction})")
            lines.append("s.add(Not(spec))")
        else:
            lines.append("# No formulas to negate")

        lines.append("")
        lines.append("result = s.check()")
        lines.append("if result == sat:")
        lines.append("    print('COUNTEREXAMPLE FOUND:')")
        lines.append("    print(s.model())")
        lines.append("else:")
        lines.append("    print('No counterexample (spec appears valid)')")

        return "\n".join(lines)

    @staticmethod
    def _declare(vname: str, vtype: str) -> str:
        type_map = {
            "int": f"{vname} = Int('{vname}')",
            "float": f"{vname} = Real('{vname}')",
            "real": f"{vname} = Real('{vname}')",
            "bool": f"{vname} = Bool('{vname}')",
            "str": f"{vname} = String('{vname}')",
            "string": f"{vname} = String('{vname}')",
            "list": f"{vname} = Array('{vname}', IntSort(), IntSort())",
            "set": f"{vname} = Const('{vname}', SetSort(IntSort()))",
        }
        return type_map.get(vtype.lower(), f"{vname} = Int('{vname}')")


# ===================================================================
# LeanFileGenerator — emit standalone Lean 4 files
# ===================================================================

class LeanFileGenerator:
    """
    Generate complete Lean 4 files from compiled constraints,
    extending the ``LeanFromZ3`` translator with proper file
    structure, imports, and proof scaffolding.
    """

    def __init__(self) -> None:
        self._translator = LeanFromZ3()

    def generate(
        self,
        constraints: List[Z3Constraint],
        module_name: str = "Spec",
        imports: Optional[List[str]] = None,
    ) -> str:
        lines: List[str] = []

        if imports:
            for imp in imports:
                lines.append(f"import {imp}")
        else:
            lines.append("import Mathlib.Tactic")
            lines.append("import Mathlib.Data.List.Basic")
            lines.append("import Mathlib.Data.Finset.Basic")
        lines.append("")

        lines.append(f"namespace {module_name}")
        lines.append("")

        var_decls = self._translator.variable_declarations(constraints)
        if var_decls:
            lines.append("-- Variable declarations")
            lines.append(var_decls)
            lines.append("")

        for idx, c in enumerate(constraints):
            lines.append(f"/-! ### Constraint {idx}: {c.name} -/")
            lines.append("")

            lean = self._translator.translate_constraint(c)
            if lean.startswith("theorem") or lean.startswith("def") or lean.startswith("--"):
                lines.append(lean)
            else:
                safe_name = _sanitize(c.name)
                lines.append(f"theorem {safe_name} :")
                lines.append(f"    {lean} := by")
                lines.append(f"  sorry  -- TODO: prove")
            lines.append("")

        lines.append(f"end {module_name}")
        lines.append("")
        return "\n".join(lines)

    def generate_proof_obligations(
        self,
        constraints: List[Z3Constraint],
    ) -> List[Dict[str, str]]:
        """
        Return a list of proof obligation dicts, each containing:
          ``name``, ``statement``, ``tactic_sketch``
        """
        obligations: List[Dict[str, str]] = []
        for c in constraints:
            lean = self._translator.translate_constraint(c)
            obligations.append({
                "name": _sanitize(c.name),
                "statement": lean,
                "tactic_sketch": "sorry  -- auto-generated stub",
            })
        return obligations
