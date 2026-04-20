"""
SynHoPy Module Signatures

F*-style module interface declarations for SynHoPy.  A ModuleSignature
declares the VERIFIED INTERFACE of a module — the types, effects,
pre/postconditions, and invariants it guarantees — separately from
the implementation.

Architecture:
    ModuleSignature     — declares what a module guarantees
    FunctionSig         — signature of a single function
    ClassSig            — signature of a class (methods + invariants)
    SignatureChecker     — verify implementation matches signature
    SignatureBuilder     — fluent API for building signatures
    SignatureFileParser  — parse / serialize .synhopy-sig files
    SignatureAlgebra     — compose, merge, refine signatures
"""
from __future__ import annotations

import ast
import copy
import json
import re
import textwrap
from dataclasses import dataclass, field
from typing import Any

from synhopy.core.types import (
    SynType,
    PyObjType,
    PyIntType,
    PyFloatType,
    PyStrType,
    PyBoolType,
    PyNoneType,
    PyListType,
    PyDictType,
    PyCallableType,
    PyClassType,
    RefinementType,
    Context,
    Judgment,
    JudgmentKind,
    Var,
    FunctionSpec,
    Spec,
    SpecKind,
)
from synhopy.core.kernel import TrustLevel, VerificationResult

# ═══════════════════════════════════════════════════════════════════
# Effect ordering (mirrors type_checker._EFFECT_ORDER)
# ═══════════════════════════════════════════════════════════════════

_EFFECT_ORDER: dict[str, int] = {"pure": 0, "reads": 1, "mutates": 2, "IO": 3, "unsafe": 4}


def _effect_le(a: str, b: str) -> bool:
    """Is effect *a* a sub-effect of *b*?"""
    return _EFFECT_ORDER.get(a, 99) <= _EFFECT_ORDER.get(b, 99)


# ═══════════════════════════════════════════════════════════════════
# Lightweight type parsing  (string -> SynType)
# ═══════════════════════════════════════════════════════════════════

_SIMPLE_TYPES: dict[str, type[SynType]] = {
    "int": PyIntType,
    "float": PyFloatType,
    "str": PyStrType,
    "bool": PyBoolType,
    "None": PyNoneType,
    "object": PyObjType,
    "any": PyObjType,
    "Any": PyObjType,
    "unit": PyNoneType,
}


def parse_type(text: str) -> SynType:
    """Parse a type string into a SynType.

    Supports: int, str, bool, float, None, object, any,
              list[T], dict[K,V], Callable[[A,...],R],
              and falls back to PyObjType.
    """
    text = text.strip()
    if text in _SIMPLE_TYPES:
        return _SIMPLE_TYPES[text]()

    # list[T]
    m = re.fullmatch(r"list\[(.+)\]", text)
    if m:
        return PyListType(element_type=parse_type(m.group(1)))

    # dict[K, V]
    m = re.fullmatch(r"dict\[(.+),\s*(.+)\]", text)
    if m:
        return PyDictType(key_type=parse_type(m.group(1)),
                          value_type=parse_type(m.group(2)))

    # Callable[[...], R]
    m = re.fullmatch(r"Callable\[\[(.*)],\s*(.+)]", text)
    if m:
        params_raw = m.group(1).strip()
        params = tuple(parse_type(p) for p in params_raw.split(",") if p.strip()) if params_raw else ()
        return PyCallableType(param_types=params, return_type=parse_type(m.group(2)))

    return PyObjType()


def _type_to_str(ty: SynType) -> str:
    """Render a SynType back to a compact string."""
    return repr(ty)


# ═══════════════════════════════════════════════════════════════════
# Data classes
# ═══════════════════════════════════════════════════════════════════

@dataclass
class FunctionSig:
    """Signature of a single function in a module interface."""
    name: str
    params: dict[str, SynType] = field(default_factory=dict)
    return_type: SynType = field(default_factory=PyObjType)
    guarantees: list[str] = field(default_factory=list)
    requires: list[str] = field(default_factory=list)
    ensures: list[str] = field(default_factory=list)
    effects: list[str] = field(default_factory=list)
    is_total: bool = False

    # -- helpers ----------------------------------------------------------

    def declared_effect(self) -> str:
        """Return the strongest declared effect (or 'pure')."""
        if not self.effects:
            return "pure"
        best = "pure"
        for e in self.effects:
            if _EFFECT_ORDER.get(e, 99) > _EFFECT_ORDER.get(best, 0):
                best = e
        return best

    def to_json(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "params": {k: _type_to_str(v) for k, v in self.params.items()},
            "return_type": _type_to_str(self.return_type),
            "guarantees": self.guarantees,
            "requires": self.requires,
            "ensures": self.ensures,
            "effects": self.effects,
            "is_total": self.is_total,
        }

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> FunctionSig:
        return cls(
            name=data["name"],
            params={k: parse_type(v) for k, v in data.get("params", {}).items()},
            return_type=parse_type(data.get("return_type", "object")),
            guarantees=data.get("guarantees", []),
            requires=data.get("requires", []),
            ensures=data.get("ensures", []),
            effects=data.get("effects", []),
            is_total=data.get("is_total", False),
        )


@dataclass
class ClassSig:
    """Signature of a class in a module interface."""
    name: str
    methods: dict[str, FunctionSig] = field(default_factory=dict)
    invariants: list[str] = field(default_factory=list)
    bases: list[str] = field(default_factory=list)

    def to_json(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "methods": {k: v.to_json() for k, v in self.methods.items()},
            "invariants": self.invariants,
            "bases": self.bases,
        }

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> ClassSig:
        return cls(
            name=data["name"],
            methods={k: FunctionSig.from_json(v) for k, v in data.get("methods", {}).items()},
            invariants=data.get("invariants", []),
            bases=data.get("bases", []),
        )


@dataclass
class TypeMismatch:
    """A type mismatch between signature and implementation."""
    function: str
    param_or_return: str
    expected: str
    actual: str

    def __str__(self) -> str:
        return (f"{self.function}: {self.param_or_return}: "
                f"expected {self.expected}, got {self.actual}")


@dataclass
class EffectViolation:
    """An effect violation: implementation has a stronger effect."""
    function: str
    declared: str
    actual: str

    def __str__(self) -> str:
        return (f"{self.function}: declared effect '{self.declared}', "
                f"but implementation uses '{self.actual}'")


@dataclass
class SignatureCheckResult:
    """Result of checking an implementation against a signature."""
    matches: bool
    missing_functions: list[str] = field(default_factory=list)
    missing_classes: list[str] = field(default_factory=list)
    type_mismatches: list[TypeMismatch] = field(default_factory=list)
    effect_violations: list[EffectViolation] = field(default_factory=list)
    unproved_guarantees: list[str] = field(default_factory=list)

    def report(self) -> str:
        """Human-readable report."""
        if self.matches:
            return "✅ Implementation satisfies the signature."
        lines = ["❌ Signature check FAILED:"]
        for f in self.missing_functions:
            lines.append(f"  • missing function: {f}")
        for c in self.missing_classes:
            lines.append(f"  • missing class: {c}")
        for tm in self.type_mismatches:
            lines.append(f"  • type mismatch: {tm}")
        for ev in self.effect_violations:
            lines.append(f"  • effect violation: {ev}")
        for ug in self.unproved_guarantees:
            lines.append(f"  • unproved guarantee: {ug}")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# ModuleSignature
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ModuleSignature:
    """A verified module signature — declares what a module guarantees.

    Analogous to an F* ``.fsti`` interface file: you state *what*
    your module provides (function types, effects, guarantees)
    without saying *how*.
    """
    name: str
    version: str | None = None
    functions: dict[str, FunctionSig] = field(default_factory=dict)
    classes: dict[str, ClassSig] = field(default_factory=dict)
    axioms: list[str] = field(default_factory=list)
    invariants: list[str] = field(default_factory=list)
    exports: list[str] = field(default_factory=list)
    trust_level: TrustLevel = TrustLevel.UNTRUSTED

    # -- mutators ---------------------------------------------------------

    def add_function(self, name: str, sig: FunctionSig) -> None:
        self.functions[name] = sig

    def add_class(self, name: str, sig: ClassSig) -> None:
        self.classes[name] = sig

    # -- checking ---------------------------------------------------------

    def check_implementation(self, source: str) -> SignatureCheckResult:
        """Check that *source* satisfies this signature."""
        return SignatureChecker().check(self, source)

    # -- .pyi generation --------------------------------------------------

    def to_pyi(self) -> str:
        """Generate a .pyi stub file with SynHoPy annotations."""
        lines: list[str] = [
            "# Auto-generated SynHoPy stub",
            "from __future__ import annotations",
            "",
        ]
        for fname, fsig in self.functions.items():
            params_s = ", ".join(
                f"{p}: {_type_to_str(t)}" for p, t in fsig.params.items()
            )
            ret_s = _type_to_str(fsig.return_type)
            lines.append(f"def {fname}({params_s}) -> {ret_s}: ...")
            for g in fsig.guarantees:
                lines.append(f"    # @guarantee: {g}")
            for r in fsig.requires:
                lines.append(f"    # @requires: {r}")
            for e in fsig.ensures:
                lines.append(f"    # @ensures: {e}")
            if fsig.effects:
                lines.append(f"    # effects: {', '.join(fsig.effects)}")
            lines.append("")

        for cname, csig in self.classes.items():
            bases_s = ", ".join(csig.bases) if csig.bases else ""
            lines.append(f"class {cname}({bases_s}):" if bases_s else f"class {cname}:")
            for inv in csig.invariants:
                lines.append(f"    # @invariant: {inv}")
            for mname, msig in csig.methods.items():
                params_s = ", ".join(
                    f"{p}: {_type_to_str(t)}" for p, t in msig.params.items()
                )
                ret_s = _type_to_str(msig.return_type)
                lines.append(f"    def {mname}({params_s}) -> {ret_s}: ...")
                for g in msig.guarantees:
                    lines.append(f"        # @guarantee: {g}")
                for r in msig.requires:
                    lines.append(f"        # @requires: {r}")
            if not csig.methods and not csig.invariants:
                lines.append("    ...")
            lines.append("")

        return "\n".join(lines)

    # -- JSON serialization -----------------------------------------------

    def to_json(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "version": self.version,
            "functions": {k: v.to_json() for k, v in self.functions.items()},
            "classes": {k: v.to_json() for k, v in self.classes.items()},
            "axioms": self.axioms,
            "invariants": self.invariants,
            "exports": self.exports,
            "trust_level": self.trust_level.name,
        }

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> ModuleSignature:
        trust = TrustLevel[data.get("trust_level", "UNTRUSTED")]
        return cls(
            name=data["name"],
            version=data.get("version"),
            functions={k: FunctionSig.from_json(v) for k, v in data.get("functions", {}).items()},
            classes={k: ClassSig.from_json(v) for k, v in data.get("classes", {}).items()},
            axioms=data.get("axioms", []),
            invariants=data.get("invariants", []),
            exports=data.get("exports", []),
            trust_level=trust,
        )

    # -- extract from decorated source ------------------------------------

    @classmethod
    def from_source(cls, source: str) -> ModuleSignature:
        """Extract a module signature from decorated Python source code.

        Scans for ``@guarantee``, ``@requires``, ``@ensures``, ``@pure``,
        ``@total`` decorators and builds a signature from the AST.
        """
        tree = ast.parse(source)
        sig = cls(name="<source>")

        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                fsig = _extract_function_sig(node)
                sig.functions[fsig.name] = fsig
            elif isinstance(node, ast.ClassDef):
                csig = _extract_class_sig(node)
                sig.classes[csig.name] = csig

        return sig

    # -- parse from .pyi --------------------------------------------------

    @classmethod
    def from_pyi(cls, pyi_source: str) -> ModuleSignature:
        """Parse a .pyi stub file with SynHoPy comment annotations."""
        sig = cls(name="<pyi>")
        tree = ast.parse(pyi_source)

        for node in ast.iter_child_nodes(tree):
            if isinstance(node, ast.FunctionDef):
                fsig = _extract_function_sig(node)
                # Also parse comment annotations
                _parse_pyi_comments(pyi_source, node, fsig)
                sig.functions[fsig.name] = fsig
            elif isinstance(node, ast.ClassDef):
                csig = _extract_class_sig(node)
                sig.classes[csig.name] = csig

        return sig


# ═══════════════════════════════════════════════════════════════════
# AST helpers for from_source / from_pyi
# ═══════════════════════════════════════════════════════════════════

def _annotation_to_str(node: ast.expr | None) -> str:
    """Convert an AST annotation node to a string."""
    if node is None:
        return "object"
    return ast.unparse(node)


def _extract_function_sig(node: ast.FunctionDef) -> FunctionSig:
    """Build a FunctionSig from an AST FunctionDef."""
    params: dict[str, SynType] = {}
    for arg in node.args.args:
        name = arg.arg
        if name == "self":
            continue
        ty = parse_type(_annotation_to_str(arg.annotation))
        params[name] = ty

    ret = parse_type(_annotation_to_str(node.returns))
    guarantees: list[str] = []
    requires: list[str] = []
    ensures: list[str] = []
    effects: list[str] = []
    is_total = False

    for dec in node.decorator_list:
        dname, dargs = _parse_decorator(dec)
        if dname == "guarantee" and dargs:
            guarantees.append(dargs[0])
        elif dname == "requires" and dargs:
            requires.append(dargs[0])
        elif dname == "ensures" and dargs:
            ensures.append(dargs[0])
        elif dname == "pure":
            effects.append("pure")
        elif dname == "total":
            is_total = True
        elif dname in ("reads", "mutates", "IO"):
            effects.append(dname)

    return FunctionSig(
        name=node.name,
        params=params,
        return_type=ret,
        guarantees=guarantees,
        requires=requires,
        ensures=ensures,
        effects=effects,
        is_total=is_total,
    )


def _extract_class_sig(node: ast.ClassDef) -> ClassSig:
    """Build a ClassSig from an AST ClassDef."""
    methods: dict[str, FunctionSig] = {}
    invariants: list[str] = []
    bases = [ast.unparse(b) for b in node.bases]

    for item in node.body:
        if isinstance(item, ast.FunctionDef):
            msig = _extract_function_sig(item)
            methods[msig.name] = msig

    # Scan decorators for invariants
    for dec in node.decorator_list:
        dname, dargs = _parse_decorator(dec)
        if dname == "invariant" and dargs:
            invariants.append(dargs[0])

    return ClassSig(name=node.name, methods=methods, invariants=invariants, bases=bases)


def _parse_decorator(dec: ast.expr) -> tuple[str, list[str]]:
    """Return (decorator_name, [string args])."""
    if isinstance(dec, ast.Name):
        return dec.id, []
    if isinstance(dec, ast.Call):
        func = dec.func
        name = func.id if isinstance(func, ast.Name) else (
            func.attr if isinstance(func, ast.Attribute) else ""
        )
        args = []
        for a in dec.args:
            if isinstance(a, ast.Constant) and isinstance(a.value, str):
                args.append(a.value)
        return name, args
    return "", []


def _parse_pyi_comments(source: str, node: ast.FunctionDef, fsig: FunctionSig) -> None:
    """Parse ``# @guarantee:``, etc. comments following a def in a .pyi."""
    lines = source.splitlines()
    start = node.end_lineno if node.end_lineno else node.lineno
    for i in range(start, min(start + 20, len(lines))):
        line = lines[i].strip()
        if not line.startswith("#"):
            break
        m = re.match(r"#\s*@(guarantee|requires|ensures):\s*(.+)", line)
        if m:
            kind, text = m.group(1), m.group(2).strip()
            if kind == "guarantee":
                fsig.guarantees.append(text)
            elif kind == "requires":
                fsig.requires.append(text)
            elif kind == "ensures":
                fsig.ensures.append(text)
        m2 = re.match(r"#\s*effects:\s*(.+)", line)
        if m2:
            for eff in m2.group(1).split(","):
                eff = eff.strip()
                if eff:
                    fsig.effects.append(eff)


# ═══════════════════════════════════════════════════════════════════
# SignatureChecker
# ═══════════════════════════════════════════════════════════════════

class SignatureChecker:
    """Check that an implementation satisfies its module signature."""

    def check(self, sig: ModuleSignature, source: str) -> SignatureCheckResult:
        """Check *source* against *sig*.

        Verifies:
          1. All declared functions exist in source
          2. Parameter types are compatible
          3. Effects are sub-effects of declared
          4. All declared classes exist
        """
        impl = ModuleSignature.from_source(source)
        return self._compare(sig, impl)

    def check_subtyping(self, impl_sig: ModuleSignature,
                        iface_sig: ModuleSignature) -> bool:
        """Check that *impl_sig* is a valid implementation of *iface_sig*."""
        result = self._compare(iface_sig, impl_sig)
        return result.matches

    def infer_signature(self, source: str) -> ModuleSignature:
        """Infer a module signature from source code."""
        return ModuleSignature.from_source(source)

    # -- internals --------------------------------------------------------

    def _compare(self, iface: ModuleSignature,
                 impl: ModuleSignature) -> SignatureCheckResult:
        missing_functions: list[str] = []
        missing_classes: list[str] = []
        type_mismatches: list[TypeMismatch] = []
        effect_violations: list[EffectViolation] = []
        unproved: list[str] = []

        # Check functions
        for fname, fsig in iface.functions.items():
            if fname not in impl.functions:
                missing_functions.append(fname)
                continue
            impl_f = impl.functions[fname]
            self._check_function(fsig, impl_f, type_mismatches, effect_violations, unproved)

        # Check classes
        for cname, csig in iface.classes.items():
            if cname not in impl.classes:
                missing_classes.append(cname)
                continue
            impl_c = impl.classes[cname]
            for mname, msig in csig.methods.items():
                if mname not in impl_c.methods:
                    missing_functions.append(f"{cname}.{mname}")
                    continue
                impl_m = impl_c.methods[mname]
                self._check_function(
                    msig, impl_m, type_mismatches,
                    effect_violations, unproved, prefix=f"{cname}.",
                )

        ok = (not missing_functions and not missing_classes
              and not type_mismatches and not effect_violations
              and not unproved)

        return SignatureCheckResult(
            matches=ok,
            missing_functions=missing_functions,
            missing_classes=missing_classes,
            type_mismatches=type_mismatches,
            effect_violations=effect_violations,
            unproved_guarantees=unproved,
        )

    def _check_function(
        self,
        iface_f: FunctionSig,
        impl_f: FunctionSig,
        type_mismatches: list[TypeMismatch],
        effect_violations: list[EffectViolation],
        unproved: list[str],
        prefix: str = "",
    ) -> None:
        full_name = prefix + iface_f.name

        # Check parameter types (contravariant: impl may be more general)
        for pname, itype in iface_f.params.items():
            if pname in impl_f.params:
                atype = impl_f.params[pname]
                if itype != atype:
                    type_mismatches.append(TypeMismatch(
                        function=full_name,
                        param_or_return=f"param '{pname}'",
                        expected=_type_to_str(itype),
                        actual=_type_to_str(atype),
                    ))

        # Check return type (covariant: impl may be more specific)
        if iface_f.return_type != impl_f.return_type:
            type_mismatches.append(TypeMismatch(
                function=full_name,
                param_or_return="return",
                expected=_type_to_str(iface_f.return_type),
                actual=_type_to_str(impl_f.return_type),
            ))

        # Check effects: implementation effects must be ≤ declared
        decl_eff = iface_f.declared_effect()
        impl_eff = impl_f.declared_effect()
        if not _effect_le(impl_eff, decl_eff):
            effect_violations.append(EffectViolation(
                function=full_name, declared=decl_eff, actual=impl_eff,
            ))

        # Guarantees: impl must carry at least the same guarantees
        impl_g_set = set(impl_f.guarantees)
        for g in iface_f.guarantees:
            if g not in impl_g_set:
                unproved.append(f"{full_name}: {g}")


# ═══════════════════════════════════════════════════════════════════
# SignatureBuilder  (fluent API)
# ═══════════════════════════════════════════════════════════════════

class FunctionSigBuilder:
    """Fluent builder for a single function signature."""

    def __init__(self, parent: SignatureBuilder, name: str) -> None:
        self._parent = parent
        self._sig = FunctionSig(name=name)

    def param(self, name: str, typ: str) -> FunctionSigBuilder:
        self._sig.params[name] = parse_type(typ)
        return self

    def returns(self, typ: str) -> FunctionSigBuilder:
        self._sig.return_type = parse_type(typ)
        return self

    def guarantee(self, g: str) -> FunctionSigBuilder:
        self._sig.guarantees.append(g)
        return self

    def requires(self, r: str) -> FunctionSigBuilder:
        self._sig.requires.append(r)
        return self

    def ensures(self, e: str) -> FunctionSigBuilder:
        self._sig.ensures.append(e)
        return self

    def effect(self, eff: str) -> FunctionSigBuilder:
        self._sig.effects.append(eff)
        return self

    def pure(self) -> FunctionSigBuilder:
        self._sig.effects.append("pure")
        return self

    def total(self) -> FunctionSigBuilder:
        self._sig.is_total = True
        return self

    def done(self) -> SignatureBuilder:
        self._parent._sig.functions[self._sig.name] = self._sig
        return self._parent


class ClassSigBuilder:
    """Fluent builder for a class signature."""

    def __init__(self, parent: SignatureBuilder, name: str) -> None:
        self._parent = parent
        self._csig = ClassSig(name=name)

    def base(self, base_name: str) -> ClassSigBuilder:
        self._csig.bases.append(base_name)
        return self

    def invariant(self, inv: str) -> ClassSigBuilder:
        self._csig.invariants.append(inv)
        return self

    def method(self, name: str) -> _MethodSigBuilder:
        return _MethodSigBuilder(self, name)

    def done(self) -> SignatureBuilder:
        self._parent._sig.classes[self._csig.name] = self._csig
        return self._parent


class _MethodSigBuilder:
    """Fluent builder for a method inside a ClassSigBuilder."""

    def __init__(self, parent: ClassSigBuilder, name: str) -> None:
        self._parent = parent
        self._sig = FunctionSig(name=name)

    def param(self, name: str, typ: str) -> _MethodSigBuilder:
        self._sig.params[name] = parse_type(typ)
        return self

    def returns(self, typ: str) -> _MethodSigBuilder:
        self._sig.return_type = parse_type(typ)
        return self

    def guarantee(self, g: str) -> _MethodSigBuilder:
        self._sig.guarantees.append(g)
        return self

    def requires(self, r: str) -> _MethodSigBuilder:
        self._sig.requires.append(r)
        return self

    def ensures(self, e: str) -> _MethodSigBuilder:
        self._sig.ensures.append(e)
        return self

    def effect(self, eff: str) -> _MethodSigBuilder:
        self._sig.effects.append(eff)
        return self

    def pure(self) -> _MethodSigBuilder:
        self._sig.effects.append("pure")
        return self

    def total(self) -> _MethodSigBuilder:
        self._sig.is_total = True
        return self

    def done(self) -> ClassSigBuilder:
        self._parent._csig.methods[self._sig.name] = self._sig
        return self._parent


class SignatureBuilder:
    """Fluent API for building module signatures."""

    def __init__(self, name: str) -> None:
        self._sig = ModuleSignature(name=name)

    def version(self, v: str) -> SignatureBuilder:
        self._sig.version = v
        return self

    def function(self, name: str) -> FunctionSigBuilder:
        return FunctionSigBuilder(self, name)

    def cls(self, name: str) -> ClassSigBuilder:
        return ClassSigBuilder(self, name)

    def axiom(self, statement: str) -> SignatureBuilder:
        self._sig.axioms.append(statement)
        return self

    def invariant(self, inv: str) -> SignatureBuilder:
        self._sig.invariants.append(inv)
        return self

    def exports(self, *names: str) -> SignatureBuilder:
        self._sig.exports.extend(names)
        return self

    def trust(self, level: TrustLevel) -> SignatureBuilder:
        self._sig.trust_level = level
        return self

    def build(self) -> ModuleSignature:
        return self._sig


# ═══════════════════════════════════════════════════════════════════
# .synhopy-sig file parser / serializer
# ═══════════════════════════════════════════════════════════════════

class SignatureFileParser:
    """Parse and serialize the ``.synhopy-sig`` text format.

    Format example::

        module mylib
        version "1.0"

        axiom "all elements are comparable"

        val sort : list[int] -> list[int]
          requires: len(xs) >= 0
          ensures: result is sorted
          ensures: len(result) == len(xs)
          effect: pure

        class Stack:
          invariant: len(self._items) >= 0
          val push : int -> None
            effect: mutates
          val pop : unit -> int
            requires: len(self._items) > 0
            effect: mutates
    """

    def parse(self, text: str) -> ModuleSignature:
        """Parse a .synhopy-sig file into a ModuleSignature."""
        sig = ModuleSignature(name="<unknown>")
        lines = text.splitlines()
        i = 0
        current_class: ClassSig | None = None

        while i < len(lines):
            line = lines[i]
            stripped = line.strip()

            if not stripped or stripped.startswith("#"):
                i += 1
                continue

            # module <name>
            m = re.match(r"^module\s+(\S+)", stripped)
            if m:
                sig.name = m.group(1)
                i += 1
                continue

            # version "<ver>"
            m = re.match(r'^version\s+"([^"]+)"', stripped)
            if m:
                sig.version = m.group(1)
                i += 1
                continue

            # axiom "<text>"
            m = re.match(r'^axiom\s+"([^"]+)"', stripped)
            if m:
                sig.axioms.append(m.group(1))
                i += 1
                continue

            # invariant: <text> — at top level only (not inside a class)
            m = re.match(r"^invariant:\s+(.+)", stripped)
            if m and current_class is None:
                sig.invariants.append(m.group(1))
                i += 1
                continue

            # invariant inside a class block (indented)
            if m and current_class is not None:
                current_class.invariants.append(m.group(1).strip())
                i += 1
                continue

            # trust <level>
            m = re.match(r"^trust\s+(\S+)", stripped)
            if m:
                try:
                    sig.trust_level = TrustLevel[m.group(1)]
                except KeyError:
                    pass
                i += 1
                continue

            # export <names>
            m = re.match(r"^export\s+(.+)", stripped)
            if m:
                for name in m.group(1).split(","):
                    name = name.strip()
                    if name:
                        sig.exports.append(name)
                i += 1
                continue

            # class <Name>:
            m = re.match(r"^class\s+(\w+)\s*(?:\(([^)]*)\))?\s*:", stripped)
            if m:
                cname = m.group(1)
                bases = [b.strip() for b in m.group(2).split(",")] if m.group(2) else []
                current_class = ClassSig(name=cname, bases=bases)
                sig.classes[cname] = current_class
                i += 1
                continue

            # val <name> : <params> -> <return>  (at top level or inside class)
            indent = len(line) - len(line.lstrip())
            m = re.match(r"^val\s+(\w+)\s*:\s*(.+)", stripped)
            if m:
                fname = m.group(1)
                type_str = m.group(2).strip()
                fsig, i = self._parse_val(fname, type_str, lines, i)

                if current_class is not None and indent > 0:
                    current_class.methods[fname] = fsig
                else:
                    if indent == 0:
                        current_class = None
                    sig.functions[fname] = fsig
                continue

            # End of class block: non-indented non-val line
            if indent == 0 and current_class is not None:
                current_class = None
                # don't increment — re-process line
                continue

            i += 1

        return sig

    def _parse_val(self, name: str, type_str: str,
                   lines: list[str], start: int) -> tuple[FunctionSig, int]:
        """Parse a ``val`` declaration and its annotation lines."""
        # Split "A -> B -> C" into params and return
        parts = [p.strip() for p in type_str.split("->")]
        if len(parts) >= 2:
            param_types = parts[:-1]
            ret_type = parts[-1]
        else:
            param_types = []
            ret_type = type_str

        params: dict[str, SynType] = {}
        for idx, pt in enumerate(param_types):
            pname = f"x{idx}"
            if pt.startswith("'"):
                params[pname] = PyObjType()
            else:
                params[pname] = parse_type(pt)

        fsig = FunctionSig(
            name=name,
            params=params,
            return_type=parse_type(ret_type) if not ret_type.startswith("'") else PyObjType(),
        )

        # Indent of the val line itself — annotations must be strictly deeper
        val_indent = len(lines[start]) - len(lines[start].lstrip())

        i = start + 1
        while i < len(lines):
            raw = lines[i]
            stripped = raw.strip()
            if not stripped:
                i += 1
                continue
            indent = len(raw) - len(raw.lstrip())
            if indent <= val_indent:
                break

            m = re.match(r"requires:\s+(.+)", stripped)
            if m:
                fsig.requires.append(m.group(1).strip())
                i += 1
                continue

            m = re.match(r"ensures:\s+(.+)", stripped)
            if m:
                fsig.ensures.append(m.group(1).strip())
                i += 1
                continue

            m = re.match(r"guarantee:\s+(.+)", stripped)
            if m:
                fsig.guarantees.append(m.group(1).strip())
                i += 1
                continue

            m = re.match(r"effect:\s+(.+)", stripped)
            if m:
                fsig.effects.append(m.group(1).strip())
                i += 1
                continue

            m = re.match(r"total", stripped)
            if m:
                fsig.is_total = True
                i += 1
                continue

            # Unknown annotation line — skip
            i += 1

        return fsig, i

    def serialize(self, sig: ModuleSignature) -> str:
        """Serialize a ModuleSignature to .synhopy-sig format."""
        lines: list[str] = []
        lines.append(f"module {sig.name}")
        if sig.version:
            lines.append(f'version "{sig.version}"')
        if sig.trust_level != TrustLevel.UNTRUSTED:
            lines.append(f"trust {sig.trust_level.name}")
        if sig.exports:
            lines.append(f"export {', '.join(sig.exports)}")
        for ax in sig.axioms:
            lines.append(f'axiom "{ax}"')
        for inv in sig.invariants:
            lines.append(f"invariant: {inv}")

        if sig.functions:
            lines.append("")
        for fname, fsig in sig.functions.items():
            lines.append(self._serialize_val(fsig, indent=0))

        for cname, csig in sig.classes.items():
            lines.append("")
            bases_s = f"({', '.join(csig.bases)})" if csig.bases else ""
            lines.append(f"class {cname}{bases_s}:")
            for inv in csig.invariants:
                lines.append(f"  invariant: {inv}")
            for mname, msig in csig.methods.items():
                lines.append(self._serialize_val(msig, indent=2))

        return "\n".join(lines) + "\n"

    def _serialize_val(self, fsig: FunctionSig, indent: int = 0) -> str:
        """Serialize a single val declaration."""
        prefix = " " * indent
        parts: list[str] = []
        for _pname, ptype in fsig.params.items():
            parts.append(_type_to_str(ptype))
        parts.append(_type_to_str(fsig.return_type))
        type_str = " -> ".join(parts)

        lines = [f"{prefix}val {fsig.name} : {type_str}"]
        inner = prefix + "  "
        for r in fsig.requires:
            lines.append(f"{inner}requires: {r}")
        for e in fsig.ensures:
            lines.append(f"{inner}ensures: {e}")
        for g in fsig.guarantees:
            lines.append(f"{inner}guarantee: {g}")
        for eff in fsig.effects:
            lines.append(f"{inner}effect: {eff}")
        if fsig.is_total:
            lines.append(f"{inner}total")

        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# SignatureAlgebra — compose, merge, refine
# ═══════════════════════════════════════════════════════════════════

class SignatureAlgebra:
    """Algebraic operations on module signatures."""

    def merge(self, *sigs: ModuleSignature) -> ModuleSignature:
        """Merge multiple signatures (union of requirements).

        Functions/classes from all signatures are collected.  For
        duplicates, guarantees/requires/ensures are unioned.
        """
        if not sigs:
            return ModuleSignature(name="<empty>")

        result = ModuleSignature(name="+".join(s.name for s in sigs))
        for s in sigs:
            if s.version and not result.version:
                result.version = s.version
            for fname, fsig in s.functions.items():
                if fname in result.functions:
                    self._merge_function(result.functions[fname], fsig)
                else:
                    result.functions[fname] = copy.deepcopy(fsig)
            for cname, csig in s.classes.items():
                if cname in result.classes:
                    self._merge_class(result.classes[cname], csig)
                else:
                    result.classes[cname] = copy.deepcopy(csig)
            for ax in s.axioms:
                if ax not in result.axioms:
                    result.axioms.append(ax)
            for inv in s.invariants:
                if inv not in result.invariants:
                    result.invariants.append(inv)
            for ex in s.exports:
                if ex not in result.exports:
                    result.exports.append(ex)
            result.trust_level = TrustLevel(
                min(result.trust_level.value, s.trust_level.value)
            )

        return result

    def intersect(self, *sigs: ModuleSignature) -> ModuleSignature:
        """Intersect signatures (only common functions, intersection of guarantees)."""
        if not sigs:
            return ModuleSignature(name="<empty>")
        if len(sigs) == 1:
            return copy.deepcopy(sigs[0])

        # Start with the first, keep only what appears in all
        result = ModuleSignature(name="&".join(s.name for s in sigs))

        common_funcs = set(sigs[0].functions.keys())
        for s in sigs[1:]:
            common_funcs &= set(s.functions.keys())

        for fname in common_funcs:
            merged = copy.deepcopy(sigs[0].functions[fname])
            for s in sigs[1:]:
                other = s.functions[fname]
                merged.guarantees = [
                    g for g in merged.guarantees if g in other.guarantees
                ]
                merged.requires = [
                    r for r in merged.requires if r in other.requires
                ]
                merged.ensures = [
                    e for e in merged.ensures if e in other.ensures
                ]
            result.functions[fname] = merged

        common_classes = set(sigs[0].classes.keys())
        for s in sigs[1:]:
            common_classes &= set(s.classes.keys())

        for cname in common_classes:
            result.classes[cname] = copy.deepcopy(sigs[0].classes[cname])

        # Axioms that appear in all
        if sigs:
            common_axioms = set(sigs[0].axioms)
            for s in sigs[1:]:
                common_axioms &= set(s.axioms)
            result.axioms = list(common_axioms)

        return result

    def refine(self, base: ModuleSignature,
               refinement: ModuleSignature) -> ModuleSignature:
        """Refine a signature with stronger guarantees.

        The refinement can add new functions, tighten guarantees,
        and strengthen invariants.
        """
        result = copy.deepcopy(base)
        result.name = f"{base.name}+{refinement.name}"

        for fname, fsig in refinement.functions.items():
            if fname in result.functions:
                self._merge_function(result.functions[fname], fsig)
            else:
                result.functions[fname] = copy.deepcopy(fsig)

        for cname, csig in refinement.classes.items():
            if cname in result.classes:
                self._merge_class(result.classes[cname], csig)
            else:
                result.classes[cname] = copy.deepcopy(csig)

        for ax in refinement.axioms:
            if ax not in result.axioms:
                result.axioms.append(ax)
        for inv in refinement.invariants:
            if inv not in result.invariants:
                result.invariants.append(inv)

        return result

    def is_subtype(self, sub: ModuleSignature,
                   sup: ModuleSignature) -> bool:
        """Check if *sub* is a valid subtype (refinement) of *sup*.

        *sub* must provide at least all functions in *sup* with
        compatible types and at least the same guarantees.
        """
        return SignatureChecker().check_subtyping(sub, sup)

    # -- helpers ----------------------------------------------------------

    @staticmethod
    def _merge_function(target: FunctionSig, source: FunctionSig) -> None:
        for g in source.guarantees:
            if g not in target.guarantees:
                target.guarantees.append(g)
        for r in source.requires:
            if r not in target.requires:
                target.requires.append(r)
        for e in source.ensures:
            if e not in target.ensures:
                target.ensures.append(e)
        for eff in source.effects:
            if eff not in target.effects:
                target.effects.append(eff)

    @staticmethod
    def _merge_class(target: ClassSig, source: ClassSig) -> None:
        for inv in source.invariants:
            if inv not in target.invariants:
                target.invariants.append(inv)
        for mname, msig in source.methods.items():
            if mname not in target.methods:
                target.methods[mname] = copy.deepcopy(msig)
            else:
                SignatureAlgebra._merge_function(target.methods[mname], msig)


# ═══════════════════════════════════════════════════════════════════
# Self-tests
# ═══════════════════════════════════════════════════════════════════

def _self_test() -> None:
    """Run self-tests for the signatures module."""
    passed = 0
    failed = 0

    def ok(name: str, cond: bool, detail: str = "") -> None:
        nonlocal passed, failed
        if cond:
            passed += 1
            print(f"  ✅ {name}")
        else:
            failed += 1
            msg = f"  ❌ {name}"
            if detail:
                msg += f" — {detail}"
            print(msg)

    print("=" * 60)
    print("synhopy.core.signatures — self-tests")
    print("=" * 60)

    # ── 1. parse_type ────────────────────────────────────────────
    print("\n── parse_type ──")
    ok("int", isinstance(parse_type("int"), PyIntType))
    ok("str", isinstance(parse_type("str"), PyStrType))
    ok("bool", isinstance(parse_type("bool"), PyBoolType))
    ok("float", isinstance(parse_type("float"), PyFloatType))
    ok("None", isinstance(parse_type("None"), PyNoneType))
    ok("object fallback", isinstance(parse_type("SomeCustom"), PyObjType))
    ok("list[int]", isinstance(parse_type("list[int]"), PyListType))
    lt = parse_type("list[int]")
    assert isinstance(lt, PyListType)
    ok("list[int] element", isinstance(lt.element_type, PyIntType))
    ok("dict[str, int]", isinstance(parse_type("dict[str, int]"), PyDictType))

    # ── 2. FunctionSig basics ────────────────────────────────────
    print("\n── FunctionSig ──")
    fs = FunctionSig(
        name="sort",
        params={"xs": PyListType(PyIntType())},
        return_type=PyListType(PyIntType()),
        guarantees=["result is sorted"],
        requires=["len(xs) >= 0"],
        effects=["pure"],
    )
    ok("name", fs.name == "sort")
    ok("declared_effect pure", fs.declared_effect() == "pure")
    ok("guarantees", fs.guarantees == ["result is sorted"])

    fs2 = FunctionSig(name="do_io", effects=["IO"])
    ok("declared_effect IO", fs2.declared_effect() == "IO")

    fs3 = FunctionSig(name="mixed", effects=["pure", "mutates"])
    ok("declared_effect strongest", fs3.declared_effect() == "mutates")

    # ── 3. FunctionSig JSON round-trip ───────────────────────────
    print("\n── JSON round-trip ──")
    j = fs.to_json()
    ok("to_json keys", "name" in j and "params" in j)
    fs_back = FunctionSig.from_json(j)
    ok("from_json name", fs_back.name == "sort")
    ok("from_json guarantees", fs_back.guarantees == ["result is sorted"])
    ok("from_json requires", fs_back.requires == ["len(xs) >= 0"])

    # ── 4. ClassSig JSON round-trip ──────────────────────────────
    cs = ClassSig(
        name="Stack",
        methods={"push": fs, "pop": FunctionSig(name="pop")},
        invariants=["len(self._items) >= 0"],
        bases=["Generic"],
    )
    cj = cs.to_json()
    ok("ClassSig to_json", cj["name"] == "Stack")
    cs_back = ClassSig.from_json(cj)
    ok("ClassSig from_json", cs_back.name == "Stack")
    ok("ClassSig methods", "push" in cs_back.methods)
    ok("ClassSig invariants", cs_back.invariants == ["len(self._items) >= 0"])

    # ── 5. ModuleSignature basics ────────────────────────────────
    print("\n── ModuleSignature ──")
    msig = ModuleSignature(name="mylib", version="1.0")
    msig.add_function("sort", fs)
    msig.add_class("Stack", cs)
    ok("add_function", "sort" in msig.functions)
    ok("add_class", "Stack" in msig.classes)

    # ── 6. ModuleSignature JSON round-trip ───────────────────────
    mj = msig.to_json()
    ok("ModuleSignature to_json", mj["name"] == "mylib")
    msig_back = ModuleSignature.from_json(mj)
    ok("ModuleSignature from_json", msig_back.name == "mylib")
    ok("from_json version", msig_back.version == "1.0")
    ok("from_json functions", "sort" in msig_back.functions)
    ok("from_json classes", "Stack" in msig_back.classes)

    # ── 7. to_pyi ────────────────────────────────────────────────
    print("\n── to_pyi ──")
    pyi = msig.to_pyi()
    ok("pyi contains def sort", "def sort" in pyi)
    ok("pyi contains class Stack", "class Stack" in pyi)
    ok("pyi contains guarantee", "@guarantee" in pyi)

    # ── 8. from_source ───────────────────────────────────────────
    print("\n── from_source ──")
    src = textwrap.dedent("""\
        from synhopy.proofs.sugar import guarantee, requires, pure

        @guarantee("result is sorted")
        @pure
        def sort(xs: list) -> list:
            return sorted(xs)

        class Stack:
            def push(self, item: int) -> None:
                pass
            def pop(self) -> int:
                pass
    """)
    sig_from_src = ModuleSignature.from_source(src)
    ok("from_source finds sort", "sort" in sig_from_src.functions)
    ok("from_source guarantee", sig_from_src.functions["sort"].guarantees == ["result is sorted"])
    ok("from_source finds Stack", "Stack" in sig_from_src.classes)
    ok("from_source Stack.push", "push" in sig_from_src.classes["Stack"].methods)

    # ── 9. SignatureChecker — matching ───────────────────────────
    print("\n── SignatureChecker ──")
    iface = (
        SignatureBuilder("mylib")
        .function("add")
            .param("a", "int").param("b", "int")
            .returns("int").pure()
            .done()
        .build()
    )
    impl_src = textwrap.dedent("""\
        @pure
        def add(a: int, b: int) -> int:
            return a + b
    """)
    result = SignatureChecker().check(iface, impl_src)
    ok("matching impl", result.matches, result.report())

    # ── 10. SignatureChecker — missing function ──────────────────
    iface2 = (
        SignatureBuilder("mylib")
        .function("add").param("a", "int").returns("int").done()
        .function("multiply").param("a", "int").returns("int").done()
        .build()
    )
    result2 = SignatureChecker().check(iface2, impl_src)
    ok("missing function detected", not result2.matches)
    ok("missing multiply", "multiply" in result2.missing_functions)

    # ── 11. SignatureChecker — type mismatch ─────────────────────
    iface3 = (
        SignatureBuilder("mylib")
        .function("add").param("a", "str").returns("int").done()
        .build()
    )
    result3 = SignatureChecker().check(iface3, impl_src)
    ok("type mismatch detected", not result3.matches)
    ok("type mismatch list", len(result3.type_mismatches) > 0)

    # ── 12. SignatureChecker — effect violation ──────────────────
    iface4 = (
        SignatureBuilder("mylib")
        .function("add").param("a", "int").param("b", "int")
            .returns("int").pure().done()
        .build()
    )
    impl_io = textwrap.dedent("""\
        @IO
        def add(a: int, b: int) -> int:
            print(a + b)
            return a + b
    """)
    result4 = SignatureChecker().check(iface4, impl_io)
    ok("effect violation detected", not result4.matches)
    ok("effect violation list", len(result4.effect_violations) > 0)

    # ── 13. SignatureChecker — unproved guarantee ────────────────
    iface5 = (
        SignatureBuilder("mylib")
        .function("add").param("a", "int").param("b", "int")
            .returns("int").guarantee("result > 0").done()
        .build()
    )
    result5 = SignatureChecker().check(iface5, impl_src)
    ok("unproved guarantee", not result5.matches)
    ok("unproved guarantee list", len(result5.unproved_guarantees) > 0)

    # ── 14. SignatureCheckResult.report ───────────────────────────
    print("\n── SignatureCheckResult.report ──")
    ok("pass report", "✅" in SignatureCheckResult(matches=True).report())
    ok("fail report", "❌" in SignatureCheckResult(
        matches=False, missing_functions=["foo"]
    ).report())

    # ── 15. SignatureBuilder fluent API ───────────────────────────
    print("\n── SignatureBuilder ──")
    sig = (
        SignatureBuilder("stack_lib")
        .version("2.0")
        .axiom("all elements are comparable")
        .invariant("stack size >= 0")
        .exports("Stack", "sort")
        .function("sort")
            .param("xs", "list[int]")
            .returns("list[int]")
            .guarantee("result is sorted")
            .ensures("len(result) == len(xs)")
            .pure().total()
            .done()
        .cls("Stack")
            .base("Generic")
            .invariant("len(self._items) >= 0")
            .method("push")
                .param("item", "int")
                .returns("None")
                .effect("mutates")
                .done()
            .method("pop")
                .returns("int")
                .requires("len(self._items) > 0")
                .effect("mutates")
                .done()
            .done()
        .trust(TrustLevel.Z3_VERIFIED)
        .build()
    )
    ok("builder name", sig.name == "stack_lib")
    ok("builder version", sig.version == "2.0")
    ok("builder axiom", "all elements are comparable" in sig.axioms)
    ok("builder invariant", "stack size >= 0" in sig.invariants)
    ok("builder exports", sig.exports == ["Stack", "sort"])
    ok("builder function", "sort" in sig.functions)
    ok("builder function total", sig.functions["sort"].is_total)
    ok("builder class", "Stack" in sig.classes)
    ok("builder class base", sig.classes["Stack"].bases == ["Generic"])
    ok("builder class invariant",
       "len(self._items) >= 0" in sig.classes["Stack"].invariants)
    ok("builder method push", "push" in sig.classes["Stack"].methods)
    ok("builder method pop requires",
       "len(self._items) > 0" in sig.classes["Stack"].methods["pop"].requires)
    ok("builder trust", sig.trust_level == TrustLevel.Z3_VERIFIED)

    # ── 16. SignatureFileParser — parse ───────────────────────────
    print("\n── SignatureFileParser ──")
    sig_text = textwrap.dedent("""\
        module mylib
        version "1.0"
        axiom "all elements are comparable"
        trust Z3_VERIFIED

        val sort : list[int] -> list[int]
          requires: len(xs) >= 0
          ensures: result is sorted
          ensures: len(result) == len(xs)
          effect: pure

        class Stack:
          invariant: len(self._items) >= 0
          val push : int -> None
            effect: mutates
          val pop : unit -> int
            requires: len(self._items) > 0
            effect: mutates
    """)
    parser = SignatureFileParser()
    parsed = parser.parse(sig_text)
    ok("parse module name", parsed.name == "mylib")
    ok("parse version", parsed.version == "1.0")
    ok("parse axiom", "all elements are comparable" in parsed.axioms)
    ok("parse trust", parsed.trust_level == TrustLevel.Z3_VERIFIED)
    ok("parse sort", "sort" in parsed.functions)
    ok("parse sort requires", "len(xs) >= 0" in parsed.functions["sort"].requires)
    ok("parse sort ensures", "result is sorted" in parsed.functions["sort"].ensures)
    ok("parse sort effect", "pure" in parsed.functions["sort"].effects)
    ok("parse Stack", "Stack" in parsed.classes)
    ok("parse Stack invariant",
       "len(self._items) >= 0" in parsed.classes["Stack"].invariants)
    ok("parse Stack push", "push" in parsed.classes["Stack"].methods)
    ok("parse Stack pop", "pop" in parsed.classes["Stack"].methods)
    ok("parse pop requires",
       "len(self._items) > 0" in parsed.classes["Stack"].methods["pop"].requires)
    ok("parse push effect",
       "mutates" in parsed.classes["Stack"].methods["push"].effects)

    # ── 17. SignatureFileParser — round-trip ──────────────────────
    print("\n── SignatureFileParser round-trip ──")
    serialized = parser.serialize(parsed)
    ok("serialize contains module", "module mylib" in serialized)
    ok("serialize contains version", 'version "1.0"' in serialized)
    ok("serialize contains val sort", "val sort" in serialized)
    ok("serialize contains class Stack", "class Stack" in serialized)

    reparsed = parser.parse(serialized)
    ok("roundtrip name", reparsed.name == parsed.name)
    ok("roundtrip functions", set(reparsed.functions) == set(parsed.functions))
    ok("roundtrip classes", set(reparsed.classes) == set(parsed.classes))

    # ── 18. SignatureAlgebra — merge ─────────────────────────────
    print("\n── SignatureAlgebra ──")
    alg = SignatureAlgebra()

    s1 = (SignatureBuilder("a")
          .function("f").param("x", "int").returns("int")
              .guarantee("x > 0").done()
          .build())
    s2 = (SignatureBuilder("b")
          .function("g").param("y", "str").returns("str").done()
          .function("f").param("x", "int").returns("int")
              .guarantee("x < 100").done()
          .build())

    merged = alg.merge(s1, s2)
    ok("merge name", merged.name == "a+b")
    ok("merge has f", "f" in merged.functions)
    ok("merge has g", "g" in merged.functions)
    ok("merge f guarantees", "x > 0" in merged.functions["f"].guarantees
       and "x < 100" in merged.functions["f"].guarantees)

    # ── 19. SignatureAlgebra — intersect ──────────────────────────
    i1 = (SignatureBuilder("a")
          .function("f").guarantee("g1").guarantee("g2").done()
          .function("h").done()
          .build())
    i2 = (SignatureBuilder("b")
          .function("f").guarantee("g2").guarantee("g3").done()
          .build())
    inter = alg.intersect(i1, i2)
    ok("intersect has f", "f" in inter.functions)
    ok("intersect no h", "h" not in inter.functions)
    ok("intersect f guarantees", inter.functions["f"].guarantees == ["g2"])

    # ── 20. SignatureAlgebra — refine ─────────────────────────────
    base = (SignatureBuilder("base")
            .function("f").guarantee("g1").done()
            .build())
    ref = (SignatureBuilder("ref")
           .function("f").guarantee("g2").done()
           .function("new_fn").done()
           .build())
    refined = alg.refine(base, ref)
    ok("refine has f", "f" in refined.functions)
    ok("refine f has g1+g2",
       "g1" in refined.functions["f"].guarantees
       and "g2" in refined.functions["f"].guarantees)
    ok("refine has new_fn", "new_fn" in refined.functions)

    # ── 21. SignatureAlgebra — is_subtype ─────────────────────────
    sup = (SignatureBuilder("sup")
           .function("f").param("x", "int").returns("int")
               .guarantee("positive").pure().done()
           .build())
    sub_ok = (SignatureBuilder("sub")
              .function("f").param("x", "int").returns("int")
                  .guarantee("positive").pure().done()
              .function("extra").done()
              .build())
    sub_bad = (SignatureBuilder("sub_bad")
               .function("f").param("x", "str").returns("int").done()
               .build())
    ok("is_subtype (valid)", alg.is_subtype(sub_ok, sup))
    ok("is_subtype (invalid)", not alg.is_subtype(sub_bad, sup))

    # ── 22. SignatureChecker — infer_signature ───────────────────
    print("\n── infer_signature ──")
    inferred = SignatureChecker().infer_signature(impl_src)
    ok("inferred has add", "add" in inferred.functions)
    ok("inferred add params", "a" in inferred.functions["add"].params)

    # ── 23. check_subtyping via checker ──────────────────────────
    ok("checker subtyping",
       SignatureChecker().check_subtyping(sub_ok, sup))

    # ── 24. effect_le tests ──────────────────────────────────────
    print("\n── effect ordering ──")
    ok("pure <= pure", _effect_le("pure", "pure"))
    ok("pure <= IO", _effect_le("pure", "IO"))
    ok("IO !<= pure", not _effect_le("IO", "pure"))
    ok("mutates <= IO", _effect_le("mutates", "IO"))

    # ── 25. ModuleSignature.check_implementation ─────────────────
    print("\n── check_implementation ──")
    sig_stack = (
        SignatureBuilder("stack")
        .function("push")
            .param("item", "int").returns("None").effect("mutates").done()
        .function("pop")
            .returns("int").effect("mutates").done()
        .build()
    )
    stack_impl = textwrap.dedent("""\
        @mutates
        def push(item: int) -> None:
            pass

        @mutates
        def pop() -> int:
            return 0
    """)
    check_result = sig_stack.check_implementation(stack_impl)
    ok("check_implementation matches", check_result.matches, check_result.report())

    # ── 26. ClassSig in checker ──────────────────────────────────
    print("\n── class checking ──")
    iface_cls = (
        SignatureBuilder("cls_mod")
        .cls("Calc")
            .method("add").param("a", "int").param("b", "int").returns("int").done()
            .done()
        .build()
    )
    cls_impl = textwrap.dedent("""\
        class Calc:
            def add(self, a: int, b: int) -> int:
                return a + b
    """)
    cls_result = SignatureChecker().check(iface_cls, cls_impl)
    ok("class impl matches", cls_result.matches, cls_result.report())

    # Missing method
    cls_impl_bad = textwrap.dedent("""\
        class Calc:
            def subtract(self, a: int, b: int) -> int:
                return a - b
    """)
    cls_result_bad = SignatureChecker().check(iface_cls, cls_impl_bad)
    ok("class missing method", not cls_result_bad.matches)
    ok("class missing method name", "Calc.add" in cls_result_bad.missing_functions)

    # ── 27. Empty signature ──────────────────────────────────────
    print("\n── edge cases ──")
    empty = ModuleSignature(name="empty")
    empty_result = empty.check_implementation("")
    ok("empty sig matches empty source", empty_result.matches)

    # ── 28. Merge of empty ───────────────────────────────────────
    empty_merge = alg.merge()
    ok("merge zero sigs", empty_merge.name == "<empty>")

    single_merge = alg.merge(s1)
    ok("merge single sig", "f" in single_merge.functions)

    # ── 29. Intersect single ─────────────────────────────────────
    single_inter = alg.intersect(i1)
    ok("intersect single", "f" in single_inter.functions and "h" in single_inter.functions)

    # ── 30. FunctionSig with no effects ──────────────────────────
    fs_empty = FunctionSig(name="noop")
    ok("no effects -> pure", fs_empty.declared_effect() == "pure")

    # ── 31. Missing class in checker ─────────────────────────────
    iface_missing_cls = (
        SignatureBuilder("mod")
        .cls("Foo").done()
        .build()
    )
    result_mc = SignatureChecker().check(iface_missing_cls, "")
    ok("missing class detected", not result_mc.matches)
    ok("missing class list", "Foo" in result_mc.missing_classes)

    # ── 32. SignatureFileParser export ────────────────────────────
    sig_with_export = textwrap.dedent("""\
        module exmod
        export foo, bar
    """)
    parsed_exp = parser.parse(sig_with_export)
    ok("parse exports", parsed_exp.exports == ["foo", "bar"])

    # ── 33. to_pyi with class having no methods ──────────────────
    sig_bare = ModuleSignature(name="bare")
    sig_bare.add_class("Empty", ClassSig(name="Empty"))
    pyi_bare = sig_bare.to_pyi()
    ok("pyi bare class", "class Empty" in pyi_bare)

    # ── 34. Worked example: Stack ────────────────────────────────
    print("\n── Worked example: Stack module ──")
    # 1. Build the signature
    stack_sig = (
        SignatureBuilder("stack_module")
        .version("1.0")
        .cls("Stack")
            .invariant("len(self._items) >= 0")
            .method("__init__")
                .returns("None").pure().done()
            .method("push")
                .param("item", "int").returns("None")
                .effect("mutates").done()
            .method("pop")
                .returns("int")
                .requires("len(self._items) > 0")
                .effect("mutates").done()
            .method("is_empty")
                .returns("bool").pure().total().done()
            .done()
        .axiom("LIFO ordering: pop returns most recently pushed item")
        .build()
    )

    # 2. Implementation
    stack_source = textwrap.dedent("""\
        class Stack:
            @pure
            def __init__(self) -> None:
                self._items = []

            @mutates
            def push(self, item: int) -> None:
                self._items.append(item)

            @mutates
            def pop(self) -> int:
                return self._items.pop()

            @pure
            @total
            def is_empty(self) -> bool:
                return len(self._items) == 0
    """)

    # 3. Check
    stack_result = stack_sig.check_implementation(stack_source)
    ok("Stack impl matches sig", stack_result.matches, stack_result.report())

    # 4. Serialize to .synhopy-sig and back
    sig_file = SignatureFileParser().serialize(stack_sig)
    ok("Stack sig serializes", "module stack_module" in sig_file)
    ok("Stack sig has class", "class Stack" in sig_file)
    reparsed_stack = SignatureFileParser().parse(sig_file)
    ok("Stack sig roundtrips", "Stack" in reparsed_stack.classes)
    ok("Stack roundtrip methods",
       "push" in reparsed_stack.classes["Stack"].methods)

    # 5. JSON round-trip
    stack_json = stack_sig.to_json()
    stack_from_json = ModuleSignature.from_json(stack_json)
    ok("Stack JSON roundtrip", stack_from_json.name == "stack_module")
    ok("Stack JSON version", stack_from_json.version == "1.0")

    # ── Summary ──────────────────────────────────────────────────
    print(f"\n{'=' * 60}")
    total = passed + failed
    print(f"Results: {passed}/{total} passed, {failed} failed")
    if failed:
        raise SystemExit(1)
    print("All tests passed! ✅")


if __name__ == "__main__":
    _self_test()
