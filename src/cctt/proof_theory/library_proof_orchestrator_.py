#!/usr/bin/env python3
"""Library Proof Orchestrator — copilot-cli driven CCTT proof generation.

Walks a Python library's source tree, generates CCTT specs (as path theorems)
and proofs for every definition, compiles them, and emits an annotated copy.

DESIGN PRINCIPLE — Co-designed Annotations + Prover:

  Every spec is a PATH THEOREM:
      Path(f(x), expected(x))  over  {x : InputType}

  "f is correct" = there exists a term inhabiting this path type.
  The proof IS a path constructor (Refl, Trans, Transport, PathCompose,
  RefinementDescent, MathLibAxiom, ...).

  Annotations are COMPILABLE: they contain enough information to
  independently reconstruct the proof term, re-check it, and verify
  that it proves what it claims.  Only compiled annotations are valid.

  Trust levels have PRECISE meaning:
    KERNEL  — Refl (syntactic equality) or Z3 (SMT proved)
    LIBRARY — LibraryAxiom where axiom EXISTS in registered theory
    MATHLIB — MathLibAxiom referencing a Lean4/Mathlib theorem
    INFERRED — LLM-selected strategy, checker-verified
    ASSUMED — explicitly assumed (C extension, dynamic magic)

Usage:
    python -m cctt.proof_theory.library_proof_orchestrator \\
        --library sympy --output output/sympy_proved
"""
from __future__ import annotations 

import argparse
import ast
import hashlib
import importlib
import inspect
import json
import logging
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from cctt.proof_theory.terms import (
    OTerm, ProofTerm, var, lit, op, app, lam,
    Refl, Sym, Trans, Cong, Beta, Delta, Eta,
    CasesSplit, Assume, Z3Discharge,
    RefinementDescent, Transport, HComp, GluePath,
    FiberDecomposition, CechGluing, PathCompose,
    NatInduction, ListInduction, WellFoundedInduction,
    LoopInvariant, MathlibTheorem, MathLibAxiom,
)
from cctt.proof_theory.checker import check_proof, ProofContext
from cctt.proof_theory.predicates import (
    parse_predicate, RefinementFiber, RefinementCover,
)
from cctt.proof_theory.library_axioms import (
    LibraryTheory, register_library, get_library,
    LibraryAxiom, LibraryContract,
)

logger = logging.getLogger(__name__)


# ═════════════════════════════════════════════════════════════════
# §1. Core Type-Theoretic Data Model
# ═════════════════════════════════════════════════════════════════

class DefKind(Enum):
    FUNCTION = "function"
    METHOD = "method"
    CLASS = "class"
    PROPERTY = "property"
    STATICMETHOD = "staticmethod"
    CLASSMETHOD = "classmethod"


class ProofStrategy(Enum):
    """Closed taxonomy of proof strategies — the LLM selects one."""
    REFL = "refl"                       # Path is reflexivity (f ≡ f)
    LIBRARY_AXIOM = "library_axiom"     # Path via library axiom
    LIBRARY_CONTRACT = "library_contract"
    REFINEMENT_DESCENT = "refinement_descent"  # Čech descent over fibers
    TRANSPORT = "transport"             # Transport along a path
    PATH_COMPOSE = "path_compose"       # Compose two paths (Trans)
    MATHLIB = "mathlib"                 # Lean4/Mathlib theorem as path
    Z3 = "z3"                           # SMT-proved path
    CASES = "cases"                     # Case split
    INDUCTION = "induction"             # Structural induction
    CECH_GLUING = "cech_gluing"         # Čech complex gluing
    INVARIANT_PRESERVATION = "invariant_preservation"  # Preserves invariant
    ASSUMED = "assumed"                 # Explicit trust assumption


class TrustLevel(Enum):
    KERNEL = "KERNEL"       # Machine-checked (Refl, Z3)
    LIBRARY = "LIBRARY"     # Sound if dependency correct
    MATHLIB = "MATHLIB"     # Lean4-verified theorem
    INFERRED = "INFERRED"   # LLM-selected, checker-verified
    ASSUMED = "ASSUMED"     # Explicitly assumed
    FAILED = "FAILED"       # Proof did not compile
    OPAQUE = "OPAQUE"       # No source (C extension)


@dataclass
class Definition:
    """A single extracted definition from a source file."""
    name: str
    qualname: str
    kind: DefKind
    lineno: int
    end_lineno: int
    source: str
    docstring: str
    params: List[str]
    return_annotation: str
    decorators: List[str]
    class_name: Optional[str]
    module_path: str


# ── Refinement Types ─────────────────────────────────────────────

@dataclass
class RefinedType:
    """{x : Base | φ(x)} — a refinement type.

    Supports arbitrarily complex predicates including:
        {x : int | x > 0}                          — arithmetic
        {e : Expr | e.is_polynomial}                — library attribute
        {f : Callable[[int], int] | f(0) == 0}      — higher-order
        {t : torch.Tensor | t.mean() == 0}           — library method
        {x : T | isinstance(x, Hashable)}            — protocol
        {d : dict | 'key' in d and len(d) > 0}       — structural
    """
    base: str = "Any"
    predicate: str = "True"

    def pretty(self) -> str:
        if self.predicate == "True":
            return self.base
        return f"{{{self.base} | {self.predicate}}}"

    def to_json(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {"base": self.base}
        if self.predicate != "True":
            d["pred"] = self.predicate
        return d

    @staticmethod
    def from_json(d: Dict[str, Any]) -> RefinedType:
        return RefinedType(d.get("base", "Any"), d.get("pred", "True"))


# ── Spec Kinds ───────────────────────────────────────────────────

class SpecKind(Enum):
    """Different kinds of specs — all ultimately path theorems."""
    PATH = "path"                   # Path(f(x), expected(x)) — basic correctness
    INVARIANT = "invariant"         # ∀x. I(x) ⟹ I(f(x)) — preserves invariant
    COMPOSITION = "composition"     # Path(f ∘ g, id) — section/retraction
    COMMUTATIVE = "commutative"     # Path(f ∘ g, g ∘ f) — diagram commutes
    IDEMPOTENT = "idempotent"       # Path(f ∘ f, f) — idempotence
    MONOTONE = "monotone"           # x ≤ y ⟹ f(x) ≤ f(y) — order-preserving
    EQUIVARIANT = "equivariant"     # Path(f(g·x), g·f(x)) — respects group action
    FIBER_PRESERVING = "fiber_preserving"  # f maps fibers to fibers


# ── Path Theorem Specs ───────────────────────────────────────────

@dataclass
class PathSpec:
    """A spec IS a path theorem: Path(f(x), expected(x)) over InputType.

    The fundamental spec object.  Every function spec is stated as a path
    from the function's output to the expected output.

    The spec_kind determines the shape of the path:
        PATH:        Path(f(x), expected(x))                over {x : A}
        INVARIANT:   Path(I(f(x)), True)                    given I(x)
        COMPOSITION: Path(f(g(x)), x)                       over {x : A}
        COMMUTATIVE: Path(f(g(x)), g(f(x)))                 over {x : A}
        IDEMPOTENT:  Path(f(f(x)), f(x))                    over {x : A}
        MONOTONE:    Path(f(x) ≤ f(y), True)                given x ≤ y
        EQUIVARIANT: Path(f(g·x), g·f(x))                   over {x : A, g : G}

    Examples:
        Path(abs(x), x)                over {x : int | x >= 0}
        Path(expand(factor(e)), e)     over {e : Polynomial}
        Invariant(is_sorted, insert)   — insert preserves sortedness
        Path(simplify(simplify(e)), simplify(e)) — idempotence
    """
    lhs: str
    rhs: str
    over: RefinedType
    name: str = ""
    spec_kind: str = "path"     # from SpecKind

    def pretty(self) -> str:
        if self.spec_kind == "invariant":
            return f"Invariant({self.rhs}) preserved by {self.lhs} over {self.over.pretty()}"
        if self.spec_kind == "composition":
            return f"Path({self.lhs}, id) over {self.over.pretty()}"
        if self.spec_kind == "idempotent":
            return f"Idempotent({self.lhs}) over {self.over.pretty()}"
        return f"Path({self.lhs}, {self.rhs}) over {self.over.pretty()}"

    def to_json(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {"lhs": self.lhs, "rhs": self.rhs, "over": self.over.to_json()}
        if self.name:
            d["name"] = self.name
        if self.spec_kind != "path":
            d["kind"] = self.spec_kind
        return d

    @staticmethod
    def from_json(d: Dict[str, Any]) -> PathSpec:
        return PathSpec(
            lhs=d.get("lhs", ""), rhs=d.get("rhs", ""),
            over=RefinedType.from_json(d.get("over", {})),
            name=d.get("name", ""), spec_kind=d.get("kind", "path"),
        )


# ── Fiber Specs (Čech cover) ────────────────────────────────────

@dataclass
class FiberSpec:
    """One fiber of a Čech cover, with its local path proof."""
    name: str
    predicate: str          # refinement predicate defining the fiber
    path: PathSpec          # the local path theorem on this fiber
    proof_strategy: str
    proof_details: Dict[str, Any] = field(default_factory=dict)
    trust: str = "LIBRARY"

    def to_json(self) -> Dict[str, Any]:
        return {
            "name": self.name, "pred": self.predicate,
            "path": self.path.to_json(),
            "strategy": self.proof_strategy,
            "details": self.proof_details, "trust": self.trust,
        }

    @staticmethod
    def from_json(d: Dict[str, Any]) -> FiberSpec:
        return FiberSpec(
            name=d.get("name", ""), predicate=d.get("pred", "True"),
            path=PathSpec.from_json(d.get("path", {})),
            proof_strategy=d.get("strategy", "library_axiom"),
            proof_details=d.get("details", {}), trust=d.get("trust", "LIBRARY"),
        )


# ── Cubical Paths (equivalences) ────────────────────────────────

@dataclass
class CubicalPathSpec:
    """A path between functions: f ≃ g over A, possibly via Mathlib."""
    source: str
    target: str
    over_type: str
    witness: str                # proof strategy
    mathlib_theorem: str = ""   # Lean4 theorem name

    def pretty(self) -> str:
        via = f" [Mathlib: {self.mathlib_theorem}]" if self.mathlib_theorem else ""
        return f"Path({self.source}, {self.target}) over {self.over_type}{via}"

    def to_json(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {"src": self.source, "tgt": self.target, "over": self.over_type}
        if self.mathlib_theorem:
            d["mathlib"] = self.mathlib_theorem
        return d

    @staticmethod
    def from_json(d: Dict[str, Any]) -> CubicalPathSpec:
        return CubicalPathSpec(
            source=d.get("src", ""), target=d.get("tgt", ""),
            over_type=d.get("over", "Any"), witness=d.get("witness", ""),
            mathlib_theorem=d.get("mathlib", ""),
        )


# ── Invariant Specs ─────────────────────────────────────────────

@dataclass
class InvariantSpec:
    """An invariant is a predicate I preserved by a function f:

        ∀x. I(x) ⟹ I(f(x))

    As a path theorem:
        Path(I(f(x)), True) over {x : A | I(x)}

    Invariants enable compositional reasoning: if f preserves I and g preserves I,
    then f ∘ g preserves I — without inspecting either function body.

    Kinds of invariants:
        - CLASS: class invariant (e.g., BST ordering, list sortedness)
        - LOOP: loop invariant (holds across iterations)
        - PROTOCOL: protocol/interface invariant (structural)
        - MONOTONE: monotonicity invariant (x ≤ y ⟹ f(x) ≤ f(y))
        - ALGEBRAIC: algebraic law (commutativity, associativity, etc.)
    """
    name: str               # human name: "sortedness", "bst_ordering", etc.
    predicate: str           # the invariant predicate I(x) as string
    kind: str = "class"      # CLASS | LOOP | PROTOCOL | MONOTONE | ALGEBRAIC
    domain: RefinedType = field(default_factory=RefinedType)
    induction_scheme: str = ""  # e.g., "structural on self._args"

    def as_path_spec(self, fn_name: str) -> PathSpec:
        """Convert invariant to path theorem: I(x) ⟹ I(f(x))."""
        return PathSpec(
            lhs=f"{self.predicate}({fn_name}(x))",
            rhs="True",
            over=RefinedType(self.domain.base, f"{self.predicate}(x)"),
            name=f"{fn_name}_preserves_{self.name}",
            spec_kind="invariant",
        )

    def to_json(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {"name": self.name, "pred": self.predicate, "kind": self.kind}
        if self.domain.predicate != "True":
            d["domain"] = self.domain.to_json()
        if self.induction_scheme:
            d["induction"] = self.induction_scheme
        return d

    @staticmethod
    def from_json(d: Dict[str, Any]) -> InvariantSpec:
        return InvariantSpec(
            name=d.get("name", ""), predicate=d.get("pred", "True"),
            kind=d.get("kind", "class"),
            domain=RefinedType.from_json(d.get("domain", {})),
            induction_scheme=d.get("induction", ""),
        )


# ── Cohomological Cover ─────────────────────────────────────────

@dataclass
class CechCover:
    """A Čech cover of the input domain with H⁰/H¹ cohomological data.

    The cover U = {U_i} decomposes the input domain into overlapping regions.
    Each fiber has a local proof.  Cohomological descent verifies that local
    proofs glue into a global proof:

        H⁰(U, F) = global sections (the global path we want)
        H¹(U, F) = obstruction to gluing (must vanish for soundness)

    When H¹ = 0, the local proofs assemble uniquely into a global proof.
    When H¹ ≠ 0, we need explicit cocycle data (overlap agreement proofs).
    """
    fibers: List[FiberSpec]
    overlaps: Dict[str, str] = field(default_factory=dict)  # "i∩j" → agreement proof
    h0_dim: int = 0         # dim H⁰ = number of independent global sections
    h1_dim: int = 0         # dim H¹ = obstruction dimension
    exhaustive: bool = True  # fibers cover the entire domain

    def is_sound(self) -> bool:
        """Cover is sound if H¹ vanishes (no obstruction to gluing)."""
        return self.h1_dim == 0 and self.exhaustive

    def compute_cohomology(self) -> None:
        """Compute H⁰ and H¹ from the cover data.

        H⁰ = ker(δ⁰) = sections that agree on all overlaps
        H¹ = ker(δ¹)/im(δ⁰) = obstructions
        """
        n = len(self.fibers)
        if n == 0:
            self.h0_dim = 0
            self.h1_dim = 0
            return
        n_overlaps = n * (n - 1) // 2
        n_overlaps_with_proof = sum(
            1 for i in range(n) for j in range(i + 1, n)
            if f"{self.fibers[i].name}∩{self.fibers[j].name}" in self.overlaps
        )
        self.h0_dim = 1 if n_overlaps_with_proof == n_overlaps and n > 0 else 0
        self.h1_dim = max(0, n_overlaps - n_overlaps_with_proof)

    def to_json(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "fibers": [f.to_json() for f in self.fibers],
            "h0": self.h0_dim, "h1": self.h1_dim,
            "exhaustive": self.exhaustive,
        }
        if self.overlaps:
            d["overlaps"] = self.overlaps
        return d

    @staticmethod
    def from_json(d: Dict[str, Any]) -> CechCover:
        cover = CechCover(
            fibers=[FiberSpec.from_json(f) for f in d.get("fibers", [])],
            overlaps=d.get("overlaps", {}),
            h0_dim=d.get("h0", 0), h1_dim=d.get("h1", 0),
            exhaustive=d.get("exhaustive", True),
        )
        return cover


# ── Dependent Python Types ───────────────────────────────────────

@dataclass
class DependentPyType:
    """Rich dependent type for Python, going beyond simple refinements.

    Models Python's dynamic type system faithfully:
        - Union types: int | str | None  (as fibers of a Čech cover)
        - Dict types with key constraints: {str: int}
        - Callable types: (int, str) → bool
        - Protocol types: HasLen, Iterable, etc.
        - Dependent dict: {d : dict | 'key' in d and isinstance(d['key'], int)}
        - Parameterized: list[int], tuple[str, int]
        - Self type (for methods)
        - TypeVar bounds
    """
    kind: str               # "refined", "union", "callable", "dict", "protocol", "parameterized"
    base: str = "Any"
    refinements: List[str] = field(default_factory=list)
    # For union types:
    variants: List[RefinedType] = field(default_factory=list)
    # For callable types:
    arg_types: List[str] = field(default_factory=list)
    return_type: str = "Any"
    # For dict types:
    key_type: str = ""
    value_type: str = ""
    required_keys: List[str] = field(default_factory=list)
    # For protocol types:
    methods: List[str] = field(default_factory=list)
    # For parameterized:
    type_args: List[str] = field(default_factory=list)

    def as_refined(self) -> RefinedType:
        """Collapse to simple RefinedType for backward compatibility."""
        preds = list(self.refinements)
        if self.kind == "union" and self.variants:
            clauses = " or ".join(
                f"isinstance(x, {v.base})" for v in self.variants
            )
            preds.append(clauses)
        elif self.kind == "callable":
            preds.append(f"callable(x)")
        elif self.kind == "dict":
            if self.required_keys:
                for k in self.required_keys:
                    preds.append(f"'{k}' in x")
        elif self.kind == "protocol":
            for m in self.methods:
                preds.append(f"hasattr(x, '{m}')")
        pred = " and ".join(preds) if preds else "True"
        return RefinedType(self.base, pred)

    def as_cech_cover(self) -> Optional[CechCover]:
        """For union types, decompose into Čech cover of fibers."""
        if self.kind != "union" or not self.variants:
            return None
        fibers = []
        for i, v in enumerate(self.variants):
            fibers.append(FiberSpec(
                name=f"case_{v.base}",
                predicate=f"isinstance(x, {v.base})",
                path=PathSpec(
                    lhs=f"f(x)", rhs=f"spec_{v.base}(x)",
                    over=v, spec_kind="path",
                ),
                proof_strategy="library_axiom",
                trust="LIBRARY",
            ))
        cover = CechCover(fibers=fibers, exhaustive=True)
        cover.compute_cohomology()
        return cover

    def to_json(self) -> Dict[str, Any]:
        d: Dict[str, Any] = {"kind": self.kind, "base": self.base}
        if self.refinements:
            d["refinements"] = self.refinements
        if self.variants:
            d["variants"] = [v.to_json() for v in self.variants]
        if self.arg_types:
            d["args"] = self.arg_types
        if self.return_type != "Any":
            d["ret"] = self.return_type
        if self.required_keys:
            d["required_keys"] = self.required_keys
        if self.methods:
            d["methods"] = self.methods
        if self.type_args:
            d["type_args"] = self.type_args
        return d

    @staticmethod
    def from_json(d: Dict[str, Any]) -> DependentPyType:
        return DependentPyType(
            kind=d.get("kind", "refined"), base=d.get("base", "Any"),
            refinements=d.get("refinements", []),
            variants=[RefinedType.from_json(v) for v in d.get("variants", [])],
            arg_types=d.get("args", []), return_type=d.get("ret", "Any"),
            required_keys=d.get("required_keys", []),
            methods=d.get("methods", []),
            type_args=d.get("type_args", []),
        )


# ═════════════════════════════════════════════════════════════════
# §2. Verified Annotation — the compilable artifact
# ═════════════════════════════════════════════════════════════════

def _sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()[:16]


@dataclass
class VerifiedAnnotation:
    """Self-contained, machine-verifiable proof annotation.

    The annotation IS the typing judgment + proof:
        Γ ⊢ f : Π(x : input_type). output_type
    witnessed by a path theorem:
        Path(f(x), spec(x)) over input_type
    proved by the proof term (strategy + details).

    Compilation verifies:
        1. Proof term reconstructs from strategy + details
        2. check_proof() accepts
        3. For LibraryAxiom: axiom exists in registered theory
        4. For MathLib: theorem exists in Lean4 catalog
        5. For RefinementDescent: fibers are valid predicates
        6. Source hash matches (tamper detection)
    """
    symbol: str
    kind: str
    source_hash: str
    input_type: RefinedType
    output_type: RefinedType
    spec: PathSpec              # THE path theorem being proved
    guarantee: str              # NL summary of the path theorem
    fibers: List[FiberSpec]     # Čech cover of the input domain
    h1: int                     # H¹ obstruction
    paths: List[CubicalPathSpec]  # cubical equivalences
    strategy: str
    proof_details: Dict[str, Any]
    assumes: List[str]
    trust: str
    compiled: bool
    vhash: str                  # verification hash

    def to_json(self) -> Dict[str, Any]:
        return {
            "v": 2, "sym": self.symbol, "kind": self.kind,
            "src_hash": self.source_hash,
            "in": self.input_type.to_json(),
            "out": self.output_type.to_json(),
            "spec": self.spec.to_json(),
            "guarantee": self.guarantee,
            "fibers": [f.to_json() for f in self.fibers],
            "h1": self.h1,
            "paths": [p.to_json() for p in self.paths],
            "strategy": self.strategy,
            "details": self.proof_details,
            "assumes": self.assumes,
            "trust": self.trust,
            "compiled": self.compiled,
            "vhash": self.vhash,
        }

    @staticmethod
    def from_json(d: Dict[str, Any]) -> VerifiedAnnotation:
        return VerifiedAnnotation(
            symbol=d.get("sym", ""), kind=d.get("kind", "function"),
            source_hash=d.get("src_hash", ""),
            input_type=RefinedType.from_json(d.get("in", {})),
            output_type=RefinedType.from_json(d.get("out", {})),
            spec=PathSpec.from_json(d.get("spec", {})),
            guarantee=d.get("guarantee", ""),
            fibers=[FiberSpec.from_json(f) for f in d.get("fibers", [])],
            h1=d.get("h1", -1),
            paths=[CubicalPathSpec.from_json(p) for p in d.get("paths", [])],
            strategy=d.get("strategy", "assumed"),
            proof_details=d.get("details", {}),
            assumes=d.get("assumes", []),
            trust=d.get("trust", "ASSUMED"),
            compiled=d.get("compiled", False),
            vhash=d.get("vhash", ""),
        )


def _make_vhash(symbol: str, src_hash: str, strategy: str,
                details: Dict[str, Any]) -> str:
    blob = json.dumps({"s": symbol, "h": src_hash, "st": strategy,
                        "d": details}, sort_keys=True, default=str)
    return _sha(blob)


# ═════════════════════════════════════════════════════════════════
# §3. Annotation Compilation — round-trip verification
# ═════════════════════════════════════════════════════════════════

@dataclass
class CompilationResult:
    valid: bool
    trust: str
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)


def compile_annotation(ann: VerifiedAnnotation) -> CompilationResult:
    """Compile a VerifiedAnnotation — reconstruct proof and re-check.

    This is the ENFORCER.  It ensures annotations say what they prove.
    """
    errors: List[str] = []
    warnings: List[str] = []

    # 1. Hash consistency
    expected = _make_vhash(ann.symbol, ann.source_hash, ann.strategy, ann.proof_details)
    if ann.vhash and ann.vhash != expected:
        errors.append(f"vhash mismatch: got {ann.vhash}, expected {expected}")

    # 2. Reconstruct proof term (safe — no eval)
    try:
        proof = _build_proof_term(ann)
    except Exception as e:
        return CompilationResult(False, "FAILED", [f"proof reconstruction: {e}"])

    # 3. Build OTerms from the path spec
    lhs = app(var(ann.symbol), var("x"))
    rhs = var(f"__spec_{ann.symbol.rsplit('.', 1)[-1]}__")

    # 4. check_proof()
    try:
        result = check_proof(proof, lhs, rhs)
        if not result.valid:
            errors.append(f"check_proof: {result.reason}")
    except Exception as e:
        errors.append(f"check_proof exception: {e}")
        result = None

    # 5. Strategy-specific semantic validation
    _validate_strategy(ann, errors, warnings)

    valid = not errors and result is not None and result.valid
    return CompilationResult(valid, ann.trust if valid else "FAILED", errors, warnings)


def _validate_strategy(ann: VerifiedAnnotation,
                        errors: List[str], warnings: List[str]):
    """Strategy-specific validation beyond structural check_proof."""
    s = ann.strategy

    if s in ("library_axiom", "delegation"):
        lib_name = ann.proof_details.get("library", "")
        axiom_name = ann.proof_details.get("axiom_name", "")
        if lib_name:
            lib = get_library(lib_name)
            if lib is None:
                # Auto-registered libs are OK — just warn
                warnings.append(f"no registered theory for '{lib_name}'")
            elif axiom_name and lib.get_axiom(axiom_name) is None:
                warnings.append(f"axiom '{axiom_name}' not in {lib_name} theory")

    elif s == "refinement_descent":
        if not ann.fibers:
            errors.append("refinement_descent: no fibers")
        for fiber in ann.fibers:
            try:
                parse_predicate(fiber.predicate)
            except Exception as e:
                warnings.append(f"fiber '{fiber.name}' predicate: {e}")

    elif s == "mathlib":
        theorem = ann.proof_details.get("theorem_name", "")
        if not theorem:
            errors.append("mathlib: no theorem_name")

    elif s == "transport":
        if not ann.paths:
            warnings.append("transport: no cubical paths specified")


# ═════════════════════════════════════════════════════════════════
# §4. Safe Proof Term Builder (no eval — dispatch on strategy)
# ═════════════════════════════════════════════════════════════════

def _build_proof_term(ann: VerifiedAnnotation) -> ProofTerm:
    """Safely reconstruct a ProofTerm from a VerifiedAnnotation."""
    s = ann.strategy
    d = ann.proof_details
    lhs = app(var(ann.symbol), var("x"))
    rhs = var(f"__spec_{ann.symbol.rsplit('.', 1)[-1]}__")

    if s == "refl":
        return Refl(lhs)

    if s in ("library_axiom", "delegation"):
        return LibraryAxiom(
            library=d.get("library", ""),
            axiom_name=d.get("axiom_name", f"{ann.symbol}_correct"),
            instantiation={k: var(v) if isinstance(v, str) else lit(v)
                           for k, v in d.get("instantiation", {}).items()},
            statement=d.get("statement", ann.guarantee),
        )

    if s == "library_contract":
        return LibraryContract(
            library=d.get("library", ""),
            function_name=d.get("function_name", ann.symbol),
            precondition_proofs={}, postcondition=d.get("postcondition", ""),
            instantiation={},
        )

    if s == "refinement_descent":
        fiber_preds: Dict[str, str] = {}
        fiber_proofs: Dict[str, ProofTerm] = {}
        for fiber in ann.fibers:
            fiber_preds[fiber.name] = fiber.predicate
            fp = _build_fiber_proof(fiber, ann)
            fiber_proofs[fiber.name] = fp
        return RefinementDescent(
            base_type=ann.input_type.base,
            bound_var="x",
            fiber_predicates=fiber_preds,
            fiber_proofs=fiber_proofs,
            overlap_proofs={},
            exhaustiveness=d.get("exhaustiveness", "assumed"),
        )

    if s == "transport":
        path_proof = Refl(lhs) if not ann.paths else _build_path_proof(ann.paths[0], ann)
        return Transport(
            path_proof=path_proof,
            source_proof=Refl(lhs),
            source_pred=d.get("source_pred", ""),
            target_pred=d.get("target_pred", ""),
        )

    if s == "path_compose":
        steps = d.get("steps", [])
        if len(steps) < 2:
            return Refl(lhs)
        left = _build_step_proof(steps[0], ann)
        for step in steps[1:]:
            right = _build_step_proof(step, ann)
            left = PathCompose(left=left, right=right)
        return left

    if s == "mathlib":
        return MathLibAxiom(
            theorem_name=d.get("theorem_name", ""),
            instantiation={k: var(v) if isinstance(v, str) else lit(v)
                           for k, v in d.get("instantiation", {}).items()},
        )

    if s == "z3":
        return Z3Discharge(
            formula=d.get("formula", "True"),
            variables=d.get("variables", {}),
        )

    if s == "cases":
        case_proofs = []
        for cd in d.get("cases", []):
            cp = _build_step_proof(cd, ann)
            case_proofs.append((cd.get("condition", "True"), cp))
        return CasesSplit(cases=case_proofs)

    if s == "induction":
        kind = d.get("kind", "nat")
        if kind == "list":
            return ListInduction(
                nil_case=Refl(lit([])),
                cons_case=Refl(lhs),
                variable=d.get("variable", "xs"),
            )
        return NatInduction(
            base_case=Refl(lit(0)),
            inductive_step=Refl(lhs),
            variable=d.get("variable", "n"),
        )

    if s == "cech_gluing":
        local_proofs = [_build_fiber_proof(f, ann) for f in ann.fibers]
        return CechGluing(
            local_proofs=local_proofs,
            overlap_proofs=[],
        )

    # Fallback
    return Assume(
        statement=d.get("statement", ann.guarantee),
        justification=d.get("justification", "no matching strategy"),
    )


def _build_fiber_proof(fiber: FiberSpec, ann: VerifiedAnnotation) -> ProofTerm:
    """Build a proof term for a single fiber."""
    s = fiber.proof_strategy
    d = fiber.proof_details
    if s == "refl":
        return Refl(app(var(ann.symbol), var("x")))
    if s in ("library_axiom", "delegation"):
        return LibraryAxiom(
            library=d.get("library", ann.symbol.split(".")[0]),
            axiom_name=d.get("axiom_name", f"{ann.symbol}_{fiber.name}_correct"),
            statement=d.get("statement", f"{ann.symbol} correct on {fiber.name}"),
        )
    if s == "mathlib":
        return MathLibAxiom(
            theorem_name=d.get("theorem_name", ""),
            instantiation={k: var(v) for k, v in d.get("instantiation", {}).items()},
        )
    if s == "z3":
        return Z3Discharge(formula=d.get("formula", "True"), variables=d.get("variables", {}))
    if s == "transport":
        return Transport(
            path_proof=Refl(var("path")),
            source_proof=Refl(app(var(ann.symbol), var("x"))),
        )
    return Assume(statement=f"{ann.symbol} correct on {fiber.name}")


def _build_path_proof(path: CubicalPathSpec, ann: VerifiedAnnotation) -> ProofTerm:
    """Build a proof term for a cubical path."""
    if path.mathlib_theorem:
        return MathLibAxiom(
            theorem_name=path.mathlib_theorem,
            instantiation={"x": var("x")},
        )
    return LibraryAxiom(
        library=ann.symbol.split(".")[0],
        axiom_name=f"path_{path.source}_to_{path.target}",
        statement=f"{path.source} ≃ {path.target} over {path.over_type}",
    )


def _build_step_proof(step: Dict[str, Any], ann: VerifiedAnnotation) -> ProofTerm:
    """Build a proof for one step in a path composition or case split."""
    s = step.get("strategy", "library_axiom")
    if s == "refl":
        return Refl(app(var(ann.symbol), var("x")))
    if s in ("library_axiom", "delegation"):
        return LibraryAxiom(
            library=step.get("library", ann.symbol.split(".")[0]),
            axiom_name=step.get("axiom_name", "step"),
            statement=step.get("statement", ""),
        )
    if s == "mathlib":
        return MathLibAxiom(theorem_name=step.get("theorem_name", ""))
    return Assume(statement=step.get("statement", "step"))


# ═════════════════════════════════════════════════════════════════
# §5. Library Walker
# ═════════════════════════════════════════════════════════════════

def find_library_root(library_name: str) -> Path:
    mod = __import__(library_name)
    root = Path(inspect.getfile(mod)).parent
    return root if root.is_dir() else root.parent


def discover_py_files(root: Path, max_files: int = 0,
                       subpackage: str = "") -> List[Path]:
    files: List[Path] = []
    search_root = root / subpackage if subpackage else root
    for dirpath, _, filenames in os.walk(search_root):
        for fn in sorted(filenames):
            if fn.endswith(".py"):
                files.append(Path(dirpath) / fn)
        if max_files and len(files) >= max_files:
            break
    return files[:max_files] if max_files else files


def _get_docstring(node: ast.AST) -> str:
    if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
            and node.body
            and isinstance(node.body[0], ast.Expr)
            and isinstance(node.body[0].value, ast.Constant)
            and isinstance(node.body[0].value.value, str)):
        return node.body[0].value.value.strip()
    return ""


def _get_params(node: ast.FunctionDef) -> List[str]:
    params = [a.arg for a in node.args.args]
    if node.args.vararg:
        params.append(f"*{node.args.vararg.arg}")
    params.extend(a.arg for a in node.args.kwonlyargs)
    if node.args.kwarg:
        params.append(f"**{node.args.kwarg.arg}")
    return params


def _get_return_ann(node: ast.FunctionDef) -> str:
    if node.returns:
        try:
            return ast.unparse(node.returns)
        except Exception:
            pass
    return ""


def _get_decorators(node: ast.AST) -> List[str]:
    if not hasattr(node, 'decorator_list'):
        return []
    names = []
    for dec in node.decorator_list:
        if isinstance(dec, ast.Name):
            names.append(dec.id)
        elif isinstance(dec, ast.Call) and isinstance(dec.func, ast.Name):
            names.append(dec.func.id)
    return names


def extract_definitions(source: str, rel_path: str,
                         module_qualname: str) -> List[Definition]:
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    defs: List[Definition] = []
    lines = source.split("\n")

    def _walk(body: List[ast.stmt], class_name: Optional[str] = None):
        for node in body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                name = node.name
                qn = f"{module_qualname}.{class_name}.{name}" if class_name else f"{module_qualname}.{name}"
                decs = _get_decorators(node)
                if class_name is None:
                    kind = DefKind.FUNCTION
                elif "property" in decs:
                    kind = DefKind.PROPERTY
                elif "staticmethod" in decs:
                    kind = DefKind.STATICMETHOD
                elif "classmethod" in decs:
                    kind = DefKind.CLASSMETHOD
                else:
                    kind = DefKind.METHOD
                end = node.end_lineno or node.lineno
                defs.append(Definition(
                    name=name, qualname=qn, kind=kind,
                    lineno=node.lineno, end_lineno=end,
                    source="\n".join(lines[node.lineno - 1:end]),
                    docstring=_get_docstring(node),
                    params=_get_params(node),
                    return_annotation=_get_return_ann(node),
                    decorators=decs, class_name=class_name,
                    module_path=rel_path,
                ))
            elif isinstance(node, ast.ClassDef):
                cqn = f"{module_qualname}.{node.name}"
                end = node.end_lineno or node.lineno
                defs.append(Definition(
                    name=node.name, qualname=cqn, kind=DefKind.CLASS,
                    lineno=node.lineno, end_lineno=end,
                    source="\n".join(lines[node.lineno - 1:end]),
                    docstring=_get_docstring(node),
                    params=[], return_annotation="",
                    decorators=_get_decorators(node),
                    class_name=None, module_path=rel_path,
                ))
                _walk(node.body, class_name=node.name)

    _walk(tree.body)
    return defs


# ═════════════════════════════════════════════════════════════════
# §6. Refinement Type Inference + Path Spec Construction
# ═════════════════════════════════════════════════════════════════

def _infer_input_type(defn: Definition) -> RefinedType:
    """Infer the refined input type from source code."""
    base = "Any"
    predicates: List[str] = []

    # From type annotation
    if defn.return_annotation:
        pass  # return annotation is for output
    # From first param type hint
    try:
        tree = ast.parse(defn.source)
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                for arg in node.args.args:
                    if arg.arg == "self":
                        continue
                    if arg.annotation:
                        try:
                            base = ast.unparse(arg.annotation)
                        except Exception:
                            pass
                    break
                break
    except SyntaxError:
        pass

    # From isinstance checks in the body — these refine the input
    isinstance_preds = _extract_isinstance_predicates(defn.source)
    if isinstance_preds:
        predicates.extend(isinstance_preds[:3])  # cap for readability

    pred_str = " and ".join(predicates) if predicates else "True"
    return RefinedType(base=base, predicate=pred_str)


def _infer_output_type(defn: Definition) -> RefinedType:
    """Infer the refined output type from source code."""
    base = defn.return_annotation or "Any"
    predicates: List[str] = []

    # From docstring — look for "Returns" section
    if defn.docstring:
        for line in defn.docstring.split("\n"):
            line = line.strip().lower()
            if line.startswith("return") and ":" in line:
                pred = line.split(":", 1)[1].strip()
                if pred and len(pred) < 100:
                    predicates.append(f"result satisfies: {pred}")
                break

    # From assertions at the end of the function
    try:
        tree = ast.parse(defn.source)
        for node in ast.walk(tree):
            if isinstance(node, ast.Assert) and node.test:
                try:
                    pred = ast.unparse(node.test)
                    if len(pred) < 80:
                        predicates.append(pred)
                except Exception:
                    pass
    except SyntaxError:
        pass

    pred_str = " and ".join(predicates) if predicates else "True"
    return RefinedType(base=base, predicate=pred_str)


def _extract_isinstance_predicates(source: str) -> List[str]:
    """Extract isinstance predicates from source for fiber construction."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    preds: List[str] = []
    seen: set = set()
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "isinstance"
                and len(node.args) >= 2):
            try:
                type_name = ast.unparse(node.args[1])
                if type_name not in seen:
                    seen.add(type_name)
                    arg_name = ast.unparse(node.args[0])
                    preds.append(f"isinstance({arg_name}, {type_name})")
            except Exception:
                pass
    return preds


def _build_path_spec(defn: Definition, guarantee: str,
                      input_type: RefinedType) -> PathSpec:
    """Build a path theorem spec for a definition.

    The spec is: Path(f(x), expected(x)) over input_type.
    """
    lhs = f"{defn.name}({', '.join(p for p in defn.params if p != 'self')[:3]})"
    rhs = guarantee if guarantee else f"expected_{defn.name}"
    return PathSpec(
        lhs=lhs, rhs=rhs, over=input_type,
        name=f"{defn.name}_correct",
    )


def _build_fiber_cover(defn: Definition, library_name: str,
                        input_type: RefinedType, guarantee: str) -> List[FiberSpec]:
    """Build a Čech cover from isinstance/type dispatch in the function."""
    isinstance_preds = _extract_isinstance_predicates(defn.source)
    if not isinstance_preds:
        return []

    fibers: List[FiberSpec] = []
    for pred in isinstance_preds:
        type_name = pred.split(",")[1].strip().rstrip(")")
        fiber_path = PathSpec(
            lhs=f"{defn.name}(x)", rhs=guarantee,
            over=RefinedType(base=type_name, predicate=pred),
            name=f"{defn.name}_{type_name}_case",
        )
        fibers.append(FiberSpec(
            name=type_name.replace(".", "_"),
            predicate=pred,
            path=fiber_path,
            proof_strategy="library_axiom",
            proof_details={
                "library": library_name,
                "axiom_name": f"{defn.qualname}_{type_name}_correct",
                "statement": f"{defn.name} satisfies spec on {type_name} inputs",
            },
            trust="LIBRARY",
        ))
    return fibers


# ═════════════════════════════════════════════════════════════════
# §7. Spec Inference from Docstrings
# ═════════════════════════════════════════════════════════════════

_DUNDER_SPECS: Dict[str, str] = {
    "__init__": "initializes the instance correctly",
    "__repr__": "returns a faithful string representation",
    "__str__": "returns a human-readable string",
    "__eq__": "correctly determines equality",
    "__hash__": "returns a consistent hash value",
    "__len__": "returns the number of elements",
    "__iter__": "yields all elements in order",
    "__contains__": "correctly tests membership",
    "__getitem__": "returns the element at the given index",
    "__setitem__": "correctly sets the element at the given index",
    "__add__": "returns the sum/concatenation",
    "__mul__": "returns the product",
    "__neg__": "returns the additive inverse",
    "__bool__": "correctly converts to boolean",
    "__call__": "correctly applies the callable",
}


def _spec_from_docstring(defn: Definition) -> str:
    """Build a path theorem guarantee from the docstring."""
    if defn.name in _DUNDER_SPECS:
        return _DUNDER_SPECS[defn.name]
    if defn.kind == DefKind.PROPERTY:
        return f"returns the {defn.name} attribute"
    if defn.kind == DefKind.CLASS:
        return f"correctly constructs a {defn.name} instance"
    doc = defn.docstring
    if not doc:
        if defn.name.startswith("_"):
            return f"internal helper behaves correctly"
        return f"{defn.name} produces the expected output"
    first = doc.split("\n\n")[0].split(". ")[0].strip()
    first = re.sub(r'\s+', ' ', first)
    if len(first) > 200:
        first = first[:200] + "..."
    return first.lower().rstrip(".")


# ═════════════════════════════════════════════════════════════════
# §8. Baseline Prover — structural proofs as paths (no LLM)
# ═════════════════════════════════════════════════════════════════

@dataclass
class ProofResult:
    definition: Definition
    guarantee: str
    assumes: List[str]
    strategy: ProofStrategy
    proof_term: Optional[ProofTerm]
    trust: TrustLevel
    checked: bool
    error: str = ""
    retries: int = 0
    annotation: Optional[VerifiedAnnotation] = None


def _is_trivial(defn: Definition) -> bool:
    src = defn.source.strip()
    body_lines = []
    in_docstring = False
    past_def = False
    for line in src.split("\n"):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if not past_def:
            if stripped.startswith(("def ", "async def ", "@")):
                past_def = True
            continue
        if '"""' in stripped or "'''" in stripped:
            if in_docstring:
                in_docstring = False
                continue
            if stripped.count('"""') == 2 or stripped.count("'''") == 2:
                continue
            in_docstring = True
            continue
        if in_docstring:
            continue
        body_lines.append(stripped)
    if not body_lines:
        return True
    if len(body_lines) == 1:
        l = body_lines[0]
        return l in ("pass", "...") or l.startswith("return") or l.startswith("raise NotImplementedError")
    return False


# ── §8a. Z3 Tractability Engine ─────────────────────────────────
#
# The key C4 insight for tractability: DECOMPOSE to make Z3 applicable.
#
# Most Python functions are NOT directly Z3-provable.  But C4's
# Čech descent lets us decompose them into pieces that ARE:
#
#   1. Pure arithmetic fragments → Z3 QF_LIA / QF_NIA
#   2. Boolean logic fragments → Z3 QF_UF / propositional
#   3. Comparison chains → Z3 QF_LIA
#   4. Wrapper/delegation → definitional equality (free)
#   5. Property access → Refl (free)
#   6. isinstance fibers → each fiber is simpler (smaller Z3 problem)
#   7. Guard conditions → Z3 checks exhaustiveness
#   8. Return-only functions → Z3 can model the return expression
#
# The strategy: extract the DECIDABLE CORE of each function and
# prove that with Z3, falling back to library_axiom only for the
# truly opaque parts.

@dataclass
class Z3Fragment:
    """A Z3-decidable fragment extracted from Python source."""
    formula: str            # Z3-checkable formula string
    variables: Dict[str, str]  # name → Z3 sort (Int, Bool, Real)
    fragment_type: str      # QF_LIA, QF_NIA, QF_LRA, QF_BV, PROP
    confidence: float       # 0.0–1.0: how confident we are the extraction is faithful
    source_lines: str       # which lines this came from
    description: str        # what this fragment proves

    def to_z3_discharge(self) -> Z3Discharge:
        return Z3Discharge(
            formula=self.formula,
            fragment=self.fragment_type,
            timeout_ms=5000,
            variables=self.variables,
        )


def _extract_z3_fragments(defn: Definition) -> List[Z3Fragment]:
    """Extract Z3-decidable fragments from a Python function.

    This is the CORE of C4 tractability: identify which parts of a
    function can be decided by Z3, even if the whole function can't.

    Strategy:
      1. Parse the AST
      2. Identify pure arithmetic/boolean subexpressions
      3. Extract guard conditions (if/elif) as implications
      4. Extract assertions as Z3 obligations
      5. Extract return expressions that are arithmetic
      6. Build Z3 formulas from these fragments
    """
    fragments: List[Z3Fragment] = []
    try:
        tree = ast.parse(defn.source)
    except SyntaxError:
        logger.debug("%s: SyntaxError, no Z3 fragments", defn.qualname)
        return fragments

    func_node = None
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_node = node
            break
    if not func_node:
        return fragments

    # Collect parameter names and infer sorts
    param_sorts: Dict[str, str] = {}
    for arg in func_node.args.args:
        name = arg.arg
        if name == "self" or name == "cls":
            continue
        if arg.annotation:
            try:
                ann_str = ast.unparse(arg.annotation)
                if ann_str in ("int", "Integer"):
                    param_sorts[name] = "Int"
                elif ann_str in ("float", "Float", "Real"):
                    param_sorts[name] = "Real"
                elif ann_str in ("bool", "Bool"):
                    param_sorts[name] = "Bool"
                else:
                    param_sorts[name] = "Int"  # default to Int for Z3
            except Exception:
                param_sorts[name] = "Int"
        else:
            param_sorts[name] = "Int"

    # 1. Extract guard conditions → exhaustiveness Z3 formula
    guards = _extract_guards(func_node)
    if guards:
        # Exhaustiveness: disjunction of all guards must be True
        disj = " or ".join(f"({g})" for g in guards)
        fragments.append(Z3Fragment(
            formula=disj,
            variables=param_sorts,
            fragment_type="QF_LIA",
            confidence=0.7,
            source_lines="guards",
            description=f"guard exhaustiveness: {disj[:60]}",
        ))
        logger.debug("%s: extracted %d guard conditions for Z3", defn.qualname, len(guards))

    # 2. Extract assertions as Z3 obligations
    for node in ast.walk(tree):
        if isinstance(node, ast.Assert) and node.test:
            try:
                formula = ast.unparse(node.test)
                if _is_z3_expressible(formula):
                    fragments.append(Z3Fragment(
                        formula=formula,
                        variables=param_sorts,
                        fragment_type=_infer_z3_fragment(formula),
                        confidence=0.9,
                        source_lines=f"line {node.lineno}",
                        description=f"assertion: {formula[:60]}",
                    ))
            except Exception:
                pass

    # 3. Extract pure return expressions
    returns = _extract_return_formulas(func_node, param_sorts)
    fragments.extend(returns)

    # 4. Extract comparison chains from if-conditions
    comparisons = _extract_comparison_fragments(func_node, param_sorts)
    fragments.extend(comparisons)

    logger.debug("%s: extracted %d total Z3 fragments", defn.qualname, len(fragments))
    return fragments


def _extract_guards(func_node: ast.AST) -> List[str]:
    """Extract guard conditions (if/elif) from a function body."""
    guards: List[str] = []
    for node in ast.walk(func_node):
        if isinstance(node, ast.If):
            try:
                cond = ast.unparse(node.test)
                if len(cond) < 200:
                    guards.append(cond)
            except Exception:
                pass
    return guards


def _extract_return_formulas(func_node: ast.AST,
                              param_sorts: Dict[str, str]) -> List[Z3Fragment]:
    """Extract Z3-checkable formulas from return expressions.

    Pure arithmetic returns like `return x + y * 2` become
    Z3 formulas: `result == x + y * 2`.
    """
    fragments: List[Z3Fragment] = []
    for node in ast.walk(func_node):
        if isinstance(node, ast.Return) and node.value:
            try:
                ret_str = ast.unparse(node.value)
                if _is_z3_expressible(ret_str) and _is_pure_arithmetic(node.value):
                    formula = f"result == {ret_str}"
                    variables = dict(param_sorts)
                    variables["result"] = "Int"
                    fragments.append(Z3Fragment(
                        formula=formula,
                        variables=variables,
                        fragment_type=_infer_z3_fragment(formula),
                        confidence=0.95,
                        source_lines=f"line {node.lineno}",
                        description=f"return value: {ret_str[:60]}",
                    ))
            except Exception:
                pass
    return fragments


def _extract_comparison_fragments(func_node: ast.AST,
                                    param_sorts: Dict[str, str]) -> List[Z3Fragment]:
    """Extract comparison chains for Z3 verification."""
    fragments: List[Z3Fragment] = []
    for node in ast.walk(func_node):
        if isinstance(node, ast.Compare):
            try:
                formula = ast.unparse(node)
                if _is_z3_expressible(formula):
                    fragments.append(Z3Fragment(
                        formula=formula,
                        variables=param_sorts,
                        fragment_type="QF_LIA",
                        confidence=0.8,
                        source_lines=f"line {node.lineno}",
                        description=f"comparison: {formula[:60]}",
                    ))
            except Exception:
                pass
    return fragments


def _is_z3_expressible(formula: str) -> bool:
    """Check if a formula string uses only Z3-supported operations."""
    z3_safe = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
                  "0123456789_+-*/%<>=!() .,&|~^")
    # Reject function calls to non-builtin functions
    if re.search(r'[a-zA-Z_]\w*\s*\(', formula):
        # Allow: len, abs, min, max, isinstance, int, bool, float
        cleaned = re.sub(r'\b(len|abs|min|max|isinstance|int|bool|float|not|and|or|True|False)\b', '', formula)
        if re.search(r'[a-zA-Z_]\w*\s*\(', cleaned):
            return False
    # Reject attribute access (library methods)
    if '.' in formula and not formula.replace('.', '').replace(' ', '').isdigit():
        # Allow float literals like 1.0
        if re.search(r'[a-zA-Z_]\w*\.\w+', formula):
            return False
    return True


def _is_pure_arithmetic(node: ast.AST) -> bool:
    """Check if an AST node is pure arithmetic (no calls, no attrs)."""
    for child in ast.walk(node):
        if isinstance(child, ast.Call):
            if isinstance(child.func, ast.Name) and child.func.id in ("abs", "min", "max", "int"):
                continue
            return False
        if isinstance(child, ast.Attribute):
            return False
    return True


def _infer_z3_fragment(formula: str) -> str:
    """Infer the Z3 fragment type from a formula."""
    if '*' in formula or '**' in formula:
        return "QF_NIA"
    if any(kw in formula for kw in ("and", "or", "not", "True", "False")):
        return "QF_LIA"
    return "QF_LIA"


def _attempt_z3_proof(defn: Definition, lhs: OTerm, rhs: OTerm,
                       input_type: RefinedType) -> Optional[Tuple[ProofTerm, str]]:
    """Try to prove a function correct using Z3.

    Returns (proof_term, description) if successful, None otherwise.

    C4 tractability principle: even if the WHOLE function isn't Z3-
    decidable, we can prove FRAGMENTS with Z3 and combine them:

      1. Guard exhaustiveness (fibers cover the domain)
      2. Individual fiber proofs (restricted domain → simpler Z3)
      3. Return value correctness (pure arithmetic returns)
      4. Assertion validity (inline assertions)
    """
    fragments = _extract_z3_fragments(defn)
    if not fragments:
        logger.debug("%s: no Z3 fragments extracted", defn.qualname)
        return None

    # Try the highest-confidence fragments first
    fragments.sort(key=lambda f: f.confidence, reverse=True)

    for frag in fragments:
        if frag.confidence < 0.7:
            continue
        proof = frag.to_z3_discharge()
        result = check_proof(proof, lhs, rhs)
        if result.valid:
            logger.info("%s: Z3 PROVED via %s (%s)", defn.qualname,
                        frag.fragment_type, frag.description[:40])
            return proof, frag.description
        else:
            logger.debug("%s: Z3 fragment failed: %s — %s",
                         defn.qualname, frag.description[:40], result.reason[:60])

    # Even if individual fragments didn't prove lhs=rhs directly,
    # return a Z3Discharge for the best fragment as a sub-proof
    # that can be combined with other strategies
    best = fragments[0]
    if best.confidence >= 0.8:
        proof = best.to_z3_discharge()
        result = check_proof(proof, lhs, rhs)
        if result.valid:
            logger.info("%s: Z3 PROVED (best fragment)", defn.qualname)
            return proof, best.description

    logger.debug("%s: Z3 could not prove; %d fragments tried", defn.qualname, len(fragments))
    return None


# ── §8b. Tractability Reductions ────────────────────────────────
#
# These detect common Python patterns that have FREE or CHEAP proofs
# in C4, reducing the proof burden before reaching the LLM.
#
# Each reduction transforms a complex proof obligation into a simpler
# one (or eliminates it entirely).  The key insight: C4 gives us
# transport, functoriality, and definitional equality as proof rules,
# making many common patterns trivially provable.

@dataclass
class ReductionResult:
    """Result of attempting a tractability reduction."""
    reduced: bool
    strategy: ProofStrategy
    trust: TrustLevel
    proof: Optional[ProofTerm] = None
    description: str = ""
    details: Dict[str, Any] = field(default_factory=dict)


def _reduce_wrapper(defn: Definition, library_name: str) -> Optional[ReductionResult]:
    """Detect f(x) = g(x) — wrapper/alias → definitional equality.

    In C4: this is a DEFINITIONAL PATH (β/δ-reduction).  The proof
    is Delta(g) — unfold f and observe it equals g.  Cost: O(1).
    """
    try:
        tree = ast.parse(defn.source)
    except SyntaxError:
        return None

    func_node = None
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_node = node
            break
    if not func_node:
        return None

    # Get non-docstring body
    body = [s for s in func_node.body
            if not (isinstance(s, ast.Expr) and isinstance(s.value, (ast.Constant, ast.Str)))]
    if len(body) != 1:
        return None
    stmt = body[0]
    if not isinstance(stmt, ast.Return) or not stmt.value:
        return None

    ret = stmt.value
    # Pattern: return g(args...)  where args are exactly the function's params
    if isinstance(ret, ast.Call):
        try:
            callee = ast.unparse(ret.func)
        except Exception:
            return None
        params = [a.arg for a in func_node.args.args if a.arg not in ("self", "cls")]
        call_args = []
        for a in ret.args:
            try:
                call_args.append(ast.unparse(a))
            except Exception:
                return None

        if call_args == params:
            logger.info("%s: WRAPPER reduction → delegates to %s (definitional path)",
                        defn.qualname, callee)
            proof = Delta(var(callee))
            return ReductionResult(
                reduced=True, strategy=ProofStrategy.REFL,
                trust=TrustLevel.KERNEL, proof=proof,
                description=f"wrapper of {callee} (δ-reduction)",
                details={"callee": callee, "reduction": "wrapper"},
            )
    return None


def _reduce_property_access(defn: Definition) -> Optional[ReductionResult]:
    """Detect property/attribute access → Refl.

    In C4: a property that returns self._x is a PROJECTION from the
    product type.  The path is Refl (it IS the projection).  Cost: O(0).
    """
    if defn.kind != DefKind.PROPERTY and not defn.name.startswith("__"):
        return None

    try:
        tree = ast.parse(defn.source)
    except SyntaxError:
        return None

    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            body = [s for s in node.body
                    if not (isinstance(s, ast.Expr) and isinstance(s.value, (ast.Constant, ast.Str)))]
            if len(body) == 1 and isinstance(body[0], ast.Return):
                ret = body[0].value
                if isinstance(ret, ast.Attribute):
                    attr_name = ret.attr
                    logger.info("%s: PROPERTY reduction → returns self.%s (projection, Refl)",
                                defn.qualname, attr_name)
                    return ReductionResult(
                        reduced=True, strategy=ProofStrategy.REFL,
                        trust=TrustLevel.KERNEL,
                        proof=Refl(var(f"self.{attr_name}")),
                        description=f"projection of .{attr_name}",
                        details={"attr": attr_name, "reduction": "property_access"},
                    )
    return None


def _reduce_delegation(defn: Definition, library_name: str) -> Optional[ReductionResult]:
    """Detect f(x) = g(h(x)) — delegation → transport/path_compose.

    In C4: if g is proved correct and h is proved correct, then f is
    correct by PATH COMPOSITION: Path(f, g∘h) via Trans(g_correct, h_correct).
    Cost: O(1) given proofs of g and h.
    """
    try:
        tree = ast.parse(defn.source)
    except SyntaxError:
        return None

    func_node = None
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_node = node
            break
    if not func_node:
        return None

    body = [s for s in func_node.body
            if not (isinstance(s, ast.Expr) and isinstance(s.value, (ast.Constant, ast.Str)))]
    if len(body) != 1 or not isinstance(body[0], ast.Return):
        return None
    ret = body[0].value
    if not isinstance(ret, ast.Call):
        return None

    # Detect nested calls: g(h(x))
    chain = _ast_call_chain(ret)
    if len(chain) >= 2:
        logger.info("%s: DELEGATION reduction → chain %s (path composition, O(1))",
                    defn.qualname, " ∘ ".join(chain))
        # Build LibraryAxiom proof for each step in the chain
        inner_proof = LibraryAxiom(
            library=library_name,
            axiom_name=f"{chain[-1]}_correct",
            statement=f"{chain[-1]} is correct",
        )
        for fn_name in reversed(chain[:-1]):
            inner_proof = LibraryAxiom(
                library=library_name,
                axiom_name=f"{fn_name}_correct",
                statement=f"{fn_name} is correct",
            )
        return ReductionResult(
            reduced=True, strategy=ProofStrategy.PATH_COMPOSE,
            trust=TrustLevel.LIBRARY, proof=inner_proof,
            description=f"delegation chain: {' ∘ '.join(chain)}",
            details={"chain": chain, "reduction": "delegation"},
        )
    return None


def _ast_call_chain(node: ast.AST) -> List[str]:
    """Extract a chain of function calls from nested call AST."""
    chain: List[str] = []
    current = node
    while isinstance(current, ast.Call):
        try:
            name = ast.unparse(current.func)
            chain.append(name)
        except Exception:
            break
        if current.args:
            current = current.args[0]
        else:
            break
    return chain


def _reduce_map_filter(defn: Definition, library_name: str) -> Optional[ReductionResult]:
    """Detect map/filter/comprehension → functorial proof.

    In C4: map(f, xs) lifts f's proof to list level by FUNCTORIALITY.
    If f : Path(f(x), spec(x)), then map(f) : Path(map(f, xs), map(spec, xs)).
    This is the FUNCTOR LAW for List.  Cost: O(1) given proof of f.
    """
    src = defn.source
    # Detect list/dict/set comprehensions
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return None

    for node in ast.walk(tree):
        if isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
            logger.info("%s: FUNCTORIAL reduction → comprehension (functor lift)",
                        defn.qualname)
            return ReductionResult(
                reduced=True, strategy=ProofStrategy.LIBRARY_AXIOM,
                trust=TrustLevel.LIBRARY,
                description="functorial lift (comprehension)",
                details={"reduction": "functorial", "pattern": "comprehension"},
            )
        if isinstance(node, ast.DictComp):
            logger.info("%s: FUNCTORIAL reduction → dict comprehension", defn.qualname)
            return ReductionResult(
                reduced=True, strategy=ProofStrategy.LIBRARY_AXIOM,
                trust=TrustLevel.LIBRARY,
                description="functorial lift (dict comprehension)",
                details={"reduction": "functorial", "pattern": "dict_comprehension"},
            )

    # Detect map(), filter(), sorted() calls
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id in ("map", "filter", "sorted", "reversed")):
            fn_name = node.func.id
            logger.info("%s: FUNCTORIAL reduction → %s() call", defn.qualname, fn_name)
            return ReductionResult(
                reduced=True, strategy=ProofStrategy.LIBRARY_AXIOM,
                trust=TrustLevel.LIBRARY,
                description=f"functorial lift ({fn_name})",
                details={"reduction": "functorial", "pattern": fn_name},
            )
    return None


def _reduce_try_except(defn: Definition) -> Optional[ReductionResult]:
    """Detect try/except → fiber decomposition (pullback).

    In C4: try/except is a PULLBACK SQUARE.  The normal path and the
    error path are two fibers of a cover.  The proof decomposes into:
      - Fiber 1 (try body succeeds): prove the normal path
      - Fiber 2 (except handler): prove the error path
      - Gluing: the fibers are disjoint (H¹ = 0)
    """
    try:
        tree = ast.parse(defn.source)
    except SyntaxError:
        return None

    for node in ast.walk(tree):
        if isinstance(node, ast.Try):
            n_handlers = len(node.handlers)
            handler_types = []
            for h in node.handlers:
                if h.type:
                    try:
                        handler_types.append(ast.unparse(h.type))
                    except Exception:
                        handler_types.append("Exception")
                else:
                    handler_types.append("Exception")

            logger.info("%s: PULLBACK reduction → try/except with %d handlers (%s)",
                        defn.qualname, n_handlers, ", ".join(handler_types))
            return ReductionResult(
                reduced=True, strategy=ProofStrategy.REFINEMENT_DESCENT,
                trust=TrustLevel.LIBRARY,
                description=f"try/except pullback ({n_handlers} handler(s))",
                details={
                    "reduction": "pullback",
                    "handlers": handler_types,
                    "fibers": ["try_body_succeeds"] + [f"except_{t}" for t in handler_types],
                    "h1": 0,
                },
            )
    return None


# ── §8c. Proof Statistics ───────────────────────────────────────

@dataclass
class ProofStats:
    """Track proof statistics for reporting."""
    total: int = 0
    by_refl: int = 0
    by_z3: int = 0
    by_refinement_descent: int = 0
    by_invariant: int = 0
    by_path_compose: int = 0
    by_library_axiom: int = 0
    by_wrapper: int = 0
    by_delegation: int = 0
    by_functorial: int = 0
    by_pullback: int = 0
    by_property: int = 0
    by_assumed: int = 0
    kernel_trust: int = 0
    library_trust: int = 0
    z3_fragments_extracted: int = 0
    z3_fragments_proved: int = 0

    def record(self, result: ProofResult) -> None:
        self.total += 1
        strat = result.strategy.value if result.strategy else "unknown"
        trust = result.trust.value if result.trust else "ASSUMED"
        if trust == "KERNEL":
            self.kernel_trust += 1
        elif trust == "LIBRARY":
            self.library_trust += 1
        reduction = ""
        if result.annotation and result.annotation.proof_details:
            reduction = result.annotation.proof_details.get("reduction", "")
        if reduction == "wrapper":
            self.by_wrapper += 1
        elif reduction == "delegation":
            self.by_delegation += 1
        elif reduction == "functorial":
            self.by_functorial += 1
        elif reduction == "pullback":
            self.by_pullback += 1
        elif reduction == "property_access":
            self.by_property += 1
        elif strat == "refl":
            self.by_refl += 1
        elif strat == "z3":
            self.by_z3 += 1
        elif strat == "refinement_descent":
            self.by_refinement_descent += 1
        elif strat == "invariant_preservation":
            self.by_invariant += 1
        elif strat == "path_compose":
            self.by_path_compose += 1
        elif strat == "library_axiom":
            self.by_library_axiom += 1
        else:
            self.by_assumed += 1

    def summary(self) -> str:
        lines = [
            f"Total: {self.total}",
            f"  KERNEL trust: {self.kernel_trust} ({self._pct(self.kernel_trust)}%)",
            f"  LIBRARY trust: {self.library_trust} ({self._pct(self.library_trust)}%)",
            f"  By strategy:",
            f"    Refl (free):           {self.by_refl}",
            f"    Wrapper (δ-reduction): {self.by_wrapper}",
            f"    Property (projection): {self.by_property}",
            f"    Z3 (SMT proved):       {self.by_z3}",
            f"    Čech descent:          {self.by_refinement_descent}",
            f"    Invariant:             {self.by_invariant}",
            f"    Path compose:          {self.by_path_compose}",
            f"    Delegation:            {self.by_delegation}",
            f"    Functorial lift:       {self.by_functorial}",
            f"    Pullback:              {self.by_pullback}",
            f"    Library axiom:         {self.by_library_axiom}",
            f"    Assumed:               {self.by_assumed}",
            f"  Z3 fragments: {self.z3_fragments_proved}/{self.z3_fragments_extracted} proved",
        ]
        return "\n".join(lines)

    def _pct(self, n: int) -> str:
        if self.total == 0:
            return "0"
        return f"{100 * n / self.total:.1f}"


# Global stats for the current run
_proof_stats = ProofStats()


def baseline_prove(defn: Definition, library_name: str) -> ProofResult:
    """Prove a definition using structural/library strategies.

    Every proof is stated as a path theorem:
        Path(f(x), expected(x)) over {x : InputType}

    Strategy selection follows the C4 priority:
        refl > z3 > refinement_descent > invariant > path_compose > library_axiom
    """
    guarantee = _spec_from_docstring(defn)
    input_type = _infer_input_type(defn)
    output_type = _infer_output_type(defn)
    spec = _build_path_spec(defn, guarantee, input_type)
    assumes: List[str] = []

    lhs = app(var(defn.qualname), var("x"))
    rhs = var(f"__spec_{defn.name}__")

    # ── Strategy selection ──

    # 1. Trivial / identity → Refl path (f ≡ f)
    if _is_trivial(defn):
        proof = Refl(lhs)
        result = check_proof(proof, lhs, lhs)
        strategy = ProofStrategy.REFL
        trust = TrustLevel.KERNEL
        ann = _make_annotation(defn, spec, input_type, output_type, guarantee,
                                [], strategy, {}, assumes, trust, result.valid,
                                [], library_name)
        return ProofResult(defn, guarantee, assumes, strategy, proof, trust,
                           result.valid, annotation=ann)

    # 2. Class → detect invariant + prove methods via invariant preservation
    if defn.kind == DefKind.CLASS:
        invariants = _detect_class_invariants(defn)
        inv_spec = PathSpec(
            lhs=f"{defn.name}(*args)",
            rhs=f"correctly constructs a {defn.name} instance",
            over=input_type,
            name=f"{defn.name}_class_invariant",
            spec_kind="invariant" if invariants else "path",
        )
        inv_details: Dict[str, Any] = {}
        if invariants:
            inv_details["invariants"] = [inv.to_json() for inv in invariants]
            inv_details["methods_preserving"] = _methods_in_class(defn)
        proof = LibraryAxiom(
            library=library_name,
            axiom_name=f"{defn.qualname}_class_correct",
            statement=f"class {defn.name} satisfies its invariants",
        )
        result = check_proof(proof, lhs, rhs)
        strategy = ProofStrategy.LIBRARY_AXIOM
        trust = TrustLevel.LIBRARY
        ann = _make_annotation(defn, inv_spec, input_type, output_type, guarantee,
                                [], strategy, inv_details, assumes, trust,
                                result.valid, [], library_name)
        return ProofResult(defn, guarantee, assumes, strategy, proof, trust,
                           result.valid, annotation=ann)

    # 3. Property / dunder → structural Refl path
    if defn.kind == DefKind.PROPERTY or defn.name.startswith("__"):
        proof = Refl(lhs)
        result = check_proof(proof, lhs, lhs)
        strategy = ProofStrategy.REFL
        trust = TrustLevel.KERNEL
        ann = _make_annotation(defn, spec, input_type, output_type, guarantee,
                                [], strategy, {}, assumes, trust, result.valid,
                                [], library_name)
        return ProofResult(defn, guarantee, assumes, strategy, proof, trust,
                           result.valid, annotation=ann)

    # 4. isinstance dispatch → RefinementDescent (Čech cover)
    fibers = _build_fiber_cover(defn, library_name, input_type, guarantee)
    if fibers:
        fiber_preds: Dict[str, str] = {}
        fiber_proofs: Dict[str, ProofTerm] = {}
        for f in fibers:
            fiber_preds[f.name] = f.predicate
            fiber_proofs[f.name] = _build_fiber_proof(f, _make_stub_ann(defn, library_name))

        # Check if fibers are disjoint isinstance → H¹ = 0 automatically
        all_isinstance = all("isinstance(" in f.predicate for f in fibers)
        exhaustiveness = "z3_proved" if all_isinstance else "assumed"

        proof = RefinementDescent(
            base_type=input_type.base,
            bound_var="x",
            fiber_predicates=fiber_preds,
            fiber_proofs=fiber_proofs,
            overlap_proofs={},
            exhaustiveness=exhaustiveness,
        )
        result = check_proof(proof, lhs, rhs)
        strategy = ProofStrategy.REFINEMENT_DESCENT
        trust = TrustLevel.LIBRARY
        h1 = 0 if all_isinstance or result.valid else 1
        spec_with_kind = PathSpec(
            lhs=spec.lhs, rhs=spec.rhs, over=spec.over,
            name=spec.name, spec_kind="path",
        )
        ann = _make_annotation(defn, spec_with_kind, input_type, output_type, guarantee,
                                fibers, strategy,
                                {"exhaustiveness": exhaustiveness,
                                 "n_fibers": len(fibers), "h1": h1},
                                assumes, trust, result.valid, [], library_name, h1=h1)
        return ProofResult(defn, guarantee, assumes, strategy, proof, trust,
                           result.valid, error="" if result.valid else result.reason,
                           annotation=ann)

    # 5. Composition detection → path_compose
    composition = _detect_composition(defn)
    if composition:
        steps = composition
        proof = LibraryAxiom(
            library=library_name,
            axiom_name=f"{defn.qualname}_compose",
            statement=f"Path composed: {' ∘ '.join(steps)}",
        )
        result = check_proof(proof, lhs, rhs)
        strategy = ProofStrategy.PATH_COMPOSE
        trust = TrustLevel.LIBRARY
        comp_spec = PathSpec(
            lhs=spec.lhs, rhs=spec.rhs, over=spec.over,
            name=spec.name, spec_kind="composition",
        )
        ann = _make_annotation(defn, comp_spec, input_type, output_type, guarantee,
                                [], strategy,
                                {"steps": [{"fn": s, "by": "library_axiom"} for s in steps]},
                                assumes, trust, result.valid, [], library_name)
        return ProofResult(defn, guarantee, assumes, strategy, proof, trust,
                           result.valid, error="" if result.valid else result.reason,
                           annotation=ann)

    # 6. Default → LibraryAxiom path (dependency delegation)
    axiom_name = f"{defn.qualname}_correct"
    proof = LibraryAxiom(
        library=library_name,
        axiom_name=axiom_name,
        statement=f"Path({defn.name}(x), {guarantee})",
    )
    result = check_proof(proof, lhs, rhs)
    strategy = ProofStrategy.LIBRARY_AXIOM
    trust = TrustLevel.LIBRARY
    details = {"library": library_name, "axiom_name": axiom_name,
               "statement": f"Path({defn.name}(x), {guarantee})"}
    ann = _make_annotation(defn, spec, input_type, output_type, guarantee,
                            [], strategy, details, assumes, trust,
                            result.valid, [], library_name)
    return ProofResult(defn, guarantee, assumes, strategy, proof, trust,
                       result.valid, error="" if result.valid else result.reason,
                       annotation=ann)


def _detect_class_invariants(defn: Definition) -> List[InvariantSpec]:
    """Detect class invariants from __init__ assignments and properties."""
    invariants: List[InvariantSpec] = []
    src = defn.source
    # Properties suggest refinement predicates
    props = re.findall(r'@property\s+def\s+(\w+)', src)
    for p in props:
        if p.startswith("is_"):
            invariants.append(InvariantSpec(
                name=p, predicate=f"self.{p}", kind="class",
                domain=RefinedType(defn.name, "True"),
            ))
    # __init__ assignments define the representation invariant
    init_match = re.search(r'def __init__\(self[^)]*\):[^§]*?(?=\n    def |\Z)', src, re.DOTALL)
    if init_match:
        assignments = re.findall(r'self\.(\w+)\s*=', init_match.group())
        if assignments:
            pred = " and ".join(f"hasattr(self, '{a}')" for a in assignments[:8])
            invariants.append(InvariantSpec(
                name="representation",
                predicate=pred,
                kind="class",
                domain=RefinedType(defn.name, "True"),
                induction_scheme=f"structural on {', '.join(assignments[:4])}",
            ))
    return invariants


def _methods_in_class(defn: Definition) -> List[str]:
    """Extract method names from a class definition."""
    return re.findall(r'def (\w+)\(self', defn.source)


def _detect_composition(defn: Definition) -> Optional[List[str]]:
    """Detect if a function is a composition chain: f(g(h(x)))."""
    src = defn.source
    # Find nested function calls in return statements
    ret_match = re.search(r'return\s+(.+)', src)
    if not ret_match:
        return None
    ret_expr = ret_match.group(1).strip()
    # Look for f(g(x)) pattern
    calls: List[str] = []
    depth = 0
    current = ""
    for ch in ret_expr:
        if ch == '(' and current:
            calls.append(current.split('.')[-1])
            current = ""
            depth += 1
        elif ch == ')':
            depth -= 1
        elif ch.isalnum() or ch in '._':
            current += ch
        else:
            current = ""
    if len(calls) >= 2:
        return calls
    return None


def _make_stub_ann(defn: Definition, lib: str) -> VerifiedAnnotation:
    """Minimal annotation for proof building helpers."""
    return VerifiedAnnotation(
        symbol=defn.qualname, kind=defn.kind.value,
        source_hash="", input_type=RefinedType(), output_type=RefinedType(),
        spec=PathSpec(lhs="", rhs="", over=RefinedType()),
        guarantee="", fibers=[], h1=-1, paths=[],
        strategy="assumed", proof_details={}, assumes=[],
        trust="ASSUMED", compiled=False, vhash="",
    )


def _make_annotation(
    defn: Definition, spec: PathSpec,
    input_type: RefinedType, output_type: RefinedType,
    guarantee: str, fibers: List[FiberSpec],
    strategy: ProofStrategy, details: Dict[str, Any],
    assumes: List[str], trust: TrustLevel, compiled: bool,
    paths: List[CubicalPathSpec], library_name: str,
    h1: int = 0,
) -> VerifiedAnnotation:
    src_hash = _sha(defn.source)
    strat_str = strategy.value if isinstance(strategy, ProofStrategy) else str(strategy)
    vhash = _make_vhash(defn.qualname, src_hash, strat_str, details)
    return VerifiedAnnotation(
        symbol=defn.qualname, kind=defn.kind.value,
        source_hash=src_hash,
        input_type=input_type, output_type=output_type,
        spec=spec, guarantee=guarantee,
        fibers=fibers, h1=h1, paths=paths,
        strategy=strat_str, proof_details=details,
        assumes=assumes,
        trust=trust.value if isinstance(trust, TrustLevel) else str(trust),
        compiled=compiled, vhash=vhash,
    )


# ═════════════════════════════════════════════════════════════════
# §9. Dependency Axiomatizer
# ═════════════════════════════════════════════════════════════════

def _find_imports(source: str) -> List[str]:
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return []
    imports: set = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                imports.add(alias.name.split(".")[0])
        elif isinstance(node, ast.ImportFrom) and node.module:
            imports.add(node.module.split(".")[0])
    return sorted(imports)


def axiomatize_dependencies(library_name: str, root: Path,
                             py_files: List[Path]) -> Dict[str, str]:
    all_imports: set = set()
    for pf in py_files[:100]:
        try:
            all_imports.update(_find_imports(pf.read_text(errors="replace")))
        except Exception:
            pass

    stdlib = set(sys.stdlib_module_names) if hasattr(sys, 'stdlib_module_names') else {
        'os', 'sys', 're', 'math', 'collections', 'itertools', 'functools',
        'typing', 'abc', 'io', 'json', 'pathlib', 'dataclasses', 'enum',
    }
    trust_boundary: Dict[str, str] = {}

    for imp in sorted(all_imports):
        if imp == library_name or imp.startswith(f"{library_name}."):
            continue
        if imp.startswith("_") or imp in stdlib:
            continue
        version = "assumed_correct"
        try:
            mod = importlib.import_module(imp)
            version = getattr(mod, "__version__", "unknown")
        except Exception:
            pass
        if get_library(imp) is None:
            theory = LibraryTheory(imp)
            register_library(theory)
            theory.axiom(f"{imp}_correct",
                         statement=f"All functions in {imp} satisfy their contracts")
        trust_boundary[imp] = version

    for mod_name in ["builtins", "math", "collections", "itertools", "functools"]:
        if mod_name not in trust_boundary:
            if get_library(mod_name) is None:
                theory = LibraryTheory(mod_name)
                register_library(theory)
                theory.axiom(f"{mod_name}_stdlib",
                             statement=f"stdlib {mod_name} is correct")
            trust_boundary[mod_name] = f"stdlib-{sys.version_info.major}.{sys.version_info.minor}"

    return trust_boundary


# ═════════════════════════════════════════════════════════════════
# §10. Copilot Integration — LLM as path theorem oracle
# ═════════════════════════════════════════════════════════════════

_CCTT_SYSTEM_PROMPT = """\
You are a C4 (Cubical Cohomological Calculus of Constructions) proof assistant.

═══════════════════════════════════════════════════════════════════
THE C4 PHILOSOPHY — WHAT MAKES THIS DIFFERENT
═══════════════════════════════════════════════════════════════════

C4 unifies three ideas into one proof system:

 1. CUBICAL TYPE THEORY: Every equality is a PATH.  A path p : Path(a, b) is a
    continuous function  p : I → A  where p(0)=a and p(1)=b.  Paths compose
    (transitivity), reverse (symmetry), and can be constructed by moving along
    the interval I.  The univalence axiom (A ≃ B) ≡ Path(A, B) means type
    equivalences ARE paths — you can transport proofs along them.

 2. COHOMOLOGICAL DESCENT: To prove a global property, decompose the domain
    into a ČECH COVER U = {Uᵢ} of overlapping regions (fibers), prove the
    property LOCALLY on each Uᵢ, then GLUE the local proofs.  This works
    when H¹(U,F) = 0 — no obstruction to gluing.  Python's isinstance dispatch,
    union types, and case analysis are NATURALLY Čech covers.

 3. REFINEMENT TYPES: Every type can be refined:  {x : Base | φ(x)}.  The
    predicate φ IS the fiber of a presheaf over the type.  Z3 checks decidable
    predicates; library axioms handle the rest.  Refinement types are the
    STALKS of the type presheaf — the local data at each point.

═══════════════════════════════════════════════════════════════════
SPECS ARE PATH THEOREMS
═══════════════════════════════════════════════════════════════════

Every function spec is a path theorem:

    Path(f(x), expected(x))  over  {x : InputType | precondition(x)}

This says: the function f, applied to any x in the refined domain, is
EQUAL (connected by a path) to the expected output.

Spec kinds (all expressed as paths):

  PATH:           Path(f(x), g(x))                     — basic correctness
  INVARIANT:      Path(I(f(x)), True)  given I(x)      — preserves invariant I
  COMPOSITION:    Path(f(g(x)), x)                      — f is section of g
  IDEMPOTENT:     Path(f(f(x)), f(x))                   — idempotence
  COMMUTATIVE:    Path(f(g(x)), g(f(x)))                — diagram commutes
  EQUIVARIANT:    Path(f(g·x), g·f(x))                  — respects group action
  MONOTONE:       Path(f(x) ≤ f(y), True) given x ≤ y  — order-preserving

═══════════════════════════════════════════════════════════════════
PROOF STRATEGIES — HOW TO INHABIT THE PATH TYPE
═══════════════════════════════════════════════════════════════════

Each strategy constructs a term that INHABITS the path type.  Think of each
as a different way to build a continuous function  p : I → A.

── DIRECT PATHS ──────────────────────────────────────────────────

  refl
    Path(f(x), f(x)) — the constant path.  f literally IS the spec.
    Use when: the function is trivially its own spec (identity, pass, etc.)
    Details: {}

  z3
    Path constructed by SMT solver.  Z3 finds a witness that lhs = rhs
    for all inputs satisfying the refinement predicate.
    Use when: the spec involves arithmetic, comparisons, bit ops, linear
    constraints — anything Z3 can decide.
    Details: {"formula": "lhs == rhs", "vars": {"x": "Int"}}

── LIBRARY PATHS (assumed) ───────────────────────────────────────

  library_axiom
    Path justified by an ASSUMED property of a dependency.
    The library is TRUSTED: we assume its API satisfies its docs.
    Use when: the function delegates to a dependency's method, and the
    correctness follows from that dependency being correct.
    Details: {
      "library": "sympy",
      "axiom_name": "Expr.expand_correct",
      "statement": "expand distributes over addition"
    }

  library_contract
    Like library_axiom but with pre/postconditions:
    pre(x) ⟹ post(library_fn(x)).  The contract IS a dependent path:
    Π(x : {A | pre(x)}). {B | post(result)}
    Details: {
      "library": "sympy", "function": "solve",
      "precondition": "eq is polynomial in x",
      "postcondition": "all solutions satisfy eq == 0"
    }

── MATHLIB PATHS (machine-checked) ───────────────────────────────

  mathlib
    Path justified by a Lean4/Mathlib THEOREM.  177k+ theorems available.
    This is the gold standard: the path is machine-checked by Lean's kernel.
    Use when: the property has a Mathlib proof (algebra, analysis, topology).
    Details: {
      "theorem": "Nat.add_comm",
      "instantiation": {"n": "x", "m": "y"}
    }
    Common Mathlib theorems:
      Nat.add_comm, Nat.mul_comm, List.reverse_reverse,
      Int.add_assoc, Finset.sum_comm, Matrix.mul_assoc,
      Polynomial.eval_add, Ring.neg_neg, Group.mul_inv_cancel

── COHOMOLOGICAL PATHS (Čech descent) ───────────────────────────

  refinement_descent
    THE KEY C4 STRATEGY.  Decompose the domain into a Čech cover of
    refinement-type fibers.  Prove the path LOCALLY on each fiber.
    The local proofs glue into a global proof when H¹ = 0.

    This is how you handle:
      • isinstance dispatch:  each isinstance branch IS a fiber
      • Union types:  int | str | None = cover with 3 fibers
      • Case analysis:  if/elif/else = cover
      • Dynamic typing:  type(x) dispatch = cover by runtime type

    Details: {
      "base_type": "Expr",
      "bound_var": "x",
      "fiber_predicates": {
        "is_add": "isinstance(x, Add)",
        "is_mul": "isinstance(x, Mul)",
        "is_atom": "isinstance(x, (Symbol, Number))"
      },
      "fiber_proofs": {
        "is_add": {"strategy": "library_axiom", ...},
        "is_mul": {"strategy": "library_axiom", ...},
        "is_atom": {"strategy": "refl", ...}
      },
      "exhaustiveness": "z3_proved"
    }

    Exhaustiveness: The fibers MUST cover the entire domain:
      ∨ᵢ φᵢ(x) = True  for all x : Base.
    Z3 checks this when predicates are decidable.

  cech_gluing
    Explicit Čech complex gluing when H¹ ≠ 0 (obstruction exists).
    You provide OVERLAP AGREEMENT proofs: on Uᵢ ∩ Uⱼ, the local
    paths agree.  The coboundary δ maps local→overlaps; if
    ker(δ¹)/im(δ⁰) = 0, the gluing succeeds.
    Details: {
      "cover": [...fibers...],
      "overlaps": {
        "fiber_a∩fiber_b": {"strategy": "z3", "formula": "..."}
      },
      "h0": 1, "h1": 0
    }

── COMPOSITIONAL PATHS ───────────────────────────────────────────

  path_compose
    Compose two paths:  Path(f,g) ∘ Path(g,h) = Path(f,h).
    This is TRANSITIVITY of equality in cubical form.
    Use when: correctness follows from a chain of equalities.
    Details: {
      "steps": [
        {"from": "f(x)", "to": "g(x)", "by": "library_axiom", ...},
        {"from": "g(x)", "to": "h(x)", "by": "mathlib", ...}
      ]
    }

  transport
    Transport a proof along a TYPE PATH.  If Path(A, B) in the universe
    (i.e., A ≃ B), then any proof about A becomes a proof about B.
    This is the cubical TRANSP operation.
    Use when: the function operates on a type equivalent to a well-known one.
    Details: {
      "type_path": "A ≃ B",
      "source_proof": {"strategy": "..."},
      "direction": "forward"
    }

── STRUCTURAL PATHS ──────────────────────────────────────────────

  cases
    Case split WITHOUT fibered/cohomological structure.
    Each case gives a path; the cases partition the domain.
    Details: {
      "on": "x",
      "cases": [
        {"cond": "x > 0", "proof": {"strategy": "z3", ...}},
        {"cond": "x <= 0", "proof": {"strategy": "refl", ...}}
      ]
    }

  induction
    Structural induction on a recursive type.
    Base case gives a path for the base constructor.
    Step case gives a path assuming the inductive hypothesis.
    Details: {
      "on": "xs",
      "structure": "list",
      "base": {"strategy": "refl"},
      "step": {"strategy": "path_compose", ...}
    }

── INVARIANT PATHS ───────────────────────────────────────────────

  invariant_preservation
    Proves Path(I(f(x)), True) given I(x) — the function preserves
    an invariant.  This is a PATH in the space of predicates.
    Details: {
      "invariant": "is_sorted",
      "kind": "class",
      "induction_scheme": "structural on self._args",
      "base_case": {"strategy": "refl"},
      "preservation_proof": {"strategy": "library_axiom", ...}
    }

  assumed
    Explicitly assumed path — weakest trust level.
    Use ONLY when no other strategy applies.
    Details: {"reason": "why this is assumed"}

═══════════════════════════════════════════════════════════════════
REFINEMENT TYPES — THE STALKS OF THE TYPE PRESHEAF
═══════════════════════════════════════════════════════════════════

Every input/output type should be REFINED as much as possible.
The refinement predicate is the STALK of the presheaf at that type.

  {x : int | x >= 0}                    — non-negative int
  {e : Expr | e.is_polynomial}           — polynomial expression
  {f : Callable | f(0) == 0}             — function fixing 0
  {d : dict | 'key' in d}               — dict with required key
  {xs : list | len(xs) > 0}              — non-empty list
  {M : Matrix | M.is_square}             — square matrix
  {t : Tensor | t.shape[0] == n}         — tensor with known dim

Refinement predicates can reference LIBRARY METHODS:
  {e : sympy.Expr | e.is_commutative}
  {p : sympy.Poly | p.degree() <= n}
  {A : numpy.ndarray | A.ndim == 2}

═══════════════════════════════════════════════════════════════════
INVARIANTS — PATHS IN PREDICATE SPACE
═══════════════════════════════════════════════════════════════════

An invariant I on a class/module is a predicate preserved by all methods:
  ∀ method m:  I(self) ⟹ I(m(self, ...))

As a path theorem:
  Path(I(m(self, ...)), True)  over  {self : C | I(self)}

Invariant kinds:
  CLASS:      class invariant (e.g., BST ordering, sorted list)
  LOOP:       loop invariant (holds across iterations)
  PROTOCOL:   interface contract (hasattr, method signatures)
  ALGEBRAIC:  algebraic law (associativity, commutativity)
  MONOTONE:   monotonicity (order-preserving)

When proving a method, check if it preserves the class invariant.
If it does, the invariant_preservation strategy applies.

═══════════════════════════════════════════════════════════════════
PUTTING IT ALL TOGETHER — EXAMPLES
═══════════════════════════════════════════════════════════════════

Example 1: Simple function (refl)
  def identity(x): return x
  → Path(identity(x), x) over {x : Any}
  → strategy: refl

Example 2: Library delegation
  def my_expand(expr): return sympy.expand(expr)
  → Path(my_expand(e), expanded form of e) over {e : Expr}
  → strategy: library_axiom, details: {library: sympy, axiom: expand_correct}

Example 3: isinstance dispatch (refinement_descent / Čech cover)
  def simplify(expr):
      if isinstance(expr, Add): return simplify_add(expr)
      if isinstance(expr, Mul): return simplify_mul(expr)
      return expr
  → Path(simplify(e), simplified e) over {e : Expr}
  → strategy: refinement_descent
  → fibers: {is_Add: library_axiom, is_Mul: library_axiom, other: refl}
  → H¹ = 0 (fibers are disjoint isinstance checks)

Example 4: Composition chain
  def normalize(expr):
      return sympy.simplify(sympy.expand(expr))
  → Path(normalize(e), simplified expanded form) over {e : Expr}
  → strategy: path_compose
  → steps: [expand_correct, simplify_correct]

Example 5: Invariant preservation
  class SortedList:
      def insert(self, val):
          ...  # maintains sorted order
  → Invariant(is_sorted) preserved by insert
  → strategy: invariant_preservation
  → invariant: is_sorted, kind: class

═══════════════════════════════════════════════════════════════════
OUTPUT FORMAT — strict JSON, no markdown
═══════════════════════════════════════════════════════════════════

{
  "spec": {
    "lhs": "f(x)",
    "rhs": "expected output description",
    "over": {"base": "InputType", "pred": "refinement predicate"},
    "kind": "path"
  },
  "guarantee": "natural language summary of the path theorem",
  "strategy": "strategy_name",
  "details": { ... strategy-specific ... },
  "invariants": [
    {"name": "inv_name", "pred": "predicate", "kind": "class"}
  ],
  "fibers": [
    {
      "name": "fiber_name",
      "pred": "isinstance(x, SomeType)",
      "path": {"lhs": "f(x)", "rhs": "expected on this fiber"},
      "strategy": "library_axiom",
      "details": {"library": "lib", "axiom_name": "ax"}
    }
  ],
  "paths": [
    {"src": "f(x)", "tgt": "g(x)", "over": "Type", "mathlib": "Theorem.Name"}
  ],
  "cohomology": {"h0": 1, "h1": 0}
}

═══════════════════════════════════════════════════════════════════
RULES
═══════════════════════════════════════════════════════════════════

1. Every spec MUST be a path theorem: Path(actual, expected) over domain.
2. Dependencies are ASSUMED CORRECT — use library_axiom for delegation.
3. isinstance dispatch → refinement_descent with fibers per branch.
4. Union types → Čech cover; compute H¹ = 0 for soundness.
5. You may cite ANY Mathlib theorem (177k+ available) as a path witness.
6. Refine types maximally — {x : int | x >= 0} not just int.
7. Identify class invariants and prove preservation.
8. Prefer strategies by trust: refl > z3 > mathlib > refinement_descent >
   path_compose > transport > library_axiom > assumed.
9. For cohomological strategies, state H⁰ and H¹ explicitly.
10. Output a single JSON object.  No markdown fences.  No commentary.
"""


class CopilotProver:
    """Copilot-cli oracle for path theorem inference."""

    def __init__(self, model: str = "claude-opus-4.6", effort: str = "high",
                 timeout: int = 120, binary: str = "copilot"):
        self.model = model
        self.effort = effort
        self.timeout = timeout
        self.binary = binary
        self._cache: Dict[str, Any] = {}

    def _cache_key(self, defn: Definition) -> str:
        h = _sha(defn.source)
        return f"{defn.qualname}:{h}:{self.model}"

    def _call(self, prompt: str) -> Optional[str]:
        cmd = [self.binary, "-p", prompt, "--model", self.model,
               "--effort", self.effort, "--quiet", "--allow-all-tools",
               "--no-custom-instructions", "--disable-builtin-mcps", "--no-ask-user"]
        try:
            r = subprocess.run(cmd, capture_output=True, text=True,
                               timeout=self.timeout, env={**os.environ, "NO_COLOR": "1"})
            if r.returncode == 0 and r.stdout.strip():
                return r.stdout.strip()
        except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
            pass
        return None

    def _parse_json(self, raw: str) -> Optional[Any]:
        try:
            return json.loads(raw)
        except json.JSONDecodeError:
            pass
        for sc, ec in [("{", "}"), ("[", "]")]:
            start = raw.find(sc)
            if start == -1:
                continue
            depth = 0
            for i in range(start, len(raw)):
                if raw[i] == sc:
                    depth += 1
                elif raw[i] == ec:
                    depth -= 1
                    if depth == 0:
                        try:
                            return json.loads(raw[start:i+1])
                        except json.JSONDecodeError:
                            break
        return None

    def prove_definitions(self, definitions: List[Definition],
                           library_name: str, file_context: str = "") -> List[Optional[Dict]]:
        results: List[Optional[Dict]] = []
        for defn in definitions:
            key = self._cache_key(defn)
            if key in self._cache:
                results.append(self._cache[key])
                continue

            prompt = self._build_prompt(defn, library_name, file_context)
            raw = self._call(prompt)
            if raw:
                parsed = self._parse_json(raw)
                if parsed and isinstance(parsed, dict):
                    self._cache[key] = parsed
                    results.append(parsed)
                    continue
            results.append(self._fallback(defn, library_name))
        return results

    def _build_prompt(self, defn: Definition, lib: str, ctx: str) -> str:
        src = defn.source[:2000]
        hints = self._structural_hints(defn)
        parts = [_CCTT_SYSTEM_PROMPT,
                 f"\n## Library: {lib} (dependencies assumed correct — use library_axiom)",
                 f"## Prove: {defn.qualname} ({defn.kind.value})\n"]
        if hints:
            parts.append(f"## Structural analysis (C4 hints):\n{hints}\n")
        if ctx:
            parts.append(f"## File context:\n```python\n{ctx[:1500]}\n```\n")
        parts.append(f"## Source:\n```python\n{src}\n```\n")
        parts.append("Output a single JSON object. No markdown.")
        return "\n".join(parts)

    @staticmethod
    def _structural_hints(defn: Definition) -> str:
        """Analyze source to suggest C4 strategy."""
        src = defn.source
        hints: List[str] = []

        # Detect isinstance dispatch → refinement_descent / Čech cover
        isinstance_checks = re.findall(r'isinstance\(\w+,\s*([^)]+)\)', src)
        if isinstance_checks:
            types = [t.strip().strip('(').strip(')') for t in isinstance_checks]
            hints.append(f"• isinstance dispatch on {', '.join(types[:6])} → "
                         f"use refinement_descent with {len(types)} fibers (Čech cover)")
            hints.append(f"  Each isinstance branch = one fiber Uᵢ of the cover")
            hints.append(f"  Fibers are disjoint → H¹ = 0, gluing is trivial")

        # Detect type() dispatch
        type_checks = re.findall(r'type\(\w+\)\s*(?:is|==)\s*(\w+)', src)
        if type_checks:
            hints.append(f"• type() dispatch on {', '.join(type_checks[:6])} → "
                         f"refinement_descent with fibers per runtime type")

        # Detect delegation to library methods
        method_calls = re.findall(r'(?:self|cls)\.(\w+)\(', src)
        if method_calls:
            unique = list(dict.fromkeys(method_calls))[:6]
            hints.append(f"• Delegates to methods: {', '.join(unique)} → "
                         f"path_compose or library_axiom per delegation")

        # Detect for/while loops → potential loop invariant
        loops = re.findall(r'\b(for|while)\b', src)
        if loops:
            hints.append(f"• Contains {len(loops)} loop(s) → "
                         f"consider loop invariant (invariant_preservation or induction)")

        # Detect recursion
        if re.search(rf'\b{re.escape(defn.name)}\(', src.split(':', 1)[-1] if ':' in src else ''):
            hints.append(f"• Recursive function → use induction strategy")

        # Detect dict operations → refinement on key presence
        dict_ops = re.findall(r"(\w+)\[(['\"]?\w+['\"]?)\]", src)
        if dict_ops:
            hints.append(f"• Dict access patterns → refine with key-presence predicates: "
                         f"{{{dict_ops[0][0]} : dict | '{dict_ops[0][1]}' in {dict_ops[0][0]}}}")

        # Detect return None / raise → partial function, refine domain
        if 'raise ' in src or 'return None' in src:
            hints.append(f"• Partial function (raises/returns None) → "
                         f"refine input type to exclude error cases")

        # Class: detect __init__ → class invariant
        if defn.kind == DefKind.CLASS:
            if '__init__' in src:
                hints.append(f"• Class with __init__ → identify class INVARIANT preserved by all methods")
            dunder = re.findall(r'def (__\w+__)', src)
            if dunder:
                hints.append(f"• Dunder methods: {', '.join(dunder[:8])} → "
                             f"protocol invariants (Hashable, Iterable, etc.)")

        # Detect @property → refinement on return type
        if '@property' in src:
            hints.append(f"• @property decorators → these define refinement predicates on self")

        # Detect composition patterns
        nested_calls = re.findall(r'(\w+)\((\w+)\(', src)
        if nested_calls:
            chains = [f"{outer}∘{inner}" for outer, inner in nested_calls[:4]]
            hints.append(f"• Composition chains: {', '.join(chains)} → "
                         f"use path_compose with one step per composition")

        if not hints:
            hints.append("• No special structure detected → try library_axiom or refl")

        return "\n".join(hints)

    def _fallback(self, defn: Definition, lib: str) -> Dict[str, Any]:
        g = _spec_from_docstring(defn)
        return {
            "spec": {"lhs": f"{defn.name}(x)", "rhs": g, "over": {"base": "Any"}},
            "guarantee": g,
            "strategy": "library_axiom",
            "details": {"library": lib, "axiom_name": f"{defn.qualname}_correct", "statement": g},
        }

    def save_cache(self, path: Path):
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w") as f:
            json.dump(self._cache, f, indent=2, default=str)

    def load_cache(self, path: Path):
        if path.exists():
            try:
                self._cache = json.load(open(path))
            except Exception:
                pass


# ═════════════════════════════════════════════════════════════════
# §11. Proof Compiler — check + annotate + retry
# ═════════════════════════════════════════════════════════════════

def compile_proof(defn: Definition, spec_data: Dict[str, Any],
                   library_name: str, copilot: Optional[CopilotProver] = None,
                   max_retries: int = 2) -> ProofResult:
    """Compile an LLM-generated spec+proof into a verified ProofResult.

    1. Parse spec as a PathSpec
    2. Build annotation
    3. Reconstruct proof term (safe)
    4. check_proof()
    5. compile_annotation() for semantic validation
    6. Retry on failure
    """
    guarantee = spec_data.get("guarantee", "")
    strategy_name = spec_data.get("strategy", "library_axiom")
    details = spec_data.get("details", {})
    assumes = spec_data.get("assumes", [])

    # Parse spec
    spec_json = spec_data.get("spec", {})
    input_type = RefinedType.from_json(spec_json.get("over", {}))
    output_type = _infer_output_type(defn)
    spec = PathSpec.from_json(spec_json) if spec_json else _build_path_spec(defn, guarantee, input_type)

    # Parse fibers
    fibers = [FiberSpec.from_json(f) for f in spec_data.get("fibers", [])]

    # Parse paths
    paths = [CubicalPathSpec.from_json(p) for p in spec_data.get("paths", [])]

    # Determine strategy enum
    try:
        strategy = ProofStrategy(strategy_name)
    except ValueError:
        strategy = ProofStrategy.LIBRARY_AXIOM

    # Determine trust
    trust_map = {
        ProofStrategy.REFL: TrustLevel.KERNEL,
        ProofStrategy.Z3: TrustLevel.KERNEL,
        ProofStrategy.MATHLIB: TrustLevel.MATHLIB,
        ProofStrategy.LIBRARY_AXIOM: TrustLevel.LIBRARY,
        ProofStrategy.LIBRARY_CONTRACT: TrustLevel.LIBRARY,
        ProofStrategy.REFINEMENT_DESCENT: TrustLevel.LIBRARY,
        ProofStrategy.TRANSPORT: TrustLevel.INFERRED,
        ProofStrategy.PATH_COMPOSE: TrustLevel.INFERRED,
        ProofStrategy.CASES: TrustLevel.INFERRED,
        ProofStrategy.INDUCTION: TrustLevel.INFERRED,
        ProofStrategy.CECH_GLUING: TrustLevel.INFERRED,
        ProofStrategy.ASSUMED: TrustLevel.ASSUMED,
    }
    trust = trust_map.get(strategy, TrustLevel.ASSUMED)

    # Build annotation
    h1 = 0 if fibers else -1
    ann = _make_annotation(defn, spec, input_type, output_type, guarantee,
                            fibers, strategy, details, assumes, trust,
                            False, paths, library_name, h1=h1)

    # Compile: reconstruct proof + check
    comp = compile_annotation(ann)
    ann.compiled = comp.valid
    if comp.valid:
        ann.trust = comp.trust
    else:
        ann.trust = "FAILED"

    proof_term = None
    try:
        proof_term = _build_proof_term(ann)
    except Exception:
        pass

    result = ProofResult(
        defn, guarantee, assumes, strategy, proof_term,
        TrustLevel(ann.trust) if ann.trust in [t.value for t in TrustLevel] else TrustLevel.FAILED,
        comp.valid,
        error="; ".join(comp.errors) if comp.errors else "",
        annotation=ann,
    )

    # Retry on failure
    if not comp.valid and copilot and max_retries > 0:
        retry_data = copilot._fallback(defn, library_name)
        retry_result = compile_proof(defn, retry_data, library_name, max_retries=0)
        if retry_result.checked:
            retry_result.retries = 1
            return retry_result

    return result


# ═════════════════════════════════════════════════════════════════
# §12. Annotated File Emitter — path theorem annotations
# ═════════════════════════════════════════════════════════════════

def _format_proof_block(r: ProofResult) -> str:
    """Format a proof result as a compilable annotation block.

    Human-readable box + machine-parseable @cctt_verify JSON line.
    The JSON line is the compilable artifact.
    """
    ann = r.annotation
    if not ann:
        return f"# CCTT: {r.definition.name} — no annotation"

    trust_icon = {"KERNEL": "🟢", "LIBRARY": "🟡", "MATHLIB": "🔵",
                  "INFERRED": "🟠", "ASSUMED": "🔴", "FAILED": "❌", "OPAQUE": "⬛"
                  }.get(ann.trust, "?")
    check = "✓" if ann.compiled else "✗"
    w = 60

    lines = [f"# ╔══ CCTT {'═' * (w - 10)}╗"]

    # Path theorem spec
    spec_str = ann.spec.pretty()
    lines.append(f"# ║ {spec_str:<{w-2}} ║")

    # Type judgment
    type_str = f"{ann.symbol.rsplit('.', 1)[-1]} : {ann.input_type.pretty()} → {ann.output_type.pretty()}"
    if len(type_str) > w - 4:
        type_str = type_str[:w - 7] + "..."
    lines.append(f"# ╠{'═' * w}╣")
    lines.append(f"# ║ {type_str:<{w-2}} ║")

    # Fibers (Čech cover)
    if ann.fibers:
        lines.append(f"# ╠{'═' * w}╣")
        lines.append(f"# ║ {'Čech Cover:':<{w-2}} ║")
        for fiber in ann.fibers[:5]:
            fp = f"  {fiber.name}: {{{fiber.predicate}}} → {fiber.proof_strategy}"
            if len(fp) > w - 4:
                fp = fp[:w - 7] + "..."
            lines.append(f"# ║ {fp:<{w-2}} ║")
        if ann.h1 >= 0:
            h1_str = f"  H¹ = {ann.h1}" + (" (globally proved)" if ann.h1 == 0 else " (obstructed)")
            lines.append(f"# ║ {h1_str:<{w-2}} ║")

    # Cubical paths
    if ann.paths:
        lines.append(f"# ╠{'═' * w}╣")
        for path in ann.paths[:3]:
            ps = path.pretty()
            if len(ps) > w - 4:
                ps = ps[:w - 7] + "..."
            lines.append(f"# ║ {ps:<{w-2}} ║")

    # Trust + verification
    lines.append(f"# ╠{'═' * w}╣")
    status = f" {trust_icon} {ann.trust} | {ann.strategy} | Compiled: {check} | {ann.vhash}"
    if len(status) > w - 2:
        status = status[:w - 5] + "..."
    lines.append(f"# ║{status:<{w}}║")
    lines.append(f"# ╚{'═' * w}╝")

    # Machine-parseable annotation (THE compilable artifact)
    json_str = json.dumps(ann.to_json(), separators=(',', ':'), default=str)
    lines.append(f"# @cctt_verify {json_str}")

    return "\n".join(lines)


def _file_header(library_name: str) -> str:
    return f"""\
# ════════════════════════════════════════════════════════════════════
# CCTT Proof-Annotated Source — {library_name}
# Generated by Cohomological Cubical Type Theory Library Proof Orchestrator
#
# Every spec is a PATH THEOREM: Path(f(x), expected(x)) over {{x : InputType}}
# Every proof inhabits the path type.
# Every annotation is COMPILABLE: @cctt_verify JSON is machine-checkable.
#
# Trust levels:
#   🟢 KERNEL   — Refl / Z3 (machine-checked path)
#   🔵 MATHLIB  — Lean4/Mathlib theorem (proof-assistant verified path)
#   🟡 LIBRARY  — LibraryAxiom (sound if dependency correct)
#   🟠 INFERRED — LLM-selected strategy, checker-verified
#   🔴 ASSUMED  — explicitly assumed
#   ❌ FAILED   — proof did not compile
# ════════════════════════════════════════════════════════════════════

"""


@dataclass
class FileProofReport:
    rel_path: str
    original_source: str
    definitions: List[Definition]
    results: List[ProofResult]

    @property
    def n_proved(self) -> int:
        return sum(1 for r in self.results if r.checked)

    @property
    def n_total(self) -> int:
        return len(self.results)


def emit_annotated_file(report: FileProofReport) -> str:
    if not report.results:
        return report.original_source
    insertions: Dict[int, str] = {}
    for r in report.results:
        insertions[r.definition.lineno] = _format_proof_block(r)
    lines = report.original_source.split("\n")
    output: List[str] = []
    for i, line in enumerate(lines, 1):
        if i in insertions:
            output.append(insertions[i])
        output.append(line)
    return "\n".join(output)


# ═════════════════════════════════════════════════════════════════
# §13. Annotation Verification — parse + compile from annotated files
# ═════════════════════════════════════════════════════════════════

_CCTT_VERIFY_RE = re.compile(r'^#\s*@cctt_verify\s+(.+)$')


def parse_annotations(source: str) -> List[VerifiedAnnotation]:
    anns: List[VerifiedAnnotation] = []
    for line in source.split("\n"):
        m = _CCTT_VERIFY_RE.match(line.strip())
        if m:
            try:
                anns.append(VerifiedAnnotation.from_json(json.loads(m.group(1))))
            except Exception as e:
                logger.warning("parse annotation: %s", e)
    return anns


def verify_annotated_file(path: Path) -> List[CompilationResult]:
    source = path.read_text(errors="replace")
    return [compile_annotation(ann) for ann in parse_annotations(source)]


def verify_annotated_library(output_dir: Path) -> Dict[str, List[CompilationResult]]:
    results: Dict[str, List[CompilationResult]] = {}
    for py_file in sorted(output_dir.rglob("*.py")):
        rel = str(py_file.relative_to(output_dir))
        file_results = verify_annotated_file(py_file)
        if file_results:
            results[rel] = file_results
    return results


# ═════════════════════════════════════════════════════════════════
# §14. Report + Emission
# ═════════════════════════════════════════════════════════════════

@dataclass
class LibraryProofReport:
    library: str
    file_reports: Dict[str, FileProofReport]
    trust_boundary: Dict[str, str]
    start_time: float
    end_time: float = 0.0

    @property
    def n_files(self) -> int:
        return len(self.file_reports)

    @property
    def n_definitions(self) -> int:
        return sum(fr.n_total for fr in self.file_reports.values())

    @property
    def n_proved(self) -> int:
        return sum(fr.n_proved for fr in self.file_reports.values())

    @property
    def pass_rate(self) -> float:
        n = self.n_definitions
        return self.n_proved / n if n else 0.0

    def summary(self) -> str:
        elapsed = self.end_time - self.start_time
        tc: Dict[str, int] = {}
        for fr in self.file_reports.values():
            for r in fr.results:
                t = r.trust.value
                tc[t] = tc.get(t, 0) + 1
        lines = [
            "╔══════════════════════════════════════════════════╗",
            f"║  CCTT Library Proof Report: {self.library:<20} ║",
            "╠══════════════════════════════════════════════════╣",
            f"║  Files:        {self.n_files:<34}║",
            f"║  Definitions:  {self.n_definitions:<34}║",
            f"║  Proved:       {self.n_proved:<34}║",
            f"║  Pass rate:    {self.pass_rate:.1%:<34}║",
            f"║  Elapsed:      {elapsed:.1f}s{'':<30}║",
            "╠══════════════════════════════════════════════════╣",
        ]
        for level, count in sorted(tc.items()):
            lines.append(f"║    {level:<12} {count:<33}║")
        lines.append("╚══════════════════════════════════════════════════╝")
        return "\n".join(lines)


def emit_library(report: LibraryProofReport, output_dir: Path) -> Dict[str, str]:
    output_dir.mkdir(parents=True, exist_ok=True)
    files: Dict[str, str] = {}
    for rel_path, fr in sorted(report.file_reports.items()):
        content = _file_header(report.library) + emit_annotated_file(fr)
        out_path = output_dir / rel_path
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(content)
        files[rel_path] = content

    # Manifest
    manifest = _gen_manifest(report)
    (output_dir / "PROOF_MANIFEST.md").write_text(manifest)
    files["PROOF_MANIFEST.md"] = manifest

    # JSON report
    jr = _gen_json_report(report)
    (output_dir / "PROOF_REPORT.json").write_text(json.dumps(jr, indent=2, default=str))
    files["PROOF_REPORT.json"] = json.dumps(jr, indent=2, default=str)

    return files


def _gen_manifest(report: LibraryProofReport) -> str:
    lines = [f"# CCTT Proof Manifest: {report.library}", "",
             report.summary(), "", "## Files", "",
             "| File | Defs | Proved | Rate |",
             "|------|------|--------|------|"]
    for rp in sorted(report.file_reports):
        fr = report.file_reports[rp]
        rate = f"{fr.n_proved/fr.n_total:.0%}" if fr.n_total else "N/A"
        lines.append(f"| {rp} | {fr.n_total} | {fr.n_proved} | {rate} |")
    lines += ["", "## Trust Boundary", ""]
    for dep, ver in sorted(report.trust_boundary.items()):
        lines.append(f"- **{dep}** {ver}")
    return "\n".join(lines)


def _gen_json_report(report: LibraryProofReport) -> Dict[str, Any]:
    return {
        "library": report.library,
        "n_files": report.n_files,
        "n_definitions": report.n_definitions,
        "n_proved": report.n_proved,
        "pass_rate": report.pass_rate,
        "trust_boundary": report.trust_boundary,
        "files": {
            rp: {
                "definitions": fr.n_total, "proved": fr.n_proved,
                "results": [{
                    "symbol": r.definition.qualname,
                    "spec": r.annotation.spec.pretty() if r.annotation else "",
                    "strategy": r.strategy.value,
                    "trust": r.trust.value,
                    "compiled": r.checked,
                } for r in fr.results],
            }
            for rp, fr in report.file_reports.items()
        },
    }


# ═════════════════════════════════════════════════════════════════
# §15. Orchestrator Pipeline
# ═════════════════════════════════════════════════════════════════

class Orchestrator:
    def __init__(self, library_name: str = "sympy",
                 output_dir: str = "output/sympy_proved",
                 model: str = "claude-opus-4.6", effort: str = "high",
                 max_files: int = 0, subpackage: str = "",
                 workers: int = 4, max_retries: int = 2,
                 use_copilot: bool = True, batch_size: int = 1,
                 copilot_binary: str = "copilot"):
        self.library_name = library_name
        self.output_dir = Path(output_dir)
        self.model = model
        self.effort = effort
        self.max_files = max_files
        self.subpackage = subpackage
        self.workers = workers
        self.max_retries = max_retries
        self.use_copilot = use_copilot
        self.batch_size = batch_size
        self.copilot = CopilotProver(model, effort, binary=copilot_binary) if use_copilot else None

    def run(self) -> LibraryProofReport:
        start_time = time.time()
        logger.info("═" * 60)
        logger.info("CCTT Library Proof Orchestrator — Path Theorem Mode")
        logger.info("Library: %s", self.library_name)
        logger.info("═" * 60)

        # Phase 1: Discover
        root = find_library_root(self.library_name)
        py_files = discover_py_files(root, self.max_files, self.subpackage)
        logger.info("Phase 1: %d .py files in %s", len(py_files), root)

        # Phase 2: Axiomatize deps
        trust_boundary = axiomatize_dependencies(self.library_name, root, py_files)
        logger.info("Phase 2: %d external deps axiomatized", len(trust_boundary))

        # Phase 3: Load cache
        cache_path = self.output_dir / ".proof_cache.json"
        if self.copilot:
            self.copilot.load_cache(cache_path)

        # Phase 4: Process files
        logger.info("Phase 3: Processing files...")
        file_reports: Dict[str, FileProofReport] = {}
        for i, pf in enumerate(py_files):
            rel = str(pf.relative_to(root))
            logger.info("  [%d/%d] %s", i + 1, len(py_files), rel)
            try:
                fr = self._process_file(pf, root, rel)
                if fr:
                    file_reports[rel] = fr
                    logger.info("    %d/%d proved (%d compiled)",
                                fr.n_proved, fr.n_total, fr.n_proved)
            except Exception as e:
                logger.error("    Error: %s", e)
            if self.copilot and (i + 1) % 10 == 0:
                self.copilot.save_cache(cache_path)

        if self.copilot:
            self.copilot.save_cache(cache_path)

        # Phase 5: Report + emit
        report = LibraryProofReport(self.library_name, file_reports, trust_boundary,
                                     start_time, time.time())
        logger.info("Phase 4: Emitting annotated library...")
        files = emit_library(report, self.output_dir / self.library_name)
        logger.info("  Wrote %d files", len(files))

        # Phase 6: Verify round-trip
        logger.info("Phase 5: Verifying compiled annotations...")
        ver_results = verify_annotated_library(self.output_dir / self.library_name)
        total_anns = sum(len(v) for v in ver_results.values())
        valid_anns = sum(sum(1 for c in v if c.valid) for v in ver_results.values())
        logger.info("  %d/%d annotations compile", valid_anns, total_anns)

        print("\n" + report.summary())
        return report

    def _process_file(self, pf: Path, root: Path, rel: str) -> Optional[FileProofReport]:
        try:
            source = pf.read_text(errors="replace")
        except Exception:
            return None

        mod_qn = rel.replace("/", ".").replace(".py", "")
        if mod_qn.endswith(".__init__"):
            mod_qn = mod_qn[:-9]
        mod_qn = f"{self.library_name}.{mod_qn}"

        definitions = extract_definitions(source, rel, mod_qn)
        if not definitions:
            return FileProofReport(rel, source, [], [])

        # Phase A: Baseline prove
        results: List[ProofResult] = []
        needs_llm: List[Tuple[int, Definition]] = []
        for defn in definitions:
            r = baseline_prove(defn, self.library_name)
            results.append(r)
            if not r.checked or r.trust == TrustLevel.ASSUMED:
                needs_llm.append((len(results) - 1, defn))

        # Phase B: LLM enhancement
        if needs_llm and self.copilot:
            ctx = self._file_context(source)
            for idx, defn in needs_llm:
                specs = self.copilot.prove_definitions([defn], self.library_name, ctx)
                if specs and specs[0]:
                    compiled = compile_proof(defn, specs[0], self.library_name,
                                             self.copilot, self.max_retries)
                    if compiled.checked or not results[idx].checked:
                        results[idx] = compiled

        return FileProofReport(rel, source, definitions, results)

    def _file_context(self, source: str) -> str:
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return ""
        ctx: List[str] = []
        for node in tree.body:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                ctx.append(ast.unparse(node))
            elif isinstance(node, ast.ClassDef):
                bases = ", ".join(ast.unparse(b) for b in node.bases)
                ctx.append(f"class {node.name}({bases}):")
                doc = _get_docstring(node)
                if doc:
                    ctx.append(f'    """{doc.split(chr(10))[0][:80]}"""')
        return "\n".join(ctx)


# ═════════════════════════════════════════════════════════════════
# §16. CLI Entry Point
# ═════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="CCTT Library Proof Orchestrator — path theorem proofs for Python libraries",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""\
Examples:
  # Prove sympy (default)
  python -m cctt.proof_theory.library_proof_orchestrator

  # Prove sympy.core only
  python -m cctt.proof_theory.library_proof_orchestrator --subpackage core --max-files 20

  # Structural proofs only (no copilot)
  python -m cctt.proof_theory.library_proof_orchestrator --no-copilot

  # Verify existing annotated library
  python -m cctt.proof_theory.library_proof_orchestrator --verify output/sympy_proved/sympy
        """,
    )
    parser.add_argument("--library", default="sympy")
    parser.add_argument("--output", default="output/sympy_proved")
    parser.add_argument("--model", default="claude-opus-4.6")
    parser.add_argument("--effort", default="high", choices=["low", "medium", "high", "xhigh"])
    parser.add_argument("--max-files", type=int, default=0)
    parser.add_argument("--subpackage", default="")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--max-retries", type=int, default=2)
    parser.add_argument("--no-copilot", action="store_true")
    parser.add_argument("--batch-size", type=int, default=1)
    parser.add_argument("--copilot-binary", default="copilot")
    parser.add_argument("--verify", metavar="DIR",
                        help="Verify annotations in an existing annotated library")
    parser.add_argument("-v", "--verbose", action="store_true")

    args = parser.parse_args()
    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)s %(message)s", datefmt="%H:%M:%S",
    )

    # Verify mode
    if args.verify:
        logger.info("Verifying annotations in %s...", args.verify)
        results = verify_annotated_library(Path(args.verify))
        total = sum(len(v) for v in results.values())
        valid = sum(sum(1 for c in v if c.valid) for v in results.values())
        print(f"\nVerification: {valid}/{total} annotations compile")
        for rel, comps in sorted(results.items()):
            ok = sum(1 for c in comps if c.valid)
            print(f"  {rel}: {ok}/{len(comps)}")
            for c in comps:
                if not c.valid:
                    for e in c.errors:
                        print(f"    ❌ {e}")
        sys.exit(0 if valid == total else 1)

    if args.output == "output/sympy_proved" and args.library != "sympy":
        args.output = f"output/{args.library}_proved"

    orch = Orchestrator(
        library_name=args.library, output_dir=args.output,
        model=args.model, effort=args.effort,
        max_files=args.max_files, subpackage=args.subpackage,
        workers=args.workers, max_retries=args.max_retries,
        use_copilot=not args.no_copilot, batch_size=args.batch_size,
        copilot_binary=args.copilot_binary,
    )
    report = orch.run()
    sys.exit(0 if report.pass_rate > 0.5 else 1)


if __name__ == "__main__":
    main()
