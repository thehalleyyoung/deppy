"""Spec Compiler — translate @guarantee annotations to C⁴ dependent types.

This module bridges deppy's surface syntax (@guarantee, @spec, assume, check)
and C⁴'s type system. A guarantee like:

    @guarantee("returns a sorted list with no duplicates")

compiles to a C⁴ Σ-type:

    Σ(result : List[int]). sorted(result) ∧ unique(result)

The verification pipeline then checks: does the code's OTerm inhabit this Σ-type?

Architecture
============
  1. Parse the NL spec text into structural + semantic predicates
  2. Compile structural predicates to Z3-checkable formulas
  3. Compile semantic predicates to oracle judgments
  4. Combine into a HybridSpec (Σ-type with both components)
  5. Generate the C⁴ proof obligation
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

from cctt.proof_theory.terms import (
    ProofTerm, Refl, Assume, CasesSplit, Ext,
    Z3Discharge, FiberDecomposition,
    var, lit, op, abstract,
)

from cctt.proof_theory.checker import (
    check_proof, VerificationResult, ProofContext,
)


# ═══════════════════════════════════════════════════════════════════
# Compiled spec types
# ═══════════════════════════════════════════════════════════════════

@dataclass
class StructuralPredicate:
    """A predicate checkable by Z3 (decidable fragment)."""
    name: str
    formula: str
    variables: Dict[str, str] = field(default_factory=dict)
    z3_fragment: str = 'qf_lia'

    def to_z3_discharge(self) -> Z3Discharge:
        return Z3Discharge(
            formula=self.formula,
            fragment=self.z3_fragment,
            variables=self.variables,
        )


@dataclass
class SemanticPredicate:
    """A predicate requiring oracle judgment (undecidable)."""
    name: str
    description: str
    confidence_threshold: float = 0.8


@dataclass
class CompiledSpec:
    """A compiled specification as a C⁴ Σ-type.

    The Σ-type is: Σ(result : ReturnType). structural ∧ semantic

    where structural predicates are Z3-checkable and semantic
    predicates require oracle judgment.
    """
    original_text: str
    return_var: str = 'result'
    return_type: str = 'Any'
    structural: List[StructuralPredicate] = field(default_factory=list)
    semantic: List[SemanticPredicate] = field(default_factory=list)
    parameters: Dict[str, str] = field(default_factory=dict)
    fiber_decomposition: Optional[Dict[str, str]] = None

    def sigma_type_str(self) -> str:
        """Human-readable Σ-type representation."""
        parts = []
        for sp in self.structural:
            parts.append(sp.formula)
        for sem in self.semantic:
            parts.append(f'oracle({sem.description!r})')
        conjunction = ' ∧ '.join(parts) if parts else '⊤'
        return f'Σ({self.return_var} : {self.return_type}). {conjunction}'

    def to_oterm(self) -> OTerm:
        """Convert the spec to an OTerm (abstract description)."""
        return OAbstract(self.sigma_type_str(), ())

    def proof_obligations(self) -> List[Dict[str, Any]]:
        """Generate the proof obligations for this spec."""
        obligations = []

        for sp in self.structural:
            obligations.append({
                'kind': 'structural',
                'name': sp.name,
                'formula': sp.formula,
                'z3_fragment': sp.z3_fragment,
                'method': 'Z3Discharge',
            })

        for sem in self.semantic:
            obligations.append({
                'kind': 'semantic',
                'name': sem.name,
                'description': sem.description,
                'threshold': sem.confidence_threshold,
                'method': 'oracle_judgment',
            })

        return obligations

    def generate_proof_skeleton(self) -> ProofTerm:
        """Generate a proof skeleton for this spec.

        Returns a proof term with Assume nodes for obligations that
        need to be filled in by the verifier.
        """
        if not self.structural and not self.semantic:
            return Refl(term=self.to_oterm())

        if len(self.structural) == 1 and not self.semantic:
            return self.structural[0].to_z3_discharge()

        # Multiple obligations → fiber decomposition
        fiber_proofs: Dict[str, ProofTerm] = {}

        for sp in self.structural:
            fiber_proofs[f'structural_{sp.name}'] = sp.to_z3_discharge()

        for sem in self.semantic:
            fiber_proofs[f'semantic_{sem.name}'] = Assume(
                label=f'oracle_{sem.name}',
                assumed_lhs=OVar(self.return_var),
                assumed_rhs=OAbstract(sem.description, ()),
            )

        return FiberDecomposition(fiber_proofs=fiber_proofs)


# ═══════════════════════════════════════════════════════════════════
# NL → Spec parser
# ═══════════════════════════════════════════════════════════════════

# Keyword → structural predicate patterns
_STRUCTURAL_PATTERNS: List[Tuple[List[str], str, str, str]] = [
    # (keywords, predicate_name, formula_template, z3_fragment)
    (['sorted', 'ascending', 'non-decreasing', 'ordered'],
     'sorted', '∀i. 0 ≤ i < len(result)-1 → result[i] ≤ result[i+1]', 'qf_lia'),
    (['descending', 'non-increasing', 'reverse sorted'],
     'descending', '∀i. 0 ≤ i < len(result)-1 → result[i] ≥ result[i+1]', 'qf_lia'),
    (['unique', 'no duplicate', 'distinct', 'no repeated'],
     'unique', '∀i,j. 0 ≤ i < j < len(result) → result[i] ≠ result[j]', 'qf_lia'),
    (['non-negative', 'positive', 'nonnegative', '>= 0', '≥ 0'],
     'nonneg', '∀i. 0 ≤ i < len(result) → result[i] ≥ 0', 'qf_lia'),
    (['non-empty', 'nonempty', 'not empty'],
     'nonempty', 'len(result) > 0', 'qf_lia'),
    (['same length', 'same size', 'preserves length'],
     'same_length', 'len(result) = len(input)', 'qf_lia'),
    (['permutation', 'rearrangement', 'same elements'],
     'permutation', 'multiset(result) = multiset(input)', 'qf_lia'),
    (['idempotent', 'applying twice'],
     'idempotent', 'f(f(x)) = f(x)', 'qf_uf'),
    (['monotonic', 'monotone', 'order preserving'],
     'monotonic', '∀a,b. a ≤ b → f(a) ≤ f(b)', 'qf_lia'),
    (['bounded', 'within range', 'in range'],
     'bounded', 'lo ≤ result ≤ hi', 'qf_lia'),
]

# Semantic predicate keywords (not Z3-decidable)
_SEMANTIC_PATTERNS: List[Tuple[List[str], str]] = [
    (['correct', 'valid', 'accurate'], 'correctness'),
    (['optimal', 'minimum', 'maximum', 'best'], 'optimality'),
    (['equivalent', 'same behavior', 'bisimilar'], 'equivalence'),
    (['safe', 'secure', 'no vulnerability'], 'safety'),
    (['terminating', 'always terminates', 'halts'], 'termination'),
    (['efficient', 'fast', 'O(n log n)', 'linear time'], 'efficiency'),
    (['readable', 'clean', 'well-structured'], 'readability'),
]


def parse_guarantee(text: str) -> CompiledSpec:
    """Parse a @guarantee text into a CompiledSpec.

    Analyzes the natural language specification and decomposes it
    into structural (Z3-decidable) and semantic (oracle) predicates.

    Parameters
    ----------
    text : str
        The guarantee text, e.g., "returns a sorted list with no duplicates".

    Returns
    -------
    CompiledSpec
        The compiled specification.
    """
    text_lower = text.lower().strip()
    spec = CompiledSpec(original_text=text)

    # Detect return type hints
    spec.return_type = _infer_return_type(text_lower)

    # Match structural predicates
    for keywords, name, formula, fragment in _STRUCTURAL_PATTERNS:
        if any(kw in text_lower for kw in keywords):
            spec.structural.append(StructuralPredicate(
                name=name,
                formula=formula,
                z3_fragment=fragment,
            ))

    # Match semantic predicates
    for keywords, name in _SEMANTIC_PATTERNS:
        if any(kw in text_lower for kw in keywords):
            spec.semantic.append(SemanticPredicate(
                name=name,
                description=text,
            ))

    # If no patterns matched, treat the whole thing as semantic
    if not spec.structural and not spec.semantic:
        spec.semantic.append(SemanticPredicate(
            name='full_spec',
            description=text,
        ))

    return spec


def _infer_return_type(text: str) -> str:
    """Infer the return type from natural language."""
    if any(w in text for w in ['list', 'array', 'sequence', 'elements']):
        return 'List'
    if any(w in text for w in ['dict', 'dictionary', 'mapping']):
        return 'Dict'
    if any(w in text for w in ['set', 'unique set']):
        return 'Set'
    if any(w in text for w in ['number', 'integer', 'int', 'count']):
        return 'int'
    if any(w in text for w in ['string', 'str', 'text']):
        return 'str'
    if any(w in text for w in ['bool', 'boolean', 'true', 'false']):
        return 'bool'
    if any(w in text for w in ['float', 'decimal', 'real']):
        return 'float'
    return 'Any'


# ═══════════════════════════════════════════════════════════════════
# Spec → C⁴ type compilation
# ═══════════════════════════════════════════════════════════════════

def compile_guarantee_to_type(
    guarantee_text: str,
    function_name: str = 'f',
    parameter_types: Optional[Dict[str, str]] = None,
) -> CompiledSpec:
    """Compile a @guarantee annotation to a C⁴ Σ-type.

    This is the main entry point for the spec compiler. It takes
    a guarantee text and produces a compiled specification that
    can be used by the verification pipeline.

    Parameters
    ----------
    guarantee_text : str
        The @guarantee text.
    function_name : str
        Name of the function being specified.
    parameter_types : dict, optional
        Parameter name → type mappings.

    Returns
    -------
    CompiledSpec
        The compiled specification with proof obligations.
    """
    spec = parse_guarantee(guarantee_text)
    spec.parameters = parameter_types or {}
    return spec


def compile_assume_to_precondition(
    assume_text: str,
) -> CompiledSpec:
    """Compile an assume() call to a C⁴ precondition type."""
    spec = parse_guarantee(assume_text)
    # Preconditions are the caller's proof obligation
    return spec


def compile_check_to_assertion(
    check_text: str,
) -> CompiledSpec:
    """Compile a check() call to a C⁴ internal invariant."""
    spec = parse_guarantee(check_text)
    return spec


# ═══════════════════════════════════════════════════════════════════
# Integration: verify code against compiled spec
# ═══════════════════════════════════════════════════════════════════

def verify_against_spec(
    code_oterm: OTerm,
    guarantee_text: str,
    proof: Optional[ProofTerm] = None,
    ctx: Optional[ProofContext] = None,
) -> Tuple[CompiledSpec, VerificationResult]:
    """Verify that a code OTerm satisfies a guarantee.

    Parameters
    ----------
    code_oterm : OTerm
        The denotational semantics of the code.
    guarantee_text : str
        The @guarantee text.
    proof : ProofTerm, optional
        An explicit proof. If None, a skeleton is generated.
    ctx : ProofContext, optional
        Proof context.

    Returns
    -------
    (CompiledSpec, VerificationResult)
    """
    spec = compile_guarantee_to_type(guarantee_text)
    spec_oterm = spec.to_oterm()

    if proof is None:
        proof = spec.generate_proof_skeleton()

    result = check_proof(proof, code_oterm, spec_oterm, ctx)
    return spec, result


# ═══════════════════════════════════════════════════════════════════
# Pretty printing
# ═══════════════════════════════════════════════════════════════════

def spec_to_markdown(spec: CompiledSpec) -> str:
    """Render a compiled spec as Markdown documentation."""
    lines = [
        f'## Specification: {spec.original_text}',
        '',
        f'**Σ-type**: `{spec.sigma_type_str()}`',
        '',
        f'**Return type**: `{spec.return_type}`',
        '',
    ]

    if spec.structural:
        lines.append('### Structural Predicates (Z3-decidable)')
        for sp in spec.structural:
            lines.append(f'- **{sp.name}**: `{sp.formula}` [{sp.z3_fragment}]')
        lines.append('')

    if spec.semantic:
        lines.append('### Semantic Predicates (oracle-judged)')
        for sem in spec.semantic:
            lines.append(f'- **{sem.name}**: {sem.description} '
                         f'(threshold: {sem.confidence_threshold})')
        lines.append('')

    obligations = spec.proof_obligations()
    if obligations:
        lines.append('### Proof Obligations')
        for i, obl in enumerate(obligations, 1):
            lines.append(f'{i}. [{obl["kind"]}] **{obl["name"]}**: {obl.get("formula", obl.get("description", ""))}')
        lines.append('')

    return '\n'.join(lines)
