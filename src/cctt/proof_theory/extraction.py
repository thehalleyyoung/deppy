"""C⁴ Code Extraction — extract executable Python from verified proofs.

This module implements bidirectional code extraction from C⁴ proof terms.
Unlike F*'s extraction (which targets OCaml/F#/C), C⁴ extraction targets
Python — the same language as the verification source — and automatically
attaches @guarantee annotations from the proof certificate.

Key advantages over F* extraction:
  1. Same-language: extracted code is Python, matching the verification target.
  2. Bidirectional: proof → code (forward) and code → proof obligation (backward).
  3. Direct: OTerm denotational semantics compile straight to Python AST.
  4. Trust-tracked: extracted code carries its verification certificate.

Extraction Strategies
=====================
  - Σ-type projection: proof of Σ(x: Code). spec(x) extracts to x.
  - NatInduction → recursive or iterative Python function.
  - Simulation → extract one side of the bisimulation relation.
  - CechGluing → dispatch function over fibers.
  - AbstractionRefinement → extract the concrete refinement.
  - LoopInvariant → extract a while-loop with the invariant as assert.
"""
from __future__ import annotations

import textwrap
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Set, Tuple

from cctt.denotation import (
    OTerm, OVar, OLit, OOp, OFold, OCase, OFix, OSeq, ODict,
    OUnknown, OQuotient, OAbstract, OLam, OMap, OCatch,
)

from cctt.proof_theory.terms import (
    ProofTerm,
    Refl, Sym, Trans, Cong,
    Beta, Delta, Eta,
    NatInduction, ListInduction, WellFoundedInduction,
    AxiomApp, MathlibTheorem,
    LoopInvariant, Simulation, AbstractionRefinement,
    CommDiagram, FunctorMap,
    Z3Discharge,
    FiberDecomposition, CechGluing,
    Assume, Cut, LetProof,
    CasesSplit, Ext,
    Rewrite, RewriteChain,
    ArithmeticSimp, ListSimp, Definitional,
    FiberRestrict, Descent, PathCompose, MathLibAxiom, FiberwiseUnivalence,
    normalize_term, free_vars,
)

from cctt.proof_theory.checker import (
    check_proof, VerificationResult, ProofContext,
)


# ═══════════════════════════════════════════════════════════════════
# Trust / certificate types
# ═══════════════════════════════════════════════════════════════════

@dataclass
class ExtractionCertificate:
    """Certificate attached to extracted code.

    Records what was proved and how, so downstream consumers
    can inspect the trust level without re-verifying.
    """
    proof_strategy: str
    lhs_description: str
    rhs_description: str
    verification_valid: bool
    assumptions_used: List[str] = field(default_factory=list)
    z3_calls: int = 0
    proof_depth: int = 0

    def trust_level(self) -> str:
        if not self.verification_valid:
            return 'UNTRUSTED'
        if self.assumptions_used:
            return 'CONDITIONAL'
        if self.z3_calls > 0:
            return 'Z3_PROVEN'
        return 'STRUCTURALLY_VERIFIED'


@dataclass
class ExtractedCode:
    """Result of code extraction from a proof.

    Contains the executable Python source together with its
    certificate and the @guarantee annotation to attach.
    """
    source: str
    function_name: str
    guarantee_text: str
    certificate: ExtractionCertificate
    parameters: List[str] = field(default_factory=list)
    return_type: str = 'Any'

    def with_guarantee(self) -> str:
        """Return source with a @guarantee decorator."""
        lines = [
            'from deppy.hybrid import guarantee',
            '',
            f'@guarantee("{self.guarantee_text}")',
            self.source,
        ]
        return '\n'.join(lines)

    def with_certificate_comment(self) -> str:
        """Return source with certificate as docstring comment."""
        cert = self.certificate
        header = textwrap.dedent(f'''\
            # ── Extraction Certificate ──
            # Strategy:    {cert.proof_strategy}
            # Trust:       {cert.trust_level()}
            # Assumptions: {cert.assumptions_used or "none"}
            # Z3 calls:    {cert.z3_calls}
            # Proof depth: {cert.proof_depth}
        ''')
        return header + '\n' + self.with_guarantee()


# ═══════════════════════════════════════════════════════════════════
# OTerm → Python source compilation
# ═══════════════════════════════════════════════════════════════════

# Operator mapping from OTerm names to Python operators
_OP_MAP = {
    '+': '+', '-': '-', '*': '*', '/': '/', '//': '//',
    '%': '%', '**': '**',
    '==': '==', '!=': '!=', '<': '<', '>': '>', '<=': '<=', '>=': '>=',
    'and': 'and', 'or': 'or', 'not': 'not',
    'min': 'min', 'max': 'max', 'abs': 'abs', 'len': 'len',
    'append': '.append', 'extend': '.extend',
}


def oterm_to_python(term: OTerm, indent: int = 0) -> str:
    """Compile an OTerm to executable Python expression/statement.

    This is the core of extraction — it turns the denotational semantics
    back into concrete Python syntax.
    """
    pad = '    ' * indent

    if isinstance(term, OVar):
        return term.name

    if isinstance(term, OLit):
        return repr(term.value)

    if isinstance(term, OOp):
        name = term.name
        args = term.args

        # Unary operators
        if name == 'not' and len(args) == 1:
            return f'not {oterm_to_python(args[0])}'
        if name in ('abs', 'len', 'sorted', 'reversed', 'list', 'set', 'tuple'):
            arg_strs = ', '.join(oterm_to_python(a) for a in args)
            return f'{name}({arg_strs})'
        if name in ('min', 'max') and len(args) >= 2:
            arg_strs = ', '.join(oterm_to_python(a) for a in args)
            return f'{name}({arg_strs})'
        if name == 'range':
            arg_strs = ', '.join(oterm_to_python(a) for a in args)
            return f'range({arg_strs})'
        if name == 'subscript' and len(args) == 2:
            return f'{oterm_to_python(args[0])}[{oterm_to_python(args[1])}]'

        # Binary operators
        if name in _OP_MAP and len(args) == 2:
            op = _OP_MAP[name]
            left = oterm_to_python(args[0])
            right = oterm_to_python(args[1])
            return f'({left} {op} {right})'

        # Function call fallback
        if len(args) > 0:
            arg_strs = ', '.join(oterm_to_python(a) for a in args)
            return f'{name}({arg_strs})'
        return name

    if isinstance(term, OCase):
        cond = oterm_to_python(term.test)
        then = oterm_to_python(term.true_branch)
        else_ = oterm_to_python(term.false_branch)
        return f'({then} if {cond} else {else_})'

    if isinstance(term, OLam):
        body = oterm_to_python(term.body)
        return f'lambda {", ".join(term.params)}: {body}'

    if isinstance(term, OFix):
        # Recursive function — extract as a def
        body = oterm_to_python(term.body, indent)
        return f'{term.name}({body})'

    if isinstance(term, OFold):
        init = oterm_to_python(term.init)
        coll = oterm_to_python(term.collection)
        return f'functools.reduce({term.op_name}, {coll}, {init})'

    if isinstance(term, OSeq):
        parts = [oterm_to_python(s, indent) for s in term.elements]
        return '; '.join(parts)

    if isinstance(term, ODict):
        entries = ', '.join(
            f'{oterm_to_python(k)}: {oterm_to_python(v)}'
            for k, v in term.pairs
        )
        return '{' + entries + '}'

    if isinstance(term, OAbstract):
        return f'# abstract: {term.spec}'

    if isinstance(term, OUnknown):
        return f'# unknown: {term.desc}'

    # Fallback
    return f'# <OTerm: {type(term).__name__}>'


def oterm_to_function(term: OTerm, name: str, params: Optional[List[str]] = None) -> str:
    """Compile an OTerm to a complete Python function definition."""
    if params is None:
        params = sorted(free_vars(term))
    param_str = ', '.join(params)

    if isinstance(term, OFix):
        # Recursive function
        body_params = sorted(free_vars(term.body) - {term.name})
        if not params:
            params = body_params
            param_str = ', '.join(params)
        body = oterm_to_python(term.body)
        return f'def {name}({param_str}):\n    return {body}'

    if isinstance(term, OFold):
        init = oterm_to_python(term.init)
        coll = oterm_to_python(term.collection)
        lines = [
            f'def {name}({param_str}):',
            f'    return functools.reduce({term.op_name}, {coll}, {init})',
        ]
        return '\n'.join(lines)

    if isinstance(term, OCase):
        cond = oterm_to_python(term.test)
        then = oterm_to_python(term.true_branch)
        else_ = oterm_to_python(term.false_branch)
        lines = [
            f'def {name}({param_str}):',
            f'    if {cond}:',
            f'        return {then}',
            f'    else:',
            f'        return {else_}',
        ]
        return '\n'.join(lines)

    # Generic
    body = oterm_to_python(term)
    return f'def {name}({param_str}):\n    return {body}'


# ═══════════════════════════════════════════════════════════════════
# Proof → Code extraction engine
# ═══════════════════════════════════════════════════════════════════

def extract_from_proof(
    proof: ProofTerm,
    lhs: OTerm,
    rhs: OTerm,
    function_name: str = 'extracted',
    params: Optional[List[str]] = None,
    prefer: str = 'lhs',
    ctx: Optional[ProofContext] = None,
) -> ExtractedCode:
    """Extract executable Python from a verified proof.

    This is the main entry point. Given a proof that lhs ≡ rhs,
    extract one side as a Python function and attach its certificate.

    Parameters
    ----------
    proof : ProofTerm
        The verified proof term.
    lhs, rhs : OTerm
        The two equivalent OTerms.
    function_name : str
        Name for the extracted function.
    params : list of str, optional
        Parameter names. Inferred from free variables if not given.
    prefer : 'lhs' or 'rhs'
        Which side to extract (the other is the spec).
    ctx : ProofContext, optional
        Context for verification.

    Returns
    -------
    ExtractedCode
        The extracted function with certificate.
    """
    # Verify the proof first
    result = check_proof(proof, lhs, rhs, ctx)

    # Choose which side to extract
    impl_term = lhs if prefer == 'lhs' else rhs
    spec_term = rhs if prefer == 'lhs' else lhs

    # Build the guarantee text from the spec
    guarantee_text = _spec_to_guarantee(spec_term, impl_term, proof)

    # Extract using strategy-specific logic
    source = _extract_by_strategy(proof, impl_term, function_name, params)

    # Build certificate
    cert = ExtractionCertificate(
        proof_strategy=type(proof).__name__,
        lhs_description=lhs.canon() if hasattr(lhs, 'canon') else str(lhs),
        rhs_description=rhs.canon() if hasattr(rhs, 'canon') else str(rhs),
        verification_valid=result.valid,
        assumptions_used=result.assumptions,
        z3_calls=result.z3_calls,
        proof_depth=result.proof_depth,
    )

    if params is None:
        params = sorted(free_vars(impl_term))

    return ExtractedCode(
        source=source,
        function_name=function_name,
        guarantee_text=guarantee_text,
        certificate=cert,
        parameters=params,
    )


def _spec_to_guarantee(spec: OTerm, impl: OTerm, proof: ProofTerm) -> str:
    """Generate a human-readable guarantee string from a spec OTerm."""
    strategy = type(proof).__name__

    if isinstance(spec, OAbstract):
        return spec.spec

    spec_str = spec.canon() if hasattr(spec, 'canon') else str(spec)
    impl_str = impl.canon() if hasattr(impl, 'canon') else str(impl)

    if strategy == 'NatInduction':
        return f'equivalent to {spec_str} by induction'
    if strategy == 'Simulation':
        return f'bisimilar to {spec_str}'
    if strategy == 'AbstractionRefinement':
        return f'refines specification {spec_str}'
    if strategy == 'LoopInvariant':
        return f'satisfies loop invariant, equivalent to {spec_str}'

    return f'proven equivalent to {spec_str}'


def _extract_by_strategy(
    proof: ProofTerm,
    impl: OTerm,
    name: str,
    params: Optional[List[str]],
) -> str:
    """Choose extraction strategy based on proof structure."""

    if isinstance(proof, NatInduction):
        return _extract_nat_induction(proof, impl, name, params)

    if isinstance(proof, ListInduction):
        return _extract_list_induction(proof, impl, name, params)

    if isinstance(proof, Simulation):
        return _extract_simulation(proof, impl, name, params)

    if isinstance(proof, (CechGluing, FiberDecomposition)):
        return _extract_fiber_dispatch(proof, impl, name, params)

    if isinstance(proof, LoopInvariant):
        return _extract_loop(proof, impl, name, params)

    if isinstance(proof, AbstractionRefinement):
        return _extract_abstraction_refinement(proof, impl, name, params)

    if isinstance(proof, CasesSplit):
        return _extract_cases(proof, impl, name, params)

    # Default: direct OTerm compilation
    return oterm_to_function(impl, name, params)


# ─── Strategy-specific extractors ────────────────────────────────

def _extract_nat_induction(
    proof: NatInduction,
    impl: OTerm,
    name: str,
    params: Optional[List[str]],
) -> str:
    """Extract iterative Python from a NatInduction proof.

    NatInduction proofs naturally yield either recursive or iterative code.
    We prefer iterative (loop) form for efficiency.
    """
    var = proof.variable
    if params is None:
        params = sorted(free_vars(impl))
    if var not in params:
        params = [var] + params
    param_str = ', '.join(params)

    # Try to extract base value and step from the impl OTerm
    base_val = oterm_to_python(proof.base_value) if hasattr(proof, 'base_value') else '0'

    # Build iterative version
    lines = [
        f'def {name}({param_str}):',
        f'    """Extracted from NatInduction proof over {var}."""',
        f'    result = {_extract_base_value(impl)}',
        f'    for _i in range({base_val}, {var}):',
        f'        result = _step(result, _i)  # inductive step',
        f'    return result',
    ]

    # If the implementation is directly compilable, prefer that
    direct = oterm_to_function(impl, name, params)
    if 'OTerm' not in direct and '# <' not in direct:
        return direct

    return '\n'.join(lines)


def _extract_list_induction(
    proof: ListInduction,
    impl: OTerm,
    name: str,
    params: Optional[List[str]],
) -> str:
    """Extract fold-based Python from a ListInduction proof."""
    var = proof.variable
    if params is None:
        params = sorted(free_vars(impl))
    if var not in params:
        params = [var] + params
    param_str = ', '.join(params)

    direct = oterm_to_function(impl, name, params)
    if 'OTerm' not in direct and '# <' not in direct:
        return direct

    lines = [
        f'def {name}({param_str}):',
        f'    """Extracted from ListInduction proof over {var}."""',
        f'    result = []  # nil case',
        f'    for {proof.elem_var} in {var}:',
        f'        result = _cons_step(result, {proof.elem_var})  # cons case',
        f'    return result',
    ]
    return '\n'.join(lines)


def _extract_simulation(
    proof: Simulation,
    impl: OTerm,
    name: str,
    params: Optional[List[str]],
) -> str:
    """Extract from a Simulation proof — use the concrete implementation side."""
    direct = oterm_to_function(impl, name, params)
    if 'OTerm' not in direct and '# <' not in direct:
        return direct

    if params is None:
        params = sorted(free_vars(impl))
    param_str = ', '.join(params)

    lines = [
        f'def {name}({param_str}):',
        f'    """Extracted from Simulation proof (relation: {proof.relation})."""',
        f'    {oterm_to_python(impl)}',
    ]
    return '\n'.join(lines)


def _extract_fiber_dispatch(
    proof: ProofTerm,
    impl: OTerm,
    name: str,
    params: Optional[List[str]],
) -> str:
    """Extract a dispatch function from CechGluing or FiberDecomposition."""
    if params is None:
        params = sorted(free_vars(impl))
    param_str = ', '.join(params)

    if isinstance(proof, FiberDecomposition):
        fibers = list(proof.fiber_proofs.keys())
    elif isinstance(proof, CechGluing):
        fibers = [f'fiber_{i}' for i in range(len(proof.local_proofs))]
    else:
        fibers = ['default']

    lines = [
        f'def {name}({param_str}):',
        f'    """Extracted from fiber decomposition ({len(fibers)} fibers)."""',
    ]

    for i, fib in enumerate(fibers):
        cond = 'if' if i == 0 else 'elif'
        lines.append(f'    {cond} _fiber == {repr(fib)}:')
        lines.append(f'        return _handle_{fib}({param_str})')

    lines.append(f'    else:')
    lines.append(f'        raise ValueError(f"Unknown fiber: {{_fiber}}")')
    return '\n'.join(lines)


def _extract_loop(
    proof: LoopInvariant,
    impl: OTerm,
    name: str,
    params: Optional[List[str]],
) -> str:
    """Extract a while-loop from a LoopInvariant proof."""
    direct = oterm_to_function(impl, name, params)
    if 'OTerm' not in direct and '# <' not in direct:
        return direct

    if params is None:
        params = sorted(free_vars(impl))
    param_str = ', '.join(params)

    lines = [
        f'def {name}({param_str}):',
        f'    """Extracted from LoopInvariant proof.',
        f'',
        f'    Invariant: {proof.invariant}',
        f'    """',
        f'    # Initialization (invariant established)',
        f'    state = _init({param_str})',
        f'    while not _done(state):',
        f'        assert {repr(proof.invariant)}  # loop invariant',
        f'        state = _step(state)',
        f'    return _output(state)',
    ]
    return '\n'.join(lines)


def _extract_abstraction_refinement(
    proof: AbstractionRefinement,
    impl: OTerm,
    name: str,
    params: Optional[List[str]],
) -> str:
    """Extract from an AbstractionRefinement proof."""
    direct = oterm_to_function(impl, name, params)
    if 'OTerm' not in direct and '# <' not in direct:
        return direct

    if params is None:
        params = sorted(free_vars(impl))
    param_str = ', '.join(params)

    lines = [
        f'def {name}({param_str}):',
        f'    """Extracted from AbstractionRefinement proof.',
        f'    Refines spec: {proof.spec_name}',
        f'    """',
        f'    return {oterm_to_python(impl)}',
    ]
    return '\n'.join(lines)


def _extract_cases(
    proof: CasesSplit,
    impl: OTerm,
    name: str,
    params: Optional[List[str]],
) -> str:
    """Extract a multi-branch function from CasesSplit."""
    direct = oterm_to_function(impl, name, params)
    if 'OTerm' not in direct and '# <' not in direct:
        return direct

    if params is None:
        params = sorted(free_vars(impl))
    param_str = ', '.join(params)

    disc = oterm_to_python(proof.discriminant)
    lines = [
        f'def {name}({param_str}):',
        f'    """Extracted from CasesSplit on {disc}."""',
        f'    _disc = {disc}',
    ]

    for i, (label, _) in enumerate(proof.cases.items()):
        cond = 'if' if i == 0 else 'elif'
        lines.append(f'    {cond} _disc == {repr(label)}:')
        lines.append(f'        return _handle_{label}({param_str})')

    return '\n'.join(lines)


def _extract_base_value(term: OTerm) -> str:
    """Try to find the base case value from an OTerm."""
    if isinstance(term, OCase):
        return oterm_to_python(term.true_branch)
    if isinstance(term, OFix) and isinstance(term.body, OCase):
        return oterm_to_python(term.body.true_branch)
    return '0'


# ═══════════════════════════════════════════════════════════════════
# Bidirectional extraction — the key advantage over F*
# ═══════════════════════════════════════════════════════════════════

def code_to_proof_obligation(
    source: str,
    guarantee_text: str,
    function_name: Optional[str] = None,
) -> Dict[str, Any]:
    """Backward extraction: Python code + guarantee → proof obligation.

    This is the reverse of extract_from_proof: given Python code with
    a @guarantee annotation, produce the C⁴ proof obligation that
    must be discharged.

    Returns a dict describing the obligation:
      - 'goal': the type to inhabit (Σ-type description)
      - 'structural': Z3-checkable component
      - 'semantic': oracle-judgeable component
      - 'suggested_strategy': which proof strategy to try
    """
    obligation = {
        'source': source,
        'guarantee': guarantee_text,
        'function_name': function_name or '_unknown',
        'goal': f'Σ(code: Impl). ({guarantee_text})(code)',
        'structural': [],
        'semantic': [],
        'suggested_strategy': 'auto',
    }

    gt = guarantee_text.lower()

    # Classify the guarantee into structural vs semantic
    if any(kw in gt for kw in ['sorted', 'ascending', 'descending', 'ordered']):
        obligation['structural'].append('∀i. result[i] ≤ result[i+1]')
        obligation['suggested_strategy'] = 'LoopInvariant'
    if any(kw in gt for kw in ['unique', 'no duplicate', 'distinct']):
        obligation['structural'].append('∀i,j. i≠j → result[i] ≠ result[j]')
    if any(kw in gt for kw in ['equivalent', 'same as', 'equal']):
        obligation['semantic'].append(f'behavioral equivalence: {guarantee_text}')
        obligation['suggested_strategy'] = 'Simulation'
    if any(kw in gt for kw in ['length', 'size', 'count']):
        obligation['structural'].append('len(result) satisfies constraint')
    if any(kw in gt for kw in ['correct', 'valid', 'satisfies']):
        obligation['semantic'].append(f'semantic correctness: {guarantee_text}')

    if not obligation['structural'] and not obligation['semantic']:
        obligation['semantic'].append(guarantee_text)

    return obligation


# ═══════════════════════════════════════════════════════════════════
# @verified decorator — attaches proof certificate to extracted code
# ═══════════════════════════════════════════════════════════════════

def verified(
    proof: ProofTerm,
    lhs: OTerm,
    rhs: OTerm,
    ctx: Optional[ProofContext] = None,
) -> Callable:
    """Decorator that attaches a verification certificate to a function.

    Usage::

        @verified(CORRECTNESS_PROOF, IMPL_OTERM, SPEC_OTERM)
        def my_function(n):
            ...

    The decorated function gains attributes:
      - _c4_certificate: ExtractionCertificate
      - _c4_verified: bool
      - _c4_proof_strategy: str
    """
    result = check_proof(proof, lhs, rhs, ctx)
    cert = ExtractionCertificate(
        proof_strategy=type(proof).__name__,
        lhs_description=lhs.canon() if hasattr(lhs, 'canon') else str(lhs),
        rhs_description=rhs.canon() if hasattr(rhs, 'canon') else str(rhs),
        verification_valid=result.valid,
        assumptions_used=result.assumptions,
        z3_calls=result.z3_calls,
        proof_depth=result.proof_depth,
    )

    def decorator(fn: Callable) -> Callable:
        fn._c4_certificate = cert  # type: ignore[attr-defined]
        fn._c4_verified = result.valid  # type: ignore[attr-defined]
        fn._c4_proof_strategy = type(proof).__name__  # type: ignore[attr-defined]
        return fn

    return decorator


# ═══════════════════════════════════════════════════════════════════
# Batch extraction from ProofDocuments
# ═══════════════════════════════════════════════════════════════════

def extract_from_document(
    doc: Any,  # ProofDocument
    prefer: str = 'lhs',
    function_name: Optional[str] = None,
) -> ExtractedCode:
    """Extract code from a ProofDocument.

    Convenience wrapper around extract_from_proof that takes a
    ProofDocument (from serialization.py) and extracts code from it.
    """
    name = function_name or doc.name.replace(' ', '_').replace('-', '_').lower()
    return extract_from_proof(
        proof=doc.proof,
        lhs=doc.lhs,
        rhs=doc.rhs,
        function_name=name,
        prefer=prefer,
    )


def extract_all(
    docs: List[Any],  # List[ProofDocument]
    prefer: str = 'lhs',
) -> Dict[str, ExtractedCode]:
    """Extract code from multiple ProofDocuments."""
    results = {}
    for doc in docs:
        name = doc.name.replace(' ', '_').replace('-', '_').lower()
        try:
            results[name] = extract_from_document(doc, prefer=prefer)
        except Exception as e:
            results[name] = ExtractedCode(
                source=f'# Extraction failed: {e}',
                function_name=name,
                guarantee_text=f'extraction failed for {doc.name}',
                certificate=ExtractionCertificate(
                    proof_strategy='FAILED',
                    lhs_description='',
                    rhs_description='',
                    verification_valid=False,
                ),
            )
    return results
